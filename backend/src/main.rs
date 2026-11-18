//! The executable server layer: glue between the model, the wire codec and rocket.
//!
//! Part 1 of this layer is pure helpers: a std-only IMF `Date` header
//! (`http_date`), the from-output map of spec/Interface.agda taking a model
//! `Result` to a wire `ApiResponse` (`to_output`), cryptographic `u64`
//! randomness from `/dev/urandom` (`random_u64`) and the spec's fresh-id sampler
//! (`sample_id`).  `to_http` lifts a rendered `WireResponse` into a rocket
//! `Response`, headers in the order the spec fixes.  The routes, state and
//! launch come in part 2; nothing here talks to a server or to the DB.
use formal_twitter::db::{apply, init_or_open, load_world};
use formal_twitter::model::{Command, Result, World, empty_world, step, used_pid, used_sid};
use formal_twitter::wire::{
	ApiResponse, WireError, WireResponse, parse_action, respond, to_command,
};
use rocket::Response;
use rocket::State;
use rocket::data::Capped;
use rocket::http::{Header, Status};
use rocket::launch;
use rocket::post;
use rocket::request::Request;
use rocket::response::Responder;
use rocket::routes;
use std::io::Cursor;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

#[doc = "Two-digit decimal, zero-padded (as the IMF-date needs dd, HH, mm, ss)."]
fn two(v: u64) -> String {
	if v < 10 {
		"0".to_string() + &v.to_string()
	} else {
		v.to_string()
	}
}

#[doc = "Gregorian leap-year test."]
fn leap(y: u64) -> bool {
	y.is_multiple_of(4) && (!y.is_multiple_of(100) || y.is_multiple_of(400))
}

#[doc = "The current moment rendered as an IMF date: \"Thu, 01 Jan 1970 00:00:00 GMT\"."]
pub fn http_date() -> String {
	let secs: u64 = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.unwrap_or_default()
		.as_secs();
	let day: u64 = secs / 86_400;
	let rest: u64 = secs % 86_400;
	let hour: u64 = rest / 3_600;
	let minute: u64 = (rest % 3_600) / 60;
	let second: u64 = rest % 60;
	let mut year: u64 = 1_970;
	let mut year_start: u64 = 0;
	loop {
		let len: u64 = if leap(year) { 366 } else { 365 };
		if day - year_start < len {
			break;
		}
		year += 1;
		year_start += len;
	}
	let month_len: [u64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
	let month_names: [&str; 12] = [
		"Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
	];
	let day_of_year: u64 = day - year_start;
	let mut month: u64 = 0;
	let mut month_start: u64 = 0;
	loop {
		let len: u64 = month_len[month as usize] + (if month == 1 && leap(year) { 1 } else { 0 });
		if day_of_year - month_start < len {
			break;
		}
		month += 1;
		month_start += len;
	}
	let day_of_month: u64 = day_of_year - month_start + 1;
	// 1970-01-01 (day 0) was a Thursday, so day counts step forward from Thu.
	let weekdays: [&str; 7] = ["Thu", "Fri", "Sat", "Sun", "Mon", "Tue", "Wed"];
	format!(
		"{}, {} {} {} {}:{}:{} GMT",
		weekdays[(day % 7) as usize],
		two(day_of_month),
		month_names[month as usize],
		year,
		two(hour),
		two(minute),
		two(second)
	)
}

#[doc = "from-output of Interface.agda: a model Result rendered as a wire ApiResponse."]
pub fn to_output(r: Result) -> ApiResponse {
	match r {
		Result::Success => ApiResponse::Ok,
		Result::Denied => ApiResponse::PermissionError,
		Result::Expired => ApiResponse::OutdatedLoginToken,
		Result::LoginFailed => ApiResponse::LoginError,
		Result::SignupFailed => ApiResponse::SignupError,
		Result::ReturnedTimeline(ids) => ApiResponse::Timeline(ids),
		Result::IssuedSession(sid) => ApiResponse::SessionToken(sid),
		Result::CreatedPost(pid) => ApiResponse::TweetId(pid),
		Result::ReturnedPost(text, author, pid, ats) => ApiResponse::Tweet(text, author, pid, ats),
	}
}

#[doc = "Eight bytes read from /dev/urandom as a big-endian u64; zero on any failure."]
pub fn random_u64() -> u64 {
	// Qualified std paths keep the top-level import list minimal.
	match std::fs::File::open("/dev/urandom") {
		Err(_) => 0,
		Ok(mut file) => {
			let mut bytes: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
			if std::io::Read::read_exact(&mut file, &mut bytes).is_err() {
				0
			} else {
				u64::from_be_bytes(bytes)
			}
		}
	}
}

#[doc = "The spec's fresh-id sampler: loop until a nonzero id is free."]
pub fn sample_id(w: World, taken: fn(&World, u64) -> bool) -> u64 {
	loop {
		let r = random_u64();
		if r != 0 && !taken(&w, r) {
			return r;
		}
	}
}

#[doc = "Lift a rendered WireResponse into a rocket Response, headers in the order the spec fixes."]
pub fn to_http(reply: WireResponse) -> Response<'static> {
	// Fold the spec's wire headers, in order, onto an empty rocket Response.
	let mut built = Response::build();
	for (name, value) in reply.headers {
		built.header(Header::new(name, value));
	}
	// All respond codes are valid; None falls back to Status::new(code).
	match Status::from_code(reply.status_code) {
		Some(status) => built.status(status),
		None => built.status(Status::new(reply.status_code)),
	};
	// The body is a fixed-size cursor over the rendered octets.
	built.sized_body(reply.body.len(), Cursor::new(reply.body));
	built.finalize()
}

#[doc = "Server state: the current world plus the DB path the world came from."]
pub struct Server {
	pub world: World,
	pub db_path: String,
}

#[doc = "Parse failures answer with the spec's 403 access_denied shape: the Interface"]
#[doc = "grammar is total, so a malformed body is treated as a denied request."]
pub fn wire_error(e: WireError) -> WireResponse {
	_ = e;
	respond(ApiResponse::PermissionError, http_date())
}

#[doc = "A pre-rendered rocket response lifted into a handler return type."]
pub struct Served {
	pub response: Response<'static>,
}

#[doc = "The trivial responder: always Ok with the pre-rendered response."]
impl<'r> Responder<'r, 'static> for Served {
	// The request is irrelevant; the response is fully rendered.
	fn respond_to(self, _req: &'r Request<'_>) -> rocket::response::Result<'static> {
		Ok(self.response)
	}
}

#[doc = "The one handler behind all 13 routes: parse, step, persist, render."]
pub fn serve(path: String, body: Capped<String>, state: &Mutex<Server>) -> Served {
	// Parse first so malformed bodies never touch the world.
	let command: Command = match parse_action(path.as_str(), body.value.as_bytes()) {
		Err(e) => {
			return Served {
				response: to_http(wire_error(e)),
			};
		}
		Ok(action) => to_command(action),
	};
	let mut locked = state.lock().unwrap();
	// A private copy of the world so step and apply see before/after values.
	let before: World = locked.world.clone();
	// The spec's fresh-id sampler, run under the lock.
	let fresh_pid: u64 = sample_id(before.clone(), used_pid);
	let fresh_sid: u64 = sample_id(before.clone(), used_sid);
	let stepped: (World, Result) = step(&before, command, fresh_pid, fresh_sid);
	let after: World = stepped.0;
	let result: Result = stepped.1;
	// Per-request DB work; a failed reopen never panics, it only skips persistence.
	match init_or_open(locked.db_path.clone()) {
		Err(_) => (),
		Ok(mut conn) => {
			let _ok = apply(&mut conn, &before, &after);
		}
	}
	// In-memory world advances either way.
	locked.world = after;
	// from-output, then respond with the current date, then lift to rocket.
	Served {
		response: to_http(respond(to_output(result), http_date())),
	}
}

#[doc = "POST /api/signup."]
#[post("/api/signup", data = "<body>")]
fn signup(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/signup".to_string(), body, state)
}

#[doc = "POST /api/login."]
#[post("/api/login", data = "<body>")]
fn login(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/login".to_string(), body, state)
}

#[doc = "POST /api/logout."]
#[post("/api/logout", data = "<body>")]
fn logout(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/logout".to_string(), body, state)
}

#[doc = "POST /api/post-tweet."]
#[post("/api/post-tweet", data = "<body>")]
fn post_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/post-tweet".to_string(), body, state)
}

#[doc = "POST /api/post-reply."]
#[post("/api/post-reply", data = "<body>")]
fn post_reply(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/post-reply".to_string(), body, state)
}

#[doc = "POST /api/delete-tweet."]
#[post("/api/delete-tweet", data = "<body>")]
fn delete_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/delete-tweet".to_string(), body, state)
}

#[doc = "POST /api/like-tweet."]
#[post("/api/like-tweet", data = "<body>")]
fn like_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/like-tweet".to_string(), body, state)
}

#[doc = "POST /api/unlike-tweet."]
#[post("/api/unlike-tweet", data = "<body>")]
fn unlike_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/unlike-tweet".to_string(), body, state)
}

#[doc = "POST /api/follow-user."]
#[post("/api/follow-user", data = "<body>")]
fn follow_user(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/follow-user".to_string(), body, state)
}

#[doc = "POST /api/unfollow-user."]
#[post("/api/unfollow-user", data = "<body>")]
fn unfollow_user(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/unfollow-user".to_string(), body, state)
}

#[doc = "POST /api/get-tweet."]
#[post("/api/get-tweet", data = "<body>")]
fn get_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/get-tweet".to_string(), body, state)
}

#[doc = "POST /api/global-timeline."]
#[post("/api/global-timeline", data = "<body>")]
fn global_timeline(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/global-timeline".to_string(), body, state)
}

#[doc = "POST /api/private-timeline."]
#[post("/api/private-timeline", data = "<body>")]
fn private_timeline(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/private-timeline".to_string(), body, state)
}

#[doc = "Launch: re-load the world from FT_DB (default twitter.db) and mount all 13 endpoints."]
#[launch]
fn rocket() -> _ {
	// The DB path comes from the environment so restarts resume the same world.
	let path: String = match std::env::var("FT_DB") {
		Err(_) => "twitter.db".to_string(),
		Ok(p) => p,
	};
	// Startup reopen must not panic; on failure the empty world still serves.
	let world: World = match init_or_open(path.clone()) {
		Err(_) => empty_world(),
		Ok(mut conn) => load_world(&mut conn),
	};
	// Mount every endpoint at the path the spec fixes.
	rocket::build()
		.manage(Mutex::new(Server {
			world,
			db_path: path,
		}))
		.mount(
			"/",
			routes![
				signup,
				login,
				logout,
				post_tweet,
				post_reply,
				delete_tweet,
				like_tweet,
				unlike_tweet,
				follow_user,
				unfollow_user,
				get_tweet,
				global_timeline,
				private_timeline,
			],
		)
}
