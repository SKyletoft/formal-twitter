//! The executable server layer: glue between the model, the wire codec and rocket.
//!
//! Part 1 of this layer is pure helpers: a std-only IMF `Date` header
//! (`http_date`), the from-output map of spec/Interface.agda taking a model
//! `Result` to a wire `ApiResponse` (`to_output`), cryptographic `u64`
//! randomness from `/dev/urandom` (`random_u64`) and the spec's fresh-id sampler
//! (`sample_id`).  `to_http` lifts a rendered `WireResponse` into a rocket
//! `Response`, headers in the order the spec fixes.  The routes, state and
//! launch come in part 2; nothing here talks to a server or to the DB.
use formal_twitter::db::{
	apply, init_or_open, load_world, reload_accounts, reload_follows, reload_posts,
	reload_sessions, reopen,
};
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

#[doc = "Server state: the world cache, the DB it mirrors, and the tick that drives"]
#[doc = "the rotating PARTIAL cache reload (one section re-queried every four requests)."]
pub struct Server {
	pub world: World,
	pub db_path: String,
	pub tick: u64,
}

#[doc = "Parse failures answer with the spec's 403 access_denied shape: the Interface"]
#[doc = "grammar is total, so a malformed body is treated as a denied request."]
pub fn wire_error(e: WireError) -> WireResponse {
	_ = e;
	respond(ApiResponse::PermissionError, http_date())
}

#[doc = "The cache-reload schedule: a pure 4-cycle 0 -> 1 -> 2 -> 3 -> 0."]
pub fn next_tick(t: u64) -> u64 {
	(t + 1) % 4
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

#[doc = "The one handler behind all 13 routes: parse, step, COMMIT, rotate, render."]
#[doc = "Enforces the AGENTS.md database rules (DB2 audit V1/V2/V3/V5/V7): the database is"]
#[doc = "the source of truth, not RAM.  The world cache advances ONLY after apply reports the"]
#[doc = "BEGIN/COMMIT transaction committed; a failed reopen or a rolled-back apply (PK clashes"]
#[doc = "on RAM-sampled ids included) serves NO data and answers the 403 access_denied shape,"]
#[doc = "so nothing can be served that is not committed in the DB.  After every commit exactly"]
#[doc = "ONE cache section is thrown out and re-queried from the same connection, rotating"]
#[doc = "follows -> sessions -> accounts -> posts by tick: RAM is refreshed periodically, never"]
#[doc = "all at once, and load_world runs only at launch.  The lock is poison-tolerant: the"]
#[doc = "guarded region keeps its invariants (clone + step + recoverable DB errors), so a"]
#[doc = "poisoned guard still holds a valid Server."]
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
	// Poison-tolerant lock: the Err carries a PoisonError whose guard we recover.
	let mut locked = match state.lock() {
		Ok(guard) => guard,
		Err(poisoned) => poisoned.into_inner(),
	};
	// A private copy of the world so step and apply see before/after values.
	let before: World = locked.world.clone();
	// The spec fresh-id sampler, run under the lock.
	let fresh_pid: u64 = sample_id(before.clone(), used_pid);
	let fresh_sid: u64 = sample_id(before.clone(), used_sid);
	let stepped: (World, Result) = step(&before, command, fresh_pid, fresh_sid);
	let after: World = stepped.0;
	let result: Result = stepped.1;
	// COMMIT FIRST: establish-only reopen, then apply BEGIN/COMMIT/ROLLBACK batch.
	// RAM-sampled ids can collide; apply PK failure rolls back and reports false.
	let committed: bool = match reopen(locked.db_path.clone()) {
		Err(_) => false,
		Ok(mut conn) => {
			if !apply(&mut conn, &before, &after) {
				// Rolled back: the DB refused the update, RAM must not advance.
				false
			} else {
				// Committed: advance the cache AND rotate ONE section through the same
				// connection, after the commit so the fresh writes stay visible.  after is
				// moved, so the reload costs no extra World clone.
				let reloaded: World = match locked.tick {
					0 => reload_follows(&mut conn, after),
					1 => reload_sessions(&mut conn, after),
					2 => reload_accounts(&mut conn, after),
					_ => reload_posts(&mut conn, after),
				};
				locked.world = reloaded;
				locked.tick = next_tick(locked.tick);
				true
			}
		}
	};
	if !committed {
		// Nothing was committed, so no data may be served: the same 403 access_denied shape
		// as a parse failure (wire_error discards its argument).
		return Served {
			response: to_http(wire_error(WireError::UnknownEndpoint)),
		};
	}
	// Only reachable after a successful commit, so every served byte is DB-backed.
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
			tick: 0,
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

#[doc = "Server-layer test pointer: the DB-facing rules are proven in Agda, not in Rust."]
#[doc = "DB3a in the Agda development: apply returns true iff the batch committed (th-apply-ok), and"]
#[doc = "rolls back otherwise; the storage pins plus ImplProofs.agda pin load_world and the"]
#[doc = "reload_* fns to the DB view; DB3b there: each reload_* replaces exactly"]
#[doc = "one cache section and leaves the rest of the cache alone.  The residue testable here"]
#[doc = "is the pure tick schedule: forall tick in {0,1,2,3}, next_tick^4 tick == tick."]
#[doc = "RV2a in the Agda development: next-tick^4 = id on {0,1,2,3} and the pinned 8-step landing sequence backs the [2,2,2,2] hit count."]
#[test]
fn test_tick_rotation_cycle() {
	// Stepping eight times from tick 0 hits each of the four sections exactly twice, so
	// every cache section is re-queried once every four requests, never all at once.
	let mut hits: [u64; 4] = [0, 0, 0, 0];
	let mut t: u64 = 0;
	for _ in 0..8 {
		t = next_tick(t);
		hits[t as usize] += 1;
	}
	assert!(hits == [2, 2, 2, 2]);
	// next_tick^4 is the identity on every residue: the schedule is a pure 4-cycle.
	for start in 0..4 {
		let s: u64 = start as u64;
		assert!(next_tick(next_tick(next_tick(next_tick(s)))) == s);
	}
	// And the schedule is exactly the (i + 1) % 4 sequence for i in 0..8.
	for i in 0..8 {
		assert!(next_tick(i as u64) == (i as u64 + 1) % 4);
	}
}
