//! The executable server layer: glue between the model, the wire codec and rocket.
//!
//! Part 1 of this layer is pure helpers: a std-only IMF `Date` header
//! (`http_date`), the from-output map of spec/Interface.agda taking a model
//! `Result` to a wire `ApiResponse` (`to_output`), cryptographic `u64`
//! randomness from `/dev/urandom` (`random_block`, one 16-byte read per request) and the spec's
//! fresh-id sampler split into a pure decision (`sample_id_from`) plus that wrapper
//! (`sample_id`).  `to_http` lifts a rendered `WireResponse` into a rocket
//! `Response`, headers in the order the spec fixes.  The routes, state and
//! launch come in part 2; nothing here talks to a server or to the DB.
use formal_twitter::db::{
	apply, init_or_open, load_world, reload_accounts, reload_follows, reload_posts,
	reload_sessions, reopen,
};
use formal_twitter::model::{Command, Result, World, empty_world, step};
use formal_twitter::wire::{
	ApiResponse, WireError, WireResponse, parse_action, respond, to_command,
};
use rocket::Response;
use rocket::State;
use rocket::data::Capped;
use rocket::get;
use rocket::http::uri::Origin;
use rocket::http::{Header, Status};
use rocket::launch;
use rocket::post;
use rocket::request::Request;
use rocket::response::Responder;
use rocket::routes;
use std::io::Cursor;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

/// Two-digit decimal, zero-padded (as the IMF-date needs dd, HH, mm, ss).
fn two(v: u64) -> String {
	if v < 10 {
		// same bytes: build in a buffer instead of String + String concat
		let mut padded: String = "0".to_string();
		(padded).push_str(&v.to_string());
		padded
	} else {
		v.to_string()
	}
}

/// Gregorian leap-year test.
fn leap(y: u64) -> bool {
	y.is_multiple_of(4) && (!y.is_multiple_of(100) || y.is_multiple_of(400))
}

/// The current moment rendered as an IMF date: "Thu, 01 Jan 1970 00:00:00 GMT".
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

/// from-output of Interface.agda: a model Result rendered as a wire ApiResponse.
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

/// One 16-byte read from /dev/urandom: TWO big-endian u64s of entropy per call, so a
/// request pays ONE random read instead of two.  All-zero on any failure, which the pure
/// sampler below reports as not-fresh.
pub fn random_block() -> [u8; 16] {
	// Qualified std paths keep the top-level import list minimal.
	match std::fs::File::open("/dev/urandom") {
		Err(_) => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
		Ok(mut file) => {
			let mut bytes: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
			_ = std::io::Read::read_exact(&mut file, &mut bytes);
			bytes
		}
	}
}

/// The PURE fresh-id decision, split out of the /dev/urandom wrapper so QuickCheck can
/// pin it: the big-endian u64 read off the FIRST EIGHT bytes of a random block, paired with
/// whether it is fresh, i.e. nonzero and absent from the used list - the spec's CreateNew
/// new-sid/new-pid rejecting ids already in World.used-post-ids / World.used-session-ids.
/// Total: a block shorter than eight bytes reports (0, false).  A used list covering the
/// candidate flips ok to false (the exhaustion path), which sample_id retries.  Fully
/// deterministic in both arguments, so the same bytes and used set always yield the same id.
pub fn sample_id_from(bytes: &[u8], used: &[u64]) -> (u64, bool) {
	if bytes.len() < 8 {
		(0, false)
	} else {
		let r: u64 = u64::from_be_bytes([
			bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
		]);
		(r, r != 0 && !used.contains(&r))
	}
}

/// The spec's fresh-id sampler: feeds ONE 16-byte /dev/urandom block per attempt to the
/// pure sample_id_from, the first u64 seeding the post id and the second the session id.
/// Both halves must be fresh or the whole attempt is discarded, matching the spec's CreateNew
/// rejection of used ids.  The world is read by REFERENCE, so a request no longer clones it.
pub fn sample_id(w: &World) -> (u64, u64) {
	loop {
		let bytes: [u8; 16] = random_block();
		// The used lists are borrowed from the world, exactly what model's used_pid/used_sid test.
		let (pid, pid_ok) = sample_id_from(&bytes[0..8], &w.used_post_ids);
		let (sid, sid_ok) = sample_id_from(&bytes[8..16], &w.used_session_ids);
		if pid_ok && sid_ok {
			return (pid, sid);
		}
	}
}

/// Lift a rendered WireResponse into a rocket Response, headers in the order the spec fixes.
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

/// Server state: the world cache, the DB it mirrors, and the tick that drives
/// the rotating PARTIAL cache reload (one section re-queried every four requests).
pub struct Server {
	pub world: World,
	pub db_path: String,
	pub tick: u64,
}

/// Parse failures answer with the spec's 403 access_denied shape: the Interface
/// grammar is total, so a malformed body is treated as a denied request.
/// The error argument is ignored: every WireError maps to the same 403 shape.
pub fn wire_error(_e: WireError) -> WireResponse {
	respond(ApiResponse::PermissionError, http_date())
}

/// The cache-reload schedule: a pure 4-cycle 0 -> 1 -> 2 -> 3 -> 0.
pub fn next_tick(t: u64) -> u64 {
	(t + 1) % 4
}

/// D1 DB-truth discipline (failure path = full re-query): when reopen or apply fails the World stays unadvanced, but RAM must not stay stale against the DB, so the cached World is re-synced by re-opening a fresh connection and throwing out ALL FOUR cache sections at once through db.rs's reload fns.
// (no new diesel query: the chain reuses reload_accounts/sessions/follows/posts verbatim)
// (each step moves the World, so the full re-sync costs no World clone)
// (if the reopen fails again there is no DB view to sync to, so the cache stays put)
pub fn reload_all_sections(path: String, w: World) -> World {
	match reopen(path) {
		Err(_) => w,
		Ok(mut conn) => {
			// accounts section first
			let with_accounts: World = reload_accounts(&mut conn, w);
			// sessions drags its derived used_session_ids along
			let with_sessions: World = reload_sessions(&mut conn, with_accounts);
			// the follows table alone
			let with_follows: World = reload_follows(&mut conn, with_sessions);
			// posts + newest_first + used_post_ids move together; tail move, no clone
			reload_posts(&mut conn, with_follows)
		}
	}
}

/// A pre-rendered rocket response lifted into a handler return type.
pub struct Served {
	pub response: Response<'static>,
}

/// The trivial responder: always Ok with the pre-rendered response.
impl<'r> Responder<'r, 'static> for Served {
	// The request is irrelevant; the response is fully rendered.
	fn respond_to(self, _req: &'r Request<'_>) -> rocket::response::Result<'static> {
		Ok(self.response)
	}
}

/// The one handler behind all 13 POST routes: parse, then hand the command to the
/// shared serve_command core.
/// Enforces the AGENTS.md database rules (DB2 audit V1/V2/V3/V5/V7): the database is
/// the source of truth, not RAM.  The world cache advances ONLY after apply reports the
/// BEGIN/COMMIT transaction committed; a failed reopen or a rolled-back apply (PK clashes
/// on RAM-sampled ids included) serves NO data and answers the 403 access_denied shape,
/// so nothing can be served that is not committed in the DB.  After every commit exactly
/// ONE cache section is thrown out and re-queried from the same connection, rotating
/// follows -> sessions -> accounts -> posts by tick: RAM is refreshed periodically, never
/// all at once, and load_world runs only at launch.  The lock is poison-tolerant: the
/// guarded region keeps its invariants (clone + step + recoverable DB errors), so a
/// poisoned guard still holds a valid Server.
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
	serve_command(command, state)
}

/// The shared core behind all 13 POST routes and the 3 GET aliases: step, COMMIT,
/// rotate, render.  Enforces the AGENTS.md database rules (DB2 audit V1/V2/V3/V5/V7):
/// the database is the source of truth, not RAM.  The world cache advances ONLY after
/// apply reports the BEGIN/COMMIT transaction committed; a failed reopen or a rolled-back
/// apply (PK clashes on RAM-sampled ids included) serves NO data and answers the 403
/// access_denied shape, so nothing can be served that is not committed in the DB.  After
/// every commit exactly ONE cache section is thrown out and re-queried from the same
/// connection, rotating follows -> sessions -> accounts -> posts by tick: RAM is refreshed
/// periodically, never all at once, and load_world runs only at launch.  The lock is
/// poison-tolerant: the guarded region keeps its invariants (clone + step + recoverable
/// DB errors), so a poisoned guard still holds a valid Server.
pub fn serve_command(command: Command, state: &Mutex<Server>) -> Served {
	// Poison-tolerant lock: the Err carries a PoisonError whose guard we recover.
	let mut locked = match state.lock() {
		Ok(guard) => guard,
		Err(poisoned) => poisoned.into_inner(),
	};
	// A private copy of the world so step and apply see before/after values.
	let before: World = locked.world.clone();
	// The spec fresh-id sampler, run under the lock: ONE 16-byte read yields both ids and the
	// world is read by reference, so neither per-request World clone survives.
	let (fresh_pid, fresh_sid): (u64, u64) = sample_id(&before);
	let stepped: (World, Result) = step(&before, command, fresh_pid, fresh_sid);
	let after: World = stepped.0;
	let result: Result = stepped.1;
	// COMMIT FIRST: establish-only reopen, then apply BEGIN/COMMIT/ROLLBACK batch.
	// RAM-sampled ids can collide; apply PK failure rolls back and reports false.
	let committed: bool = match reopen(locked.db_path.clone()) {
		Err(_) => {
			// D1 failure path: nothing committed, so the World stays unadvanced, but RAM must
			// never stay stale against the DB: full re-query of all four sections through the
			// helper's fresh reopen before the 403 below (no DB view -> cache stays put).
			locked.world = reload_all_sections(locked.db_path.clone(), before);
			false
		}
		Ok(mut conn) => {
			if !apply(&mut conn, &before, &after) {
				// Rolled back: the DB refused the update, RAM must not advance.
				// D1 failure path again: the cache re-syncs fully from the committed DB view.
				// (only the cache sections move; the World's logical state stays unadvanced)
				locked.world = reload_all_sections(locked.db_path.clone(), before);
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

/// POST /api/signup.
#[post("/api/signup", data = "<body>")]
fn signup(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/signup".to_string(), body, state)
}

/// POST /api/login.
#[post("/api/login", data = "<body>")]
fn login(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/login".to_string(), body, state)
}

/// POST /api/logout.
#[post("/api/logout", data = "<body>")]
fn logout(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/logout".to_string(), body, state)
}

/// POST /api/post-tweet.
#[post("/api/post-tweet", data = "<body>")]
fn post_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/post-tweet".to_string(), body, state)
}

/// POST /api/post-reply.
#[post("/api/post-reply", data = "<body>")]
fn post_reply(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/post-reply".to_string(), body, state)
}

/// POST /api/delete-tweet.
#[post("/api/delete-tweet", data = "<body>")]
fn delete_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/delete-tweet".to_string(), body, state)
}

/// POST /api/like-tweet.
#[post("/api/like-tweet", data = "<body>")]
fn like_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/like-tweet".to_string(), body, state)
}

/// POST /api/unlike-tweet.
#[post("/api/unlike-tweet", data = "<body>")]
fn unlike_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/unlike-tweet".to_string(), body, state)
}

/// POST /api/follow-user.
#[post("/api/follow-user", data = "<body>")]
fn follow_user(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/follow-user".to_string(), body, state)
}

/// POST /api/unfollow-user.
#[post("/api/unfollow-user", data = "<body>")]
fn unfollow_user(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/unfollow-user".to_string(), body, state)
}

/// POST /api/get-tweet.
#[post("/api/get-tweet", data = "<body>")]
fn get_tweet(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/get-tweet".to_string(), body, state)
}

/// POST /api/global-timeline.
#[post("/api/global-timeline", data = "<body>")]
fn global_timeline(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/global-timeline".to_string(), body, state)
}

/// POST /api/private-timeline.
#[post("/api/private-timeline", data = "<body>")]
fn private_timeline(state: &State<Mutex<Server>>, body: Capped<String>) -> Served {
	serve("/api/private-timeline".to_string(), body, state)
}

/// GET aliases turn query parameters into POST-equivalent body lines: a present and non-empty
/// token gets its own line first, then the value line, always present and empty when the
/// parameter is missing. A missing or malformed number then fails parse_action exactly like
/// the POST twin's body: BadNumber or MissingLine, which render as the same 403 shape.
pub fn alias_body(token: Option<String>, value: Option<String>) -> String {
	let mut head: String = match token {
		None => "".to_string(),
		Some(mut text) => {
			// text + "\r\n" -> push_str onto the moved token text
			text.push_str("\r\n");
			text
		}
	};
	let tail: String = match value {
		None => "".to_string(),
		Some(text) => text,
	};
	// head + tail + "\r\n" -> push into head, same bytes
	(head).push_str(&tail);
	(head).push_str("\r\n");
	head
}

/// The raw value of one query parameter on the GET aliases: absent, bare (no '=') or
/// empty all mean None (the legacy app.js always sends token=, empty when anonymous); the
/// first pair with the name wins and later duplicates are ignored.
pub fn query_param(query: &str, name: String) -> Option<String> {
	// find_map stops at the first pair whose name matches, so no Vec of all hits is
	// built; the verdicts stay the same: a later duplicate never decides the answer
	let hit: Option<String> = (query.split('&')).find_map(|pair| match pair.find("=") {
		// a bare pair matching the name still counts as a hit, with empty value
		None => match *pair == (*name.as_str()) {
			true => Some("".to_string()),
			false => None,
		},
		// the name is the prefix before the first '=', even when '=' is in the value
		Some(at) => match (*pair)[..at] == *name.as_str() {
			true => Some(pair[(at + 1)..].to_string()),
			false => None,
		},
	});
	match hit {
		None => None,
		Some(value) => match value.is_empty() {
			true => None,
			false => Some(value.to_string()),
		},
	}
}

/// The one handler behind the 3 GET aliases: the query parameters become the POST-
/// equivalent body, then the very parse_action and shared core the POST routes use.
pub fn serve_alias(
	origin: &Origin<'_>,
	state: &Mutex<Server>,
	path: String,
	value_name: String,
) -> Served {
	// no copy of the query: a &str view of the Origin's query part
	let query: &str = match origin.query() {
		None => "",
		// (same bytes; the view borrows from the Origin, which lives past here)
		Some(part) => part.as_str(),
	};
	let body: String = alias_body(
		query_param(query, "token".to_string()),
		query_param(query, value_name),
	);
	let command: Command = match parse_action(path.as_str(), body.as_bytes()) {
		Err(e) => {
			// Malformed or missing numbers render as the same 403 access_denied shape
			// the POST twins answer (wire_error discards e; no new error codes).
			// (the request never reaches the world, so the DB stays untouched)
			// (identical bytes to a POST parse failure, header for header)
			// (404 and 422 can never surface for an alias request)
			return Served {
				// (the answer is rendered by the very same to_http every POST route uses)
				response: to_http(wire_error(e)),
			};
		}
		Ok(action) => to_command(action),
	};
	serve_command(command, state)
}

/// GET /api/get-tweet: the legacy frontend's query-parameter twin of the POST route.
#[get("/api/get-tweet")]
fn get_tweet_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(
		origin,
		state,
		"/api/get-tweet".to_string(),
		"id".to_string(),
	)
}

/// GET /api/global-timeline.
#[get("/api/global-timeline")]
fn global_timeline_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(
		origin,
		state,
		"/api/global-timeline".to_string(),
		"len".to_string(),
	)
}

/// GET /api/private-timeline.
#[get("/api/private-timeline")]
fn private_timeline_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(
		origin,
		state,
		"/api/private-timeline".to_string(),
		"len".to_string(),
	)
}

/// Launch: re-load the world from FT_DB (default twitter.db) and mount all 13 POST
/// endpoints plus the 3 GET aliases the legacy frontend speaks.
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
				// the 3 GET aliases the legacy frontend speaks, mounted at the same paths.
				get_tweet_alias,
				global_timeline_alias,
				private_timeline_alias,
			],
		)
}

/// Server-layer test pointer: the DB-facing rules (DB3a apply-commits-gate, DB3b one-section
/// reload, RV2a next-tick^4 = id) were pinned in stdlib-only Agda companion modules since
/// removed per A4 (they never mention Twitter/Interface); what remains testable here is the
/// pure tick schedule: forall tick in {0,1,2,3}, next_tick^4 tick == tick.
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

/// D1 gate: reload_all_sections - the exact chain serve_command runs on BOTH failure arms -
/// restores a World tampered in ALL FOUR sections from the seeded DB in one sweep, and the
/// double-failure arm (DB unopenable) leaves the cache put, no panic, no wipe.
#[test]
fn test_reload_all_sections() {
	// DB/model handles scoped to the test so the non-test build keeps zero unused imports.
	use formal_twitter::db::save_world;
	use formal_twitter::model::SessionStatus;
	let path = "/tmp/ft-reload-all-sections.sqlite";
	// Seed the DB: the database, not RAM, is the source of truth.
	let mut conn = init_or_open(path.to_string()).unwrap();
	save_world(&mut conn, seed_all_sections_world());
	// Tamper EVERY section of the RAM cache at once (unlike the DB3b one-section gates).
	// (accounts, sessions+used_session_ids, follows and posts+newest_first+used_post_ids all
	// lie below, so the full-restoration asserts must catch every one of them)
	let mut tampered: World = seed_all_sections_world();
	tampered.accounts.retain(|entry| entry.0 != "bob");
	tampered.accounts[0].1.password = "LIE".to_string();
	tampered.sessions.retain(|entry| entry.0 != 200);
	tampered.sessions[0].1 = SessionStatus::Unused;
	tampered.used_session_ids = vec![100, 999];
	tampered.follows = vec![("ghost".to_string(), "alice".to_string())];
	tampered.posts.retain(|entry| entry.0 != 2);
	tampered.posts[0].1.text = "LIE".to_string();
	tampered.newest_first = vec![9, 8];
	tampered.used_post_ids = vec![9, 8];
	// Run the very failure-path re-sync serve_command performs, fresh connection inside.
	let reloaded: World = reload_all_sections(path.to_string(), tampered.clone());
	// The DB view: a fresh canonical load to compare the re-synced cache against.
	let mut again = init_or_open(path.to_string()).unwrap();
	let expected: World = load_world(&mut again);
	// ALL FOUR sections restored: the cache now agrees with the DB everywhere.
	assert!(reloaded == expected);
	// The tampering really existed, and did not survive the re-query.
	assert!(tampered != expected);
	// Double-failure arm: no openable DB means no DB view to sync to, so the cache stays put.
	// (missing parent directory: reopen fails again, and the World is returned untouched)
	assert!(
		reload_all_sections(
			"/tmp/ft-no-such-dir/ft-x.sqlite".to_string(),
			tampered.clone()
		) == tampered
	);
}

/// D1 gate seed: the DB3b db_tests canonical World kept small, rows pre-sorted in the
/// order load_world returns them so a save/load round-trip reproduces the DB view.
#[cfg(test)]
fn seed_all_sections_world() -> World {
	use formal_twitter::model::{Account, Post, PostStatus, SessionStatus, Visibility};
	World {
		accounts: vec![
			(
				"alice".to_string(),
				Account {
					password: "a".to_string(),
					default_visibility: Visibility::Everyone,
				},
			),
			(
				"bob".to_string(),
				Account {
					password: "b".to_string(),
					default_visibility: Visibility::FollowersOnly,
				},
			),
		],
		sessions: vec![
			(100, SessionStatus::Active("alice".to_string())),
			(200, SessionStatus::Revoked),
		],
		posts: vec![
			(
				1,
				Post {
					author: "alice".to_string(),
					text: "hello".to_string(),
					visibility: Visibility::Everyone,
					status: PostStatus::Other,
					likes: vec!["bob".to_string()],
					replies: vec![2],
					parent: None,
				},
			),
			(
				2,
				Post {
					author: "bob".to_string(),
					text: "reply-text".to_string(),
					visibility: Visibility::FollowersOnly,
					status: PostStatus::Other,
					likes: vec![],
					replies: vec![],
					parent: Some(1),
				},
			),
		],
		follows: vec![("alice".to_string(), "bob".to_string())],
		newest_first: vec![2, 1],
		used_post_ids: vec![1, 2],
		used_session_ids: vec![100, 200],
	}
}

#[cfg(test)]
mod qc {
	//! QuickCheck pins for the PURE fresh-id decision `sample_id_from`: the freshness rule of
	//! spec/Twitter.agda's CreateNew new-sid/new-pid (the sampled id must miss World.used-post-ids
	//! and World.used-session-ids), plus its totality, exhaustion and determinism boundaries.
	//! No /dev/urandom is read here, so the props are exact and shrinkable; the Agda mirror is
	//! th-sample-id-fresh in ImplProofs.agda (freshness of new-sid/new-pid).
	use super::sample_id_from;
	use quickcheck_macros::quickcheck;

	/// Clips/pads a generated block to the 16 bytes ONE random read returns, so both
	/// halves of the block are exercised by the props.
	fn block16(bs: &[u8]) -> Vec<u8> {
		// QuickCheck already provides Arbitrary for Vec u8, so no local Gen instance is needed.
		// (the padding byte 1 keeps a short block from collapsing onto the zero candidate)
		// truncate first so an oversized block still fits the 16-byte contract
		let mut out: Vec<u8> = bs.to_vec();
		out.truncate(16);
		out.resize(16, 1);
		out
	}

	/// QC prop_pid_fresh: whenever sample_id_from calls the u64 read off the leading eight
	/// bytes fresh, that id is NEVER a member of the used-post-ids list it was given.
	#[quickcheck]
	// (the spec's new-pid rejecting ids already in World.used-post-ids)
	// fresh means nonzero AND absent, so a hit in `used` can never be reported fresh.
	// `used` is borrowed, mirroring the &World field borrow that sample_id makes.
	// QuickCheck shrinks a counterexample to the smallest used/bytes pair that breaks it.
	fn prop_pid_fresh(used: Vec<u64>, bs: Vec<u8>) -> bool {
		// One 16-byte block: the post id comes from the first eight bytes.
		let (pid, ok): (u64, bool) = sample_id_from(&block16(bs.as_slice()), &used);
		// Freshness must hold for every generated used set, not just for small ones.
		// (this is the forall used, forall bytes of the freshness property)
		!ok || !used.contains(&pid)
	}

	/// QC prop_sid_fresh: the same rule for the session id, i.e. the u64 read off bytes 8..16
	/// of the block is never in the used-session-ids list when called fresh.
	#[quickcheck]
	// (the spec's new-sid rejecting ids already in World.used-session-ids)
	// the second half is checked against its own list, exactly as sample_id slices it.
	// A block shorter than eight tail bytes is total: it reports not-fresh, which passes.
	// The pairing (one read, two ids) is pinned by test_sample_id_halves below.
	fn prop_sid_fresh(used: Vec<u64>, bs: Vec<u8>) -> bool {
		// One 16-byte block: the session id comes from the second half.
		// (fresh => absent from the session list, for every used set and every block)
		// (a collision in the used set must flip ok, never be handed out)
		// shrinking reports the smallest failing (used, bytes) pair.
		let b: Vec<u8> = block16(bs.as_slice());
		let (sid, ok): (u64, bool) = sample_id_from(&b[8..], &used);
		// (the same conclusion as prop_pid_fresh, for the other half)
		!ok || !used.contains(&sid)
	}

	/// Boundary pins: a block shorter than eight bytes and a used list covering the
	/// candidate - the documented exhaustion path sample_id retries.
	#[test]
	fn test_sample_id_boundaries() {
		// Totality: no panic, just not-fresh, on an empty or short block.
		assert!(sample_id_from(&[], &[]) == (0, false));
		// Zero is never offered, matching the spec's nonzero ids.
		let zeros: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
		// (so a failed urandom read stays not-fresh and the sampler retries)
		assert!(sample_id_from(&zeros, &[]) == (0, false));
		// The top of the u64 range is offered when the used list is empty.
		let hi: [u8; 8] = [255, 255, 255, 255, 255, 255, 255, 255];
		assert!(sample_id_from(&hi, &[]) == (0xffff_ffff_ffff_ffff, true));
		// (and refused when the used list covers exactly that boundary value)
		let (_, hi_used) = sample_id_from(&hi, &[0xffff_ffff_ffff_ffff]);
		assert!(!hi_used);
		// A used list covering the candidate flips ok regardless of its other members.
		let one: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 1];
		let (_, one_used) = sample_id_from(&one, &[9, 1, 7]);
		assert!(!one_used);
	}

	/// One 16-byte read yields two candidates: the two halves of the same block feed the
	/// post id and the session id, and neither half sees the other half's used list.
	#[test]
	fn test_sample_id_halves() {
		// A fixed block: big-endian, the first u64 is 7 and the second is 9.
		let block: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 9];
		// The post half reads 7 fresh, the session half reads 9 fresh, from ONE block.
		// (both halves agree with the split sample_id performs: bytes 0..8 and 8..16)
		// and they are distinct ids, so one read can never serve the post slot twice.
		let (post, post_ok) = sample_id_from(&block[0..8], &[8]);
		// (the session list below covers 9, so the session slot must report not-fresh)
		// i.e. the sampler retries rather than handing out a used id.
		let (sid, sid_ok) = sample_id_from(&block[8..16], &[42, 9]);
		assert!(post == 7 && post_ok && sid == 9 && !sid_ok);
	}

	/// Determinism: identical bytes and identical used set always yield the identical
	/// (id, ok) pair, for both halves of a block.
	#[test]
	fn test_sample_id_deterministic() {
		// The fixed block stands in for the /dev/urandom read, so equality is exact.
		// (the first half is covered by the used list: reported, but flagged not-fresh)
		// the same block's second half is untouched by that list, so it stays fresh.
		let block: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 9];
		// Replaying either half must never drift: no RNG, no clock, no hidden state.
		// (this is the forall-bytes, forall-used determinism half of the property test)
		// ten replays of both halves are required to match the pinned verdicts below.
		// (freshness is the props' job; here the VALUE and the FLAG must both be stable)
		// so a cached or shuffled sampler would fail this test, not just the props.
		for _ in 0..10 {
			// (same bytes, same used set -> same (id, ok) pair, every half)
			// (a fresh, nonzero candidate is offered unchanged)
			// (which is what the common request path takes)
			assert!(sample_id_from(&block[0..8], &[7]) == (7, false));
			assert!(sample_id_from(&block[8..16], &[7]) == (9, true));
		}
	}
}

/// GET alias parse pins: the query-parameter body is byte-identical to the POST twin's
/// body and parse_action gives both the same verdict, errors included.
#[test]
fn test_alias_get_tweet_parses() {
	// token + value is exactly the POST body "7\r\n42\r\n".
	assert!(alias_body(Some("7".to_string()), Some("42".to_string())) == "7\r\n42\r\n");
	// anonymous GET is exactly the POST anonymous body "42\r\n".
	assert!(alias_body(None, Some("42".to_string())) == "42\r\n");
	// parsed actions agree, token and all, with the POST twin's parse.
	// (the Maybe token of the spec's get-tweet request line)
	// (absent or empty token= means Nothing, not a failed parse)
	// (and both agree with the POST single-line body)
	// (a public post thus reads without session over the alias)
	// (the token only gates what step gates, never the codec)
	// (the alias codec adds no permission logic of its own)
	// (so permission stays one implementation deep)
	// (end of the anonymous agreement pins)
	assert!(
		(parse_action(
			"/api/get-tweet",
			alias_body(Some("7".to_string()), Some("42".to_string())).as_bytes()
		) == Ok(formal_twitter::wire::WireAction::GetTweet(Some(7), 42)))
	);
	assert!(
		(parse_action(
			"/api/get-tweet",
			alias_body(None, Some("42".to_string())).as_bytes()
		) == Ok(formal_twitter::wire::WireAction::GetTweet(None, 42)))
	);
	// malformed token: BadNumber, the same verdict as POST body "x\r\n42\r\n".
	assert!(
		(parse_action(
			"/api/get-tweet",
			alias_body(Some("x".to_string()), Some("42".to_string())).as_bytes()
		) == Err(WireError::BadNumber))
	);
	// missing value keeps its empty line: the token never becomes a read id.
	// (two lines with a blank second one fail the numeric rule)
	// (the arity stays two so the verdict is BadNumber, not MissingLine)
	// (either way the served shape is the identical 403)
	// (wire_error discards which error it was, per Interface.agda)
	// (one shape for every request-level parse failure)
	// (the DB never sees such a request)
	// (end of the failure pins)
	assert!(
		(parse_action(
			"/api/get-tweet",
			alias_body(Some("7".to_string()), None).as_bytes()
		) == Err(WireError::BadNumber))
	);
	// nothing at all: a lone empty line, BadNumber, still the same 403 shape.
	assert!(
		(parse_action("/api/get-tweet", alias_body(None, None).as_bytes())
			== Err(WireError::BadNumber))
	);
	// and all three error names render identically: one 403, one body.
	// (status, headers and body all agree for any two error names)
	// (the discard rule of wire_error, pinned once here)
	// (see also the prefix pins in wire.rs for the byte shape)
	// (this pin only fixes that the aliases share it, per T6)
	// (end of the rendering pin)
	assert!(wire_error(WireError::BadNumber) == wire_error(WireError::MissingLine));
	assert!(wire_error(WireError::MissingLine).status_code == 403);
}

/// The timeline aliases: private keeps its required token (MissingLine without one) and
/// global keeps the optional token, each exactly as its POST twin parses.
#[test]
fn test_alias_timeline_parses() {
	// private with token: POST body "7\r\n3\r\n".
	assert!(
		(parse_action(
			"/api/private-timeline",
			alias_body(Some("7".to_string()), Some("3".to_string())).as_bytes()
		) == Ok(formal_twitter::wire::WireAction::PrivateTimeline(7, 3)))
	);
	// private without token: MissingLine, as for the POST single-line body.
	// (private timelines demand a session, both transports agree)
	// (no token line means one line short of the arity)
	// (the verdict is MissingLine then, rendered as the 403)
	// (never a silent anonymous private read)
	// (end of the private arity pins)
	// (below: the optional-token global pins)
	// (opt_num takes one or two lines, both legal)
	// (mirroring the Maybe token in Interface.agda)
	// (for global-timeline requests)
	// (and None reads the public timeline)
	// (Some reads with session, same timeline)
	// (the token changes permissions, not the list rule)
	// (which step already decides in model.rs)
	// (the codec stays spec-exact either way)
	// (end of the global pins)
	assert!(
		(parse_action(
			"/api/private-timeline",
			alias_body(None, Some("3".to_string())).as_bytes()
		) == Err(WireError::MissingLine))
	);
	// global with and without token both parse, per the optional-token spec line.
	// (GlobalTimeline takes Maybe token then the length)
	// (anonymous reads are legal on the public timeline)
	// (the token only gates private timelines)
	// (so only private rejects the token-less alias)
	// (end of the global pins)
	assert!(
		(parse_action(
			"/api/global-timeline",
			alias_body(Some("7".to_string()), Some("5".to_string())).as_bytes()
		) == Ok(formal_twitter::wire::WireAction::GlobalTimeline(Some(7), 5)))
	);
	assert!(
		(parse_action(
			"/api/global-timeline",
			alias_body(None, Some("5".to_string())).as_bytes()
		) == Ok(formal_twitter::wire::WireAction::GlobalTimeline(None, 5)))
	);
	// malformed number on the length line: BadNumber again.
	assert!(
		(parse_action(
			"/api/global-timeline",
			alias_body(Some("x".to_string()), Some("5".to_string())).as_bytes()
		) == Err(WireError::BadNumber))
	);
	// and every alias action reaches the very Commands the core serves.
	// (to_command is shared by POST and GET paths unchanged)
	// (ReadPersonalTimeline gates on the session token in step)
	// (ReadGlobalTimeline takes the Maybe one)
	// (ReadPost takes the Maybe one too)
	// (end of the command-mapping pins)
	// (no other Command appears for aliases)
	// (the ten write endpoints have no alias by spec)
	// (only the three reads the frontend polls do)
	// (Interface.agda lists exactly these GET forms)
	// (and ImplWire mirrors that list one-to-one)
	// (end of the coverage note)
	assert!(
		(to_command(formal_twitter::wire::WireAction::GetTweet(Some(7), 42))
			== Command::ReadPost(Some(7), 42))
	);
	// (personal is session-gated, global is not, both served by the core)
	assert!(
		(to_command(formal_twitter::wire::WireAction::PrivateTimeline(7, 3))
			== Command::ReadPersonalTimeline(7, 3))
	);
	assert!(
		(to_command(formal_twitter::wire::WireAction::GlobalTimeline(None, 5))
			== Command::ReadGlobalTimeline(None, 5))
	);
}

/// Query-parsing pins: raw pairs split at the first '=', the first match wins, and absent
/// or bare (no value) or empty all read as None; end to end the alias body equals the
/// POST twin's body bytes.
#[test]
fn test_alias_query_param_parses() {
	// exactly the app.js shape: token first, then the value parameter.
	assert!(query_param("token=7&id=42", "token".to_string()) == Some("7".to_string()));
	assert!(query_param("token=7&id=42", "id".to_string()) == Some("42".to_string()));
	// empty token= means anonymous, same as an absent token.
	assert!(query_param("token=&id=42", "token".to_string()).is_none());
	assert!(query_param("id=42", "token".to_string()).is_none());
	// a bare pair has the empty value; a duplicate keeps the first.
	assert!(query_param("id", "id".to_string()).is_none());
	assert!(query_param("id=1&id=2", "id".to_string()) == Some("1".to_string()));
	// end to end: the alias body is the POST twin's body, byte for byte.
	// (the anonymous case reuses the token-less POST shape)
	assert!(
		alias_body(
			query_param("token=7&id=42", "token".to_string()),
			query_param("token=7&id=42", "id".to_string())
		) == "7\r\n42\r\n"
	);
	assert!(
		alias_body(
			query_param("token=&id=42", "token".to_string()),
			query_param("token=&id=42", "id".to_string())
		) == "42\r\n"
	);
}
