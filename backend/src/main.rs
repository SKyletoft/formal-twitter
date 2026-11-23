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
// (F9) the held-connection field in Server names this type directly (same type db.rs establishes).
use diesel::SqliteConnection;
use formal_twitter::db::{
	// (F2) apply_delta: the Delta-driven write-through serve_command now commits through.
	apply_delta,
	db_max_seq,
	init_or_open,
	load_world,
	reload_accounts,
	reload_follows,
	reload_posts,
	reload_sessions,
	reopen,
};
use formal_twitter::model::{
	Command, Delta, Result, World, WorldIndex, build_index, empty_world, patch_world, step_d,
};
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
use std::sync::MutexGuard;
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

/// The epoch-second stamp of the current moment: ONE clock source for both the IMF Date
/// headers and the /log request log, so log lines and headers never disagree.
pub fn now_secs() -> u64 {
	(SystemTime::now().duration_since(UNIX_EPOCH))
		.unwrap_or_default()
		.as_secs()
}

/// An epoch-second count rendered as an IMF date: "Thu, 01 Jan 1970 00:00:00 GMT".  The pure
/// core of http_date, so a /log line's stored timestamp formats through the very same calendar
/// walk as a Date header.
pub fn http_date_from(secs: u64) -> String {
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

/// The current moment rendered as an IMF date (the Date header every response carries).
pub fn http_date() -> String {
	http_date_from(now_secs())
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

/// The pure FT_FRONTEND name guard, testable with no env mutation at all: reject the empty
/// name, anything holding '/' or '\' (a directory change is impossible at all), a name holding
/// ".." (climbing) and anything starting with '.' (dotfiles and dot-dirs).  Every refusal falls
/// back to the shipped "frontend"; a kept name is returned verbatim.
pub fn frontend_dir_name(raw: &str) -> String {
	// guard, in short locals so the disjunction stays one line: either separator flavour, a ..
	// pair (climbing) or a leading dot (hidden/dot names), plus the empty name.
	let sep: bool = raw.contains("/") || raw.contains("\\");
	let dots: bool = raw.contains("..") || raw.starts_with(".");
	if raw.is_empty() || sep || dots {
		// refused outright: the shipped site answers instead, nothing resolved, nothing read.
		return LOG_FRONTEND_DEFAULT.to_string();
	}
	// the kept name passes through verbatim; env hands us a String, so one copy answers.
	raw.to_string()
}

/// A frontend dir resolved per call, for a validated site name ("frontend", "frontend2", ...):
/// two strategies.  The INSTALL layout has the bin at $out/bin/formal-twitter, so current_exe()
/// two levels up is $out and the flake's postInstall copied the site to $out/<name>; the DEV
/// layout (cargo test / nix develop) has no $out, so fall back to CARGO_MANIFEST_DIR/../<name>,
/// one level up from backend/, i.e. the repo's <name>/.  The install dir wins only when it
/// really exists, otherwise the dev path.  <name> is only ever the output of frontend_dir_name.
pub fn frontend_root_named(name: &str) -> std::path::PathBuf {
	// dev fallback: env!("CARGO_MANIFEST_DIR") is backend/, so the site is one level up.
	let dev: std::path::PathBuf = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
		.join("..")
		.join(name);
	// install layout: $out/bin/formal-twitter joined with ../.. is $out, then $out/frontend.
	// the Option chain leaves dev untouched until the fallback, so no clone is paid per call.
	let installed: Option<std::path::PathBuf> = std::env::current_exe()
		.ok()
		// two levels up from $out/bin/formal-twitter is $out, then $out/frontend.
		.map(|exe| exe.join("../..").join(name))
		// only a real directory can serve, so a stale $out falls through.
		.filter(|site| site.is_dir());
	// the dev path covers cargo test / nix develop, and any missing install copy.
	installed.unwrap_or(dev)
}

/// The frontend dir for the FT_FRONTEND override (default "frontend"), so frontend2/ frontend3/
/// frontend4/ variants can be previewed without replacing frontend/.  The raw name goes through
/// the pure guard frontend_dir_name FIRST, so a hostile override never reaches the filesystem.
pub fn frontend_root() -> std::path::PathBuf {
	// an absent FT_FRONTEND answers the empty name, which the guard maps to the shipped site,
	// so the default path costs no copy.
	let raw: String = match std::env::var("FT_FRONTEND") {
		Err(_) => "".to_string(),
		Ok(v) => v,
	};
	// the pure guard runs first, so only a validated dir name reaches the resolver.
	frontend_root_named(frontend_dir_name(raw.as_str()).as_str())
}

/// One file off frontend_root, the guard FIRST so a hostile name never reaches the filesystem:
/// reject the empty name, anything holding '/' or '\\' (no directory change is possible at all),
/// a name holding "..", and anything starting with '.' (dotfiles and dot-dirs).  Then a plain
/// read_to_string of dir/name, with EVERY io error (missing, unreadable, a directory) folding
/// to None, so no input can panic the server.
pub fn read_frontend(name: &str) -> Option<String> {
	// guard, in short locals so the disjunction stays one line: either separator flavour, a ..
	// pair (climbing) or a leading dot (hidden/dot names), plus the empty name.
	let sep: bool = name.contains("/") || name.contains("\\");
	let dots: bool = name.contains("..") || name.starts_with(".");
	// the guard runs before any filesystem call, so a hostile name never reaches disk.
	if name.is_empty() || sep || dots {
		// refused outright: nothing was resolved, nothing was read.
		return None;
	}
	// one join + one read; every io error (missing, unreadable, a directory) folds to None.
	std::fs::read_to_string(frontend_root().join(name)).ok()
}

/// Server state: the world cache, the DB it mirrors, the tick that drives
/// the rotating PARTIAL cache reload (one section re-queried every four requests), and
/// (F3) max_seq: the highest post seq THIS writer has stamped into the DB.  Seeded once at
/// (F3) launch by db_max_seq (the only scan; the same connection load_world just used) and
/// (F3) advanced per COMMITTED insert, so apply() never re-reads the seq column.  Invariant:
/// (F3) max_seq >= every seq stored in the DB, with equality while one server owns the file;
/// (F3) another server opening the same file reseeds it at startup.  A failed reopen or a
/// (F3) rolled-back apply leaves max_seq alone, because no stamp changed in the DB from OUR
/// (F3) writer (single writer per DB file).
/// (ST) how many /log lines the RAM debug log keeps: older lines are evicted from the front,
/// so the log's footprint never grows with the request count.
pub const LOG_CAP: usize = 1_000;
/// (ST) byte-exact pieces feeding the /log request lines and fields (pins in the smoke tests
/// and test_log_entry_capture read these very values through the served lines).
pub const LOG_POST_PREFIX: &str = "POST ";
pub const LOG_HTTP_SUFFIX: &str = " HTTP/1.1";
pub const LOG_PARSE_FAILURE: &str = "parse-failure";
pub const LOG_ACCESS_DENIED: &str = "access_denied";
pub const LOG_DB_DEFAULT: &str = "twitter.db";
pub const LOG_FRONTEND_DEFAULT: &str = "frontend";
/// (ST) the CRLF line ending alias_body folds between the token and value lines.
pub const ALIAS_LINE_END: &str = "\r\n";

/// (ST) one /log entry, fully un-redacted per user instruction: the raw request line, the
/// verbatim request body (session tokens and passwords stay plaintext inside the Debug quotes
/// of the rendered line), the parsed Command and the step Result as Debug text, and whether
/// the DB commit succeeded.
#[derive(Clone, Debug)]
pub struct LogEntry {
	pub ts_secs: u64,
	pub request_line: String,
	pub body: String,
	pub command: String,
	pub result: String,
	pub committed: bool,
}

/// (ST) append one /log entry and keep the log flat: push, then evict the oldest front entry
/// while over cap, so the footprint never grows with the request count.
pub fn push_log(log: &mut Vec<LogEntry>, entry: LogEntry) {
	log.push(entry);
	// RAM debug only, not spec data: keep the newest LOG_CAP entries, evicting the front.
	if log.len() > LOG_CAP {
		log.remove(0);
	}
}

/// (ST) the one poison-tolerant lock every handler shares: the Err carries a PoisonError
/// whose guard we recover, and the guarded region keeps its invariants, so a poisoned
/// mutex still hands back a valid Server.
pub fn lock_server(state: &Mutex<Server>) -> MutexGuard<'_, Server> {
	match state.lock() {
		Ok(guard) => guard,
		Err(poisoned) => poisoned.into_inner(),
	}
}

/// (ST) the parse-failure log line shared by serve and serve_alias: byte-identical on
/// both transports — lock, then one un-redacted entry, committed stays false.
pub fn log_parse_failure(state: &Mutex<Server>, request_line: String, body: String) {
	let mut locked = lock_server(state);
	push_log(
		&mut locked.log,
		LogEntry {
			ts_secs: now_secs(),
			request_line,
			body,
			command: LOG_PARSE_FAILURE.to_string(),
			result: LOG_ACCESS_DENIED.to_string(),
			committed: false,
		},
	);
}

pub struct Server {
	pub world: World,
	pub db_path: String,
	pub tick: u64,
	/// (F3) cached max(seq) over the posts table (0 = empty DB); apply()'s stamp hint.
	pub max_seq: u64,
	/// (F9) server-held SQLite connection (None only if launch could not open the DB at all;
	/// failure arms then reopen on demand).
	pub conn: Option<SqliteConnection>,
	/// Side-index over the world; rebuilt only at reload sites (launch and the three reload arms),
	/// so step_ix probes are O(1) per request.
	pub index: WorldIndex,
	/// (ST) the /log request log: one fully un-redacted LogEntry per request (epoch secs, the raw
	/// request line, the raw body verbatim - tokens and passwords in plaintext - the Command and
	/// Result Debug texts, and the commit flag), oldest first.  RAM debug only, NOT spec data:
	/// nothing is served from it, no DB row mirrors it and a restart starts it empty, so it never
	/// feeds the model.  Capped at LOG_CAP by evicting the front.
	pub log: Vec<LogEntry>,
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

/// test-only: superseded at the serve_command call site by the delta-derived count.
/// (F3) How many posts `after` introduces over `before`: exactly the number of post INSERTs
/// (F3) apply() stamps, so Server.max_seq advances by this after a COMMITTED batch (apply()
/// (F3) stamped them sequentially at max_seq + 1 .. max_seq + that count).  World keeps both
/// (F3) post vectors pid-sorted - load_world sorts them and step preserves that order - so a
/// (F3) two-finger merge counts the extra pids with zero allocation and no hash set.
#[cfg(test)]
fn new_post_count(before: &World, after: &World) -> u64 {
	let nb: usize = before.posts.len();
	let na: usize = after.posts.len();
	let mut i: usize = 0;
	let mut j: usize = 0;
	let mut fresh: u64 = 0;
	// (F3) bounded by nb + na: every step advances i or j, so the walk always terminates.
	for _ in 0..(nb + na) {
		if j >= na {
			break;
		}
		if i >= nb {
			// (F3) before exhausted: each remaining after pid is a fresh INSERT.
			fresh += 1;
			j += 1;
		} else {
			let b: u64 = before.posts[i].0;
			let a: u64 = after.posts[j].0;
			if a < b {
				// (F3) a pid after has and before lacks: the post apply() INSERTs.
				fresh += 1;
				j += 1;
			} else if a == b {
				i += 1;
				j += 1;
			} else {
				// (F3) a pid before has and after dropped: skip it, it changes no stamp.
				i += 1;
			}
		}
	}
	fresh
}

/// D1 DB-truth discipline (failure path = full re-query) + F9 connection reuse: when reopen
/// or apply fails the World stays unadvanced, but RAM must not stay stale against the DB, so
/// the cached World is re-synced by throwing out ALL FOUR cache sections at once through db.rs's
/// reload fns, ON THE CALLER'S CONNECTION: serve_command passes its held connection for the
/// rolled-back-apply arm and a fresh reopen for the failed-reopen arm, so the connection can
/// stay alive in Server (None stays put: no DB view, exactly the old Err(_) => w behaviour,
/// now taken where serve_command reopens).  Each step moves the World, so the full re-sync
/// costs no World clone.
pub fn reload_all_sections(conn: &mut SqliteConnection, w: World) -> World {
	// accounts section first
	let with_accounts: World = reload_accounts(conn, w);
	// sessions drags its derived used_session_ids along
	let with_sessions: World = reload_sessions(conn, with_accounts);
	// the follows table alone
	let with_follows: World = reload_follows(conn, with_sessions);
	// posts + newest_first + used_post_ids move together; tail move, no clone
	reload_posts(conn, with_follows)
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
/// shared serve_command core.  The database discipline it enforces (DB2 audit V1/V2/V3/V5/V7:
/// DB is the source of truth, the cache advances only after COMMIT, one rotating section
/// re-queried per commit, poison-tolerant lock) is documented ONCE on serve_command.
pub fn serve(path: String, body: Capped<String>, state: &Mutex<Server>) -> Served {
	// (ST) the request line, built ONCE here so every /log exit below names the request verbatim.
	let request_line: String = LOG_POST_PREFIX.to_string() + &path + LOG_HTTP_SUFFIX;
	// Parse first so malformed bodies never touch the world.
	let command: Command = match parse_action(path.as_str(), body.value.as_bytes()) {
		Err(e) => {
			// (ST) a parse failure is logged too (un-redacted, committed stays false): the request
			// never reaches the world, so the DB stays untouched.
			log_parse_failure(state, request_line, body.value);
			return Served {
				response: to_http(wire_error(e)),
			};
		}
		Ok(action) => to_command(action),
	};
	serve_command(command, request_line, body.value, state)
}

/// (ST) the /log endpoint name of a Command: the request-line name the spec's Interface uses for
/// the route that produced it, so a log line reads like "post-tweet".  Publish serves both /api/post-tweet
/// and /api/post-reply, whose model Command is the same Publish, so both land under post-tweet;
/// TimePasses is not wire-reachable and is named for completeness.  (ST) Since the LOG1 change
/// this naming table is test-only: /log lines carry the real request line instead.
#[cfg(test)]
pub fn command_to_logline(c: &Command) -> String {
	match c {
		// both /api/post-tweet and /api/post-reply share the model's Publish
		Command::Publish(..) => "post-tweet".to_string(),
		Command::Delete(..) => "delete-tweet".to_string(),
		// the spec's read-post is the get-tweet endpoint
		Command::ReadPost(..) => "get-tweet".to_string(),
		Command::ReadPersonalTimeline(..) => "private-timeline".to_string(),
		Command::ReadGlobalTimeline(..) => "global-timeline".to_string(),
		// login / logout are Authenticate / RevokeToken in the model
		Command::Authenticate(..) => "login".to_string(),
		Command::RevokeToken(..) => "logout".to_string(),
		// signup is Register in the model
		Command::Register(..) => "signup".to_string(),
		// the follows endpoints keep their route names
		Command::Follow(..) => "follow-user".to_string(),
		Command::Unfollow(..) => "unfollow-user".to_string(),
		// the like endpoints keep their route names
		Command::Like(..) => "like-tweet".to_string(),
		Command::Unlike(..) => "unlike-tweet".to_string(),
		// TimePasses is the spec's silent clock tick: no route reaches it, so the name is nominal.
		Command::TimePasses => "time-passes".to_string(),
	}
}

/// (ST) the /raw body: the World's Debug rendering as raw plaintext, pretty-printed with {:#?} so
/// it is one field per line and curl or a browser shows the record verbatim.  Pure RAM debug,
/// never served as spec data.
pub fn raw_text(w: &World) -> String {
	// std.debug.show == Rust's Debug rendering of the record
	// one format!: the {:#} flag and the record share one pass, no concat of Strings
	// the reference renders through World's own Debug, so the # flag reaches every field
	format!("{:#?}", w)
}

/// The shared core behind all 13 POST routes and the 3 GET aliases: step, COMMIT,
/// rotate, render.  Enforces the AGENTS.md database rules (DB2 audit V1/V2/V3/V5/V7):
/// the database is the source of truth, not RAM.  The world cache advances ONLY after
/// apply reports the BEGIN/COMMIT transaction committed; a failed reopen or a rolled-back
/// apply (PK clashes on RAM-sampled ids included) serves NO data and answers the 403
/// access_denied shape, so nothing can be served that is not committed in the DB.  After
/// every commit exactly ONE cache section is thrown out and re-queried from the same
/// connection, rotating follows -> sessions -> accounts -> posts by tick: RAM is refreshed
/// periodically, never all at once, and load_world runs only at launch (as does the one
/// max(seq) scan behind Server.max_seq, so apply() gets its stamp hint from RAM).  The lock is
/// poison-tolerant: the guarded region keeps its invariants (move-swap + step + recoverable
/// DB errors), so a poisoned guard still holds a valid Server.
pub fn serve_command(
	command: Command,
	request_line: String,
	body: String,
	state: &Mutex<Server>,
) -> Served {
	// Poison-tolerant lock: the Err carries a PoisonError whose guard we recover.
	let mut locked = lock_server(state);
	// (ST) one epoch stamp per request: every request is logged at BOTH exits below, and the
	// committed flag distinguishes the rollbacks from the committed answers.
	let ts: u64 = now_secs();
	// (OPT-1) the (F9) swap-out idiom applied to the World: `before` MOVES out of the Server and
	// (OPT-1) empty_world() (the Agda-pinned identity) is the placeholder left in its stead, so a
	// (OPT-1) request costs ZERO World deep-copies.  Every exit below hands `before` back into
	// (OPT-1) locked.world (directly or through a reload that consumes it), undoing the swap.
	// (OPT-1) A panic between the swap and a restore leaves the placeholder, exactly as a panic
	// (OPT-1) between the conn swap and a store-back leaves Server.conn = None: the DB stays the
	// (OPT-1) source of truth, and the next request's reopen/reload re-syncs RAM.
	let mut before: World = empty_world();
	std::mem::swap(&mut locked.world, &mut before);
	// The spec fresh-id sampler, run under the lock: ONE 16-byte read yields both ids and the
	// world is read by reference, so neither per-request World clone survives.
	let (fresh_pid, fresh_sid): (u64, u64) = sample_id(&before);
	// (ST) the Command's Debug text, taken BEFORE command moves into step_d.
	let command_txt: String = format!("{:?}", command);
	// (F4b) evaluate through the held side-index: zero index rebuilds per request.
	// (F1b) effect-only step: step_d returns (Result, Delta) and patch_world rebuilds the after
	// World, so no World is cloned inside the model; (OPT-1) step_d, apply_delta and the failure
	// arms read `before` by reference or move, so it never gets copied per request.
	let stepped: (Result, Delta) = step_d(&before, &locked.index, command, fresh_pid, fresh_sid);
	let result: Result = stepped.0;
	let delta: Delta = stepped.1;
	// (ST) the Result's Debug text, computed ONCE and shared by both /log exits below.
	let result_txt: String = format!("{:?}", result);
	// (F1b) the new-post count is delta-derived: Publish is the only branch that INSERTs one row.
	let new_posts: u64 = match delta {
		Delta::Publish(..) => 1,
		_ => 0,
	};
	// (OPT-1) NO World copy on this path at all: `after` is built INSIDE the committed arm below,
	// (OPT-1) once apply_delta has borrowed `before` and can hand it over by move.  Delta still
	// (OPT-1) has two consumers (apply_delta below and patch_world in the committed arm), so the
	// (OPT-1) single Delta payload copy stays - it is the small side, never a World.
	// COMMIT FIRST: (F9) the connection HELD in Server answers every request - no reopen and
	// no db_path String copy on the happy path.  RAM-sampled ids can collide; apply PK failure
	// rolls back and reports false.
	// (F9) The held connection is swapped out of the Mutex-guarded Server into local scope for
	// the request: that is the borrow strategy - conn borrowed &mut as a local while the other
	// Server fields (world/tick/max_seq/conn) are assigned through the guard, and every arm
	// below stores its connection back into Server, undoing the swap on every path.
	let mut held_conn: Option<SqliteConnection> = None;
	std::mem::swap(&mut locked.conn, &mut held_conn);
	let committed: bool = match held_conn {
		// Failed-reopen arm (the Server never got a connection at launch, or an earlier
		// failure dropped one): D1's fresh reopen, exactly once per request here.  On Err the
		// cache stays put (no DB view - the old helper's Err(_) => w arm moved into this call
		// site); on Ok the re-sync runs over the fresh connection and THAT connection becomes
		// the Server's new one, so later requests pay no reopen either.
		// (F3) max_seq stays as it is: no batch ran, so OUR writer moved no stamp.
		// (F9) reopen happens ONLY here: launch lost the connection somehow.
		None => match reopen(locked.db_path.clone()) {
			Err(_) => {
				// (OPT-1) restore arm: nothing reopened, so `before` MOVES back into the Server,
				// (OPT-1) undoing the swap-out above (the DB view never existed on this exit).
				std::mem::swap(&mut locked.world, &mut before);
				false
			}
			Ok(mut fresh_conn) => {
				// (OPT-1) restore arm: `before` MOVES into the reload and the re-synced World lands
				// (OPT-1) back in the Server, so the swap-out above is undone on this exit.
				locked.world = reload_all_sections(&mut fresh_conn, before);
				// (F4b) reload site: re-sync the side-index with the reassigned world.
				locked.index = build_index(&locked.world);
				// (F9) store the fresh connection: reopened once, reused from then on.
				locked.conn = Some(fresh_conn);
				// D1: nothing committed, so the World stays unadvanced: 403 below.
				false
			}
		},
		// Held path: apply and the one-section reload reuse the SAME connection per request
		// (F9 hot path: zero establish, zero path copy).
		Some(mut conn) =>
		// (F3) The stamp hint is the Server's cached max_seq: apply() never re-scans the
		// (F3) posts table for it.
		{
			// (F2) delta-driven commit: one batch per Command effect, no two-World diff.
			// (OPT-1) the Delta is copied HERE so the original moves into patch_world below.
			if apply_delta(&mut conn, &before, delta.clone(), locked.max_seq) {
				// (F3) Committed: apply() stamped exactly new_posts new posts at max_seq + 1
				// (F3) .. max_seq + k, so the cache hint advances by k and stays exact for the
				// (F3) next request (the failure arms above leave it put).
				locked.max_seq += new_posts;
				// (OPT-1) patch_world(before, delta) MOVES `before`: apply_delta borrowed it just
				// (OPT-1) above, so the Server's World is rebuilt from the local copy with zero
				// (OPT-1) World clones, and the swap-out is consumed on this committed path.
				let after: World = patch_world(before, delta);
				// Committed: advance the cache AND rotate ONE section through the SAME held
				// connection (F9: this connection was established at launch, not per request);
				// after the commit so the fresh writes stay visible.  after is moved, so the
				// reload costs no extra World clone.
				let reloaded: World = match locked.tick {
					0 => reload_follows(&mut conn, after),
					1 => reload_sessions(&mut conn, after),
					2 => reload_accounts(&mut conn, after),
					_ => reload_posts(&mut conn, after),
				};
				locked.world = reloaded;
				// (F4b) reload site: re-sync the side-index with the rotated cache.
				locked.index = build_index(&locked.world);
				locked.tick = next_tick(locked.tick);
				// (F9) keep the held connection: it committed, stayed open and consistent.
				locked.conn = Some(conn);
				true
			} else {
				// Rolled back: the DB refused the update, RAM must not advance.  D1 re-syncs
				// fully over the HELD connection - a ROLLBACK leaves the DB consistent and the
				// connection usable, already proven by the db.rs tests that chain applies on
				// one conn (and by test_apply_conn_reuse below).
				// (F3) max_seq stays as it is: the ROLLBACK restored every stamp, so OUR writer
				// (F3) changed nothing in the DB and the hint is still exact.
				// (OPT-1) restore arm: `before` MOVES into the reload and the re-synced World lands
				// (OPT-1) back in the Server, so the swap-out above is undone on this exit.
				locked.world = reload_all_sections(&mut conn, before);
				// (F4b) reload site: re-sync the side-index after the rolled-back re-sync.
				locked.index = build_index(&locked.world);
				// (F9) keep the held connection: the rollback left it open and consistent.
				locked.conn = Some(conn);
				// D1: nothing committed, so the World stays unadvanced: 403 below.
				false
			}
		}
	};
	// (ST) exactly one LogEntry per request, built once: the committed flag from the apply arm
	// above already distinguishes the rollback below from the committed answer.
	push_log(
		&mut locked.log,
		LogEntry {
			ts_secs: ts,
			request_line,
			body,
			command: command_txt,
			result: result_txt,
			committed,
		},
	);
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
			text.push_str(ALIAS_LINE_END);
			text
		}
	};
	let tail: String = match value {
		None => "".to_string(),
		Some(text) => text,
	};
	// head + tail + "\r\n" -> push into head, same bytes
	(head).push_str(&tail);
	head.push_str(ALIAS_LINE_END);
	head
}

/// The raw value of one query parameter on the GET aliases: absent, bare (no '=') or
/// empty all mean None (the legacy app.js always sends token=, empty when anonymous); the
/// first pair with the name wins and later duplicates are ignored.
pub fn query_param(query: &str, name: &str) -> Option<String> {
	// find_map stops at the first pair whose name matches, so no Vec of all hits is
	// built; the verdicts stay the same: a later duplicate never decides the answer
	let hit: Option<String> = (query.split('&')).find_map(|pair| match pair.find("=") {
		// a bare pair matching the name still counts as a hit, with empty value
		None => match *pair == (*name) {
			true => Some("".to_string()),
			false => None,
		},
		// the name is the prefix before the first '=', even when '=' is in the value
		Some(at) => match (*pair)[..at] == *name {
			true => Some(pair[(at + 1)..].to_string()),
			false => None,
		},
	});
	match hit {
		None => None,
		Some(value) => match value.is_empty() {
			true => None,
			// value is already a fresh String: move it, no second copy.
			false => Some(value),
		},
	}
}

/// The one handler behind the 3 GET aliases: the query parameters become the POST-
/// equivalent body, then the very parse_action and shared core the POST routes use.
pub fn serve_alias(
	origin: &Origin<'_>,
	state: &Mutex<Server>,
	path: &str,
	value_name: &str,
) -> Served {
	// no copy of the query: a &str view of the Origin's query part
	let query: &str = match origin.query() {
		None => "",
		// (same bytes; the view borrows from the Origin, which lives past here)
		Some(part) => part.as_str(),
	};
	let body: String = alias_body(query_param(query, "token"), query_param(query, value_name));
	// (ST) the request line as it arrived: the query part only when the Origin carried one.
	let query_part: String = match query.is_empty() {
		true => "".to_string(),
		false => "?".to_string() + query,
	};
	let request_line: String = "GET ".to_string() + path + &query_part + LOG_HTTP_SUFFIX;
	let command: Command = match parse_action(path, body.as_bytes()) {
		Err(e) => {
			// Malformed or missing numbers render as the same 403 access_denied shape
			// the POST twins answer (wire_error discards e; no new error codes).
			// (the request never reaches the world, so the DB stays untouched)
			// (identical bytes to a POST parse failure, header for header)
			// (404 and 422 can never surface for an alias request)
			// (ST) logged un-redacted with the raw body, before the early return
			log_parse_failure(state, request_line, body);
			return Served {
				// (the answer is rendered by the very same to_http every POST route uses)
				response: to_http(wire_error(e)),
			};
		}
		Ok(action) => to_command(action),
	};
	serve_command(command, request_line, body, state)
}

/// GET /api/get-tweet: the legacy frontend's query-parameter twin of the POST route.
#[get("/api/get-tweet")]
fn get_tweet_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(origin, state, "/api/get-tweet", "id")
}

/// GET /api/global-timeline.
#[get("/api/global-timeline")]
fn global_timeline_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(origin, state, "/api/global-timeline", "len")
}

/// GET /api/private-timeline.
#[get("/api/private-timeline")]
fn private_timeline_alias(state: &State<Mutex<Server>>, origin: &Origin<'_>) -> Served {
	serve_alias(origin, state, "/api/private-timeline", "len")
}

/// Static frontend serving, in the very Response shape to_http builds: headers folded onto an
/// empty Response, then Status and a sized_body cursor.  Both arms return a Response (never an
/// Option), so a missing or refused file answers a plain empty 404 built HERE rather than rocket's
/// own template page: one coherent strategy covers hit and miss, and no bytes are invented.
pub fn serve_static(name: String, mime: String) -> Response<'static> {
	// read per request, never cached in RAM, so the disk stays the only source of the site.
	match read_frontend(name.as_str()) {
		// refused or absent: empty 404, so a stale frontend degrades instead of inventing bytes
		// (the traversal names read_frontend refused land here too, nothing was opened on disk)
		None => build_response(Status::NotFound, None, None),
		// the hit: 200 plus the Content-Type the route picked, body as a fixed cursor
		// (header name lowercase, the very casing the wire responses already send)
		Some(site) => build_response(Status::Ok, Some(mime), Some(site)),
	}
}

/// GET /: the static frontend's index.html (ST) static frontend per recovered instruction.
#[get("/")]
fn index() -> Served {
	Served {
		response: serve_static("index.html".to_string(), "text/html".to_string()),
	}
}

/// GET /style.css: the site's stylesheet, as text/css (ST).
#[get("/style.css")]
fn style() -> Served {
	Served {
		response: serve_static("style.css".to_string(), "text/css".to_string()),
	}
}

/// GET /app.js: the site's script, as application/javascript (ST).
#[get("/app.js")]
fn app_js() -> Served {
	Served {
		response: serve_static("app.js".to_string(), "application/javascript".to_string()),
	}
}

/// (ST) the debug-body builder behind /raw and /log: a 200 with the given content type and
/// a String body, in the very Response shape serve_static builds for a frontend hit.
pub fn serve_text(body: String, mime: String) -> Response<'static> {
	// (the same header/status/cursor fold serve_static uses, so /raw and /log never invent
	// (a different wire shape than the static site already sends)
	build_response(Status::Ok, Some(mime), Some(body))
}

/// (ST) the one Response fold behind serve_static and serve_text: headers, Status and a
/// sized_body cursor in the very shape to_http fixes.  A missing mime or body adds no
/// header and no bytes, so the empty 404 stays empty.
pub fn build_response(
	status: Status,
	mime: Option<String>,
	body: Option<String>,
) -> Response<'static> {
	let mut built = Response::build();
	match mime {
		None => {}
		Some(mime_text) => {
			built.header(Header::new("content-type", mime_text));
		}
	};
	built.status(status);
	match body {
		None => {}
		Some(text) => {
			built.sized_body(text.len(), Cursor::new(text));
		}
	};
	built.finalize()
}

/// GET /raw: the whole RAM cache as raw plaintext Debug, pretty-printed (ST) - a debug view only:
/// it is never fed back and the database stays the source of truth.
#[get("/raw")]
fn raw(state: &State<Mutex<Server>>) -> Served {
	// The same poison-tolerant lock serve_command takes: the guarded region keeps its invariants,
	// so a poisoned guard still answers with its cache.
	let locked = lock_server(state);
	Served {
		response: serve_text(raw_text(&locked.world), "text/plain".to_string()),
	}
}

/// GET /log: every request serve_command saw, one FULLY UN-REDACTED line per request (ST):
/// IMF timestamp, the raw request line, the verbatim BODY (Debug-quoted, tokens and passwords in
/// plaintext), the Command and Result Debug texts and the commit flag.  RAM debug only, never
/// spec data: a restart re-opens the DB but starts the log empty, so nothing is served from
/// the database here.
#[get("/log")]
fn request_log(state: &State<Mutex<Server>>) -> Served {
	// The same poison-tolerant lock serve_command takes.
	let locked = lock_server(state);
	// (one line per entry: the stored epoch secs through the very calendar walk a Date header
	// (uses, so a log timestamp never disagrees with a response header, then the raw request line
	// (and the verbatim body, the Command/Result Debug texts and the commit flag (CRLF-terminated;
	// (the 3 static routes never log, so the site's own traffic stays out)
	let mut lines: Vec<String> = vec![];
	for entry in &locked.log {
		lines.push(format!(
			"{} {} BODY[{:?}] CMD[{}] RES[{}] COMMITTED[{}]\r\n",
			http_date_from(entry.ts_secs),
			entry.request_line,
			entry.body,
			entry.command,
			entry.result,
			entry.committed,
		));
	}
	Served {
		response: serve_text(lines.join(""), "text/plain".to_string()),
	}
}
/// Launch: re-load the world from FT_DB (default twitter.db) and mount all 13 POST
/// endpoints plus the 3 GET aliases the legacy frontend speaks, the 3 static frontend routes and
/// the 2 RAM-debug routes /raw (the whole cache as Debug text) and /log (the request log).
/// The site dir itself is FT_FRONTEND (default frontend, guarded by frontend_dir_name), so
/// frontend2/ frontend3/ frontend4/ variants preview without replacing frontend/.
#[launch]
fn rocket() -> _ {
	// The DB path comes from the environment so restarts resume the same world.
	let path: String = match std::env::var("FT_DB") {
		Err(_) => LOG_DB_DEFAULT.to_string(),
		Ok(p) => p,
	};
	// Startup reopen must not panic; on failure the empty world still serves.
	// (F9) The world cache and the stamp hint come from ONE launch connection: db_max_seq is
	// (F9) the only max(seq) scan, so no per-request SELECT of the seq column survives.  F9 also
	// (F9) keeps that very connection alive in Server.conn instead of dropping it at launch.
	let (world, max_seq, conn): (World, u64, Option<SqliteConnection>) =
		match init_or_open(path.clone()) {
			Err(_) => (empty_world(), 0, None),
			Ok(mut conn) => {
				// (F9) This connection never dies: it is handed to Server.conn and reused by every
				// (F9) request, so serve_command's happy path pays no establish at all.
				let seeded: World = load_world(&mut conn);
				(seeded, db_max_seq(&mut conn), Some(conn))
			}
		};
	// Mount every endpoint at the path the spec fixes.
	rocket::build()
		.manage(Mutex::new(Server {
			// (F4b) the one launch rebuild; requests only probe the held index.
			index: build_index(&world),
			world,
			db_path: path,
			tick: 0,
			max_seq,
			// (F9) the launch connection, alive for the whole process (None only if launch
			// could not open the DB at all; failure arms then reopen on demand).
			conn,
			// (ST) the /log RAM debug log starts empty: a restart re-opens the DB but not the log.
			log: vec![],
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
				// (ST) static frontend per recovered instruction: the site is served off disk.
				index,
				style,
				app_js,
				// (ST) the state dump and the request log: RAM debug views, unlogged and never fed back.
				raw,
				request_log,
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
	// Run the very failure-path re-sync serve_command performs, over the connection in hand
	// (F9: the helper takes the caller's connection now; serve_command passes its held one).
	let reloaded: World = reload_all_sections(&mut conn, tampered.clone());
	// The DB view: a fresh canonical load to compare the re-synced cache against.
	let mut again = init_or_open(path.to_string()).unwrap();
	let expected: World = load_world(&mut again);
	// ALL FOUR sections restored: the cache now agrees with the DB everywhere.
	assert!(reloaded == expected);
	// The tampering really existed, and did not survive the re-query.
	assert!(tampered != expected);
	// Double-failure arm: no openable DB means no DB view, which is exactly where serve_command
	// keeps the cache put - its reopen yields Err.  (F9 moved that Err(_) => w arm to the call
	// site, so the pin here is the precondition: reopen of the missing-directory path is Err;
	// should it ever be Ok, re-syncing over that stray connection would also have to leave the
	// tampered World put for the keep to be honest.)
	assert!(
		match reopen("/tmp/ft-no-such-dir/ft-x.sqlite".to_string()) {
			Err(_) => true,
			Ok(mut stray_conn) =>
				reload_all_sections(&mut stray_conn, tampered.clone()) == tampered,
		}
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
	assert!(query_param("token=7&id=42", "token") == Some("7".to_string()));
	assert!(query_param("token=7&id=42", "id") == Some("42".to_string()));
	// empty token= means anonymous, same as an absent token.
	assert!(query_param("token=&id=42", "token").is_none());
	assert!(query_param("id=42", "token").is_none());
	// a bare pair has the empty value; a duplicate keeps the first.
	assert!(query_param("id", "id").is_none());
	assert!(query_param("id=1&id=2", "id") == Some("1".to_string()));
	// end to end: the alias body is the POST twin's body, byte for byte.
	// (the anonymous case reuses the token-less POST shape)
	assert!(
		alias_body(
			query_param("token=7&id=42", "token"),
			query_param("token=7&id=42", "id")
		) == "7\r\n42\r\n"
	);
	assert!(
		alias_body(
			query_param("token=&id=42", "token"),
			query_param("token=&id=42", "id")
		) == "42\r\n"
	);
}

/// F4b pin: the held side-index is interchangeable with the Vec scans - step_ix over a built
/// index equals step, and a reload-site rebuild round-trips the account lookups.
#[test]
fn test_serve_index_consistency() {
	// DB/model handles scoped to the test so the non-test build keeps zero unused imports.
	use formal_twitter::model::{account_at_ix, account_at_ref, step, step_ix};
	// Pure-RAM fixture: the index is a World-side structure, no DB view involved.
	let w: World = empty_world();
	// (launch build, exactly what rocket() stores next to the world cache)
	let stepped_ix: (World, Result) = step_ix(
		&w,
		&build_index(&w),
		Command::Register("u".to_string(), "p".to_string()),
		1,
		2,
	);
	// Same args through the scan path: byte-identical verdict, the index adds no drift.
	assert!(
		stepped_ix
			== step(
				&w,
				Command::Register("u".to_string(), "p".to_string()),
				1,
				2
			)
	);
	// The reload-site rebuild round-trips: hits AND misses agree with the reference scan.
	let stepped: World = stepped_ix.0;
	let rebuilt: WorldIndex = build_index(&stepped);
	assert!(account_at_ix(&stepped, &rebuilt, "u") == account_at_ref(&stepped, "u").cloned());
	assert!(account_at_ix(&stepped, &rebuilt, "zz") == account_at_ref(&stepped, "zz").cloned());
}

/// F1b pin: the serve_command path (step_d + patch_world + delta-derived k) equals the scan
/// reference step, and the Publish Delta is the only INSERT, so k matches new_post_count.
#[test]
fn test_delta_publish_equiv() {
	// the scan-path reference plus the literal-world constructors, scoped to the test build.
	// (the top-level use-line keeps step out of the non-test build)
	use formal_twitter::model::{Account, SessionStatus, Visibility, step};
	// alice owns the account so the published post's visibility follows her default.
	let w: World = World {
		accounts: vec![(
			"alice".to_string(),
			Account {
				password: "p".to_string(),
				default_visibility: Visibility::FollowersOnly,
			},
		)],
		// session 1 is alice's and active, so Publish(1, ..) is admitted.
		sessions: vec![(1, SessionStatus::Active("alice".to_string()))],
		posts: vec![],
		follows: vec![],
		newest_first: vec![],
		used_post_ids: vec![],
		// 1 is already taken, so the sampler's fresh sid 7 stays distinct.
		used_session_ids: vec![1],
	};
	let cmd: Command = Command::Publish(1, "hi".to_string(), None);
	// reference: the scan path, same fresh ids 42/7 as serve_command samples per request.
	let (want, want_res): (World, Result) = step(&w, cmd.clone(), 42, 7);
	// serve_command's own path: effect through the built index, then patch.
	let (res, delta): (Result, Delta) = step_d(&w, &build_index(&w), cmd.clone(), 42, 7);
	// delta cloned for the patch so the test keeps ownership of the effect for its own pins.
	let after: World = patch_world(w.clone(), delta.clone());
	assert!(res == Result::CreatedPost(42) && res == want_res && after == want);
	// the Delta is Publish outright: it carries the fresh pid, author, text and account default.
	assert!(
		delta
			== Delta::Publish(
				42,
				"alice".to_string(),
				"hi".to_string(),
				Visibility::FollowersOnly,
				None,
			)
	);
	// the delta-derived k equals the two-finger counter and both say one new post.
	let new_posts: u64 = match delta {
		Delta::Publish(..) => 1,
		_ => 0,
	};
	assert!(new_posts == 1 && new_posts == new_post_count(&w, &after));
}

/// read_frontend finds the site's index.html and returns exactly the bytes on disk.
#[test]
fn test_static_index_matches_disk() {
	// resolve the same dir, then read index.html straight off disk for the reference value.
	// frontend_root's install arm is absent under cargo test, so this is the repo's frontend/.
	let disk: String =
		std::fs::read_to_string(frontend_root().join("index.html")).unwrap_or("".to_string());
	// the helper must find the same bytes: Some == Some, and equal contents.
	assert_eq!(read_frontend("index.html"), Some(disk));
}

/// The traversal guard is total: no name escapes the site, so every escape attempt reads nothing.
#[test]
fn test_static_blocks_traversal() {
	// a literal climb out of the site, a nested one that climbs twice, and the empty name.
	assert!(read_frontend("../spec/Twitter.agda").is_none());
	assert!(read_frontend("a/../../x").is_none());
	assert!(read_frontend("").is_none());
	// a backslash flavour and a dot-prefixed name are refused the same way.
	assert!(read_frontend("..\\spec\\Twitter.agda").is_none());
	assert!(read_frontend(".hidden").is_none());
}

/// The pure FT_FRONTEND name guard: clean variant names pass through verbatim and every
/// hostile spelling falls back to the shipped "frontend", testable with zero env mutation.
#[test]
fn test_frontend_dir_name_validation() {
	// the shipped default and the preview variants answer with the very name given.
	assert_eq!(frontend_dir_name("frontend"), "frontend".to_string());
	assert_eq!(frontend_dir_name("frontend2"), "frontend2".to_string());
	assert_eq!(frontend_dir_name("frontend4"), "frontend4".to_string());
	// the empty name, a literal climb, a nested one, a bare .. and a dot-prefixed name all fall
	// back to the shipped site.
	assert_eq!(frontend_dir_name(""), "frontend".to_string());
	assert_eq!(frontend_dir_name("../evil"), "frontend".to_string());
	assert_eq!(frontend_dir_name("a/b"), "frontend".to_string());
	assert_eq!(frontend_dir_name(".."), "frontend".to_string());
	assert_eq!(frontend_dir_name(".hidden"), "frontend".to_string());
	// a backslash flavour is refused the same way, with and without a climb.
	assert_eq!(frontend_dir_name("..\\evil"), "frontend".to_string());
	assert_eq!(frontend_dir_name("a\\b"), "frontend".to_string());
}

/// frontend_root_named DEV fallback: under cargo test the install arm is absent (no $out),
/// so every name resolves to CARGO_MANIFEST_DIR/../<name>, one level up from backend/.
#[test]
fn test_frontend_root_named_fallback() {
	// the very dev shape the helper builds: backend/../ plus the name, spelled out here.
	let base: std::path::PathBuf = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
	// the install arm stays absent: target/debug/../frontend2 is no site dir on the test
	// machine, so the dev path answers for a variant the repo may not even ship.
	assert_eq!(frontend_root_named("frontend2"), base.join("frontend2"));
	// a second variant differs only by the name, so previewing frontend3 changes one component.
	assert_eq!(frontend_root_named("frontend3"), base.join("frontend3"));
	// the shipped name matches the old, unparameterized shape: backend/../frontend.
	assert_eq!(frontend_root_named("frontend"), base.join("frontend"));
	// the repo's default site exists, so the default resolves to a real dir (serve_static's source).
	assert!(frontend_root_named("frontend").is_dir());
}

/// FT_FRONTEND default: cargo test never sets FT_FRONTEND, so frontend_root stays byte-identical
/// to the named helper at the shipped site: today's behavior, unchanged, when the env is absent.
#[test]
fn test_ft_frontend_default() {
	assert_eq!(frontend_root(), frontend_root_named("frontend"));
	// the guard maps the empty name to the shipped site, so an absent env and an empty
	// override land on the very same dir.
	assert_eq!(
		frontend_root(),
		frontend_root_named(frontend_dir_name("").as_str())
	);
}

/// (ST) the /raw body shape: raw plaintext pretty-printing of the World's Debug rendering, with real
/// records inside - the struct names are what a reader greps the dump for.  Deliberately no Agda:
/// the rendering is Rust's own that the spec never mentions (cf. the F2 note at
/// ImplProofs.agda:516).
#[test]
fn test_raw_text_shape() {
	// the model handles are scoped here so the non-test build keeps zero unused imports.
	use formal_twitter::model::{Account, Post, PostStatus, Visibility};
	// the smallest World that still carries every record the dump must show: one account, one post.
	let tiny: World = World {
		accounts: vec![(
			"alice".to_string(),
			Account {
				password: "a".to_string(),
				default_visibility: Visibility::Everyone,
			},
		)],
		sessions: vec![],
		posts: vec![(
			1,
			Post {
				author: "alice".to_string(),
				text: "hi".to_string(),
				visibility: Visibility::Everyone,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent: None,
			},
		)],
		follows: vec![],
		newest_first: vec![1],
		used_post_ids: vec![1],
		used_session_ids: vec![],
	};
	let body: String = raw_text(&tiny);
	// raw plaintext: nothing wraps the dump, and it opens on the record itself, one field per line
	// (Rust's pretty Debug indents each field with four spaces).
	assert!(!body.starts_with("<pre>"));
	assert!(body.starts_with("World {"));
	assert!(body.contains("\n    "));
	// the payload is Debug of the record: both struct names appear in their record form.
	assert!(body.contains("World {"));
	assert!(body.contains("Post {"));
}

/// (ST) the /log naming: every Command constructor logs under the Interface request name of the
/// route that produced it, i.e. command_to_logline after to_command is the request name the
/// spec's Interface puts in the POST line.  Pinned by the 15 ImplWire.agda theorems read through
/// from-input; Publish answers BOTH /api/post-tweet and /api/post-reply, whose model Command is
/// the same Publish, and TimePasses is the spec's silent tick no route reaches.  (ST) The naming
/// table is now test-only: /log lines carry the real request line instead of these names.
#[test]
fn test_log_line_naming() {
	assert_eq!(
		command_to_logline(&Command::Publish(1, "x".to_string(), None)),
		"post-tweet"
	);
	assert_eq!(
		command_to_logline(&Command::Publish(1, "x".to_string(), Some(2))),
		"post-tweet"
	);
	assert_eq!(command_to_logline(&Command::Delete(1, 2)), "delete-tweet");
	assert_eq!(
		command_to_logline(&Command::ReadPost(Some(1), 2)),
		"get-tweet"
	);
	assert_eq!(command_to_logline(&Command::ReadPost(None, 2)), "get-tweet");
	assert_eq!(
		command_to_logline(&Command::ReadPersonalTimeline(1, 3)),
		"private-timeline"
	);
	assert_eq!(
		command_to_logline(&Command::ReadGlobalTimeline(Some(1), 3)),
		"global-timeline"
	);
	assert_eq!(
		command_to_logline(&Command::ReadGlobalTimeline(None, 3)),
		"global-timeline"
	);
	assert_eq!(
		command_to_logline(&Command::Authenticate("a".to_string(), "b".to_string())),
		"login"
	);
	assert_eq!(command_to_logline(&Command::RevokeToken(1)), "logout");
	assert_eq!(
		command_to_logline(&Command::Register("a".to_string(), "b".to_string())),
		"signup"
	);
	assert_eq!(
		command_to_logline(&Command::Follow(1, "b".to_string())),
		"follow-user"
	);
	assert_eq!(
		command_to_logline(&Command::Unfollow(1, "b".to_string())),
		"unfollow-user"
	);
	assert_eq!(command_to_logline(&Command::Like(1, 2)), "like-tweet");
	assert_eq!(command_to_logline(&Command::Unlike(1, 2)), "unlike-tweet");
	assert_eq!(command_to_logline(&Command::TimePasses), "time-passes");
}

/// doc: "(LOG1b) the un-redacted capture: one serve_command call appends exactly one LogEntry — the built POST/GET request line byte-exact, the body VERBATIM (session tokens and passwords stay plaintext), the parsed Command Debug text and the committed flag from the arm that ran."
#[test]
fn test_log_entry_capture() {
	use std::sync::MutexGuard;
	// Scoped imports so the non-test build keeps zero unused names:
	// (std::fs::remove_file: a fresh DB file, so both commit flags are deterministic)
	// (std::sync::MutexGuard: the poison-tolerant read-back, same idiom as serve_command)
	// formal_twitter::db::{init_or_open, reopen} and the model handles are main.rs's own
	// (top-level imports: init_or_open is main.rs:17, reopen serves_command's :573 uses too.)
	// (the DB path: /tmp keeps the smoke tests' DB files distinct from this one.)
	let db: String = "/tmp/ft-logentry.sqlite".to_string();
	// Fresh DB file: delete any leftover so re-runs pin the SAME committed flags.
	_ = std::fs::remove_file(&db);
	// Create the DB: init_or_open establishes plus CREATEs; the connection is DROPPED, so
	// (the first serve_command call below must take the reopen arm (which reports committed
	// (false and stores the fresh connection) and only THEN the held-connection commit arm.
	_ = init_or_open(db.clone());
	// The Server the routes manage: empty cache, NO held connection (conn: None), the log
	// (starts empty - the very construction launch runs at main.rs:1025 with Mutex::new.
	let srv: Mutex<Server> = Mutex::new(Server {
		world: empty_world(),
		db_path: db,
		tick: 0,
		max_seq: 0,
		conn: None,
		index: build_index(&empty_world()),
		log: vec![],
	});
	// Call 1: the reopen arm re-syncs and stores a connection but commits NOTHING, so one
	// (un-redacted entry with committed==false lands even on the 403 answer.
	// (the body carries the plaintext password; the request line is the built POST line.)
	_ = serve_command(
		Command::Register("erin".to_string(), "pw".to_string()),
		"POST /api/signup HTTP/1.1".to_string(),
		"erin\r\npw".to_string(),
		&srv,
	);
	// Call 2: conn is Some now, so apply_delta COMMITs the register INSERT over the re-synced
	// (empty DB (a DENIED register would commit its zero-statement no-op delta instead, so the
	// (flag stays true either way: Register ignores the RAM-sampled ids, hence deterministic).
	_ = serve_command(
		Command::Register("erin".to_string(), "pw".to_string()),
		"POST /api/signup HTTP/1.1".to_string(),
		"erin\r\npw".to_string(),
		&srv,
	);
	// Read back through the same poison-tolerant lock serve_command takes.
	let g: MutexGuard<Server> = lock_server(&srv);
	// One entry per call, oldest first: two calls, two LogEntry rows, nothing evicted.
	// (the naming table stays out of the line: request_line is the built POST line verbatim.)
	assert!(g.log.len() == 2);
	assert_eq!(
		g.log[0].request_line,
		"POST /api/signup HTTP/1.1".to_string()
	);
	assert_eq!(
		g.log[1].request_line,
		"POST /api/signup HTTP/1.1".to_string()
	);
	// Body VERBATIM: plaintext password, CRLF join kept as one string, no redaction.
	// (the /log rendering re-quotes it via {:?}, but the stored String stays raw.)
	assert_eq!(g.log[0].body, "erin\r\npw".to_string());
	assert_eq!(g.log[1].body, "erin\r\npw".to_string());
	// The Command arm: the Debug text of the parsed Command, taken before it moves into step_d.
	// (register is the /api/signup route's constructor, so its name is in there.)
	assert!(g.log[0].command.contains("Register"));
	// The Result Debug text is never empty at either exit (403 arm included).
	assert!(!g.log[0].result.is_empty());
	assert!(!g.log[1].result.is_empty());
	// The committed flag distinguishes the arms: reopen false, held-connection apply true.
	// (A second signup of a name the DB already carries commits its no-op delta: the flag
	// (below stays true either way, so it needs no random-id luck.)
	assert!(!g.log[0].committed);
	assert!(g.log[1].committed);
}
