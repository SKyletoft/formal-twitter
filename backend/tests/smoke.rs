/// Integration smoke tests: the real target/debug/formal-twitter server over raw TCP.
/// Starts the server on one port and DB file, killed by timeout after secs.
fn spawn_server(port: u16, db: &str, secs: u32) {
	_ = std::process::Command::new("timeout")
		.env("FT_DB", db)
		.env("ROCKET_PORT", port.to_string())
		.arg(secs.to_string())
		.arg("target/debug/formal-twitter")
		.spawn();
}

// per-test server ports: one port per lifecycle, never reused
const PORT_SIGNUP: u16 = 8011;
const PORT_POST: u16 = 8012;
const PORT_ERRORS: u16 = 8013;
const PORT_FRAMING: u16 = 8014;
const PORT_LIFECYCLE_1: u16 = 8021;
const PORT_LIFECYCLE_2: u16 = 8022;
const PORT_LIFECYCLE_3: u16 = 8023;
const PORT_ALIAS: u16 = 8024;
const PORT_STATIC: u16 = 8025;
const PORT_RAW_LOG: u16 = 8026;
const PORT_ACTIONS: u16 = 8027;

/// Octet cap on one header-block read: the headers rocket sends never reach this.
const HEADER_READ_CAP: usize = 4096;

/// Milliseconds one wait-round sleeps; every budget below is a multiple of this.
const POLL_MS: u32 = 100;

/// Polling rounds in one second: the seconds-to-rounds conversion.
const ROUNDS_PER_SEC: u32 = 1000 / POLL_MS;

/// (ST) Seconds wait_ready tolerates before the server must answer.
const READY_SECS: u32 = 5;

/// (F*) Slack past the wrapper's spawn timeout before wait_gone gives up: without it
/// the wait budget can equal the kill time and lose by the miss window alone.
const GONE_GRACE_SECS: u32 = 10;

/// Consecutive missed connects that prove the port stopped answering.
const MISS_STREAK: u32 = 5;

/// Waits until something answers on the port; false when the server never starts.
/// (the budget is READY_SECS of POLL_MS rounds, not a bare round count)
fn wait_ready(port: u16) -> bool {
	let mut tries = 0;
	while tries < READY_SECS * ROUNDS_PER_SEC {
		if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
			return true;
		}
		std::thread::sleep(std::time::Duration::from_millis(POLL_MS.into()));
		tries += 1;
	}
	false
}

/// Waits until the port stops answering, i.e. the wrapper killed the server.
/// (F*) The round cap derives from the wrapper's own timeout: secs + GONE_GRACE_SECS
/// seconds of POLL_MS rounds, so the kill always lands inside the budget.
fn wait_gone(port: u16, secs: u32) -> bool {
	let mut misses = 0;
	let mut rounds = 0;
	// (never a fixed 200: that equals a 20s spawn timeout and races it)
	let rounds_max: u32 = (secs + GONE_GRACE_SECS) * ROUNDS_PER_SEC;
	while rounds < rounds_max && misses < MISS_STREAK {
		if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
			misses = 0;
		} else {
			misses += 1;
		}
		rounds += 1;
		std::thread::sleep(std::time::Duration::from_millis(POLL_MS.into()));
	}
	misses >= MISS_STREAK
}

/// Deletes a DB file from an earlier run so the server starts from an empty world.
fn fresh_db(db: &str) {
	_ = std::fs::remove_file(db);
}

/// (ST) One fresh lifecycle: wipe the DB, spawn the wrapper, wait for the port.
/// True once something answers; the caller keeps its own never-started message.
fn boot(port: u16, db: &str, secs: u32) -> bool {
	fresh_db(db);
	spawn_server(port, db, secs);
	wait_ready(port)
}

/// Fails a test with a message when a condition is false.
fn ensure(cond: bool, what: &str) {
	assert!(cond, "{}", what);
}

/// The octets of one POST request: the frontend headers and the CRLF body.
fn request_bytes(path: String, body: String) -> Vec<u8> {
	let mut out = "POST ".to_owned();
	out += &path;
	out += " HTTP/1.1\r\nHost: 127.0.0.1\r\nAccept: application/json\r\n";
	out += "Content-Type: text/plain; charset=utf-8\r\n";
	out += "Content-Length: ";
	out += &body.len().to_string();
	out += "\r\n\r\n";
	out += &body;
	out.as_bytes().to_vec()
}

/// Sends one request's octets and returns every octet the server answered with.
/// (POST and GET share this reader: only the octets they send differ)
fn send_and_read(port: u16, wire: Vec<u8>) -> String {
	let mut sock = match std::net::TcpStream::connect(("127.0.0.1", port)) {
		Err(_) => panic!("cannot reach the server"),
		Ok(s) => s,
	};
	_ = std::io::Write::write_all(&mut sock, &wire);
	let mut got: Vec<u8> = vec![];
	let mut one: [u8; 1] = [0];
	while !headers_done(&got) && got.len() < HEADER_READ_CAP {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	// the headers are whole, so the declared length is final: read to it, rescanning nothing
	let want: usize = header_end(&got) + content_length(&got);
	while got.len() < want {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	match String::from_utf8(got) {
		Err(_) => "".to_string(),
		Ok(text) => text,
	}
}

/// Sends one POST request and returns every octet the server answered with.
fn req(port: u16, path: String, body: String) -> String {
	send_and_read(port, request_bytes(path, body))
}

/// The octets of one GET request: the frontend headers, the query inside the path, no body.
fn get_bytes(path: String) -> Vec<u8> {
	("GET ".to_owned() + &path + " HTTP/1.1\r\nHost: 127.0.0.1\r\nAccept: application/json\r\n\r\n")
		.as_bytes()
		.to_vec()
}

/// Sends one GET request and returns every octet the server answered with.
fn get(port: u16, path: String) -> String {
	send_and_read(port, get_bytes(path))
}

/// True once the CRLF CRLF that closes the response headers has been read.
fn headers_done(xs: &[u8]) -> bool {
	header_end(xs) != 0
}

/// The octet count of the header block, blank line included; zero while unseen.
fn header_end(xs: &[u8]) -> usize {
	let mut i: usize = 0;
	while i + 3 < xs.len() {
		if xs[i] == 13 && xs[i + 1] == 10 && xs[i + 2] == 13 && xs[i + 3] == 10 {
			return i + 4;
		}
		i += 1;
	}
	0
}

/// The number whose digits start at i and the index just after them; (0, i) when absent.
fn digits_at(bs: &[u8], i: usize) -> (u64, usize) {
	let mut n: u64 = 0;
	let mut j: usize = i;
	while j < bs.len() && bs[j] >= 48 && bs[j] <= 57 {
		n = n * 10 + (bs[j] - 48) as u64;
		j += 1;
	}
	(n, j)
}

/// The first number in the text at or after a byte index; zero when absent.
fn number_after(text: &str, start: usize) -> u64 {
	let bs = text.as_bytes();
	let mut i: usize = start;
	while i < bs.len() {
		let scanned: (u64, usize) = digits_at(bs, i);
		if scanned.1 != i {
			return scanned.0;
		}
		i += 1;
	}
	0
}

/// The first number that follows a label in the text; zero when the label is absent.
fn label_number(text: &str, label: &str) -> u64 {
	match text.find(label) {
		None => 0,
		Some(p) => number_after(text, p + label.len()),
	}
}

/// The Content-Length the server declared; zero while the header is unseen.
fn content_length(xs: &[u8]) -> usize {
	match String::from_utf8(xs.to_vec()) {
		Err(_) => 0,
		Ok(text) => label_number(&text, "content-length") as usize,
	}
}

/// The status line: the text before the first CRLF.
fn status_line(raw: &str) -> String {
	let bs = raw.as_bytes();
	let mut out = "".to_owned();
	let mut i: usize = 0;
	while i + 1 < bs.len() && !(bs[i] == 13 && bs[i + 1] == 10) {
		out.push(bs[i] as char);
		i += 1;
	}
	out
}

/// The body: everything after the blank line that closes the headers.
fn body_of(raw: &str) -> String {
	let bs = raw.as_bytes();
	let end = header_end(bs);
	if end == 0 {
		return "".to_string();
	}
	let mut out = "".to_owned();
	let mut i: usize = end;
	while i < bs.len() {
		out.push(bs[i] as char);
		i += 1;
	}
	out
}

/// True when the response carries a header with this name.
fn has_header(raw: &str, label: &str) -> bool {
	let needle = "\r\n".to_owned() + label + ":";
	raw.find(&needle).is_some()
}

/// The value a header carries, lowercased; empty when the name is absent.
fn header_value(raw: &str, label: &str) -> String {
	let needle = "\r\n".to_owned() + label + ":";
	match raw.find(&needle) {
		// a name the server never sent has nothing to compare
		None => "".to_string(),
		Some(p) => {
			let rest: &str = &raw[(p + needle.len())..];
			// the value runs to its own line end; a last header ends at the blank line
			let stop: usize = match rest.find("\r\n") {
				None => rest.len(),
				Some(q) => q,
			};
			rest[..stop].trim().to_lowercase()
		}
	}
}

/// Every number that appears in a JSON body.
fn numbers_in(body: &str) -> Vec<u64> {
	let bs = body.as_bytes();
	let mut out: Vec<u64> = vec![];
	let mut i: usize = 0;
	while i < bs.len() {
		let scanned: (u64, usize) = digits_at(bs, i);
		if scanned.1 != i {
			out.push(scanned.0);
			i = scanned.1;
		} else {
			i += 1;
		}
	}
	out
}

/// Asserts the exact status line of an answer.
fn expect_status(raw: &str, line: &str) {
	ensure(status_line(raw) == line, "unexpected status line");
}

/// Asserts that the declared Content-Length matches the body octets.
fn expect_length(raw: &str) {
	ensure(
		label_number(raw, "content-length") == body_of(raw).len() as u64,
		"content-length disagrees with the body",
	);
}

/// The post ids in a timeline answer.
fn ids_of(raw: &str) -> Vec<u64> {
	numbers_in(&body_of(raw))
}

/// The session or post id a JSON answer carries; zero when there is none.
fn id_of(raw: &str, key: &str) -> u64 {
	label_number(&body_of(raw), key)
}

/// Asserts the exact status line and the exact body of an answer.
fn expect(raw: &str, line: &str, want: &str) {
	ensure(status_line(raw) == line, "unexpected status line");
	ensure(body_of(raw) == want, "unexpected body");
}

/// (ST) Asserts two answers agree exactly: same status line, same body, byte for byte.
fn expect_same(left: &str, right: &str, what: &str) {
	ensure(
		status_line(left) == status_line(right),
		&(what.to_owned() + " status differs"),
	);
	ensure(
		body_of(left) == body_of(right),
		&(what.to_owned() + " body differs"),
	);
}

/// Asserts the 200 answer with an empty body: the Ok response shape.
fn expect_ok(raw: &str) {
	expect(raw, "HTTP/1.1 200 OK", "");
	ensure(
		label_number(raw, "content-length") == 0,
		"the ok body is not empty",
	);
}

/// The octets one GET answers with, read whole up to the declared length.
/// (the string reader gives up on a body whose last read split a multi-byte glyph, so the
/// site's script - which carries such glyphs - is inspected as octets instead of text)
fn get_raw(port: u16, path: String) -> Vec<u8> {
	let mut sock = match std::net::TcpStream::connect(("127.0.0.1", port)) {
		Err(_) => panic!("cannot reach the server"),
		Ok(s) => s,
	};
	_ = std::io::Write::write_all(&mut sock, &get_bytes(path));
	let mut got: Vec<u8> = vec![];
	let mut one: [u8; 1] = [0];
	// headers first, one octet at a time like every other reader here
	while !headers_done(&got) && got.len() < HEADER_READ_CAP {
		match std::io::Read::read_exact(&mut sock, &mut one) {
			Err(_) => panic!("the answer cut off in the headers"),
			Ok(_) => got.push(one[0]),
		}
	}
	// then exactly the declared body, so a short read shows as a short body
	let want: usize = header_end(&got) + content_length(&got);
	while got.len() < want {
		match std::io::Read::read_exact(&mut sock, &mut one) {
			Err(_) => break,
			Ok(_) => got.push(one[0]),
		}
	}
	got
}

/// True when a run of ASCII bytes occurs among an answer's octets.
fn bytes_find(xs: &[u8], needle: &[u8]) -> bool {
	// an empty needle matches every haystack, as the scan below did
	if needle.is_empty() {
		return true;
	}
	needle.len() <= xs.len() && xs.windows(needle.len()).any(|w| w == needle)
}

/// Signup answers empty, login issues a session token, a wrong password answers 401.
#[test]
fn test_signup_login() {
	let db = "/tmp/ft-smoke-signup.sqlite".to_string();
	ensure(boot(PORT_SIGNUP, &db, 60), "the server never started");
	let signed = req(
		PORT_SIGNUP,
		"/api/signup".to_string(),
		"alice\r\npw".to_string(),
	);
	expect_ok(&signed);
	ensure(
		!has_header(&signed, "content-type"),
		"the empty ok body carries a content-type",
	);
	let first = req(
		PORT_SIGNUP,
		"/api/login".to_string(),
		"alice\r\npw".to_string(),
	);
	expect_status(&first, "HTTP/1.1 200 OK");
	ensure(
		has_header(&first, "cache-control"),
		"a fresh token was not cached away",
	);
	let token = id_of(&first, "session_token");
	ensure(token != 0, "login issued no session token");
	let rejected = req(
		PORT_SIGNUP,
		"/api/login".to_string(),
		"alice\r\nnope".to_string(),
	);
	expect(
		&rejected,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"login_failed\"}",
	);
	let revoked = req(PORT_SIGNUP, "/api/logout".to_string(), token.to_string());
	expect_ok(&revoked);
	let again = req(
		PORT_SIGNUP,
		"/api/login".to_string(),
		"alice\r\npw".to_string(),
	);
	expect_status(&again, "HTTP/1.1 200 OK");
	ensure(
		id_of(&again, "session_token") != token,
		"login reuses a session id",
	);
}

/// Publishing a post, reading it back anonymously, liking it, and logging out.
#[test]
fn test_post_tweet() {
	let db = "/tmp/ft-smoke-post.sqlite".to_string();
	ensure(boot(PORT_POST, &db, 60), "the server never started");
	let signed = req(
		PORT_POST,
		"/api/signup".to_string(),
		"bob\r\npw".to_string(),
	);
	expect_ok(&signed);
	let logged = req(PORT_POST, "/api/login".to_string(), "bob\r\npw".to_string());
	expect_status(&logged, "HTTP/1.1 200 OK");
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	let posted = req(
		PORT_POST,
		"/api/post-tweet".to_string(),
		token.to_string() + "\r\nhello world",
	);
	expect_status(&posted, "HTTP/1.1 200 OK");
	let tweet = id_of(&posted, "tweet_id");
	ensure(tweet != 0, "publishing created no post id");
	let seen = req(
		PORT_POST,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	expect_status(&seen, "HTTP/1.1 200 OK");
	let first_ids = ids_of(&seen);
	ensure(
		first_ids.len() == 1 && first_ids[0] == tweet,
		"the timeline hides the new post",
	);
	let liked = req(
		PORT_POST,
		"/api/like-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	expect_ok(&liked);
	let unliked = req(
		PORT_POST,
		"/api/unlike-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	expect_ok(&unliked);
	let out = req(PORT_POST, "/api/logout".to_string(), token.to_string());
	expect_ok(&out);
}

/// Every reachable failure: duplicate signup, bad login, stale token, denied access.
#[test]
fn test_errors() {
	let db = "/tmp/ft-smoke-errors.sqlite".to_string();
	ensure(boot(PORT_ERRORS, &db, 60), "the server never started");
	let signed = req(
		PORT_ERRORS,
		"/api/signup".to_string(),
		"carol\r\npw".to_string(),
	);
	expect_ok(&signed);
	let dupe = req(
		PORT_ERRORS,
		"/api/signup".to_string(),
		"carol\r\nother".to_string(),
	);
	expect(
		&dupe,
		"HTTP/1.1 400 Bad Request",
		"{\"error\": \"signup_failed\"}",
	);
	let bad = req(
		PORT_ERRORS,
		"/api/login".to_string(),
		"carol\r\nnope".to_string(),
	);
	expect(
		&bad,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"login_failed\"}",
	);
	let stale = req(
		PORT_ERRORS,
		"/api/private-timeline".to_string(),
		"7\r\n3".to_string(),
	);
	expect(
		&stale,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"session_expired\"}",
	);
	let logged = req(
		PORT_ERRORS,
		"/api/login".to_string(),
		"carol\r\npw".to_string(),
	);
	expect_status(&logged, "HTTP/1.1 200 OK");
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	let missing = req(
		PORT_ERRORS,
		"/api/like-tweet".to_string(),
		token.to_string() + "\r\n999999",
	);
	expect(
		&missing,
		"HTTP/1.1 403 Forbidden",
		"{\"error\": \"access_denied\"}",
	);
	let anonymous = req(
		PORT_ERRORS,
		"/api/get-tweet".to_string(),
		"999999".to_string(),
	);
	expect(
		&anonymous,
		"HTTP/1.1 403 Forbidden",
		"{\"error\": \"access_denied\"}",
	);
	let revoked = req(PORT_ERRORS, "/api/logout".to_string(), token.to_string());
	expect_ok(&revoked);
	let after = req(
		PORT_ERRORS,
		"/api/private-timeline".to_string(),
		token.to_string() + "\r\n3",
	);
	expect(
		&after,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"session_expired\"}",
	);
}

/// The HTTP framing rocket adds: status line, headers, and Content-Length.
#[test]
fn test_http_framing() {
	let db = "/tmp/ft-smoke-framing.sqlite".to_string();
	ensure(boot(PORT_FRAMING, &db, 60), "the server never started");
	let signed = req(
		PORT_FRAMING,
		"/api/signup".to_string(),
		"dave\r\npw".to_string(),
	);
	expect_status(&signed, "HTTP/1.1 200 OK");
	ensure(
		has_header(&signed, "date"),
		"the spec date header is missing",
	);
	ensure(
		has_header(&signed, "content-length"),
		"no content-length was declared",
	);
	ensure(
		!has_header(&signed, "cache-control"),
		"an uncached empty body was cached",
	);
	expect_length(&signed);
	let logged = req(
		PORT_FRAMING,
		"/api/login".to_string(),
		"dave\r\npw".to_string(),
	);
	expect_status(&logged, "HTTP/1.1 200 OK");
	ensure(
		has_header(&logged, "cache-control"),
		"a fresh token must not be cached",
	);
	ensure(
		has_header(&logged, "content-type"),
		"a json body has no content-type",
	);
	expect_length(&logged);
	let rejected = req(
		PORT_FRAMING,
		"/api/login".to_string(),
		"dave\r\nnope".to_string(),
	);
	expect(
		&rejected,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"login_failed\"}",
	);
	ensure(
		label_number(&rejected, "content-length") == 25,
		"wrong content length for the login error",
	);
	expect_length(&rejected);
}

/// Three server lifecycles share one DB file: the world is re-read at each start.
#[test]
fn test_reentrant_three_lifecycles() {
	let db = "/tmp/ft-smoke-T5.sqlite".to_string();
	ensure(
		boot(PORT_LIFECYCLE_1, &db, 10),
		"the first server never started",
	);
	let signed = req(
		PORT_LIFECYCLE_1,
		"/api/signup".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_ok(&signed);
	let first_login = req(
		PORT_LIFECYCLE_1,
		"/api/login".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&first_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&first_login, "session_token") != 0,
		"the first login issued no token",
	);
	let first_post = req(
		PORT_LIFECYCLE_1,
		"/api/post-tweet".to_string(),
		id_of(&first_login, "session_token").to_string() + "\r\nfirst",
	);
	expect_status(&first_post, "HTTP/1.1 200 OK");
	let one = id_of(&first_post, "tweet_id");
	let seen = req(
		PORT_LIFECYCLE_1,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	ensure(
		ids_of(&seen).contains(&one),
		"the first post is not in the timeline",
	);
	ensure(
		wait_gone(PORT_LIFECYCLE_1, 10),
		"the first server never exited",
	);
	// (no boot for lifecycles 2 and 3: boot wipes the DB, and this test's whole point
	// is that the saved DB survives the restart as the source of truth)
	spawn_server(PORT_LIFECYCLE_2, &db, 10);
	ensure(
		wait_ready(PORT_LIFECYCLE_2),
		"the second server never started",
	);
	let again = req(
		PORT_LIFECYCLE_2,
		"/api/signup".to_string(),
		"erin\r\npw".to_string(),
	);
	expect(
		&again,
		"HTTP/1.1 400 Bad Request",
		"{\"error\": \"signup_failed\"}",
	);
	let second_login = req(
		PORT_LIFECYCLE_2,
		"/api/login".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&second_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&second_login, "session_token") != 0,
		"the second login issued no token",
	);
	let second_post = req(
		PORT_LIFECYCLE_2,
		"/api/post-tweet".to_string(),
		id_of(&second_login, "session_token").to_string() + "\r\nsecond",
	);
	expect_status(&second_post, "HTTP/1.1 200 OK");
	let two = id_of(&second_post, "tweet_id");
	let grown = req(
		PORT_LIFECYCLE_2,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	let ids = ids_of(&grown);
	ensure(
		ids.contains(&one) && ids.contains(&two),
		"the restarted server lost the old post",
	);
	ensure(
		wait_gone(PORT_LIFECYCLE_2, 10),
		"the second server never exited",
	);
	spawn_server(PORT_LIFECYCLE_3, &db, 10);
	ensure(
		wait_ready(PORT_LIFECYCLE_3),
		"the third server never started",
	);
	let fresh = req(
		PORT_LIFECYCLE_3,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	expect_status(&fresh, "HTTP/1.1 200 OK");
	let before = ids_of(&fresh);
	ensure(
		before.contains(&one) && before.contains(&two),
		"the third server lost the saved posts",
	);
	let third_login = req(
		PORT_LIFECYCLE_3,
		"/api/login".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&third_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&third_login, "session_token") != 0,
		"the third login issued no token",
	);
	let third_post = req(
		PORT_LIFECYCLE_3,
		"/api/post-tweet".to_string(),
		id_of(&third_login, "session_token").to_string() + "\r\nthird",
	);
	expect_status(&third_post, "HTTP/1.1 200 OK");
	let three = id_of(&third_post, "tweet_id");
	ensure(
		!ids_of(&fresh).contains(&three),
		"the third post predates the third timeline",
	);
	let last = req(
		PORT_LIFECYCLE_3,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	expect_status(&last, "HTTP/1.1 200 OK");
	let all = ids_of(&last);
	ensure(
		all.contains(&one) && all.contains(&two) && all.contains(&three),
		"the last timeline is incomplete",
	);
	ensure(
		wait_gone(PORT_LIFECYCLE_3, 10),
		"the third server never exited",
	);
}

/// The GET aliases the legacy frontend speaks answer with the very bytes their POST twins
/// do, and a token-less private read fails identically over either transport.
#[test]
fn test_get_alias_roundtrip() {
	let db = "/tmp/ft-smoke-T6-alias.sqlite".to_string();
	ensure(boot(PORT_ALIAS, &db, 10), "the alias server never started");
	let signed = req(
		PORT_ALIAS,
		"/api/signup".to_string(),
		"erin\r\npw".to_string(),
	);
	// (the alias reads need a real post and a real session to answer about)
	expect_ok(&signed);
	let logged = req(
		PORT_ALIAS,
		"/api/login".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&logged, "HTTP/1.1 200 OK");
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	let posted = req(
		PORT_ALIAS,
		"/api/post-tweet".to_string(),
		token.to_string() + "\r\nalias body",
	);
	expect_status(&posted, "HTTP/1.1 200 OK");
	let tweet = id_of(&posted, "tweet_id");
	ensure(tweet != 0, "publishing created no post id");
	// anonymous global timeline: the token-less POST shape, byte for byte.
	// (an empty token= in the query reads the public timeline like no token at all)
	let global_post = req(
		PORT_ALIAS,
		"/api/global-timeline".to_string(),
		"5".to_string(),
	);
	let global_get = get(PORT_ALIAS, "/api/global-timeline?len=5".to_string());
	expect_same(&global_get, &global_post, "the GET global timeline");
	// one post by id with a session: the token-bearing POST shape.
	let one_post = req(
		PORT_ALIAS,
		"/api/get-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	let one_get = get(
		PORT_ALIAS,
		"/api/get-tweet?token=".to_owned() + &token.to_string() + "&id=" + &tweet.to_string(),
	);
	expect_same(&one_get, &one_post, "the GET get-tweet");
	// anonymous get-tweet: the single-line POST shape, the empty value dropped.
	// (token= with nothing after it is the same None the POST twin sends)
	let anon_post = req(PORT_ALIAS, "/api/get-tweet".to_string(), tweet.to_string());
	let anon_get = get(
		PORT_ALIAS,
		"/api/get-tweet?token=&id=".to_owned() + &tweet.to_string(),
	);
	expect_same(&anon_get, &anon_post, "the anonymous GET get-tweet");
	// private timeline with the session: the two-line POST shape.
	let priv_post = req(
		PORT_ALIAS,
		"/api/private-timeline".to_string(),
		token.to_string() + "\r\n3",
	);
	// (the query order the app.js sends: token first, then len)
	let priv_get = get(
		PORT_ALIAS,
		"/api/private-timeline?token=".to_owned() + &token.to_string() + "&len=3",
	);
	expect_same(&priv_get, &priv_post, "the GET private timeline");
	// token-less private read: the same refusal over either transport.
	// (one line short of the arity, so MissingLine, so the one 403 shape)
	// (never a silent anonymous private timeline)
	let denied_post = req(
		PORT_ALIAS,
		"/api/private-timeline".to_string(),
		"3".to_string(),
	);
	let denied_get = get(PORT_ALIAS, "/api/private-timeline?len=3".to_string());
	expect_same(&denied_get, &denied_post, "the token-less private GET");
	// (the LF-only and trailing-newline query bodies the codec already tolerates)
	// (are the very bytes alias_body builds, pinned in the unit tests)
	ensure(wait_gone(PORT_ALIAS, 10), "the alias server never exited");
}

/// The static frontend answers over the wire: 200s typed per file, the site's own shapes,
/// and never a 200 for a path no route answers.
#[test]
fn test_static_serving() {
	let db = "/tmp/ft-smoke-T7-static.sqlite".to_string();
	ensure(
		boot(PORT_STATIC, &db, 10),
		"the static server never started",
	);
	// (the site is public: an anonymous GET is all a browser sends, no session at all)
	let page = get(PORT_STATIC, "/".to_string());
	// (no signup was needed to serve the index, so the DB stays empty here)
	ensure(
		label_number(&page, "content-length") > 0,
		"the index answers no bytes",
	);
	expect_status(&page, "HTTP/1.1 200 OK");
	ensure(
		header_value(&page, "content-type").contains("text/html"),
		"the index is not typed html",
	);
	let site = body_of(&page);
	// (a plausible page: a doctype or an html tag opens it, and a tagged element follows)
	let opens_html: bool = site.starts_with("<!") || site.starts_with("<html");
	ensure(
		opens_html,
		"the index does not open with a doctype or html tag",
	);
	ensure(site.contains("<html"), "the index carries no html tag");
	// the stylesheet: css rules, never a page
	let sheet = get(PORT_STATIC, "/style.css".to_string());
	expect_status(&sheet, "HTTP/1.1 200 OK");
	ensure(
		header_value(&sheet, "content-type").contains("text/css"),
		"the stylesheet is not typed css",
	);
	let rules = body_of(&sheet);
	ensure(rules.contains("{"), "the stylesheet holds no rule");
	let no_doc: bool = !rules.contains("<!doctype");
	ensure(no_doc, "the stylesheet answers a page instead of css");
	// the script carries multi-byte glyphs, so its octets are inspected as octets
	let script = get_raw(PORT_STATIC, "/app.js".to_string());
	let closed: usize = header_end(&script);
	ensure(closed > 0, "the script answer never closed its headers");
	// (only the header block is plain ASCII, so that is the part turned into text)
	let head: String = match String::from_utf8(script[..closed].to_vec()) {
		Err(_) => "".to_string(),
		Ok(text) => text,
	};
	ensure(
		status_line(&head) == "HTTP/1.1 200 OK",
		"the script answers with a non-200 status",
	);
	ensure(
		has_header(&head, "content-type"),
		"the script answers without a content type",
	);
	ensure(
		header_value(&head, "content-type").contains("javascript"),
		"the script is not typed javascript",
	);
	// (the whole declared body arrived: a read cut mid-glyph would leave this false)
	ensure(
		label_number(&head, "content-length") == (script.len() - closed) as u64,
		"the script body is not the declared length",
	);
	let body: Vec<u8> = script[closed..].to_vec();
	ensure(
		bytes_find(&body, "use strict".as_bytes()),
		"the script body holds no strict-mode opener",
	);
	ensure(
		bytes_find(&body, "const ".as_bytes()),
		"the script body declares no constant",
	);
	ensure(
		bytes_find(&body, "function ".as_bytes()),
		"the script body defines no function",
	);
	ensure(
		!bytes_find(&body, "<!doctype".as_bytes()),
		"the script answers a page instead of javascript",
	);
	// a path no route answers must never be a 200
	let lost = get(PORT_STATIC, "/definitely-not-a-route".to_string());
	expect_status(&lost, "HTTP/1.1 404 Not Found");
	ensure(
		body_of(&lost) != body_of(&page),
		"an unknown path returns the index",
	);
	ensure(wait_gone(PORT_STATIC, 10), "the static server never exited");
}
/// (ST) the debug routes answer over the wire: /log holds one IMF-timestamped line per
/// request serve_command served, /raw dumps the live cache as pretty plaintext Debug.
#[test]
fn test_raw_and_log() {
	// (a fresh DB, so the log lines come from exactly the two requests below)
	let db = "/tmp/ft-smoke-raw-log.sqlite".to_string();
	ensure(
		boot(PORT_RAW_LOG, &db, 10),
		"the raw/log server never started",
	);
	// (signup then login: the shortest run that yields two serve_command calls)
	let signed = req(
		PORT_RAW_LOG,
		"/api/signup".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&signed, "HTTP/1.1 200 OK");
	let first = req(
		PORT_RAW_LOG,
		"/api/login".to_string(),
		"erin\r\npw".to_string(),
	);
	expect_status(&first, "HTTP/1.1 200 OK");
	// (a fresh login issues a session token, so the world advanced and the cache is live)
	ensure(
		id_of(&first, "session_token") != 0,
		"login issued no session token",
	);
	// the log route: 200 text/plain, one CRLF-terminated line per request
	let logged = get(PORT_RAW_LOG, "/log".to_string());
	expect_status(&logged, "HTTP/1.1 200 OK");
	ensure(
		header_value(&logged, "content-type").contains("text/plain"),
		"the log is not typed plain text",
	);
	let lines: Vec<String> = body_of(&logged)
		.split("\r\n")
		.filter(|l| !l.is_empty())
		.map(|l| l.to_string())
		.collect();
	ensure(lines.len() >= 2, "the log holds fewer than two lines");
	for line in &lines {
		// (the year is the four-digit run http_date_from renders, so its value clears 1000)
		ensure(
			number_after(line.as_str(), 11) >= 1000,
			"a log line carries no 4-digit year",
		);
		ensure(line.contains("GMT"), "a log line is not IMF-terminated");
	}
	ensure(
		lines[0].contains("signup"),
		"the first line does not name signup",
	);
	ensure(
		lines[1].contains("login"),
		"the second line does not name login",
	);
	ensure(
		// (ST) the raw request line, not just the naming table's signup word.
		// (the line names the very POST path serve_command was handed.)
		// (the naming-table pin above stays; this one pins the endpoint itself.)
		// (the request_line field reached the line byte-exact through /log.)
		// (the same line still carries the BODY segment, pinned next.)
		lines[0].contains("/api/signup"),
		"the first line does not name the signup request line",
	);
	// (ST) the body is Debug-quoted: the CRLF join shows as literal \r\n escapes, so the
	// (needle carries the backslash spelling the /log render emits, plaintext password and all.)
	ensure(
		// (BODY["erin\r\npw"] on the wire is BODY[\"erin\\r\\npw\"] in this source string.)
		// (the verbatim-body pin: no redaction between request and log.)
		lines[0].contains("BODY[\"erin\\r\\npw\"]"),
		"the first line does not carry the raw body verbatim",
	);
	// the dump route: 200 text/plain pretty plaintext Debug of the whole cache
	let dumped = get(PORT_RAW_LOG, "/raw".to_string());
	expect_status(&dumped, "HTTP/1.1 200 OK");
	ensure(
		header_value(&dumped, "content-type").contains("text/plain"),
		"the dump is not typed plain text",
	);
	let dump = body_of(&dumped);
	ensure(
		dump.starts_with("World {"),
		"the dump never opens the World record",
	);
	ensure(!dump.contains("<pre>"), "the dump is wrapped in markup");
	ensure(
		dump.contains("Account {"),
		"the dump holds no Account record",
	);
	ensure(
		wait_gone(PORT_RAW_LOG, 10),
		"the raw/log server never exited",
	);
}

/// The six actions the codec frames exactly as the frontend's wireBody emits: the token
/// first, one line per argument joined by CRLF, and no trailing newline (signup, login and
/// post-tweet keep the LF join plus trailing newline the codec already tolerates). Every ok
/// pins the empty 200 body with Content-Length: 0, every publish pins its fresh id, and the
/// deletion pins the anonymous 403 the alias answers.
#[test]
fn test_new_actions_roundtrip() {
	let db = "/tmp/ft-smoke-T11-actions.sqlite".to_string();
	ensure(
		boot(PORT_ACTIONS, &db, 20),
		"the actions server never started",
	);
	// signup: the empty ok, in the trailing-newline form the frontend sends
	let signed = req(
		PORT_ACTIONS,
		"/api/signup".to_string(),
		"f11a\r\npw\n".to_string(),
	);
	expect_ok(&signed);
	// login hands back the session token that every later body carries first
	let logged = req(
		PORT_ACTIONS,
		"/api/login".to_string(),
		"f11a\r\npw\n".to_string(),
	);
	expect_status(&logged, "HTTP/1.1 200 OK");
	ensure(
		body_of(&logged).contains("session_token"),
		"login answers no token body",
	);
	ensure(
		has_header(&logged, "cache-control"),
		"a fresh token is not cached away",
	);
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	// post-tweet is the LF-join-plus-newline shape the frontend emits: the quoted id back
	let posted = req(
		PORT_ACTIONS,
		"/api/post-tweet".to_string(),
		token.to_string() + "\nhello f11\n",
	);
	expect_status(&posted, "HTTP/1.1 200 OK");
	ensure(
		(body_of(&posted)).starts_with("{\"tweet_id\": \""),
		"the created-post shape is missing",
	);
	let tweet = id_of(&posted, "tweet_id");
	ensure(tweet != 0, "publishing created no post id");
	// post-reply while its parent is still live: the CRLF join, token first, no trailing
	// newline, exactly as the frontend frames <token> <text> <parent-id>
	// (CanReadPost consults the parent at publish time, so the reply precedes the delete)
	let replied = req(
		PORT_ACTIONS,
		"/api/post-reply".to_string(),
		token.to_string() + "\r\nreply f11\r\n" + &tweet.to_string(),
	);
	expect_status(&replied, "HTTP/1.1 200 OK");
	ensure(
		(body_of(&replied)).starts_with("{\"tweet_id\": \""),
		"the reply answers no created-post shape",
	);
	// (the fresh sampler hands out distinct ids, so the reply never shadows its parent)
	let reply = id_of(&replied, "tweet_id");
	ensure(reply != 0, "publishing the reply created no post id");
	ensure(reply != tweet, "the reply reuses its parent id");
	// like and unlike answer the empty ok: 200, Content-Length: 0, no body at all
	let liked = req(
		PORT_ACTIONS,
		"/api/like-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	expect_ok(&liked);
	ensure(
		has_header(&liked, "content-length"),
		"the ok declares no length",
	);
	ensure(!has_header(&liked, "content-type"), "the empty ok is typed");
	let unliked = req(
		PORT_ACTIONS,
		"/api/unlike-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	// (unlike is idempotent like the spec's set-union: the same ok either way)
	expect_ok(&unliked);
	// the second account: signup is the empty ok again, no token of its own is needed
	let peer = req(
		PORT_ACTIONS,
		"/api/signup".to_string(),
		"f11b\r\npw\n".to_string(),
	);
	expect_ok(&peer);
	// follow-user carries the token line then the username (never a post id)
	let followed = req(
		PORT_ACTIONS,
		"/api/follow-user".to_string(),
		token.to_string() + "\r\nf11b",
	);
	expect_ok(&followed);
	let unfollowed = req(
		PORT_ACTIONS,
		"/api/unfollow-user".to_string(),
		token.to_string() + "\r\nf11b",
	);
	expect_ok(&unfollowed);
	// delete-tweet: the author's own post answers the empty ok
	let gone = req(
		PORT_ACTIONS,
		"/api/delete-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	// (the deletion must not answer a stale ok for a post no session can read)
	expect_ok(&gone);
	// the deleted post is not readable anonymously: the GET alias the legacy frontend
	// speaks, whose query drops an absent token so the POST twin is the one-line body
	let anon = get(
		PORT_ACTIONS,
		"/api/get-tweet?id=".to_owned() + &tweet.to_string(),
	);
	ensure(
		status_line(&anon) == "HTTP/1.1 403 Forbidden",
		"the deleted post still reads",
	);
	ensure(
		body_of(&anon).contains("access_denied"),
		"the refusal is not access_denied",
	);
	// (a live post under the same anonymous transport keeps its own record)
	ensure(
		!body_of(&anon).contains("username"),
		"the deleted post still serves its record",
	);
	expect_length(&anon);
	// the reply stays public: the parent's tombstone persists, so the reply keeps its record
	let kept = get(
		PORT_ACTIONS,
		"/api/get-tweet?id=".to_owned() + &reply.to_string(),
	);
	expect_status(&kept, "HTTP/1.1 200 OK");
	ensure(
		body_of(&kept).contains("reply f11"),
		"the reply lost its own record",
	);
	expect_length(&kept);
	// logout revokes the session, so the old token is dead from here on
	let out = req(PORT_ACTIONS, "/api/logout".to_string(), token.to_string());
	expect_ok(&out);
	// the same account logs back in and gets a token that is not the revoked one
	// (the old token no longer reads: the session check runs before the access check,
	// so a revoked or unknown token answers 401, never the 403)
	let again = req(
		PORT_ACTIONS,
		"/api/login".to_string(),
		"f11a\r\npw\n".to_string(),
	);
	expect_status(&again, "HTTP/1.1 200 OK");
	let second = id_of(&again, "session_token");
	ensure(second != 0, "the second login issued no session token");
	ensure(second != token, "the second login reuses the revoked token");
	// the new session still reaches the reply the revoked one published
	let reliked = req(
		PORT_ACTIONS,
		"/api/like-tweet".to_string(),
		second.to_string() + "\r\n" + &reply.to_string(),
	);
	expect_ok(&reliked);
	// a token no session carries is refused before any post is even consulted
	let bogus = req(
		PORT_ACTIONS,
		"/api/like-tweet".to_string(),
		"999999999\r\n".to_string() + &reply.to_string(),
	);
	ensure(
		status_line(&bogus) == "HTTP/1.1 401 Unauthorized",
		"the unknown token was accepted",
	);
	ensure(
		body_of(&bogus).contains("session_expired"),
		"the refusal is not session_expired",
	);
	// the deleted post under a live session is the genuine 403 access_denied
	let denied = req(
		PORT_ACTIONS,
		"/api/like-tweet".to_string(),
		second.to_string() + "\r\n" + &tweet.to_string(),
	);
	ensure(
		status_line(&denied) == "HTTP/1.1 403 Forbidden",
		"the deleted post is still likeable",
	);
	ensure(
		body_of(&denied).contains("access_denied"),
		"the refusal is not access_denied",
	);
	// every request ran over the wire and the wrapper ended the lifecycle
	ensure(
		wait_gone(PORT_ACTIONS, 20),
		"the actions server never exited",
	);
}
