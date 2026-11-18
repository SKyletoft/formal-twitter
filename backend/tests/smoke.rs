#[doc = "Integration smoke tests: the real target/debug/formal-twitter server over raw TCP."]
#[doc = "Starts the server on one port and DB file, killed by timeout after secs."]
fn spawn_server(port: u16, db: &str, secs: u32) {
	_ = std::process::Command::new("timeout")
		.env("FT_DB", db)
		.env("ROCKET_PORT", port.to_string())
		.arg(secs.to_string())
		.arg("target/debug/formal-twitter")
		.spawn();
}

#[doc = "Waits until something answers on the port; false when the server never starts."]
fn wait_ready(port: u16) -> bool {
	let mut tries = 0;
	while tries < 50 {
		if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
			return true;
		}
		std::thread::sleep(std::time::Duration::from_millis(100));
		tries += 1;
	}
	false
}

#[doc = "Waits until the port stops answering, i.e. the wrapper killed the server."]
fn wait_gone(port: u16) -> bool {
	let mut misses = 0;
	let mut rounds = 0;
	while rounds < 200 && misses < 5 {
		if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
			misses = 0;
		} else {
			misses += 1;
		}
		rounds += 1;
		std::thread::sleep(std::time::Duration::from_millis(100));
	}
	misses >= 5
}

#[doc = "Deletes a DB file from an earlier run so the server starts from an empty world."]
fn fresh_db(db: &str) {
	_ = std::fs::remove_file(db);
}

#[doc = "Fails a test with a message when a condition is false."]
fn ensure(cond: bool, what: &str) {
	assert!(cond, "{}", what);
}

#[doc = "The octets of one POST request: the frontend headers and the CRLF body."]
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

#[doc = "Sends one request and returns every octet the server answered with."]
fn req(port: u16, path: String, body: String) -> String {
	let mut sock = match std::net::TcpStream::connect(("127.0.0.1", port)) {
		Err(_) => panic!("cannot reach the server"),
		Ok(s) => s,
	};
	_ = std::io::Write::write_all(&mut sock, &request_bytes(path, body));
	let mut got: Vec<u8> = vec![];
	let mut one: [u8; 1] = [0];
	while !headers_done(&got) && got.len() < 4096 {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	while got.len() < header_end(&got) + content_length(&got) {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	match String::from_utf8(got) {
		Err(_) => "".to_string(),
		Ok(text) => text,
	}
}

#[doc = "True once the CRLF CRLF that closes the response headers has been read."]
fn headers_done(xs: &[u8]) -> bool {
	header_end(xs) != 0
}

#[doc = "The octet count of the header block, blank line included; zero while unseen."]
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

#[doc = "The first number in the text at or after a byte index; zero when absent."]
fn number_after(text: &str, start: usize) -> u64 {
	let bs = text.as_bytes();
	let mut i: usize = start;
	while i < bs.len() {
		if bs[i] >= 48 && bs[i] <= 57 {
			let mut n: u64 = 0;
			while i < bs.len() && bs[i] >= 48 && bs[i] <= 57 {
				n = n * 10 + (bs[i] - 48) as u64;
				i += 1;
			}
			return n;
		}
		i += 1;
	}
	0
}

#[doc = "The first number that follows a label in the text; zero when the label is absent."]
fn label_number(text: &str, label: &str) -> u64 {
	match text.find(label) {
		None => 0,
		Some(p) => number_after(text, p + label.len()),
	}
}

#[doc = "The Content-Length the server declared; zero while the header is unseen."]
fn content_length(xs: &[u8]) -> usize {
	match String::from_utf8(xs.to_vec()) {
		Err(_) => 0,
		Ok(text) => label_number(&text, "content-length") as usize,
	}
}

#[doc = "The status line: the text before the first CRLF."]
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

#[doc = "The body: everything after the blank line that closes the headers."]
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

#[doc = "True when the response carries a header with this name."]
fn has_header(raw: &str, label: &str) -> bool {
	let needle = "\r\n".to_owned() + label + ":";
	raw.find(&needle).is_some()
}

#[doc = "Every number that appears in a JSON body."]
fn numbers_in(body: &str) -> Vec<u64> {
	let bs = body.as_bytes();
	let mut out: Vec<u64> = vec![];
	let mut i: usize = 0;
	while i < bs.len() {
		if bs[i] >= 48 && bs[i] <= 57 {
			let mut n: u64 = 0;
			while i < bs.len() && bs[i] >= 48 && bs[i] <= 57 {
				n = n * 10 + (bs[i] - 48) as u64;
				i += 1;
			}
			out.push(n);
		} else {
			i += 1;
		}
	}
	out
}

#[doc = "Asserts the exact status line of an answer."]
fn expect_status(raw: &str, line: &str) {
	ensure(status_line(raw) == line, "unexpected status line");
}

#[doc = "Asserts that the declared Content-Length matches the body octets."]
fn expect_length(raw: &str) {
	ensure(
		label_number(raw, "content-length") == body_of(raw).len() as u64,
		"content-length disagrees with the body",
	);
}

#[doc = "The post ids in a timeline answer."]
fn ids_of(raw: &str) -> Vec<u64> {
	numbers_in(&body_of(raw))
}

#[doc = "The session or post id a JSON answer carries; zero when there is none."]
fn id_of(raw: &str, key: &str) -> u64 {
	label_number(&body_of(raw), key)
}

#[doc = "Asserts the exact status line and the exact body of an answer."]
fn expect(raw: &str, line: &str, want: &str) {
	ensure(status_line(raw) == line, "unexpected status line");
	ensure(body_of(raw) == want, "unexpected body");
}

#[doc = "Asserts the 200 answer with an empty body: the Ok response shape."]
fn expect_ok(raw: &str) {
	expect(raw, "HTTP/1.1 200 OK", "");
	ensure(
		label_number(raw, "content-length") == 0,
		"the ok body is not empty",
	);
}

#[doc = "Signup answers empty, login issues a session token, a wrong password answers 401."]
#[test]
fn test_signup_login() {
	let db = "/tmp/ft-smoke-signup.sqlite".to_string();
	fresh_db(&db);
	spawn_server(8011, &db, 60);
	ensure(wait_ready(8011), "the server never started");
	let signed = req(8011, "/api/signup".to_string(), "alice\r\npw".to_string());
	expect_ok(&signed);
	ensure(
		!has_header(&signed, "content-type"),
		"the empty ok body carries a content-type",
	);
	let first = req(8011, "/api/login".to_string(), "alice\r\npw".to_string());
	expect_status(&first, "HTTP/1.1 200 OK");
	ensure(
		has_header(&first, "cache-control"),
		"a fresh token was not cached away",
	);
	let token = id_of(&first, "session_token");
	ensure(token != 0, "login issued no session token");
	let rejected = req(8011, "/api/login".to_string(), "alice\r\nnope".to_string());
	expect(
		&rejected,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"login_failed\"}",
	);
	let revoked = req(8011, "/api/logout".to_string(), token.to_string());
	expect_ok(&revoked);
	let again = req(8011, "/api/login".to_string(), "alice\r\npw".to_string());
	expect_status(&again, "HTTP/1.1 200 OK");
	ensure(
		id_of(&again, "session_token") != token,
		"login reuses a session id",
	);
}

#[doc = "Publishing a post, reading it back anonymously, liking it, and logging out."]
#[test]
fn test_post_tweet() {
	let db = "/tmp/ft-smoke-post.sqlite".to_string();
	fresh_db(&db);
	spawn_server(8012, &db, 60);
	ensure(wait_ready(8012), "the server never started");
	let signed = req(8012, "/api/signup".to_string(), "bob\r\npw".to_string());
	expect_ok(&signed);
	let logged = req(8012, "/api/login".to_string(), "bob\r\npw".to_string());
	expect_status(&logged, "HTTP/1.1 200 OK");
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	let posted = req(
		8012,
		"/api/post-tweet".to_string(),
		token.to_string() + "\r\nhello world",
	);
	expect_status(&posted, "HTTP/1.1 200 OK");
	let tweet = id_of(&posted, "tweet_id");
	ensure(tweet != 0, "publishing created no post id");
	let seen = req(8012, "/api/global-timeline".to_string(), "5".to_string());
	expect_status(&seen, "HTTP/1.1 200 OK");
	let first_ids = ids_of(&seen);
	ensure(
		first_ids.len() == 1 && first_ids[0] == tweet,
		"the timeline hides the new post",
	);
	let liked = req(
		8012,
		"/api/like-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	expect_ok(&liked);
	let unliked = req(
		8012,
		"/api/unlike-tweet".to_string(),
		token.to_string() + "\r\n" + &tweet.to_string(),
	);
	expect_ok(&unliked);
	let out = req(8012, "/api/logout".to_string(), token.to_string());
	expect_ok(&out);
}

#[doc = "Every reachable failure: duplicate signup, bad login, stale token, denied access."]
#[test]
fn test_errors() {
	let db = "/tmp/ft-smoke-errors.sqlite".to_string();
	fresh_db(&db);
	spawn_server(8013, &db, 60);
	ensure(wait_ready(8013), "the server never started");
	let signed = req(8013, "/api/signup".to_string(), "carol\r\npw".to_string());
	expect_ok(&signed);
	let dupe = req(
		8013,
		"/api/signup".to_string(),
		"carol\r\nother".to_string(),
	);
	expect(
		&dupe,
		"HTTP/1.1 400 Bad Request",
		"{\"error\": \"signup_failed\"}",
	);
	let bad = req(8013, "/api/login".to_string(), "carol\r\nnope".to_string());
	expect(
		&bad,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"login_failed\"}",
	);
	let stale = req(
		8013,
		"/api/private-timeline".to_string(),
		"7\r\n3".to_string(),
	);
	expect(
		&stale,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"session_expired\"}",
	);
	let logged = req(8013, "/api/login".to_string(), "carol\r\npw".to_string());
	expect_status(&logged, "HTTP/1.1 200 OK");
	let token = id_of(&logged, "session_token");
	ensure(token != 0, "login issued no session token");
	let missing = req(
		8013,
		"/api/like-tweet".to_string(),
		token.to_string() + "\r\n999999",
	);
	expect(
		&missing,
		"HTTP/1.1 403 Forbidden",
		"{\"error\": \"access_denied\"}",
	);
	let anonymous = req(8013, "/api/get-tweet".to_string(), "999999".to_string());
	expect(
		&anonymous,
		"HTTP/1.1 403 Forbidden",
		"{\"error\": \"access_denied\"}",
	);
	let revoked = req(8013, "/api/logout".to_string(), token.to_string());
	expect_ok(&revoked);
	let after = req(
		8013,
		"/api/private-timeline".to_string(),
		token.to_string() + "\r\n3",
	);
	expect(
		&after,
		"HTTP/1.1 401 Unauthorized",
		"{\"error\": \"session_expired\"}",
	);
}

#[doc = "The HTTP framing rocket adds: status line, headers, and Content-Length."]
#[test]
fn test_http_framing() {
	let db = "/tmp/ft-smoke-framing.sqlite".to_string();
	fresh_db(&db);
	spawn_server(8014, &db, 60);
	ensure(wait_ready(8014), "the server never started");
	let signed = req(8014, "/api/signup".to_string(), "dave\r\npw".to_string());
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
	let logged = req(8014, "/api/login".to_string(), "dave\r\npw".to_string());
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
	let rejected = req(8014, "/api/login".to_string(), "dave\r\nnope".to_string());
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

#[doc = "Three server lifecycles share one DB file: the world is re-read at each start."]
#[test]
fn test_reentrant_three_lifecycles() {
	let db = "/tmp/ft-smoke-T5.sqlite".to_string();
	fresh_db(&db);
	spawn_server(8021, &db, 10);
	ensure(wait_ready(8021), "the first server never started");
	let signed = req(8021, "/api/signup".to_string(), "erin\r\npw".to_string());
	expect_ok(&signed);
	let first_login = req(8021, "/api/login".to_string(), "erin\r\npw".to_string());
	expect_status(&first_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&first_login, "session_token") != 0,
		"the first login issued no token",
	);
	let first_post = req(
		8021,
		"/api/post-tweet".to_string(),
		id_of(&first_login, "session_token").to_string() + "\r\nfirst",
	);
	expect_status(&first_post, "HTTP/1.1 200 OK");
	let one = id_of(&first_post, "tweet_id");
	let seen = req(8021, "/api/global-timeline".to_string(), "5".to_string());
	ensure(
		ids_of(&seen).contains(&one),
		"the first post is not in the timeline",
	);
	ensure(wait_gone(8021), "the first server never exited");
	spawn_server(8022, &db, 10);
	ensure(wait_ready(8022), "the second server never started");
	let again = req(8022, "/api/signup".to_string(), "erin\r\npw".to_string());
	expect(
		&again,
		"HTTP/1.1 400 Bad Request",
		"{\"error\": \"signup_failed\"}",
	);
	let second_login = req(8022, "/api/login".to_string(), "erin\r\npw".to_string());
	expect_status(&second_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&second_login, "session_token") != 0,
		"the second login issued no token",
	);
	let second_post = req(
		8022,
		"/api/post-tweet".to_string(),
		id_of(&second_login, "session_token").to_string() + "\r\nsecond",
	);
	expect_status(&second_post, "HTTP/1.1 200 OK");
	let two = id_of(&second_post, "tweet_id");
	let grown = req(8022, "/api/global-timeline".to_string(), "5".to_string());
	let ids = ids_of(&grown);
	ensure(
		ids.contains(&one) && ids.contains(&two),
		"the restarted server lost the old post",
	);
	ensure(wait_gone(8022), "the second server never exited");
	spawn_server(8023, &db, 10);
	ensure(wait_ready(8023), "the third server never started");
	let fresh = req(8023, "/api/global-timeline".to_string(), "5".to_string());
	expect_status(&fresh, "HTTP/1.1 200 OK");
	let before = ids_of(&fresh);
	ensure(
		before.contains(&one) && before.contains(&two),
		"the third server lost the saved posts",
	);
	let third_login = req(8023, "/api/login".to_string(), "erin\r\npw".to_string());
	expect_status(&third_login, "HTTP/1.1 200 OK");
	ensure(
		id_of(&third_login, "session_token") != 0,
		"the third login issued no token",
	);
	let third_post = req(
		8023,
		"/api/post-tweet".to_string(),
		id_of(&third_login, "session_token").to_string() + "\r\nthird",
	);
	expect_status(&third_post, "HTTP/1.1 200 OK");
	let three = id_of(&third_post, "tweet_id");
	ensure(
		!ids_of(&fresh).contains(&three),
		"the third post predates the third timeline",
	);
	let last = req(8023, "/api/global-timeline".to_string(), "5".to_string());
	expect_status(&last, "HTTP/1.1 200 OK");
	let all = ids_of(&last);
	ensure(
		all.contains(&one) && all.contains(&two) && all.contains(&three),
		"the last timeline is incomplete",
	);
	ensure(wait_gone(8023), "the third server never exited");
}
