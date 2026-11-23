//! Byte-level wire codec: request parsing and response rendering.
//!
//! Pure Rust, no rocket, no diesel. Mirrors the to-request and to-response
//! sections of spec/Interface.agda byte for byte. Content-Length is deliberately
//! left out of every response: rocket writes the status line and appends
//! Content-Length itself. Everything else (order, spelling, body bytes) is exact.
use crate::model::Command;

/// Hex nibbles for the \\u00XY escapes in escape_json.
const HEX: [char; 16] = [
	'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
];

/// Parse errors: unknown path, wrong line count, non-numeric line.
#[derive(Clone, Debug, PartialEq)]
pub enum WireError {
	UnknownEndpoint,
	MissingLine,
	UnexpectedLine,
	BadNumber,
}

/// The 13 parsed actions of spec/Interface.agda.
#[derive(Clone, Debug, PartialEq)]
pub enum WireAction {
	PostTweet(u64, String),
	PostReply(u64, String, u64),
	DeleteTweet(u64, u64),
	Like(u64, u64),
	Unlike(u64, u64),
	Follow(u64, String),
	Unfollow(u64, String),
	GetTweet(Option<u64>, u64),
	GlobalTimeline(Option<u64>, u64),
	PrivateTimeline(u64, u64),
	Login(String, String),
	Logout(u64),
	Signup(String, String),
}

/// The 9 possible public-API responses of spec/Interface.agda.
#[derive(Clone, Debug, PartialEq)]
pub enum ApiResponse {
	Ok,
	PermissionError,
	OutdatedLoginToken,
	TweetId(u64),
	Timeline(Vec<u64>),
	SessionToken(u64),
	LoginError,
	SignupError,
	Tweet(String, String, u64, Vec<u64>),
}

/// A rendered response without the status line and without Content-Length.
#[derive(Clone, Debug, PartialEq)]
pub struct WireResponse {
	pub status_code: u16,
	pub headers: Vec<(String, String)>,
	pub body: Vec<u8>,
}

/// Parse a line as u64: ASCII digits only, no sign, no space, no overflow.
fn parse_u64(s: &str) -> Option<u64> {
	// an empty string already fails parse::<u64>, so no explicit emptiness check
	if !s.bytes().all(|b| b.is_ascii_digit()) {
		return None;
	}
	s.parse::<u64>().ok()
}

/// Decode one line of the body; empty string when the bytes are not UTF-8.
fn line_text(bytes: Vec<u8>) -> String {
	// non-UTF-8 bytes decode to the empty string
	String::from_utf8(bytes).unwrap_or_default()
}

/// Split a body on CRLF, LF or bare CR; drop exactly one trailing empty line.
fn split_lines(body: &[u8]) -> Vec<String> {
	let mut lines: Vec<String> = vec![];
	let mut current: Vec<u8> = vec![];
	let mut i = 0;
	while i < body.len() {
		let c = body[i];
		if c == 13 {
			lines.push(line_text(current));
			current = vec![];
			if i + 1 < body.len() && body[i + 1] == 10 {
				i += 2;
			} else {
				i += 1;
			}
		} else if c == 10 {
			lines.push(line_text(current));
			current = vec![];
			i += 1;
		} else {
			current.push(c);
			i += 1;
		}
	}
	lines.push(line_text(current));
	// drop exactly one trailing empty line; the vec always has one here, guard anyway
	if lines.last().map(|l| l.is_empty()).unwrap_or(false) {
		lines.pop();
	}
	lines
}

/// The arity error for a body with the wrong number of lines.
fn count_err(lines: &[String], want: usize) -> WireError {
	if lines.len() < want {
		return WireError::MissingLine;
	}
	WireError::UnexpectedLine
}

/// Body of exactly two numeric lines.
fn two_nums(lines: &[String]) -> Result<(u64, u64), WireError> {
	if lines.len() != 2 {
		return Err(count_err(lines, 2));
	}
	match (parse_u64(&lines[0]), parse_u64(&lines[1])) {
		(Some(a), Some(b)) => Ok((a, b)),
		(_, _) => Err(WireError::BadNumber),
	}
}

/// Body of a token followed by free text.
fn token_text(lines: &[String]) -> Result<(u64, String), WireError> {
	if lines.len() != 2 {
		return Err(count_err(lines, 2));
	}
	match parse_u64(&lines[0]) {
		Some(tk) => Ok((tk, lines[1].clone())),
		None => Err(WireError::BadNumber),
	}
}

/// Body of two free-text lines (login and signup).
fn two_texts(lines: &[String]) -> Result<(String, String), WireError> {
	if lines.len() != 2 {
		return Err(count_err(lines, 2));
	}
	Ok((lines[0].clone(), lines[1].clone()))
}

/// Body of exactly one numeric line.
fn one_num(lines: &[String]) -> Result<u64, WireError> {
	if lines.len() != 1 {
		return Err(count_err(lines, 1));
	}
	match parse_u64(&lines[0]) {
		Some(n) => Ok(n),
		None => Err(WireError::BadNumber),
	}
}

/// Body <token> <text> <tweet-id> of to-request post-reply.
fn reply(lines: &[String]) -> Result<(u64, String, u64), WireError> {
	if lines.len() != 3 {
		return Err(count_err(lines, 3));
	}
	match (parse_u64(&lines[0]), parse_u64(&lines[2])) {
		(Some(tk), Some(twt)) => Ok((tk, lines[1].clone(), twt)),
		(_, _) => Err(WireError::BadNumber),
	}
}

/// A single numeric line is anonymous; two numeric lines carry a token.
fn opt_num(lines: &[String]) -> Result<(Option<u64>, u64), WireError> {
	if lines.len() == 1 {
		match parse_u64(&lines[0]) {
			Some(n) => Ok((None, n)),
			None => Err(WireError::BadNumber),
		}
	} else if lines.len() == 2 {
		two_nums(lines).map(|(tk, n)| (Some(tk), n))
	} else {
		Err(count_err(lines, 2))
	}
}

/// Parse a request body for one of the 13 endpoints.
pub fn parse_action(path: &str, body: &[u8]) -> Result<WireAction, WireError> {
	let lines = split_lines(body);
	match path {
		"/api/post-tweet" => token_text(&lines).map(|(tk, txt)| WireAction::PostTweet(tk, txt)),
		"/api/post-reply" => {
			reply(&lines).map(|(tk, txt, twt)| WireAction::PostReply(tk, txt, twt))
		}
		"/api/delete-tweet" => two_nums(&lines).map(|(tk, twt)| WireAction::DeleteTweet(tk, twt)),
		"/api/like-tweet" => two_nums(&lines).map(|(tk, twt)| WireAction::Like(tk, twt)),
		"/api/unlike-tweet" => two_nums(&lines).map(|(tk, twt)| WireAction::Unlike(tk, twt)),
		"/api/follow-user" => token_text(&lines).map(|(tk, u)| WireAction::Follow(tk, u)),
		"/api/unfollow-user" => token_text(&lines).map(|(tk, u)| WireAction::Unfollow(tk, u)),
		"/api/get-tweet" => opt_num(&lines).map(|(tk, twt)| WireAction::GetTweet(tk, twt)),
		"/api/global-timeline" => opt_num(&lines).map(|(tl, n)| WireAction::GlobalTimeline(tl, n)),
		"/api/private-timeline" => {
			two_nums(&lines).map(|(tk, n)| WireAction::PrivateTimeline(tk, n))
		}
		"/api/logout" => one_num(&lines).map(WireAction::Logout),
		"/api/login" => two_texts(&lines).map(|(u, p)| WireAction::Login(u, p)),
		"/api/signup" => two_texts(&lines).map(|(u, p)| WireAction::Signup(u, p)),
		_ => Err(WireError::UnknownEndpoint),
	}
}

/// from-input of spec/Interface.agda.
pub fn to_command(a: WireAction) -> Command {
	match a {
		WireAction::PostTweet(tk, txt) => Command::Publish(tk, txt, None),
		WireAction::PostReply(tk, txt, twt) => Command::Publish(tk, txt, Some(twt)),
		WireAction::DeleteTweet(tk, twt) => Command::Delete(tk, twt),
		WireAction::Like(tk, twt) => Command::Like(tk, twt),
		WireAction::Unlike(tk, twt) => Command::Unlike(tk, twt),
		WireAction::Follow(tk, u) => Command::Follow(tk, u),
		WireAction::Unfollow(tk, u) => Command::Unfollow(tk, u),
		WireAction::GetTweet(tk, twt) => Command::ReadPost(tk, twt),
		WireAction::GlobalTimeline(tl, n) => Command::ReadGlobalTimeline(tl, n),
		WireAction::PrivateTimeline(tk, n) => Command::ReadPersonalTimeline(tk, n),
		WireAction::Login(u, p) => Command::Authenticate(u, p),
		WireAction::Logout(tk) => Command::RevokeToken(tk),
		WireAction::Signup(u, p) => Command::Register(u, p),
	}
}

/// The escape postulate of spec/Interface.agda, made concrete: JSON escaping.
fn escape_json(s: String) -> String {
	let mut out: String = String::new();
	// preallocate: sane lower bound; escape-heavy input grows to 6 chars per char (\u00XY)
	out.reserve(s.len() + 16);
	for c in s.chars() {
		if c == '"' {
			out.push('\\');
			out.push('"');
		} else if c == '\\' {
			out.push('\\');
			out.push('\\');
		} else if c == '\n' {
			out.push('\\');
			out.push('n');
		} else if c == '\r' {
			out.push('\\');
			out.push('r');
		} else if c == '\t' {
			out.push('\\');
			out.push('t');
		} else if c < ' ' {
			let code = c as u32;
			out.push('\\');
			out.push('u');
			out.push('0');
			out.push('0');
			out.push(HEX[(code / 16) as usize]);
			out.push(HEX[(code % 16) as usize]);
		} else {
			out.push(c);
		}
	}
	out
}

/// show-tweets of spec/Interface.agda: ids joined by a comma and a space.
fn show_tweets(xs: Vec<u64>) -> String {
	// append into one buffer: no full-string copy per element
	let mut out: String = String::new();
	// ids are at most 20 digits; size the buffer for the whole join
	out.reserve(xs.len() << 5);
	for (i, x) in xs.iter().enumerate() {
		if i != 0 {
			// separator between ids
			out.push_str(", ");
		}
		// push_str consumes the temporary instead of copying out
		(out).push_str(&x.to_string());
	}
	out
}

/// Render one of the 9 responses. The status line and Content-Length are
/// left to rocket; Date is always first, Cache-Control second (only for the
/// three uncached bodies) and Content-Type last (never for the empty ok body).
pub fn respond(r: ApiResponse, date: String) -> WireResponse {
	let (code, cached, body) = match r {
		ApiResponse::Ok => (200, false, "".to_string()),
		ApiResponse::PermissionError => (403, false, "{\"error\": \"access_denied\"}".to_string()),
		ApiResponse::OutdatedLoginToken => {
			(401, false, "{\"error\": \"session_expired\"}".to_string())
		}
		ApiResponse::LoginError => (401, false, "{\"error\": \"login_failed\"}".to_string()),
		ApiResponse::SignupError => (400, false, "{\"error\": \"signup_failed\"}".to_string()),
		ApiResponse::TweetId(twt) => (200, false, format!("{{\"tweet_id\": \"{}\"}}", twt)),
		ApiResponse::SessionToken(tk) => (200, true, format!("{{\"session_token\": \"{}\"}}", tk)),
		ApiResponse::Timeline(xs) => (
			200,
			true,
			format!("{{\"timeline\": [{}]}}", show_tweets(xs)),
		),
		ApiResponse::Tweet(user, txt, likes, replies) => (
			200,
			true,
			format!(
				"{{\"username\": \"{}\", \"text\": \"{}\", \"likes\": {}, \"replies\": [{}]}}",
				escape_json(user),
				escape_json(txt),
				likes,
				show_tweets(replies),
			),
		),
	};
	let mut headers: Vec<(String, String)> = vec![("Date".to_string(), date)];
	if cached {
		headers.push(("Cache-Control".to_string(), "no-store".to_string()));
	}
	if !body.is_empty() {
		headers.push(("Content-Type".to_string(), "application/json".to_string()));
	}
	WireResponse {
		status_code: code,
		headers,
		body: body.as_bytes().to_vec(),
	}
}

#[cfg(test)]
mod wire_tests {
	use super::{
		ApiResponse, WireAction, WireError, escape_json, parse_action, respond, to_command,
	};
	use crate::model::Command;
	use quickcheck_macros::quickcheck;

	/// Every endpoint: the exact body shape of to-request parses to the expected action.
	/// Covers the 13 endpoints; all 15 request-line arities incl. the anonymous
	/// token-less variants are exercised by anonymous_and_tokened below.
	#[test]
	fn endpoint_shapes() {
		let cases: Vec<(&str, &str, WireAction)> = vec![
			(
				"/api/post-tweet",
				"7\r\nhi",
				WireAction::PostTweet(7, "hi".to_string()),
			),
			(
				"/api/post-reply",
				"7\r\nhi\r\n42",
				WireAction::PostReply(7, "hi".to_string(), 42),
			),
			(
				"/api/delete-tweet",
				"7\r\n42",
				WireAction::DeleteTweet(7, 42),
			),
			("/api/like-tweet", "7\r\n42", WireAction::Like(7, 42)),
			("/api/unlike-tweet", "7\r\n42", WireAction::Unlike(7, 42)),
			(
				"/api/follow-user",
				"7\r\nbob",
				WireAction::Follow(7, "bob".to_string()),
			),
			(
				"/api/unfollow-user",
				"7\r\nbob",
				WireAction::Unfollow(7, "bob".to_string()),
			),
			(
				"/api/get-tweet",
				"7\r\n42",
				WireAction::GetTweet(Some(7), 42),
			),
			(
				"/api/global-timeline",
				"7\r\n3",
				WireAction::GlobalTimeline(Some(7), 3),
			),
			(
				"/api/private-timeline",
				"7\r\n3",
				WireAction::PrivateTimeline(7, 3),
			),
			("/api/logout", "7", WireAction::Logout(7)),
			(
				"/api/login",
				"bob\r\npw",
				WireAction::Login("bob".to_string(), "pw".to_string()),
			),
			(
				"/api/signup",
				"bob\r\npw",
				WireAction::Signup("bob".to_string(), "pw".to_string()),
			),
		];
		for (path, body, want) in cases {
			assert!(parse_action(path, body.as_bytes()) == Ok(want));
		}
	}

	/// get-tweet and global-timeline: one line is anonymous, two lines carry a token.
	#[test]
	fn anonymous_and_tokened() {
		assert!(
			parse_action("/api/get-tweet", "42".as_bytes()) == Ok(WireAction::GetTweet(None, 42))
		);
		assert!(
			parse_action("/api/get-tweet", "7\r\n42".as_bytes())
				== Ok(WireAction::GetTweet(Some(7), 42))
		);
		assert!(
			parse_action("/api/global-timeline", "3".as_bytes())
				== Ok(WireAction::GlobalTimeline(None, 3))
		);
		assert!(
			parse_action("/api/global-timeline", "7\r\n3".as_bytes())
				== Ok(WireAction::GlobalTimeline(Some(7), 3))
		);
	}

	/// to_command agrees with from-input on all 15 pins in backend/ImplWire.agda.
	/// The two extra pins are the anonymous token-less arities, wi-get-tweet-anon and wi-global-timeline-anon.
	#[test]
	fn commands() {
		let cases: Vec<(WireAction, Command)> = vec![
			(
				WireAction::PostTweet(7, "hi".to_string()),
				Command::Publish(7, "hi".to_string(), None),
			),
			(
				WireAction::PostReply(7, "hi".to_string(), 42),
				Command::Publish(7, "hi".to_string(), Some(42)),
			),
			(WireAction::DeleteTweet(7, 42), Command::Delete(7, 42)),
			(WireAction::Like(7, 42), Command::Like(7, 42)),
			(WireAction::Unlike(7, 42), Command::Unlike(7, 42)),
			(
				WireAction::Follow(7, "bob".to_string()),
				Command::Follow(7, "bob".to_string()),
			),
			(
				WireAction::Unfollow(7, "bob".to_string()),
				Command::Unfollow(7, "bob".to_string()),
			),
			(
				WireAction::GetTweet(Some(7), 42),
				Command::ReadPost(Some(7), 42),
			),
			(WireAction::GetTweet(None, 42), Command::ReadPost(None, 42)),
			(
				WireAction::GlobalTimeline(Some(7), 3),
				Command::ReadGlobalTimeline(Some(7), 3),
			),
			(
				WireAction::GlobalTimeline(None, 3),
				Command::ReadGlobalTimeline(None, 3),
			),
			(
				WireAction::PrivateTimeline(7, 3),
				Command::ReadPersonalTimeline(7, 3),
			),
			(
				WireAction::Login("bob".to_string(), "pw".to_string()),
				Command::Authenticate("bob".to_string(), "pw".to_string()),
			),
			(WireAction::Logout(7), Command::RevokeToken(7)),
			(
				WireAction::Signup("bob".to_string(), "pw".to_string()),
				Command::Register("bob".to_string(), "pw".to_string()),
			),
		];
		for (a, want) in cases {
			assert!(to_command(a) == want);
		}
	}

	/// CRLF, LF and bare CR separators agree, up to one trailing separator.
	#[test]
	fn separator_variants() {
		let want = Ok(WireAction::PostReply(7, "hi".to_string(), 42));
		assert!(parse_action("/api/post-reply", "7\r\nhi\r\n42\r\n".as_bytes()) == want);
		assert!(parse_action("/api/post-reply", "7\nhi\n42\n".as_bytes()) == want);
		assert!(parse_action("/api/post-reply", "7\rhi\r42".as_bytes()) == want);
	}

	/// Malformed requests are rejected with an error, and parsing never panics.
	#[test]
	fn malformed() {
		assert!(parse_action("/api/like-tweet", "x\n42".as_bytes()) == Err(WireError::BadNumber));
		assert!(
			parse_action("/api/get-tweet", "not-a-num".as_bytes()) == Err(WireError::BadNumber)
		);
		assert!(
			parse_action("/api/logout", "99999999999999999999999".as_bytes())
				== Err(WireError::BadNumber)
		);
		assert!(parse_action("/api/logout", "".as_bytes()) == Err(WireError::MissingLine));
		assert!(parse_action("/api/logout", "7\n8".as_bytes()) == Err(WireError::UnexpectedLine));
		assert!(parse_action("/api/nope", "7".as_bytes()) == Err(WireError::UnknownEndpoint));
	}

	/// escape_json of a tweet body.
	#[test]
	fn escaping() {
		let bs = "\\".to_string();
		let q = "\"".to_string();
		let want = format!("{}{}{}hi{}{}{}n", "he said ", bs, q, bs, q, bs);
		assert!(escape_json(format!("he said {}hi{}{}", q, q, "\u{a}")) == want);
		assert!(escape_json("a\u{0}b\u{1f}c".to_string()) == format!("a{}u0000b{}u001fc", bs, bs));
	}

	/// timeline bodies byte-exact for empty, singleton and many ids.
	#[test]
	fn timeline_bodies() {
		let d = "d".to_string();
		assert!(respond(ApiResponse::Timeline(vec![]), d.clone()).status_code == 200);
		assert!(
			respond(ApiResponse::Timeline(vec![]), d.clone()).body
				== "{\"timeline\": []}".as_bytes()
		);
		assert!(
			respond(ApiResponse::Timeline(vec![1]), d.clone()).body
				== "{\"timeline\": [1]}".as_bytes()
		);
		assert!(
			respond(ApiResponse::Timeline(vec![1, 2]), d.clone()).body
				== "{\"timeline\": [1, 2]}".as_bytes()
		);
		assert!(
			respond(ApiResponse::Timeline(vec![1, 2]), d.clone()).headers
				== vec![
					("Date".to_string(), d.clone()),
					("Cache-Control".to_string(), "no-store".to_string()),
					("Content-Type".to_string(), "application/json".to_string()),
				]
		);
		assert!(
			respond(ApiResponse::Ok, d.clone()).headers == vec![("Date".to_string(), d.clone())]
		);
	}

	/// 1:1 with backend/ImplWire.agda: wi-out-* (to-output ctors) pair each Result with
	/// its Response constructor; wi-resp-* (to-response pins) fix the status line (200/403/401/400),
	/// the header LIST, the Content-Length term and the body expression via plain refl.
	/// Each block below asserts one pin with concrete values (wi-resp-ok and wi-resp-timeline
	/// are asserted in timeline_bodies above).  Impl-defined, spec-free residuals: the exact
	/// header ORDER on the wire and the unlines-crlf framing bytes stay opaque - unlines-crlf
	/// is a postulate and the concrete-byte claim is only stated as commented wi-bytes-* signatures.
	#[test]
	fn respond_shapes() {
		let d = "d".to_string();
		// wi-out-denied: 403, Date + Content-Type, no Cache-Control, exact body.
		let r = respond(ApiResponse::PermissionError, d.clone());
		assert!(r.status_code == 403);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"error\": \"access_denied\"}".as_bytes());

		// wi-out-expired: 401, Date + Content-Type, no Cache-Control, exact body.
		let r = respond(ApiResponse::OutdatedLoginToken, d.clone());
		assert!(r.status_code == 401);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"error\": \"session_expired\"}".as_bytes());

		// wi-out-login-failed: 401, Date + Content-Type, no Cache-Control, exact body.
		let r = respond(ApiResponse::LoginError, d.clone());
		assert!(r.status_code == 401);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"error\": \"login_failed\"}".as_bytes());

		// wi-out-signup-failed: 400, Date + Content-Type, no Cache-Control, exact body.
		let r = respond(ApiResponse::SignupError, d.clone());
		assert!(r.status_code == 400);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"error\": \"signup_failed\"}".as_bytes());

		// wi-out-created: 200, Date + Content-Type, no Cache-Control, exact body.
		let r = respond(ApiResponse::TweetId(42), d.clone());
		assert!(r.status_code == 200);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"tweet_id\": \"42\"}".as_bytes());

		// wi-out-session: 200, Date + Cache-Control + Content-Type, exact body.
		let r = respond(ApiResponse::SessionToken(9), d.clone());
		assert!(r.status_code == 200);
		assert!(
			r.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Cache-Control".to_string(), "no-store".to_string()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(r.body == "{\"session_token\": \"9\"}".as_bytes());

		// wi-out-post: 200, Cache-Control, escaped username and text, replies joined.
		let post = respond(
			ApiResponse::Tweet("a\"b".to_string(), "c\nd".to_string(), 3, vec![1, 2]),
			d.clone(),
		);
		assert!(post.status_code == 200);
		assert!(
			post.headers
				== vec![
					("Date".to_string(), d.clone()),
					("Cache-Control".to_string(), "no-store".to_string()),
					("Content-Type".to_string(), "application/json".to_string())
				]
		);
		assert!(
		post.body
				== "{\"username\": \"a\\\"b\", \"text\": \"c\\nd\", \"likes\": 3, \"replies\": [1, 2]}".as_bytes()
	);
	}

	/// QuickCheck: any token and any single-line text round-trip as a post.
	#[quickcheck]
	fn qc_post_round_trip(tk: u64, txt: String) -> bool {
		if txt.contains('\n') || txt.contains('\r') {
			return true;
		}
		let body = format!("{}\r\n{}\r\n", tk, txt);
		parse_action("/api/post-tweet", body.as_bytes()) == Ok(WireAction::PostTweet(tk, txt))
	}
}
