//! The responses from the public API and their wire format, straight
//! from `to-response` in spec/Interface.agda.

#[derive(Debug)]
pub enum Response {
	// The bare `ok` constructor exists in the spec but no implemented
	// action currently returns it.
	#[allow(dead_code)]
	Ok,
	PermissionError,
	OutdatedLoginToken,
	TweetId(u64),
	Timeline(Vec<u64>),
	SessionToken(u64),
	LoginError,
	SignupError,
	Tweet {
		username: String,
		text: String,
		likes: u64,
		replies: Vec<u64>,
	},
}

fn show_tweets(ids: &[u64]) -> String {
	ids.iter()
		.map(|i| i.to_string())
		.collect::<Vec<_>>()
		.join(", ")
}

pub fn render(status: &str, content_type: Option<&str>, body: &str) -> String {
	let mut out = format!("HTTP/1.1 {}\r\n", status);
	if let Some(ct) = content_type {
		out.push_str("Content-Type: ");
		out.push_str(ct);
		out.push_str("\r\n");
	}
	out.push_str("Content-Length: ");
	out.push_str(&body.len().to_string());
	out.push_str("\r\n");
	out.push_str("Connection: close\r\n");
	out.push_str("\r\n");
	out.push_str(body);
	out
}

fn json(body: String) -> String {
	render("200 OK", Some("application/json"), &body)
}

fn error(status: &str, code: &str) -> String {
	render(
		status,
		Some("application/json"),
		&format!("{{'error': '{}'}}\n", code),
	)
}

impl Response {
	#[allow(clippy::wrong_self_convention)] // it renders and consumes
	pub fn to_http(self) -> String {
		match self {
			Response::Ok => render("200 OK", None, ""),
			Response::PermissionError => error("403 Forbidden", "access_denied"),
			Response::OutdatedLoginToken => error("401 Unauthorized", "session_expired"),
			Response::TweetId(twt) => json(format!("{{'tweet_id': '{}'}}\n", twt)),
			Response::Timeline(xs) => json(format!("{{'timeline': [{}]}}\n", show_tweets(&xs))),
			Response::SessionToken(tk) => json(format!("{{'session_token': '{}'}}\n", tk)),
			Response::LoginError => error("401 Unauthorized", "login_failed"),
			Response::SignupError => error("400 Bad Request", "signup_failed"),
			Response::Tweet {
				username,
				text,
				likes,
				replies,
			} => json(format!(
				"{{'username': '{}', 'text': '{}', 'likes': {}, 'replies': [{}]}}\n",
				username,
				text,
				likes,
				show_tweets(&replies)
			)),
		}
	}
}

pub fn not_found() -> String {
	render(
		"404 Not Found",
		Some("text/plain; charset=utf-8"),
		"not found\n",
	)
}

#[cfg(test)]
mod tests {
	use super::*;

	fn strip(x: &str) -> String {
		// Drop transport-only headers; focus on the spec payload.
		x.split_once("\r\n\r\n").unwrap().1.to_string()
	}

	#[test]
	fn ok_is_bare_status_line() {
		let r = Response::Ok.to_http();
		assert!(r.starts_with("HTTP/1.1 200 OK\r\n"));
		assert!(strip(&r).is_empty());
	}

	#[test]
	fn permission_error() {
		let r = Response::PermissionError.to_http();
		assert!(r.starts_with("HTTP/1.1 403 Forbidden\r\n"));
		assert!(r.contains("Content-Type: application/json\r\n"));
		assert_eq!(strip(&r), "{'error': 'access_denied'}\n");
	}

	#[test]
	fn outdated_login_token() {
		assert_eq!(
			strip(&Response::OutdatedLoginToken.to_http()),
			"{'error': 'session_expired'}\n"
		);
	}

	#[test]
	fn tweet_id() {
		let r = Response::TweetId(7).to_http();
		assert!(r.starts_with("HTTP/1.1 200 OK\r\n"));
		assert_eq!(strip(&r), "{'tweet_id': '7'}\n");
	}

	#[test]
	fn timeline_shapes() {
		assert_eq!(
			strip(&Response::Timeline(vec![]).to_http()),
			"{'timeline': []}\n"
		);
		assert_eq!(
			strip(&Response::Timeline(vec![3]).to_http()),
			"{'timeline': [3]}\n"
		);
		assert_eq!(
			strip(&Response::Timeline(vec![1, 2, 3]).to_http()),
			"{'timeline': [1, 2, 3]}\n"
		);
	}

	#[test]
	fn session_token() {
		assert_eq!(
			strip(&Response::SessionToken(0).to_http()),
			"{'session_token': '0'}\n"
		);
	}

	#[test]
	fn login_error() {
		assert_eq!(
			strip(&Response::LoginError.to_http()),
			"{'error': 'login_failed'}\n"
		);
	}

	#[test]
	fn signup_error() {
		let r = Response::SignupError.to_http();
		assert!(r.starts_with("HTTP/1.1 400 Bad Request\r\n"));
		assert_eq!(strip(&r), "{'error': 'signup_failed'}\n");
	}

	#[test]
	fn tweet() {
		assert_eq!(
			strip(
				&Response::Tweet {
					username: "alice".to_string(),
					text: "hello".to_string(),
					likes: 2,
					replies: vec![5, 9],
				}
				.to_http()
			),
			"{'username': 'alice', 'text': 'hello', 'likes': 2, 'replies': [5, 9]}\n"
		);
	}

	#[test]
	fn content_length_matches_bytes() {
		let r = Response::Tweet {
			username: "blåhaj".to_string(),
			text: "ændøü".to_string(),
			likes: 0,
			replies: vec![],
		}
		.to_http();
		let body = strip(&r);
		let len: usize = r
			.lines()
			.find(|l| l.starts_with("Content-Length: "))
			.unwrap()["Content-Length: ".len()..]
			.parse()
			.unwrap();
		assert_eq!(len, body.len());
	}
}
