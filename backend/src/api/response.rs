//! `to-response` (`spec/Interface.agda:224-309`) as a Rocket responder.
//!
//! The three headers the spec sets besides the body's own are reproduced
//! exactly: `Content-Type` only on JSON replies, `Cache-Control: no-store`
//! only where the spec says so, and a `Content-Length` that is the body's
//! exact octet count (sized body). `Date` is added by the server's fairing.

use std::io::Cursor;

use rocket::http::{Header, Status};
use rocket::request::Request;
use rocket::response::{Responder, Response, Result as ResponseResult};

use crate::engine::EngineResult;
use crate::model::{DbError, PostId, SessionId};

/// The media type of every JSON reply, without a charset parameter.
const JSON: &str = "application/json";

/// A reply of the public API.
pub struct ApiResponse {
	pub status: u16,
	pub body: Vec<u8>,
	pub content_type: Option<&'static str>,
	pub cache_control: bool,
}

impl ApiResponse {
	/// `to-response ok` (Interface.agda:225-230): `200`, an empty body,
	/// `Content-Length: 0` and no other headers.
	pub fn ok() -> Self {
		Self {
			status: 200,
			body: Vec::new(),
			content_type: None,
			cache_control: false,
		}
	}

	/// A JSON reply with the given status.
	pub fn json(status: u16, body: String) -> Self {
		Self {
			status,
			body: body.into_bytes(),
			content_type: Some(JSON),
			cache_control: false,
		}
	}

	/// One of the spec's `{"error": "..."}` replies.
	pub fn error(status: u16, error: &str) -> Self {
		Self::json(status, format!("{{\"error\": \"{error}\"}}"))
	}

	/// `Cache-Control: no-store`, which the spec sets on every reply that
	/// carries session-scoped content (Interface.agda:258-309).
	pub fn no_store(mut self) -> Self {
		self.cache_control = true;
		self
	}
}

/// `escape` of the spec (a postulate): JSON string escaping, as `serde_json`
/// writes it, without the quoting this adds around the body's raw text.
pub fn escape(text: &str) -> String {
	serde_json::to_string(text).unwrap_or_else(|_| "\"\"".to_owned())
}

/// `show-tweets` (Interface.agda:219-222): ids separated by `", "`.
pub fn show_tweets(ids: &[PostId]) -> String {
	ids.iter()
		.map(|id| id.0.to_string())
		.collect::<Vec<_>>()
		.join(", ")
}

/// `to-output` (Interface.agda:335-344) and `to-response` of its answer.
impl From<EngineResult> for ApiResponse {
	fn from(result: EngineResult) -> Self {
		match result {
			EngineResult::Success => Self::ok(),
			EngineResult::Denied => Self::error(403, "access_denied"),
			EngineResult::Expired => Self::error(401, "session_expired"),
			EngineResult::LoginFailed => Self::error(401, "login_failed"),
			EngineResult::SignupFailed => Self::error(400, "signup_failed"),
			EngineResult::CreatedPost(PostId(id)) => {
				Self::json(200, format!("{{\"tweet_id\": \"{id}\"}}"))
			}
			EngineResult::IssuedSession(SessionId(id)) => {
				Self::json(200, format!("{{\"session_token\": \"{id}\"}}")).no_store()
			}
			EngineResult::ReturnedTimeline(ids) => {
				Self::json(200, format!("{{\"timeline\": [{}]}}", show_tweets(&ids))).no_store()
			}
			EngineResult::ReturnedPost {
				author,
				text,
				likes,
				replies,
			} => Self::json(
				200,
				format!(
					"{{\"username\": {}, \"text\": {}, \"likes\": {likes}, \"replies\": [{}]}}",
					escape(&author),
					escape(&text),
					show_tweets(&replies)
				),
			)
			.no_store(),
		}
	}
}

/// A database error has no `Response` in the spec; it is answered as an
/// internal error, without any of the spec's cache directives.
impl From<Result<EngineResult, DbError>> for ApiResponse {
	fn from(result: Result<EngineResult, DbError>) -> Self {
		match result {
			Ok(result) => result.into(),
			Err(_) => Self::error(500, "internal"),
		}
	}
}

impl<'r> Responder<'r, 'static> for ApiResponse {
	fn respond_to(self, _request: &'r Request<'_>) -> ResponseResult<'static> {
		let mut response = Response::new();
		response.set_status(Status::new(self.status));
		if let Some(content_type) = self.content_type {
			response.set_header(Header::new("Content-Type", content_type));
		}
		if self.cache_control {
			response.set_header(Header::new("Cache-Control", "no-store"));
		}
		// Rocket's real server writes this for a sized body; setting it here
		// too keeps the byte count exact through the local client as well.
		response.set_header(Header::new("Content-Length", self.body.len().to_string()));
		response.set_sized_body(self.body.len(), Cursor::new(self.body));
		Ok(response)
	}
}
