//! The routes of `to-request` (`spec/Interface.agda:52-200`).
//!
//! Each route accepts the body `to-request` writes for its action, calls the
//! command of `from-input` (Interface.agda:346-361) and answers with the
//! `to-response` of the result.

use rocket::State;
use rocket::post;

use crate::db::Db;
use crate::engine::{auth, posts, social, timeline};
use crate::model::{PostId, SessionId};

use super::parse;
use super::response::ApiResponse;

/// A body that is not the `to-request` of the action has no `Response` in the
/// spec; it is answered as a JSON `400`.
fn bad_request() -> ApiResponse {
	ApiResponse::error(400, "bad_request")
}

/// The session a `LoginToken` line denotes.
fn session(field: &str) -> Option<SessionId> {
	parse::natural(field).map(SessionId)
}

/// The post a `TweetId` line denotes.
fn post(field: &str) -> Option<PostId> {
	parse::natural(field).map(PostId)
}

/// `post-tweet`: `publish sid txt nothing` (Interface.agda:347).
#[post("/post-tweet", data = "<body>")]
pub fn post_tweet(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, text)) = parse::two(body) else {
		return bad_request();
	};
	let Some(sid) = session(token) else {
		return bad_request();
	};
	posts::publish(db, sid, text, None).into()
}

/// `post-reply`: `publish sid txt (just pid)` (Interface.agda:348).
#[post("/post-reply", data = "<body>")]
pub fn post_reply(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, text, parent)) = parse::three(body) else {
		return bad_request();
	};
	let (Some(sid), Some(pid)) = (session(token), post(parent)) else {
		return bad_request();
	};
	posts::publish(db, sid, text, Some(pid)).into()
}

/// `delete-tweet`: `delete sid pid` (Interface.agda:357).
#[post("/delete-tweet", data = "<body>")]
pub fn delete_tweet(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, target)) = parse::two(body) else {
		return bad_request();
	};
	let (Some(sid), Some(pid)) = (session(token), post(target)) else {
		return bad_request();
	};
	posts::delete(db, sid, pid).into()
}

/// `like-tweet`: `like sid pid` (Interface.agda:358).
#[post("/like-tweet", data = "<body>")]
pub fn like_tweet(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, target)) = parse::two(body) else {
		return bad_request();
	};
	let (Some(sid), Some(pid)) = (session(token), post(target)) else {
		return bad_request();
	};
	social::like(db, sid, pid).into()
}

/// `unlike-tweet`: `unlike sid pid` (Interface.agda:359).
#[post("/unlike-tweet", data = "<body>")]
pub fn unlike_tweet(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, target)) = parse::two(body) else {
		return bad_request();
	};
	let (Some(sid), Some(pid)) = (session(token), post(target)) else {
		return bad_request();
	};
	social::unlike(db, sid, pid).into()
}

/// `follow-user`: `follow sid username` (Interface.agda:352).
#[post("/follow-user", data = "<body>")]
pub fn follow_user(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, username)) = parse::two(body) else {
		return bad_request();
	};
	let Some(sid) = session(token) else {
		return bad_request();
	};
	social::follow(db, sid, username).into()
}

/// `unfollow-user`: `unfollow sid username` (Interface.agda:353).
#[post("/unfollow-user", data = "<body>")]
pub fn unfollow_user(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, username)) = parse::two(body) else {
		return bad_request();
	};
	let Some(sid) = session(token) else {
		return bad_request();
	};
	social::unfollow(db, sid, username).into()
}

/// `get-tweet`: `read-post (just sid)` or `read-post nothing` (Interface.agda:354-355).
#[post("/get-tweet", data = "<body>")]
pub fn get_tweet(db: &State<Db>, body: &str) -> ApiResponse {
	if let Some((token, target)) = parse::two(body) {
		let (Some(sid), Some(pid)) = (session(token), post(target)) else {
			return bad_request();
		};
		return posts::read_post(db, Some(sid), pid).into();
	}
	let Some(target) = parse::one(body) else {
		return bad_request();
	};
	let Some(pid) = post(target) else {
		return bad_request();
	};
	posts::read_post(db, None, pid).into()
}

/// `global-timeline`: `read-global-timeline msid n` (Interface.agda:356).
#[post("/global-timeline", data = "<body>")]
pub fn global_timeline(db: &State<Db>, body: &str) -> ApiResponse {
	if let Some((token, length)) = parse::two(body) {
		let (Some(sid), Some(len)) = (session(token), parse::length(length)) else {
			return bad_request();
		};
		return timeline::global_timeline(db, Some(sid), len).into();
	}
	let Some(length) = parse::one(body) else {
		return bad_request();
	};
	let Some(len) = parse::length(length) else {
		return bad_request();
	};
	timeline::global_timeline(db, None, len).into()
}

/// `private-timeline`: `read-personal-timeline sid n` (Interface.agda:356).
#[post("/private-timeline", data = "<body>")]
pub fn private_timeline(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((token, length)) = parse::two(body) else {
		return bad_request();
	};
	let (Some(sid), Some(len)) = (session(token), parse::length(length)) else {
		return bad_request();
	};
	timeline::personal_timeline(db, sid, len).into()
}

/// `login`: `authenticate username passwd` (Interface.agda:360).
#[post("/login", data = "<body>")]
pub fn login(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((username, password)) = parse::two(body) else {
		return bad_request();
	};
	auth::authenticate(db, username, password).into()
}

/// `logout`: `revoke-token sid` (Interface.agda:361).
#[post("/logout", data = "<body>")]
pub fn logout(db: &State<Db>, body: &str) -> ApiResponse {
	let Some(token) = parse::one(body) else {
		return bad_request();
	};
	let Some(sid) = session(token) else {
		return bad_request();
	};
	auth::revoke_token(db, sid).into()
}

/// `signup`: `register username passwd` (Interface.agda:361).
#[post("/signup", data = "<body>")]
pub fn signup(db: &State<Db>, body: &str) -> ApiResponse {
	let Some((username, password)) = parse::two(body) else {
		return bad_request();
	};
	auth::register(db, username, password).into()
}
