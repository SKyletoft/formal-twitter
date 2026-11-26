//! Post lifecycle commands: `publish`, `delete` and `read-post`.
//!
//! Spec counterparts: `publish sid txt nothing` is `successful-post`
//! (Twitter.agda:387-398); `publish sid txt (just ppid)` is
//! `successful-reply` / `failed-reply` (Twitter.agda:400-430); `delete` is
//! `delete-post` / `failed-delete-non-existant-post` /
//! `failed-delete-not-author` (Twitter.agda:432-462); `read-post (just sid)`
//! is `read-post-logged-in` and `cant-read-post-*` (Twitter.agda:518-548);
//! `read-post nothing` is `read-post-anonymously` (Twitter.agda:550-554).
//! A command whose session is not `active` answers `Expired`, the
//! `failed-access` case (Twitter.agda:464-468) -- for `read-post` this only
//! applies when a session is supplied.
//!
//! The bodies are filled in by the implementation task; this skeleton fixes
//! the signatures used by `tests/engine_posts.rs`.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, PostId, SessionId};

/// Spec `publish sid txt parent` (Twitter.agda:387-430).
///
/// Creates a post with the given text. Without a `parent` the post takes the
/// author account's `default-visibility`; as a reply it also takes
/// `followers-only` when the parent is `followers-only`
/// (Twitter.agda:213-217). Answers `CreatedPost pid` with the fresh id, and
/// `Denied` (leaving the world unchanged) when the parent cannot be read.
pub fn publish(
	db: &Db,
	session_id: SessionId,
	text: &str,
	parent: Option<PostId>,
) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, text, parent);
	todo!("T2b skeleton")
}

/// Spec `delete sid pid` (Twitter.agda:432-462).
///
/// Turns the post `deleted` when the session's user is its author, and answers
/// `Success`. Answers `Denied` (leaving the world unchanged) when the post is
/// absent or authored by someone else.
pub fn delete(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, post_id);
	todo!("T2b skeleton")
}

/// Spec `read-post msid pid` (Twitter.agda:518-554).
///
/// Answers `ReturnedPost { author, text, likes, replies }` when the post is
/// readable -- either anonymously, when the post is public and live, or
/// through a session that `CanReadPost` (Twitter.agda:158-179) -- and `Denied`
/// otherwise (leaving the world unchanged). An inactive supplied session
/// answers `Expired` (Twitter.agda:464-468).
pub fn read_post(
	db: &Db,
	session_id: Option<SessionId>,
	post_id: PostId,
) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, post_id);
	todo!("T2b skeleton")
}
