//! Social commands: `follow`, `unfollow`, `like` and `unlike`.
//!
//! Spec counterparts: `follow sid followee` is `follow-user`
//! (Twitter.agda:655-664); `unfollow sid followee` is `unfollow-user`
//! (Twitter.agda:666-675); `like sid pid` is `like-post` (Twitter.agda:587-613)
//! and `failed-like-post` (Twitter.agda:615-619); `unlike sid pid` is
//! `unlike-post` (Twitter.agda:621-647) and `failed-unlike-post`
//! (Twitter.agda:649-653). A command whose session is not `active` answers
//! `Expired`, the `failed-access` case (Twitter.agda:464-468): all four
//! commands extract their session (`extract-sid`, Twitter.agda:203-207), so
//! -- unlike `read-post nothing` -- there is no vacuous case here.
//!
//! The bodies are filled in by the implementation task; this skeleton fixes
//! the signatures used by `tests/engine_social.rs`.  Until then each body
//! consumes its arguments (`let _ = ...`) so the skeleton is lint-clean.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, PostId, SessionId};

/// Spec `follow sid followee` (Twitter.agda:655-664).
///
/// Records that the session's user follows `followee` and answers `Success`.
/// The followee need not exist: `follow` has no failure rule at all, so
/// following an unknown username is also `Success`. `add-follower`
/// (Twitter.agda:371-375) is idempotent, so following twice changes nothing.
pub fn follow(db: &Db, session_id: SessionId, followee: &str) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, followee);
	todo!("T3a skeleton")
}

/// Spec `unfollow sid followee` (Twitter.agda:666-675).
///
/// Removes the follow edge of the session's user to `followee` and answers
/// `Success`. There is no premise that the edge existed, so unfollowing a
/// user that was never followed is also `Success` and changes nothing.
pub fn unfollow(db: &Db, session_id: SessionId, followee: &str) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, followee);
	todo!("T3a skeleton")
}

/// Spec `like sid pid` (Twitter.agda:587-619).
///
/// Adds the session's user to the post's like list and answers `Success`,
/// provided the post is readable (`CanReadPost`, Twitter.agda:158-179): `live`
/// and either `everyone`, or `followers-only` and followed by the user.
/// Otherwise `Denied` (`failed-like-post`), leaving the world unchanged. The
/// user may be the author, and liking twice changes nothing.
pub fn like(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, post_id);
	todo!("T3a skeleton")
}

/// Spec `unlike sid pid` (Twitter.agda:621-653).
///
/// Removes the session's user from the post's like list and answers `Success`,
/// with the same readability premise as `like`. Otherwise `Denied`
/// (`failed-unlike-post`), leaving the world unchanged. Unliking a post the
/// user never liked is also `Success` and changes nothing.
pub fn unlike(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, post_id);
	todo!("T3a skeleton")
}
