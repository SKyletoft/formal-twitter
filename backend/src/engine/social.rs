//! Social commands: `follow`, `unfollow`, `like` and `unlike`.
//!
//! Spec counterparts: `follow sid followee` is `follow-user`
//! (Twitter.agda:655-664); `unfollow sid followee` is `unfollow-user`
//! (Twitter.agda:666-675); `like sid pid` is `like-post` (Twitter.agda:587-613)
//! and `failed-like-post` (Twitter.agda:615-619); `unlike sid pid` is
//! `unlike-post` (Twitter.agda:621-647) and `failed-unlike-post`
//! (Twitter.agda:649-653).
//!
//! Every one of the four rules has `ValidSession before sid acc user` as its
//! first premise, and all four commands extract their session (`extract-sid`,
//! Twitter.agda:203-207), so -- unlike `read-post nothing` -- there is no
//! vacuous case here: an inactive session answers `Expired`, the `failed-access`
//! case (Twitter.agda:464-468). That step's before and after worlds are the
//! same, so `Expired` takes precedence over `Success`/`Denied` and leaves the
//! persisted world untouched.
//!
//! Each command runs in exactly one `db.write` transaction, so a `Denied` or
//! `Expired` answer commits nothing.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, PostId, SessionId};
use crate::store;

/// Spec `follow sid followee` (Twitter.agda:655-664), `follow-user`.
///
/// Records that the session's user follows `followee` -- `World.follows after ≡
/// add-follower (World.follows before) follower followee` -- and answers
/// `Success`. The followee need not exist: `follow-user` has no premise on it,
/// so following an unknown username is also `Success`. `add-follower`
/// (Twitter.agda:371-375) is idempotent, so following twice changes nothing.
/// An inactive session answers `Expired` (`failed-access`, Twitter.agda:464-468)
/// and stores nothing.
pub fn follow(db: &Db, session_id: SessionId, followee: &str) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		store::add_follow(c, &username, followee)?;
		Ok(EngineResult::Success)
	})
}

/// Spec `unfollow sid followee` (Twitter.agda:666-675), `unfollow-user`.
///
/// Removes the follow edge of the session's user to `followee` -- `World.follows
/// after ≡ remove-follower (World.follows before) follower followee` -- and
/// answers `Success`. There is no premise that the edge existed, so unfollowing
/// a user that was never followed is also `Success` and changes nothing. An
/// inactive session answers `Expired` (`failed-access`, Twitter.agda:464-468)
/// and stores nothing.
pub fn unfollow(db: &Db, session_id: SessionId, followee: &str) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		store::remove_follow(c, &username, followee)?;
		Ok(EngineResult::Success)
	})
}

/// Spec `like sid pid` (Twitter.agda:587-619), `like-post` / `failed-like-post`.
///
/// Adds the session's user to the post's like list (`user ∈ Post.likes post'`)
/// and answers `Success`, provided the post is readable (`CanReadPost`,
/// Twitter.agda:158-179): `live` and either `everyone`, or `followers-only` and
/// followed by the user. Otherwise `Denied` (`failed-like-post`,
/// Twitter.agda:615-619), leaving the world unchanged. `like-post` has no
/// distinctness premise, so the user may be the author, and `add-like` is
/// idempotent, so liking twice changes nothing. An inactive session answers
/// `Expired` (`failed-access`, Twitter.agda:464-468) and stores nothing: that
/// takes precedence over both `Success` and `Denied`.
pub fn like(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		if !store::can_read_post(c, &username, post_id)? {
			return Ok(EngineResult::Denied);
		}
		store::add_like(c, post_id, &username)?;
		Ok(EngineResult::Success)
	})
}

/// Spec `unlike sid pid` (Twitter.agda:621-653), `unlike-post` /
/// `failed-unlike-post`.
///
/// Removes the session's user from the post's like list (`user ∉ Post.likes
/// post`) and answers `Success`, with the same readability premise as `like`:
/// `CanReadPost` (Twitter.agda:158-179), read over the before world. Otherwise
/// `Denied` (`failed-unlike-post`, Twitter.agda:649-653), leaving the world
/// unchanged -- including the like itself. There is no premise that the like
/// existed, so unliking a post the user never liked is also `Success` and
/// changes nothing. An inactive session answers `Expired` (`failed-access`,
/// Twitter.agda:464-468) and stores nothing: that takes precedence over both
/// `Success` and `Denied`.
pub fn unlike(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		if !store::can_read_post(c, &username, post_id)? {
			return Ok(EngineResult::Denied);
		}
		store::remove_like(c, post_id, &username)?;
		Ok(EngineResult::Success)
	})
}
