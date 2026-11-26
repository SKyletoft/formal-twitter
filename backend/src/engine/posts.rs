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
//! applies when a session is supplied, because `extract-sid (read-post msid _)
//! = msid` (Twitter.agda:196): an anonymous read extracts no session, so
//! `failed-access` applies to it vacuously and an unreadable post read without
//! a session answers `Expired`, never `Denied`.

use diesel::SqliteConnection;

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, PostId, PostStatus, SessionId, Visibility};
use crate::store;

/// Spec `publish sid txt parent` (Twitter.agda:387-430).
///
/// Creates a post with the given text. Without a `parent` the post takes the
/// author account's `default-visibility`; as a reply it also takes
/// `followers-only` when the parent is `followers-only`
/// (Twitter.agda:213-217). Answers `CreatedPost pid` with the fresh id, and
/// `Denied` (leaving the world unchanged) when the parent cannot be read
/// (`CanReadPost`, Twitter.agda:158-179).
pub fn publish(
	db: &Db,
	session_id: SessionId,
	text: &str,
	parent: Option<PostId>,
) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		// `ValidSession` carries the account (Twitter.agda:150-157), so this is
		// an invariant; a missing row still must not panic.
		let Some(account) = store::get_account(c, &username)? else {
			return Ok(EngineResult::Expired);
		};
		match parent {
			None => {
				let pid = crate::ids::allocate_post_id(c)?;
				store::insert_post(c, pid, &username, text, account.default_visibility)?;
				Ok(EngineResult::CreatedPost(pid))
			}
			Some(ppid) => {
				let Some(ppost) = store::get_post(c, ppid)? else {
					return Ok(EngineResult::Denied);
				};
				if ppost.status != PostStatus::Live {
					return Ok(EngineResult::Denied);
				}
				let visibility = match ppost.visibility {
					Visibility::Everyone => account.default_visibility,
					Visibility::FollowersOnly => {
						if !store::is_following(c, &username, &ppost.author)? {
							return Ok(EngineResult::Denied);
						}
						Visibility::FollowersOnly
					}
				};
				let pid = crate::ids::allocate_post_id(c)?;
				store::insert_reply(c, pid, &username, text, visibility, ppid)?;
				Ok(EngineResult::CreatedPost(pid))
			}
		}
	})
}

/// Spec `delete sid pid` (Twitter.agda:432-462).
///
/// Turns the post `deleted` when the session's user is its author, and answers
/// `Success`. Answers `Denied` (leaving the world unchanged) when the post is
/// absent or authored by someone else. `delete-post` has no `live` premise, so
/// deleting an already `deleted` own post also answers `Success` and changes
/// nothing.
pub fn delete(db: &Db, session_id: SessionId, post_id: PostId) -> Result<EngineResult, DbError> {
	db.write(|c| {
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		if store::delete_own(c, post_id, &username)?.is_some() {
			Ok(EngineResult::Success)
		} else {
			Ok(EngineResult::Denied)
		}
	})
}

/// The `returned-post` answer of `read-post` (Twitter.agda:518-555).
fn returned_post(c: &mut SqliteConnection, view: store::PostView) -> Result<EngineResult, DbError> {
	let replies = store::replies_of(c, view.post.id)?;
	Ok(EngineResult::ReturnedPost {
		author: view.post.author,
		text: view.post.text,
		likes: view.likes.max(0) as u64,
		replies,
	})
}

/// Spec `read-post msid pid` (Twitter.agda:518-554).
///
/// Answers `ReturnedPost { author, text, likes, replies }` when the post is
/// readable -- either anonymously, when the post is public and live
/// (`read-post-anonymously`, Twitter.agda:550-554), or through a session that
/// `CanReadPost` (Twitter.agda:158-179) -- and `Denied` otherwise (leaving the
/// world unchanged). An inactive supplied session answers `Expired`
/// (Twitter.agda:464-468), and so does an anonymous read of a post that
/// `is-post-public` rejects: `read-post nothing` extracts no session, so
/// `failed-access` applies vacuously there.
pub fn read_post(
	db: &Db,
	session_id: Option<SessionId>,
	post_id: PostId,
) -> Result<EngineResult, DbError> {
	db.read(|c| match session_id {
		Some(sid) => {
			let Some(username) = store::active_user(c, sid)? else {
				return Ok(EngineResult::Expired);
			};
			if !store::can_read_post(c, &username, post_id)? {
				return Ok(EngineResult::Denied);
			}
			match store::post_view(c, post_id)? {
				Some(view) => returned_post(c, view),
				None => Ok(EngineResult::Denied),
			}
		}
		None => {
			if !store::can_read_anonymous(c, post_id)? {
				return Ok(EngineResult::Expired);
			}
			match store::post_view(c, post_id)? {
				Some(view) => returned_post(c, view),
				None => Ok(EngineResult::Expired),
			}
		}
	})
}
