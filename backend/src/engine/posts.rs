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
use crate::model::{DbError, Post, PostId, PostStatus, PublicPost, SessionId, Visibility};
use crate::store;

/// Spec `publish sid txt parent` (Twitter.agda:387-430).
///
/// Creates a post with the given text. Without a `parent` the post takes the
/// author account's `default-visibility`; as a reply it also takes
/// `followers-only` when the parent is `followers-only`
/// (Twitter.agda:213-217). Answers `CreatedPost pid` with the fresh id, and
/// `Denied` (leaving the world unchanged) when the parent cannot be read
/// (`CanReadPost`, Twitter.agda:158-179).
///
/// The session's account and -- for a reply -- the parent's author, visibility,
/// status and follow edge all come from one [`store::publish_context`] query,
/// so the answer keeps the spec's precedence: a session that is not `active`
/// is `Expired` before any parent is looked at, and only then can a missing,
/// `deleted` or unreadable parent turn the answer into `Denied`.
pub fn publish(
	db: &Db,
	session_id: SessionId,
	text: &str,
	parent: Option<PostId>,
) -> Result<EngineResult, DbError> {
	db.write(|c| {
		// One query for the whole decision: `ValidSession` carries the account
		// (Twitter.agda:150-157), so a missing account is impossible; the join
		// keeps it total and answers `Expired` regardless.
		let Some(context) = store::publish_context(c, session_id, parent)? else {
			return Ok(EngineResult::Expired);
		};
		let visibility = match (parent, context.parent) {
			(None, _) => context.default_visibility,
			// A named parent that has no row is `¬ CanReadPost`
			// (`failed-reply`, Twitter.agda:424-428).
			(Some(_), None) => return Ok(EngineResult::Denied),
			(Some(_), Some(ppost)) => {
				if ppost.status != PostStatus::Live {
					return Ok(EngineResult::Denied);
				}
				match ppost.visibility {
					Visibility::Everyone => context.default_visibility,
					// `CanReadPost` needs the follow edge for `followers-only`.
					Visibility::FollowersOnly if ppost.following => Visibility::FollowersOnly,
					Visibility::FollowersOnly => return Ok(EngineResult::Denied),
				}
			}
		};
		let pid = crate::ids::allocate_post_id(c)?;
		match parent {
			None => store::insert_post(c, pid, &context.username, text, visibility)?,
			Some(ppid) => {
				store::insert_reply(c, pid, &context.username, text, visibility, ppid)?;
			}
		}
		Ok(EngineResult::CreatedPost(pid))
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

/// The `returned-post` body of `read-post` (Twitter.agda:518-555): the author,
/// text, like count (`likes` is the length of the spec's like list) and reply
/// ids of `view`. Also the value the public read cache stores.
fn public_body(c: &mut SqliteConnection, view: store::PostView) -> Result<PublicPost, DbError> {
	let replies = store::replies_of(c, view.post.id)?;
	Ok(PublicPost {
		author: view.post.author,
		text: view.post.text,
		likes: view.likes.max(0) as u64,
		replies,
	})
}

fn returned_post(body: PublicPost) -> EngineResult {
	EngineResult::ReturnedPost {
		author: body.author,
		text: body.text,
		likes: body.likes,
		replies: body.replies,
	}
}

/// `is-post-public` (Twitter.agda:342-357) on a post already read: `live` and
/// visible to `everyone`. Only such a post has a reader-independent body.
fn is_public(post: &Post) -> bool {
	post.status == PostStatus::Live && post.visibility == Visibility::Everyone
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
///
/// Public bodies are served from the cache of [`Db`] when possible. Only a
/// `live`, `everyone` post is ever inserted, because only such a post has the
/// same body for every reader; every successful write empties the cache, so a
/// hit is never stale. Session validity is never cached, so the session check
/// of the `Some(sid)` path always runs first and `Expired` keeps its precedence
/// over `Denied`/`ReturnedPost` (T7 revokes sessions). The cache adds no `Step`
/// to the spec: it only recomputes the answer these same theorems define, and
/// `tests/cache.rs` checks it against an uncached `Db`.
///
/// On a miss the body, its like count and the readability decision come from
/// one fused query ([`store::post_view_for`] / [`store::post_view_anonymous`]),
/// so `Denied`/`Expired` and `ReturnedPost` are decided from the same row the
/// body is built from; only the reply list needs a second query.
pub fn read_post(
	db: &Db,
	session_id: Option<SessionId>,
	post_id: PostId,
) -> Result<EngineResult, DbError> {
	// Anonymous reads have no session to validate, and every cached body is a
	// live `everyone` post, readable without a session at all: a hit answers
	// without taking the database lock.
	let Some(sid) = session_id else {
		if let Some(body) = db.cache_get(post_id) {
			return Ok(returned_post(body));
		}
		return db.read(|c| {
			// Sampled before the database read below, and checked by `cache_put`
			// against the generation the write transaction moved: a write racing
			// in between keeps its invalidation.
			let sampled = db.cache_generation();
			// One query for both the body and `is-post-public`
			// (Twitter.agda:342-357): absent and unreadable answer the same
			// `Expired`, since `read-post nothing` extracts no session.
			let Some(read) = store::post_view_anonymous(c, post_id)? else {
				return Ok(EngineResult::Expired);
			};
			if !read.readable {
				return Ok(EngineResult::Expired);
			}
			let public = is_public(&read.view.post);
			let body = public_body(c, read.view)?;
			if public {
				db.cache_put(sampled, post_id, body.clone());
			}
			Ok(returned_post(body))
		});
	};
	db.read(|c| {
		// Never cached: a write may revoke the session, and `Expired` wins over
		// any cached body.
		let Some(username) = store::active_user(c, sid)? else {
			return Ok(EngineResult::Expired);
		};
		// A hit needs no query: the cached post is live and `everyone`, which
		// `CanReadPost` (Twitter.agda:158-179) grants to every account.
		if let Some(body) = db.cache_get(post_id) {
			return Ok(returned_post(body));
		}
		// Sampled before the database read below, and checked by `cache_put`
		// against the generation the write transaction moved: a write racing in
		// between keeps its invalidation. No cache lock is held across the I/O.
		let sampled = db.cache_generation();
		// One query for the body, its like count and `CanReadPost`
		// (Twitter.agda:168-187). An absent post is unreadable: `Denied`, the
		// same answer the spec's `cant-read-post-*` rules give.
		let Some(read) = store::post_view_for(c, &username, post_id)? else {
			return Ok(EngineResult::Denied);
		};
		if !read.readable {
			return Ok(EngineResult::Denied);
		}
		let public = is_public(&read.view.post);
		let body = public_body(c, read.view)?;
		// `Denied` and `Expired` are never cached, and neither is a
		// `followers-only` body: it depends on who is asking.
		if public {
			db.cache_put(sampled, post_id, body.clone());
		}
		Ok(returned_post(body))
	})
}
