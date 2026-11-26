//! Timelines: `personal_timeline` and `global_timeline`.
//!
//! Spec counterparts: `read-personal-timeline sid n` is `get-personal-timeline`
//! (Twitter.agda:557-566); `read-global-timeline (just sid) n` is
//! `get-private-global-timeline` (Twitter.agda:568-576); `read-global-timeline
//! nothing n` is `get-public-global-timeline` (Twitter.agda:578-585).
//!
//! All three rules filter the *whole* `World.newest-first` list before taking
//! the first `n` entries, so `n` bounds the answer, never the scanned prefix:
//! a query must not stop after `n` candidate rows. `take n` (Twitter.agda:560)
//! saturates, so `n` larger than the number of readable posts yields the whole
//! filtered list.
//!
//! The spec's answers are
//! `take n (filterᵇ (follows-post-author before user) (filter (can-read-post
//! before sid) newest-first))` for the personal timeline, the same without the
//! `follows-post-author` filter for the private global timeline, and
//! `take n (filter (is-post-public before) newest-first)` for the public one.
//! `ImplProofs.agda` (P15) proves those expressions coincide with the simple
//! characterizations implemented here, over the post rows ordered by `seq
//! DESC`:
//!
//! * personal: `live` and the session's user follows the author;
//! * private global: `live` and (`everyone` or the user follows the author);
//! * public global: `live` and `everyone`.
//!
//! Both `personal_timeline` and `global_timeline (just sid)` extract a session,
//! so an inactive one answers `Expired`, the `failed-access` case
//! (Twitter.agda:464-468). `global_timeline` with `None` is tokenless -- its
//! extracted session is `nothing` -- so `failed-access`'s premise is vacuous
//! and it never expires: it always answers `ReturnedTimeline`.
//!
//! The id lists are cached in [`Db`], keyed by [`TimelineKey`] (which timeline
//! and which `n`). A hit answers the same `ReturnedTimeline` the query would:
//! ids change only through commands that go through [`Db::write`], and every
//! successful write clears the whole cache and bumps the generation, so a list
//! cached before a write can never be served after it. Session validity is
//! never cached: `active_user` always runs first for the two session-carrying
//! forms, so `Expired` keeps precedence over a cached list. The cache adds no
//! `Step` to the spec -- the three rules above still define the answer, and
//! `tests/timeline_cache.rs` checks the cached handle against an uncached one.

use crate::db::{Db, TimelineKey};
use crate::engine::result::EngineResult;
use crate::model::{DbError, SessionId};
use crate::store;

/// Spec `read-personal-timeline sid n` (Twitter.agda:557-566),
/// `get-personal-timeline`.
///
/// Returns the `n` newest posts that are `live` and whose author the session's
/// user follows, in `World.newest-first` order. A post by the user themself is
/// *not* special-cased: it is included iff the user follows themself, exactly
/// like `follows-post-author` (Twitter.agda:366-369). Replies are ordinary
/// entries. An inactive session answers `Expired` (`failed-access`,
/// Twitter.agda:464-468), checked before the cache is consulted.
pub fn personal_timeline(db: &Db, session_id: SessionId, n: u32) -> Result<EngineResult, DbError> {
	db.read(|c| {
		// Never cached: a write may revoke the session, and `Expired` wins over
		// any cached list.
		let Some(username) = store::active_user(c, session_id)? else {
			return Ok(EngineResult::Expired);
		};
		let key = TimelineKey::Personal(username.clone(), n);
		// A hit needs no timeline query: the ids are exactly what the filter
		// below would return for this still-valid session.
		if let Some(ids) = db.cache_get_timeline(&key) {
			return Ok(EngineResult::ReturnedTimeline(ids));
		}
		// Sampled before the database read below and checked by
		// `cache_put_timeline` against the generation the write transaction
		// moved: a write racing in between keeps its invalidation.
		let sampled = db.cache_generation();
		let ids = store::personal_timeline_for(c, &username, n)?;
		db.cache_put_timeline(sampled, key, ids.clone());
		Ok(EngineResult::ReturnedTimeline(ids))
	})
}

/// Spec `read-global-timeline msid n` (Twitter.agda:568-585),
/// `get-private-global-timeline` / `get-public-global-timeline`.
///
/// With a session, returns the `n` newest posts the user can read
/// (`CanReadPost`, Twitter.agda:168-188): `live` and either `everyone`, or
/// `followers-only` and followed by the session's user. With `None` it returns
/// the `n` newest `is-post-public` posts (Twitter.agda:342-357): `live` and
/// `everyone`, whatever the follow table says. Both are in
/// `World.newest-first` order. Only the session-carrying form can answer
/// `Expired` (`failed-access`, Twitter.agda:464-468), and it checks the session
/// before the cache is consulted.
pub fn global_timeline(
	db: &Db,
	session_id: Option<SessionId>,
	n: u32,
) -> Result<EngineResult, DbError> {
	match session_id {
		Some(sid) => db.read(|c| {
			// Never cached: a write may revoke the session, and `Expired` wins
			// over any cached list.
			let Some(username) = store::active_user(c, sid)? else {
				return Ok(EngineResult::Expired);
			};
			let key = TimelineKey::Global(username.clone(), n);
			if let Some(ids) = db.cache_get_timeline(&key) {
				return Ok(EngineResult::ReturnedTimeline(ids));
			}
			let sampled = db.cache_generation();
			let ids = store::global_timeline_for(c, &username, n)?;
			db.cache_put_timeline(sampled, key, ids.clone());
			Ok(EngineResult::ReturnedTimeline(ids))
		}),
		None => {
			// No session to validate, so a hit answers without taking the
			// database lock at all.
			let key = TimelineKey::Anonymous(n);
			if let Some(ids) = db.cache_get_timeline(&key) {
				return Ok(EngineResult::ReturnedTimeline(ids));
			}
			db.read(|c| {
				// Sampled after the lock is taken, before the read: a write
				// racing between the lookup above and here either invalidates
				// this insert or the list it would serve, never leaves a stale
				// list behind.
				let sampled = db.cache_generation();
				let ids = store::public_timeline(c, n)?;
				db.cache_put_timeline(sampled, key, ids.clone());
				Ok(EngineResult::ReturnedTimeline(ids))
			})
		}
	}
}
