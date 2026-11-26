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

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, SessionId};

/// Spec `read-personal-timeline sid n` (Twitter.agda:557-566),
/// `get-personal-timeline`.
///
/// Returns the `n` newest posts that are `live` and whose author the session's
/// user follows, in `World.newest-first` order. A post by the user themself is
/// *not* special-cased: it is included iff the user follows themself, exactly
/// like `follows-post-author` (Twitter.agda:366-369). Replies are ordinary
/// entries. An inactive session answers `Expired` (`failed-access`,
/// Twitter.agda:464-468).
pub fn personal_timeline(db: &Db, session_id: SessionId, n: u32) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, n);
	todo!("T3b skeleton")
}

/// Spec `read-global-timeline msid n` (Twitter.agda:568-585),
/// `get-private-global-timeline` / `get-public-global-timeline`.
///
/// With a session, returns the `n` newest posts the user can read
/// (`CanReadPost`, Twitter.agda:158-179): `live` and either `everyone`, or
/// `followers-only` and followed by the session's user. With `None` it returns
/// the `n` newest `is-post-public` posts (Twitter.agda:342-357): `live` and
/// `everyone`, whatever the follow table says. Both are in
/// `World.newest-first` order. Only the session-carrying form can answer
/// `Expired` (`failed-access`, Twitter.agda:464-468).
pub fn global_timeline(
	db: &Db,
	session_id: Option<SessionId>,
	n: u32,
) -> Result<EngineResult, DbError> {
	let _ = (db, session_id, n);
	todo!("T3b skeleton")
}
