//! The `time-passes` command: session timeout.
//!
//! Spec counterpart: `time-passes` (Twitter.agda:124) with the
//! `session-timeout` Step (Twitter.agda:691-702): every `active` session
//! becomes `revoked` and nothing else is touched.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::DbError;
use crate::store;

/// Spec `time-passes` (Twitter.agda:124) with the `session-timeout` Step
/// (Twitter.agda:691-702): every active session becomes revoked, everything
/// else is unchanged.
///
/// The whole effect is one `UPDATE sessions SET status = 'revoked' WHERE status
/// = 'active'` inside a single write transaction, so a reader sees either the
/// world before the timeout or the world after it, never a mix. It is also
/// idempotent: a second pass finds no `active` row left to move.
pub fn time_passes(db: &Db) -> Result<EngineResult, DbError> {
	db.write(|c| {
		store::revoke_all_sessions(c)?;
		Ok(EngineResult::Success)
	})
}
