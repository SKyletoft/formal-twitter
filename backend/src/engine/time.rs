//! The `time-passes` command: session timeout.
//!
//! Spec counterpart: `time-passes` (Twitter.agda:124) with the
//! `session-timeout` Step (Twitter.agda:691-702): every `active` session
//! becomes `revoked` and nothing else is touched. The body is filled in by
//! the implementation task; this skeleton fixes the signature used by
//! `tests/engine_time.rs`.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::DbError;

/// Spec `time-passes` (Twitter.agda:124) with the `session-timeout` Step
/// (Twitter.agda:691-702): every active session becomes revoked, everything
/// else is unchanged.
pub fn time_passes(_db: &Db) -> Result<EngineResult, DbError> {
	todo!("T7 skeleton: implemented later")
}
