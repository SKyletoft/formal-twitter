//! Authentication commands: `register`, `authenticate` and `revoke-token`.
//!
//! Spec counterparts: `register` is `create-account` /
//! `failed-create-account` (Twitter.agda:470-488); `authenticate` is `login` /
//! `failed-login-1` / `failed-login-2` (Twitter.agda:490-516); `revoke-token`
//! is `logout` (Twitter.agda:677-689) and, when the session is not active,
//! `failed-access` (Twitter.agda:464-468).
//!
//! The bodies are filled in by the implementation task; this skeleton fixes
//! the signatures used by `tests/engine_auth.rs`.

use crate::db::Db;
use crate::engine::result::EngineResult;
use crate::model::{DbError, SessionId, SessionStatus};
use crate::store;

/// Spec `register username passwd` (Twitter.agda:470-488).
///
/// Creates the account with the given password and
/// `default-visibility = everyone`. Answers `Success` when the username was
/// free, and `SignupFailed` (leaving the world unchanged) when it was taken.
pub fn register(db: &Db, username: &str, password: &str) -> Result<EngineResult, DbError> {
	db.write(|c| {
		if store::create_account(c, username, password)? {
			Ok(EngineResult::Success)
		} else {
			Ok(EngineResult::SignupFailed)
		}
	})
}

/// Spec `authenticate username passwd` (Twitter.agda:490-516).
///
/// Answers `IssuedSession sid` with a fresh, active session on a username /
/// password match, and `LoginFailed` (leaving the world unchanged)
/// otherwise.
pub fn authenticate(db: &Db, username: &str, password: &str) -> Result<EngineResult, DbError> {
	db.write(|c| match store::get_account(c, username)? {
		None => Ok(EngineResult::LoginFailed),
		Some(account) if account.password != password => Ok(EngineResult::LoginFailed),
		Some(_) => {
			let sid = crate::ids::allocate_session_id(c)?;
			store::activate_session(c, sid, username)?;
			Ok(EngineResult::IssuedSession(sid))
		}
	})
}

/// Spec `revoke-token sid` (Twitter.agda:677-689).
///
/// Answers `Success` when the session is active and turns it `revoked`.
/// Answers `Expired` without touching the world when the session is already
/// revoked or was never issued (Twitter.agda:464-468).
pub fn revoke_token(db: &Db, session_id: SessionId) -> Result<EngineResult, DbError> {
	db.write(|c| match store::get_session(c, session_id)? {
		SessionStatus::Active(_) => {
			store::revoke_session(c, session_id)?;
			Ok(EngineResult::Success)
		}
		SessionStatus::Unused | SessionStatus::Revoked => Ok(EngineResult::Expired),
	})
}
