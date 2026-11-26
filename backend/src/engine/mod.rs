//! Engine: a spec-faithful operational layer over the database.
//!
//! Every function here corresponds to one `Command` of
//! `spec/Twitter.agda:111-125` and answers with the `Result` for which the
//! spec has a `Step` (Twitter.agda:385-720). Commands that need a session
//! and are given a session that is not `active` answer `Expired`, the
//! `failed-access` case (Twitter.agda:464-468).

pub mod auth;
pub mod posts;
pub mod result;
pub mod social;

pub use crate::db::Db;
pub use result::EngineResult;
