//! HTTP surface: Rocket routes for `spec/Interface.agda`'s `Action`s.
//!
//! Every route is a `POST` whose body is `unlines-crlf` of the action's
//! arguments (`to-request`, Interface.agda:52-200), answered with
//! `to-response` of `to-output` of the engine's `Result`
//! (Interface.agda:224-344).

use rocket::{Build, Rocket};

use crate::db::Db;

pub fn build(_db: Db) -> Rocket<Build> {
	todo!("T4 skeleton")
}
