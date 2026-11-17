//! Formal-twitter backend library.
//!
//! The [`model`] module is a faithful, pure mirror of the Agda model in
//! `spec/Twitter.agda` (World state, the Step relation as a deterministic
//! step function and the Result set). It is the reference implementation the
//! Diesel/Rocket server layer must agree with.

pub mod model;
pub mod wire;
