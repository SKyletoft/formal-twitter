//! The HTTP surface of `spec/Interface.agda`.
//!
//! `to-request` (Interface.agda:52-200) fixes the requests, `to-response`
//! (Interface.agda:224-309) the replies, and `to-output`
//! (Interface.agda:335-344) maps the engine's `Result` onto a `Response`.

pub mod parse;
pub mod response;
pub mod routes;

pub use response::ApiResponse;
