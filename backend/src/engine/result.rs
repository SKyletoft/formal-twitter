use crate::model::{PostId, SessionId};

/// The `Result` of `spec/Twitter.agda:127-141`, translated to Rust.
///
/// Every `EngineResult` is a one-to-one translation of a `Result`
/// constructor; the engine only answers with a result for which the spec
/// proves a `Step` (see `ImplProofs.agda`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EngineResult {
	/// `success`
	Success,
	/// `denied`
	Denied,
	/// `expired` (the answer to `failed-access`, Twitter.agda:464-468)
	Expired,
	/// `login-failed`
	LoginFailed,
	/// `signup-failed`
	SignupFailed,
	/// `returned-timeline` (Twitter.agda:133)
	ReturnedTimeline(Vec<PostId>),
	/// `issued-session`
	IssuedSession(SessionId),
	/// `created-post`
	CreatedPost(PostId),
	/// `returned-post` (`likes` is the length of the spec's like list)
	ReturnedPost {
		author: String,
		text: String,
		likes: u64,
		replies: Vec<PostId>,
	},
}
