use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PostId(pub i64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SessionId(pub i64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
	Everyone,
	FollowersOnly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PostStatus {
	Live,
	Deleted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SessionStatus {
	Unused,
	Active(String),
	Revoked,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Account {
	pub username: String,
	pub password: String,
	pub default_visibility: Visibility,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Post {
	pub id: PostId,
	pub author: String,
	pub text: String,
	pub visibility: Visibility,
	pub status: PostStatus,
	pub parent: Option<PostId>,
}

/// The user-independent body of a public post, exactly the fields of the
/// spec's `returned-post` (Twitter.agda:133, rendered at 518-555): `likes` is
/// the length of the post's like list and `replies` its `replies`.
///
/// This is what the read cache of [`crate::db::Cache`] stores. Only posts that
/// are `live` and visible to `everyone` (`is-post-public`, Twitter.agda:342-357)
/// are ever inserted, so a cached body answers every reader alike; visibility
/// and status are therefore not part of the cached value -- they can only
/// change through a write, and every successful write drops the whole cache.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicPost {
	pub author: String,
	pub text: String,
	pub likes: u64,
	pub replies: Vec<PostId>,
}

#[derive(Debug)]
pub struct DbError(pub diesel::result::Error);

impl fmt::Display for DbError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "database error: {}", self.0)
	}
}

impl std::error::Error for DbError {}

impl From<diesel::result::Error> for DbError {
	fn from(error: diesel::result::Error) -> Self {
		DbError(error)
	}
}
