use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Integer, Nullable, Text};
use diesel::{QueryableByName, SqliteConnection};

use crate::model::{
	Account, DbError, Post, PostId, PostStatus, SessionId, SessionStatus, Visibility,
};

fn invalid(message: impl Into<String>) -> DbError {
	DbError(diesel::result::Error::DeserializationError(Box::new(
		std::io::Error::other(message.into()),
	)))
}

fn visibility_str(visibility: Visibility) -> &'static str {
	match visibility {
		Visibility::Everyone => "everyone",
		Visibility::FollowersOnly => "followers-only",
	}
}

fn parse_visibility(value: &str) -> Result<Visibility, DbError> {
	match value {
		"everyone" => Ok(Visibility::Everyone),
		"followers-only" => Ok(Visibility::FollowersOnly),
		other => Err(invalid(format!("invalid visibility: {other}"))),
	}
}

fn parse_post_status(value: &str) -> Result<PostStatus, DbError> {
	match value {
		"live" => Ok(PostStatus::Live),
		"deleted" => Ok(PostStatus::Deleted),
		other => Err(invalid(format!("invalid post status: {other}"))),
	}
}

#[derive(QueryableByName)]
struct AccountRow {
	#[diesel(sql_type = Text)]
	username: String,
	#[diesel(sql_type = Text)]
	password: String,
	#[diesel(sql_type = Text)]
	default_visibility: String,
}

#[derive(QueryableByName)]
struct SessionRow {
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Text)]
	username: String,
}

#[derive(QueryableByName)]
struct ActiveAccountRow {
	#[diesel(sql_type = Text)]
	username: String,
	#[diesel(sql_type = Text)]
	default_visibility: String,
}

#[derive(QueryableByName)]
struct PostRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
	#[diesel(sql_type = Text)]
	author: String,
	#[diesel(sql_type = Text)]
	text: String,
	#[diesel(sql_type = Text)]
	visibility: String,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Nullable<BigInt>)]
	parent: Option<i64>,
}

#[derive(QueryableByName)]
struct IdRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
}

#[derive(QueryableByName)]
struct ExistsRow {
	#[diesel(sql_type = Integer)]
	present: i32,
}

#[derive(QueryableByName)]
struct CountRow {
	#[diesel(sql_type = BigInt)]
	count: i64,
}

#[derive(QueryableByName)]
struct PostViewRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
	#[diesel(sql_type = Text)]
	author: String,
	#[diesel(sql_type = Text)]
	text: String,
	#[diesel(sql_type = Text)]
	visibility: String,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Nullable<BigInt>)]
	parent: Option<i64>,
	#[diesel(sql_type = BigInt)]
	likes: i64,
}

/// A post together with its like count, read in a single query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PostView {
	pub post: Post,
	pub likes: i64,
}

fn load_ids(c: &mut SqliteConnection, query: String) -> Result<Vec<PostId>, DbError> {
	let rows: Vec<IdRow> = diesel::sql_query(query).load(c)?;
	Ok(rows.into_iter().map(|row| PostId(row.id)).collect())
}

fn load_ids_for_user(
	c: &mut SqliteConnection,
	query: String,
	user: &str,
) -> Result<Vec<PostId>, DbError> {
	let rows: Vec<IdRow> = diesel::sql_query(query).bind::<Text, _>(user).load(c)?;
	Ok(rows.into_iter().map(|row| PostId(row.id)).collect())
}

pub fn create_account(
	c: &mut SqliteConnection,
	username: &str,
	password: &str,
) -> Result<bool, DbError> {
	let inserted = diesel::sql_query(
		"INSERT INTO accounts (username, password, default_visibility) \
		VALUES (?, ?, 'everyone') ON CONFLICT(username) DO NOTHING",
	)
	.bind::<Text, _>(username)
	.bind::<Text, _>(password)
	.execute(c)?;
	Ok(inserted > 0)
}

pub fn get_account(c: &mut SqliteConnection, username: &str) -> Result<Option<Account>, DbError> {
	let rows: Vec<AccountRow> = diesel::sql_query(
		"SELECT username, password, default_visibility FROM accounts WHERE username = ?",
	)
	.bind::<Text, _>(username)
	.load(c)?;
	match rows.into_iter().next() {
		None => Ok(None),
		Some(row) => Ok(Some(Account {
			username: row.username,
			password: row.password,
			default_visibility: parse_visibility(&row.default_visibility)?,
		})),
	}
}

pub fn activate_session(
	c: &mut SqliteConnection,
	sid: SessionId,
	username: &str,
) -> Result<(), DbError> {
	diesel::sql_query("INSERT INTO sessions (id, status, username) VALUES (?, 'active', ?)")
		.bind::<BigInt, _>(sid.0)
		.bind::<Text, _>(username)
		.execute(c)?;
	Ok(())
}

pub fn get_session(c: &mut SqliteConnection, sid: SessionId) -> Result<SessionStatus, DbError> {
	let rows: Vec<SessionRow> =
		diesel::sql_query("SELECT status, username FROM sessions WHERE id = ?")
			.bind::<BigInt, _>(sid.0)
			.load(c)?;
	match rows.into_iter().next() {
		None => Ok(SessionStatus::Unused),
		Some(row) => match row.status.as_str() {
			"active" => Ok(SessionStatus::Active(row.username)),
			"revoked" => Ok(SessionStatus::Revoked),
			other => Err(invalid(format!("invalid session status: {other}"))),
		},
	}
}

/// The account behind `sid` iff the session is `active` and its account exists,
/// read in one query: the username and the account's `default-visibility`.
///
/// `only-valid-sessions` (Twitter.agda) makes the account existence an
/// invariant; the join keeps the helper total regardless.
pub fn active_account(
	c: &mut SqliteConnection,
	sid: SessionId,
) -> Result<Option<(String, Visibility)>, DbError> {
	let rows: Vec<ActiveAccountRow> = diesel::sql_query(
		"SELECT accounts.username AS username, \
		accounts.default_visibility AS default_visibility FROM sessions \
		JOIN accounts ON accounts.username = sessions.username \
		WHERE sessions.id = ? AND sessions.status = 'active'",
	)
	.bind::<BigInt, _>(sid.0)
	.load(c)?;
	match rows.into_iter().next() {
		None => Ok(None),
		Some(row) => Ok(Some((
			row.username,
			parse_visibility(&row.default_visibility)?,
		))),
	}
}

/// The user behind `sid` iff the session is `active` and its account exists.
pub fn active_user(c: &mut SqliteConnection, sid: SessionId) -> Result<Option<String>, DbError> {
	Ok(active_account(c, sid)?.map(|(username, _)| username))
}

pub fn revoke_session(c: &mut SqliteConnection, sid: SessionId) -> Result<(), DbError> {
	let updated = diesel::sql_query("UPDATE sessions SET status = 'revoked' WHERE id = ?")
		.bind::<BigInt, _>(sid.0)
		.execute(c)?;
	if updated == 0 {
		Err(DbError(diesel::result::Error::NotFound))
	} else {
		Ok(())
	}
}

pub fn revoke_all_sessions(c: &mut SqliteConnection) -> Result<(), DbError> {
	diesel::sql_query("UPDATE sessions SET status = 'revoked' WHERE status = 'active'")
		.execute(c)?;
	Ok(())
}

pub fn insert_post(
	c: &mut SqliteConnection,
	id: PostId,
	author: &str,
	text: &str,
	vis: Visibility,
) -> Result<(), DbError> {
	diesel::sql_query(
		"INSERT INTO posts (id, seq, author, text, visibility, status, parent) \
		VALUES (?, COALESCE((SELECT MAX(seq) FROM posts), 0) + 1, ?, ?, ?, 'live', NULL)",
	)
	.bind::<BigInt, _>(id.0)
	.bind::<Text, _>(author)
	.bind::<Text, _>(text)
	.bind::<Text, _>(visibility_str(vis))
	.execute(c)?;
	Ok(())
}

pub fn insert_reply(
	c: &mut SqliteConnection,
	id: PostId,
	author: &str,
	text: &str,
	vis: Visibility,
	parent: PostId,
) -> Result<(), DbError> {
	diesel::sql_query(
		"INSERT INTO posts (id, seq, author, text, visibility, status, parent) \
		VALUES (?, COALESCE((SELECT MAX(seq) FROM posts), 0) + 1, ?, ?, ?, 'live', ?)",
	)
	.bind::<BigInt, _>(id.0)
	.bind::<Text, _>(author)
	.bind::<Text, _>(text)
	.bind::<Text, _>(visibility_str(vis))
	.bind::<BigInt, _>(parent.0)
	.execute(c)?;
	Ok(())
}

pub fn get_post(c: &mut SqliteConnection, id: PostId) -> Result<Option<Post>, DbError> {
	let rows: Vec<PostRow> = diesel::sql_query(
		"SELECT id, author, text, visibility, status, parent FROM posts WHERE id = ?",
	)
	.bind::<BigInt, _>(id.0)
	.load(c)?;
	match rows.into_iter().next() {
		None => Ok(None),
		Some(row) => Ok(Some(Post {
			id: PostId(row.id),
			author: row.author,
			text: row.text,
			visibility: parse_visibility(&row.visibility)?,
			status: parse_post_status(&row.status)?,
			parent: row.parent.map(PostId),
		})),
	}
}

pub fn soft_delete_post(c: &mut SqliteConnection, id: PostId) -> Result<(), DbError> {
	let updated = diesel::sql_query("UPDATE posts SET status = 'deleted' WHERE id = ?")
		.bind::<BigInt, _>(id.0)
		.execute(c)?;
	if updated == 0 {
		Err(DbError(diesel::result::Error::NotFound))
	} else {
		Ok(())
	}
}

/// Spec `CanReadPost` (Twitter.agda:158-179): the post is `live` and either
/// `everyone`, or `followers-only` and `user` follows its author.
pub fn can_read_post(c: &mut SqliteConnection, user: &str, id: PostId) -> Result<bool, DbError> {
	let row: ExistsRow = diesel::sql_query(
		"SELECT EXISTS(SELECT 1 FROM posts p WHERE p.id = ? AND p.status = 'live' \
		AND (p.visibility = 'everyone' OR EXISTS(SELECT 1 FROM follows f \
		WHERE f.follower = ? AND f.followee = p.author))) AS present",
	)
	.bind::<BigInt, _>(id.0)
	.bind::<Text, _>(user)
	.get_result(c)?;
	Ok(row.present != 0)
}

/// Spec `is-post-public` (Twitter.agda:342-357): the post exists, is `live`
/// and is visible to `everyone`.
pub fn can_read_anonymous(c: &mut SqliteConnection, id: PostId) -> Result<bool, DbError> {
	let row: ExistsRow = diesel::sql_query(
		"SELECT EXISTS(SELECT 1 FROM posts p WHERE p.id = ? AND p.status = 'live' \
		AND p.visibility = 'everyone') AS present",
	)
	.bind::<BigInt, _>(id.0)
	.get_result(c)?;
	Ok(row.present != 0)
}

/// The post `id` (absent if there is none) together with its like count, in
/// one query.
pub fn post_view(c: &mut SqliteConnection, id: PostId) -> Result<Option<PostView>, DbError> {
	let rows: Vec<PostViewRow> = diesel::sql_query(
		"SELECT p.id AS id, p.author AS author, p.text AS text, \
		p.visibility AS visibility, p.status AS status, p.parent AS parent, \
		COUNT(l.pid) AS likes \
		FROM posts p LEFT JOIN post_likes l ON l.pid = p.id \
		WHERE p.id = ? \
		GROUP BY p.id, p.author, p.text, p.visibility, p.status, p.parent",
	)
	.bind::<BigInt, _>(id.0)
	.load(c)?;
	match rows.into_iter().next() {
		None => Ok(None),
		Some(row) => Ok(Some(PostView {
			post: Post {
				id: PostId(row.id),
				author: row.author,
				text: row.text,
				visibility: parse_visibility(&row.visibility)?,
				status: parse_post_status(&row.status)?,
				parent: row.parent.map(PostId),
			},
			likes: row.likes,
		})),
	}
}

/// Soft-delete `id` iff `author` owns it, returning the pre-image.
///
/// `None` covers both "absent" and "not the author": the spec's
/// `failed-delete-non-existant-post` / `failed-delete-not-author`
/// (Twitter.agda:451-462) answer the same `denied`. Call inside a write
/// transaction.
pub fn delete_own(
	c: &mut SqliteConnection,
	id: PostId,
	author: &str,
) -> Result<Option<Post>, DbError> {
	match get_post(c, id)? {
		Some(post) if post.author == author => {
			soft_delete_post(c, id)?;
			Ok(Some(post))
		}
		_ => Ok(None),
	}
}

pub fn replies_of(c: &mut SqliteConnection, id: PostId) -> Result<Vec<PostId>, DbError> {
	let rows: Vec<IdRow> =
		diesel::sql_query("SELECT id FROM posts WHERE parent = ? ORDER BY seq DESC")
			.bind::<BigInt, _>(id.0)
			.load(c)?;
	Ok(rows.into_iter().map(|row| PostId(row.id)).collect())
}

pub fn add_follow(c: &mut SqliteConnection, follower: &str, followee: &str) -> Result<(), DbError> {
	diesel::sql_query("INSERT OR IGNORE INTO follows (follower, followee) VALUES (?, ?)")
		.bind::<Text, _>(follower)
		.bind::<Text, _>(followee)
		.execute(c)?;
	Ok(())
}

pub fn remove_follow(
	c: &mut SqliteConnection,
	follower: &str,
	followee: &str,
) -> Result<(), DbError> {
	diesel::sql_query("DELETE FROM follows WHERE follower = ? AND followee = ?")
		.bind::<Text, _>(follower)
		.bind::<Text, _>(followee)
		.execute(c)?;
	Ok(())
}

pub fn is_following(
	c: &mut SqliteConnection,
	follower: &str,
	followee: &str,
) -> Result<bool, DbError> {
	let row: ExistsRow = diesel::sql_query(
		"SELECT EXISTS(SELECT 1 FROM follows WHERE follower = ? AND followee = ?) AS present",
	)
	.bind::<Text, _>(follower)
	.bind::<Text, _>(followee)
	.get_result(c)?;
	Ok(row.present != 0)
}

pub fn add_like(c: &mut SqliteConnection, id: PostId, user: &str) -> Result<(), DbError> {
	diesel::sql_query("INSERT OR IGNORE INTO post_likes (pid, user) VALUES (?, ?)")
		.bind::<BigInt, _>(id.0)
		.bind::<Text, _>(user)
		.execute(c)?;
	Ok(())
}

pub fn remove_like(c: &mut SqliteConnection, id: PostId, user: &str) -> Result<(), DbError> {
	diesel::sql_query("DELETE FROM post_likes WHERE pid = ? AND user = ?")
		.bind::<BigInt, _>(id.0)
		.bind::<Text, _>(user)
		.execute(c)?;
	Ok(())
}

pub fn is_liked(c: &mut SqliteConnection, id: PostId, user: &str) -> Result<bool, DbError> {
	let row: ExistsRow = diesel::sql_query(
		"SELECT EXISTS(SELECT 1 FROM post_likes WHERE pid = ? AND user = ?) AS present",
	)
	.bind::<BigInt, _>(id.0)
	.bind::<Text, _>(user)
	.get_result(c)?;
	Ok(row.present != 0)
}

pub fn like_count(c: &mut SqliteConnection, id: PostId) -> Result<i64, DbError> {
	let row: CountRow = diesel::sql_query("SELECT COUNT(*) AS count FROM post_likes WHERE pid = ?")
		.bind::<BigInt, _>(id.0)
		.get_result(c)?;
	Ok(row.count)
}

pub fn newest_first(c: &mut SqliteConnection, n: u32) -> Result<Vec<PostId>, DbError> {
	load_ids(
		c,
		format!(
			"SELECT id FROM posts ORDER BY seq DESC LIMIT {}",
			i64::from(n)
		),
	)
}

pub fn public_timeline(c: &mut SqliteConnection, n: u32) -> Result<Vec<PostId>, DbError> {
	load_ids(
		c,
		format!(
			"SELECT id FROM posts WHERE status = 'live' AND visibility = 'everyone' \
			ORDER BY seq DESC LIMIT {}",
			i64::from(n)
		),
	)
}

pub fn global_timeline_for(
	c: &mut SqliteConnection,
	user: &str,
	n: u32,
) -> Result<Vec<PostId>, DbError> {
	load_ids_for_user(
		c,
		format!(
			"SELECT id FROM posts WHERE status = 'live' AND (visibility = 'everyone' \
			OR EXISTS(SELECT 1 FROM follows WHERE follows.follower = ? \
			AND follows.followee = posts.author)) ORDER BY seq DESC LIMIT {}",
			i64::from(n)
		),
		user,
	)
}

pub fn personal_timeline_for(
	c: &mut SqliteConnection,
	user: &str,
	n: u32,
) -> Result<Vec<PostId>, DbError> {
	load_ids_for_user(
		c,
		format!(
			"SELECT id FROM posts WHERE status = 'live' AND EXISTS(SELECT 1 FROM follows \
			WHERE follows.follower = ? AND follows.followee = posts.author) \
			ORDER BY seq DESC LIMIT {}",
			i64::from(n)
		),
		user,
	)
}
