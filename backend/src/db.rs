//! Diesel/SQLite persistence for the formal-twitter backend (task T3; no Rocket here).
//!
//! Six SQL tables mirror the DB schema note in todo.md. Encodings mirror
//! spec/Twitter.agda; the stdlib-only encoding-pin module was removed per A4
//! (recovery commit b6b868b keeps it).

#![allow(clippy::cast_lossless, clippy::cast_possible_truncation)]

use crate::model::{Account, Post, PostStatus, SessionStatus, Visibility, World};

use std::collections::HashMap;
use std::collections::HashSet;

use diesel::connection::SimpleConnection;
use diesel::delete;
use diesel::insert_into;
use diesel::prelude::*;
use diesel::update;

table!(accounts (username) {
	username -> Text,
	password -> Text,
	visibility -> Integer,
});

table!(sessions (sid) {
	sid -> BigInt,
	status -> Integer,
	 user -> Nullable<Text>,
});

table!(posts (pid) {
	 pid -> BigInt,
	author -> Text,
	 text -> Text,
	visibility -> Integer,
	 status -> Integer,
	 parent -> Nullable<BigInt>,
	 seq -> BigInt,
});

table!(likes (post_pid, user) {
	 post_pid -> BigInt,
	 user -> Text,
});

table!(replies (post_pid, reply_pid) {
	 post_pid -> BigInt,
	 reply_pid -> BigInt,
});

table!(follows (follower, followee) {
	 follower -> Text,
	 followee -> Text,
});

// ---- Encodings ----

/// enc-vis: Everyone = 0, FollowersOnly = 1.
pub fn enc_vis(vis: Visibility) -> i32 {
	match vis {
		Visibility::Everyone => 0,
		Visibility::FollowersOnly => 1,
	}
}

/// dec-vis: 1 = FollowersOnly, anything else = Everyone (corruption-tolerant).
pub fn dec_vis(code: i32) -> Visibility {
	if code == 1 {
		Visibility::FollowersOnly
	} else {
		Visibility::Everyone
	}
}

/// enc-status: live (PostStatus::Other) = 0, Deleted = 1.
pub fn enc_status(status: PostStatus) -> i32 {
	match status {
		PostStatus::Other => 0,
		PostStatus::Deleted => 1,
	}
}

/// dec-status: 1 = Deleted, anything else = live.
pub fn dec_status(code: i32) -> PostStatus {
	if code == 1 {
		PostStatus::Deleted
	} else {
		PostStatus::Other
	}
}

/// Session row encoding: (1, user) = Active, (2, NULL) = Revoked, (0, NULL) = Unused.
pub fn enc_sess_row(st: SessionStatus) -> (i32, Option<String>) {
	match st {
		SessionStatus::Active(username) => (1, Some(username)),
		SessionStatus::Revoked => (2, None),
		SessionStatus::Unused => (0, None),
	}
}

#[doc = "Borrowed sibling of enc_sess_row (task TB): the status arrives by reference, so apply()'s"]
#[doc = "borrowed views never copy it; only the Active username is copied, where this runs."]
pub fn enc_sess_row_ref(st: &SessionStatus) -> (i32, Option<String>) {
	match st {
		SessionStatus::Active(username) => (1, Some(username.clone())),
		SessionStatus::Revoked => (2, None),
		SessionStatus::Unused => (0, None),
	}
}

/// Session row decoding: (1, just u) -> Active u, (2, nothing) -> Revoked,
/// (0, nothing) -> Unused; malformed rows decode to Unused.
pub fn dec_sess_row(code: i32, user: Option<String>) -> SessionStatus {
	match (code, user) {
		(1, Some(username)) => SessionStatus::Active(username),
		(2, None) => SessionStatus::Revoked,
		(0, None) => SessionStatus::Unused,
		_ => SessionStatus::Unused,
	}
}

// ---- Reentrant DB initialisation ----

const CREATE_SQL: &str = r"CREATE TABLE accounts (username TEXT PRIMARY KEY, password TEXT, visibility INTEGER);
CREATE TABLE sessions (sid INTEGER PRIMARY KEY, status INTEGER, user TEXT);
CREATE TABLE posts (pid INTEGER PRIMARY KEY, author TEXT, text TEXT, visibility INTEGER, status INTEGER, parent BIGINT, seq BIGINT);
CREATE TABLE likes (post_pid INTEGER, user TEXT);
CREATE TABLE replies (post_pid INTEGER, reply_pid INTEGER);
CREATE TABLE follows (follower TEXT, followee TEXT);";

/// Open (or create) the SQLite database at path. The CREATEs are attempted on
/// every startup: on an existing DB they all fail atomically (batch_execute is
/// one transaction), and we ignore that error, which makes startup reentrant.
pub fn init_or_open(path: String) -> ConnectionResult<SqliteConnection> {
	let mut conn = SqliteConnection::establish(&path)?;
	let _created = conn.batch_execute(CREATE_SQL);
	Ok(conn)
}

/// Open an existing SQLite DB without touching the CREATEs: the pure open used
/// by reload paths, so write-through can be observed from a fresh connection.
pub fn reopen(path: String) -> ConnectionResult<SqliteConnection> {
	SqliteConnection::establish(&path)
}

// ---- Loading World from the DB ----

/// Load every table with static typed queries. A query error (corrupt or
/// missing table) is treated as no rows: an empty World component, never a
/// panic; save_world rewrites everything regardless. Canonical row order
/// keeps World equality stable (lexicographic per table; newest_first from
/// ORDER BY seq DESC; likes/replies keep row order within a post).
pub fn load_world(conn: &mut SqliteConnection) -> World {
	let mut account_rows = accounts::dsl::accounts
		.select((
			accounts::dsl::username,
			accounts::dsl::password,
			accounts::dsl::visibility,
		))
		.load::<(String, String, i32)>(conn)
		.unwrap_or_default();
	let mut session_rows = sessions::dsl::sessions
		.select((
			sessions::dsl::sid,
			sessions::dsl::status,
			sessions::dsl::user,
		))
		.load::<(i64, i32, Option<String>)>(conn)
		.unwrap_or_default();
	let mut post_rows = posts::dsl::posts
		.select((
			posts::dsl::pid,
			posts::dsl::author,
			posts::dsl::text,
			posts::dsl::visibility,
			posts::dsl::status,
			posts::dsl::parent,
			posts::dsl::seq,
		))
		.load::<(i64, String, String, i32, i32, Option<i64>, i64)>(conn)
		.unwrap_or_default();
	let mut like_rows = likes::dsl::likes
		.select((likes::dsl::post_pid, likes::dsl::user))
		.load::<(i64, String)>(conn)
		.unwrap_or_default();
	let mut reply_rows = replies::dsl::replies
		.select((replies::dsl::post_pid, replies::dsl::reply_pid))
		.load::<(i64, i64)>(conn)
		.unwrap_or_default();
	let mut follow_rows = follows::dsl::follows
		.select((follows::dsl::follower, follows::dsl::followee))
		.load::<(String, String)>(conn)
		.unwrap_or_default();
	account_rows.sort();
	session_rows.sort();
	post_rows.sort();
	like_rows.sort();
	reply_rows.sort();
	follow_rows.sort();
	let newest_first: Vec<u64> = posts::dsl::posts
		.select(posts::dsl::pid)
		.order(posts::dsl::seq.desc())
		.load::<i64>(conn)
		.unwrap_or_default()
		.into_iter()
		.map(|id| id as u64)
		.collect();
	let posts_map: Vec<(u64, Post)> = post_rows
		.into_iter()
		.map(|(pid, author, text, vis, code, parent, _seq)| {
			(
				pid as u64,
				Post {
					author,
					text,
					visibility: dec_vis(vis),
					status: dec_status(code),
					likes: like_rows
						.iter()
						.filter(|row| row.0 == pid)
						.map(|row| row.1.clone())
						.collect(),
					replies: reply_rows
						.iter()
						.filter(|row| row.0 == pid)
						.map(|row| row.1 as u64)
						.collect(),
					parent: parent.map(|p| p as u64),
				},
			)
		})
		.collect();
	let used_post_ids: Vec<u64> = posts_map.iter().map(|row| row.0).collect();
	let used_session_ids: Vec<u64> = session_rows.iter().map(|row| row.0 as u64).collect();
	World {
		accounts: account_rows
			.into_iter()
			.map(|(username, password, vis)| {
				(
					username,
					Account {
						password,
						default_visibility: dec_vis(vis),
					},
				)
			})
			.collect(),
		sessions: session_rows
			.into_iter()
			.map(|(sid, code, user)| (sid as u64, dec_sess_row(code, user)))
			.collect(),
		posts: posts_map,
		follows: follow_rows,
		newest_first,
		used_post_ids,
		used_session_ids,
	}
}

// ---- Per-section reload (task DB3b: partial cache rotation) ----

/// reload-accounts (task DB3b): throw ONLY the accounts section of the RAM cache out
/// and re-query it from the DB, leaving every other World field at its cached
/// value.  Uses load_world's select + sort + decode pipeline verbatim, so the
/// reloaded section always agrees with load_world.  Lets main.rs rotate one
/// World field group per request instead of re-loading the whole World.
pub fn reload_accounts(conn: &mut SqliteConnection, w: World) -> World {
	let mut out = w;
	let mut account_rows = accounts::dsl::accounts
		.select((
			accounts::dsl::username,
			accounts::dsl::password,
			accounts::dsl::visibility,
		))
		.load::<(String, String, i32)>(conn)
		.unwrap_or_default();
	account_rows.sort();
	out.accounts = account_rows
		.into_iter()
		.map(|(username, password, vis)| {
			(
				username,
				Account {
					password,
					default_visibility: dec_vis(vis),
				},
			)
		})
		.collect();
	out
}

/// reload-sessions (task DB3b): ONE section covering sessions AND used_session_ids,
/// both derived from the sessions table, replaced together so they stay consistent.
/// Same select + sort + decode as load_world's sessions query; all other fields
/// keep their cached values.
pub fn reload_sessions(conn: &mut SqliteConnection, w: World) -> World {
	let mut out = w;
	let mut session_rows = sessions::dsl::sessions
		.select((
			sessions::dsl::sid,
			sessions::dsl::status,
			sessions::dsl::user,
		))
		.load::<(i64, i32, Option<String>)>(conn)
		.unwrap_or_default();
	session_rows.sort();
	out.used_session_ids = session_rows.iter().map(|row| row.0 as u64).collect();
	out.sessions = session_rows
		.into_iter()
		.map(|(sid, code, user)| (sid as u64, dec_sess_row(code, user)))
		.collect();
	out
}

/// reload-follows (task DB3b): ONE section for the follows table only; the cached
/// rows are dropped and re-queried with load_world's select + sort.
/// Everything else keeps its cached value.
pub fn reload_follows(conn: &mut SqliteConnection, w: World) -> World {
	let mut out = w;
	let mut follow_rows = follows::dsl::follows
		.select((follows::dsl::follower, follows::dsl::followee))
		.load::<(String, String)>(conn)
		.unwrap_or_default();
	follow_rows.sort();
	out.follows = follow_rows;
	out
}

/// reload-posts (task DB3b): ONE section for posts, newest_first and used_post_ids,
/// which all derive from the posts tables, so they must move together.  Re-queries
/// posts (plus the likes/replies rows load_world's Post decode reads) and rebuilds
/// newest_first with load_world's ORDER BY seq DESC query; accounts, sessions and
/// follows keep their cached values.
pub fn reload_posts(conn: &mut SqliteConnection, w: World) -> World {
	let mut out = w;
	let mut post_rows = posts::dsl::posts
		.select((
			posts::dsl::pid,
			posts::dsl::author,
			posts::dsl::text,
			posts::dsl::visibility,
			posts::dsl::status,
			posts::dsl::parent,
			posts::dsl::seq,
		))
		.load::<(i64, String, String, i32, i32, Option<i64>, i64)>(conn)
		.unwrap_or_default();
	let mut like_rows = likes::dsl::likes
		.select((likes::dsl::post_pid, likes::dsl::user))
		.load::<(i64, String)>(conn)
		.unwrap_or_default();
	let mut reply_rows = replies::dsl::replies
		.select((replies::dsl::post_pid, replies::dsl::reply_pid))
		.load::<(i64, i64)>(conn)
		.unwrap_or_default();
	let newest_first: Vec<u64> = posts::dsl::posts
		.select(posts::dsl::pid)
		.order(posts::dsl::seq.desc())
		.load::<i64>(conn)
		.unwrap_or_default()
		.into_iter()
		.map(|id| id as u64)
		.collect();
	post_rows.sort();
	like_rows.sort();
	reply_rows.sort();
	let posts_map: Vec<(u64, Post)> = post_rows
		.into_iter()
		.map(|(pid, author, text, vis, code, parent, _seq)| {
			(
				pid as u64,
				Post {
					author,
					text,
					visibility: dec_vis(vis),
					status: dec_status(code),
					likes: like_rows
						.iter()
						.filter(|row| row.0 == pid)
						.map(|row| row.1.clone())
						.collect(),
					replies: reply_rows
						.iter()
						.filter(|row| row.0 == pid)
						.map(|row| row.1 as u64)
						.collect(),
					parent: parent.map(|p| p as u64),
				},
			)
		})
		.collect();
	out.used_post_ids = posts_map.iter().map(|row| row.0).collect();
	out.posts = posts_map;
	out.newest_first = newest_first;
	out
}

// ---- Saving World (full rewrite) ----

/// Full rewrite of the DB: wipe the six tables, then insert every row of w.
/// seq is re-stamped 1..n over newest_first REVERSED (oldest to newest), so
/// a later ORDER BY seq DESC reproduces w.newest_first exactly.
pub fn save_world(conn: &mut SqliteConnection, w: World) {
	let _wiped_accounts = delete(accounts::dsl::accounts).execute(conn);
	let _wiped_sessions = delete(sessions::dsl::sessions).execute(conn);
	let _wiped_posts = delete(posts::dsl::posts).execute(conn);
	let _wiped_likes = delete(likes::dsl::likes).execute(conn);
	let _wiped_replies = delete(replies::dsl::replies).execute(conn);
	let _wiped_follows = delete(follows::dsl::follows).execute(conn);
	let mut seq_of: HashMap<u64, i64> = HashMap::new();
	for (index, pid) in w.newest_first.into_iter().rev().enumerate() {
		seq_of.insert(pid, (index as i64) + 1);
	}
	let account_rows: Vec<_> = w
		.accounts
		.into_iter()
		.map(|(username, account)| {
			(
				accounts::dsl::username.eq(username),
				accounts::dsl::password.eq(account.password),
				accounts::dsl::visibility.eq(enc_vis(account.default_visibility)),
			)
		})
		.collect();
	let session_rows: Vec<_> = w
		.sessions
		.into_iter()
		.map(|(sid, st)| {
			let (code, user) = enc_sess_row(st);
			(
				sessions::dsl::sid.eq(sid as i64),
				sessions::dsl::status.eq(code),
				sessions::dsl::user.eq(user),
			)
		})
		.collect();
	let mut post_rows = vec![];
	let mut like_rows = vec![];
	let mut reply_rows = vec![];
	for (pid, post) in w.posts.into_iter() {
		post_rows.push((
			posts::dsl::pid.eq(pid as i64),
			posts::dsl::author.eq(post.author),
			posts::dsl::text.eq(post.text),
			posts::dsl::visibility.eq(enc_vis(post.visibility)),
			posts::dsl::status.eq(enc_status(post.status)),
			posts::dsl::parent.eq(post.parent.map(|p| p as i64)),
			posts::dsl::seq.eq(*seq_of.get(&pid).unwrap_or(&0)),
		));
		for user in post.likes.into_iter() {
			like_rows.push((
				likes::dsl::post_pid.eq(pid as i64),
				likes::dsl::user.eq(user),
			));
		}
		for reply_pid in post.replies.into_iter() {
			reply_rows.push((
				replies::dsl::post_pid.eq(pid as i64),
				replies::dsl::reply_pid.eq(reply_pid as i64),
			));
		}
	}
	if !account_rows.is_empty() {
		let _ = insert_into(accounts::dsl::accounts)
			.values(&account_rows)
			.execute(conn);
	}
	if !session_rows.is_empty() {
		let _ = insert_into(sessions::dsl::sessions)
			.values(&session_rows)
			.execute(conn);
	}
	if !post_rows.is_empty() {
		let _ = insert_into(posts::dsl::posts)
			.values(&post_rows)
			.execute(conn);
	}
	if !like_rows.is_empty() {
		let _ = insert_into(likes::dsl::likes)
			.values(&like_rows)
			.execute(conn);
	}
	if !reply_rows.is_empty() {
		let _ = insert_into(replies::dsl::replies)
			.values(&reply_rows)
			.execute(conn);
	}
	let follow_rows: Vec<_> = w
		.follows
		.into_iter()
		.map(|(follower, followee)| {
			(
				follows::dsl::follower.eq(follower),
				follows::dsl::followee.eq(followee),
			)
		})
		.collect();
	if !follow_rows.is_empty() {
		let _ = insert_into(follows::dsl::follows)
			.values(&follow_rows)
			.execute(conn);
	}
	// used_post_ids / used_session_ids are not stored: load_world derives them
	// from the keys actually present, which keeps the DB the reentrant source of truth.
}

// ---- Write-through diff (task T4) ----

#[doc = "Bounded write-through: the DB must already mirror `before`; we mutate only"]
#[doc = "the delta to `after`. Accounts only ever get INSERTs (password/visibility of"]
#[doc = "an existing account never changes). Sessions UPDATE on status/user change,"]
#[doc = "INSERT when new, DELETE when dropped (defensive). Posts: a new pid is INSERTed"]
#[doc = "with seq = (max existing seq in the DB) + 1, growing by one per insertion, so"]
#[doc = "ORDER BY seq DESC keeps newest_first (new posts prepend); existing seqs stay put."]
#[doc = "Status flips (live<->deleted) UPDATE the row; likes/replies are pair INSERT/DELETE;"]
#[doc = "follows likewise. Nothing existing is rewritten, so this is O(delta)."]
#[doc = "The whole batch is one sqlite transaction (raw BEGIN/COMMIT or ROLLBACK pragmas);"]
#[doc = "the Bool reports whether the batch committed, i.e. false means the DB is unchanged."]
pub fn apply(conn: &mut SqliteConnection, before: &World, after: &World) -> bool {
	// Transactional write-through: BEGIN first; every statement's recoverable QueryResult
	// is ANDed into ok, and the batch COMMITs only if all of them (plus BEGIN) succeeded.
	let mut ok = conn.batch_execute("BEGIN TRANSACTION;").is_ok();
	let prev_users: HashSet<&String> = before
		.accounts
		.iter()
		.map(|(username, _)| username)
		.collect();
	let next_users: HashSet<&String> = after
		.accounts
		.iter()
		.map(|(username, _)| username)
		.collect();
	for (username, account) in after.accounts.iter() {
		if !prev_users.contains(&username) {
			ok &= insert_into(accounts::dsl::accounts)
				.values((
					accounts::dsl::username.eq(username),
					accounts::dsl::password.eq(account.password.clone()),
					accounts::dsl::visibility.eq(enc_vis(account.default_visibility.clone())),
				))
				.execute(conn)
				.is_ok();
		}
	}
	for (username, _) in before.accounts.iter() {
		if !next_users.contains(&username) {
			ok &= delete(accounts::dsl::accounts)
				.filter(accounts::dsl::username.eq(username))
				.execute(conn)
				.is_ok();
		}
	}
	let prev_sessions: HashMap<u64, &SessionStatus> = before
		.sessions
		.iter()
		.map(|(sid, status)| (*sid, status))
		.collect();
	let next_sids: HashSet<u64> = after.sessions.iter().map(|(sid, _)| *sid).collect();
	for (sid, status) in after.sessions.iter() {
		match prev_sessions.get(sid) {
			None => {
				let (code, user) = enc_sess_row_ref(status);
				ok &= insert_into(sessions::dsl::sessions)
					.values((
						sessions::dsl::sid.eq(*sid as i64),
						sessions::dsl::status.eq(code),
						sessions::dsl::user.eq(user),
					))
					.execute(conn)
					.is_ok();
			}
			Some(old) => {
				if **old != *status {
					let (code, user) = enc_sess_row_ref(status);
					ok &= update(sessions::dsl::sessions)
						.filter(sessions::dsl::sid.eq(*sid as i64))
						.set((sessions::dsl::status.eq(code), sessions::dsl::user.eq(user)))
						.execute(conn)
						.is_ok();
				}
			}
		}
	}
	for (sid, _) in before.sessions.iter() {
		if !next_sids.contains(sid) {
			ok &= delete(sessions::dsl::sessions)
				.filter(sessions::dsl::sid.eq(*sid as i64))
				.execute(conn)
				.is_ok();
		}
	}
	// max existing seq via plain load (bounded): avoids the Aggregates type soup.
	let seqs: Vec<i64> = posts::dsl::posts
		.select(posts::dsl::seq)
		.load::<i64>(conn)
		.unwrap_or_default();
	let mut next_seq: i64 = 1;
	for s in seqs.into_iter() {
		if s >= next_seq {
			next_seq = s + 1;
		}
	}
	let prev_posts: HashMap<u64, &Post> = before
		.posts
		.iter()
		.map(|(pid, post)| (*pid, post))
		.collect();
	let next_pids: HashSet<u64> = after.posts.iter().map(|(pid, _)| *pid).collect();
	for (pid, post) in after.posts.iter() {
		match prev_posts.get(pid) {
			None => {
				ok &= insert_into(posts::dsl::posts)
					.values((
						posts::dsl::pid.eq(*pid as i64),
						posts::dsl::author.eq(post.author.clone()),
						posts::dsl::text.eq(post.text.clone()),
						posts::dsl::visibility.eq(enc_vis(post.visibility.clone())),
						posts::dsl::status.eq(enc_status(post.status.clone())),
						posts::dsl::parent.eq(post.parent.map(|p| p as i64)),
						posts::dsl::seq.eq(next_seq),
					))
					.execute(conn)
					.is_ok();
				next_seq += 1;
				for user in post.likes.iter() {
					ok &= insert_into(likes::dsl::likes)
						.values((
							likes::dsl::post_pid.eq(*pid as i64),
							likes::dsl::user.eq(user.clone()),
						))
						.execute(conn)
						.is_ok();
				}
				for reply_pid in post.replies.iter() {
					ok &= insert_into(replies::dsl::replies)
						.values((
							replies::dsl::post_pid.eq(*pid as i64),
							replies::dsl::reply_pid.eq(*reply_pid as i64),
						))
						.execute(conn)
						.is_ok();
				}
			}
			Some(old) => {
				if old.status != post.status || old.visibility != post.visibility {
					ok &= update(posts::dsl::posts)
						.filter(posts::dsl::pid.eq(*pid as i64))
						.set((
							posts::dsl::status.eq(enc_status(post.status.clone())),
							posts::dsl::visibility.eq(enc_vis(post.visibility.clone())),
						))
						.execute(conn)
						.is_ok();
				}
				for user in post.likes.iter() {
					if !old.likes.iter().any(|prev| prev == user) {
						ok &= insert_into(likes::dsl::likes)
							.values((
								likes::dsl::post_pid.eq(*pid as i64),
								likes::dsl::user.eq(user),
							))
							.execute(conn)
							.is_ok();
					}
				}
				for user in old.likes.iter() {
					if !post.likes.iter().any(|next| next == user) {
						ok &= delete(likes::dsl::likes)
							.filter(
								likes::dsl::post_pid
									.eq(*pid as i64)
									.and(likes::dsl::user.eq(user)),
							)
							.execute(conn)
							.is_ok();
					}
				}
				for reply_pid in post.replies.iter() {
					if !old.replies.iter().any(|prev| prev == reply_pid) {
						ok &= insert_into(replies::dsl::replies)
							.values((
								replies::dsl::post_pid.eq(*pid as i64),
								replies::dsl::reply_pid.eq(*reply_pid as i64),
							))
							.execute(conn)
							.is_ok();
					}
				}
				for reply_pid in old.replies.iter() {
					if !post.replies.iter().any(|next| next == reply_pid) {
						ok &= delete(replies::dsl::replies)
							.filter(
								replies::dsl::post_pid
									.eq(*pid as i64)
									.and(replies::dsl::reply_pid.eq(*reply_pid as i64)),
							)
							.execute(conn)
							.is_ok();
					}
				}
			}
		}
	}
	for (pid, _old) in before.posts.iter() {
		if !next_pids.contains(pid) {
			ok &= delete(posts::dsl::posts)
				.filter(posts::dsl::pid.eq(*pid as i64))
				.execute(conn)
				.is_ok();
			ok &= delete(likes::dsl::likes)
				.filter(likes::dsl::post_pid.eq(*pid as i64))
				.execute(conn)
				.is_ok();
			ok &= delete(replies::dsl::replies)
				.filter(replies::dsl::post_pid.eq(*pid as i64))
				.execute(conn)
				.is_ok();
		}
	}
	let prev_follows: HashSet<(&String, &String)> = before
		.follows
		.iter()
		.map(|(follower, followee)| (follower, followee))
		.collect();
	let next_follows: HashSet<(&String, &String)> = after
		.follows
		.iter()
		.map(|(follower, followee)| (follower, followee))
		.collect();
	for (follower, followee) in after.follows.iter() {
		if !prev_follows.contains(&(follower, followee)) {
			ok &= insert_into(follows::dsl::follows)
				.values((
					follows::dsl::follower.eq(follower),
					follows::dsl::followee.eq(followee),
				))
				.execute(conn)
				.is_ok();
		}
	}
	for (follower, followee) in before.follows.iter() {
		if !next_follows.contains(&(follower, followee)) {
			ok &= delete(follows::dsl::follows)
				.filter(
					follows::dsl::follower
						.eq(follower)
						.and(follows::dsl::followee.eq(followee)),
				)
				.execute(conn)
				.is_ok();
		}
	}
	if !ok {
		let _ = conn.batch_execute("ROLLBACK TRANSACTION;");
		return false;
	}
	conn.batch_execute("COMMIT TRANSACTION;").is_ok()
}

#[cfg(test)]
mod db_tests {
	use super::{
		Account, Post, PostStatus, SessionStatus, Visibility, World, apply, init_or_open,
		load_world, reload_accounts, reload_follows, reload_posts, reload_sessions, reopen,
		save_world,
	};
	use crate::model::empty_world;

	#[doc = "Canonical well-formed World for the save/load tests; rows are pre-sorted in the"]
	#[doc = "order load_world returns them, so equality holds after a full save/reopen round-trip."]
	fn build_world() -> World {
		World {
			accounts: vec![
				(
					"alice".to_string(),
					Account {
						password: "a".to_string(),
						default_visibility: Visibility::Everyone,
					},
				),
				(
					"bob".to_string(),
					Account {
						password: "b".to_string(),
						default_visibility: Visibility::FollowersOnly,
					},
				),
			],
			sessions: vec![
				(100, SessionStatus::Active("alice".to_string())),
				(200, SessionStatus::Revoked),
			],
			posts: vec![
				(
					1,
					Post {
						author: "alice".to_string(),
						text: "hello".to_string(),
						visibility: Visibility::Everyone,
						status: PostStatus::Other,
						likes: vec!["bob".to_string()],
						replies: vec![2],
						parent: None,
					},
				),
				(
					2,
					Post {
						author: "bob".to_string(),
						text: "reply-text".to_string(),
						visibility: Visibility::FollowersOnly,
						status: PostStatus::Other,
						likes: vec![],
						replies: vec![],
						parent: Some(1),
					},
				),
				(
					3,
					Post {
						author: "alice".to_string(),
						text: "gone".to_string(),
						visibility: Visibility::Everyone,
						status: PostStatus::Deleted,
						likes: vec![],
						replies: vec![],
						parent: None,
					},
				),
			],
			follows: vec![
				("alice".to_string(), "bob".to_string()),
				("bob".to_string(), "alice".to_string()),
			],
			newest_first: vec![3, 2, 1],
			used_post_ids: vec![1, 2, 3],
			used_session_ids: vec![100, 200],
		}
	}

	#[doc = "init_or_open creates the DB file; load_world on a fresh DB gives the empty World."]
	#[test]
	#[doc = "T3 gate: fresh database loads as the empty World."]
	fn test_db_empty() {
		let mut conn = init_or_open("/tmp/ft-db-test-empty.sqlite".to_string()).unwrap();
		assert!(load_world(&mut conn) == empty_world());
	}

	#[doc = "save_world then reopen init_or_open + load_world: loaded == w (full round-trip)."]
	#[test]
	#[doc = "T3 gate: save_world then load_world reproduces the World exactly."]
	fn test_db_roundtrip() {
		let path = "/tmp/ft-db-test-roundtrip.sqlite";
		let w = build_world();
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, w.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == w);
	}

	#[doc = "Reopening the same file twice yields equal Worlds (reentrancy)."]
	#[test]
	#[doc = "T3 gate: two reopened loads agree on the same DB file."]
	fn test_db_reopen_equal() {
		let path = "/tmp/ft-db-test-reopen.sqlite";
		let w = build_world();
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, w);
		let mut first = init_or_open(path.to_string()).unwrap();
		let a = load_world(&mut first);
		let mut second = init_or_open(path.to_string()).unwrap();
		let b = load_world(&mut second);
		assert!(a == b);
	}

	#[doc = "A Revoked session row (NULL user) survives save+load."]
	#[test]
	#[doc = "T3 gate: Revoked sessions (no user) are preserved."]
	fn test_db_revoked_preserved() {
		let path = "/tmp/ft-db-test-revoked.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut again = init_or_open(path.to_string()).unwrap();
		let loaded = load_world(&mut again);
		assert!(loaded.sessions.len() == 2);
		assert!(loaded.sessions[1] == (200, SessionStatus::Revoked));
	}

	#[doc = "The after-World for the bounded-diff test: signup zoe (INSERT),"]
	#[doc = "session 100 Active->Revoked (UPDATE), 200 dropped (DELETE), 300 inserted"]
	#[doc = "(INSERT, Unused), post 1 liked by carol and replied to by pid 500 (whose"]
	#[doc = "parent stays 1), post 2 flipped to deleted, follows changed. Rows stay in"]
	#[doc = "load_world's canonical sorted order."]
	fn build_after() -> World {
		World {
			accounts: vec![
				(
					"alice".to_string(),
					Account {
						password: "a".to_string(),
						default_visibility: Visibility::Everyone,
					},
				),
				(
					"bob".to_string(),
					Account {
						password: "b".to_string(),
						default_visibility: Visibility::FollowersOnly,
					},
				),
				(
					"zoe".to_string(),
					Account {
						password: "z".to_string(),
						default_visibility: Visibility::Everyone,
					},
				),
			],
			sessions: vec![(100, SessionStatus::Revoked), (300, SessionStatus::Unused)],
			posts: vec![
				(
					1,
					Post {
						author: "alice".to_string(),
						text: "hello".to_string(),
						visibility: Visibility::Everyone,
						status: PostStatus::Other,
						likes: vec!["bob".to_string(), "carol".to_string()],
						replies: vec![2, 500],
						parent: None,
					},
				),
				(
					2,
					Post {
						author: "bob".to_string(),
						text: "reply-text".to_string(),
						visibility: Visibility::FollowersOnly,
						status: PostStatus::Deleted,
						likes: vec![],
						replies: vec![],
						parent: Some(1),
					},
				),
				(
					3,
					Post {
						author: "alice".to_string(),
						text: "gone".to_string(),
						visibility: Visibility::Everyone,
						status: PostStatus::Deleted,
						likes: vec![],
						replies: vec![],
						parent: None,
					},
				),
				(
					500,
					Post {
						author: "alice".to_string(),
						text: "new reply".to_string(),
						visibility: Visibility::Everyone,
						status: PostStatus::Other,
						likes: vec![],
						replies: vec![],
						parent: Some(1),
					},
				),
			],
			follows: vec![
				("alice".to_string(), "bob".to_string()),
				("carol".to_string(), "alice".to_string()),
			],
			newest_first: vec![500, 3, 2, 1],
			used_post_ids: vec![1, 2, 3, 500],
			used_session_ids: vec![100, 300],
		}
	}

	#[test]
	#[doc = "T4 gate: apply on an empty DB (before = empty) INSERTs every row of after;"]
	#[doc = "new pids get seq = max+1 from scratch, and reload reproduces after."]
	fn test_apply_inserts_all() {
		let path = "/tmp/ft-apply-empty.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// Wipe first so the test is hermetic when the file already exists from an earlier run.
		save_world(&mut conn, empty_world());
		let after = build_world();
		let _ok = apply(&mut conn, &empty_world(), &after);
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == after);
	}

	#[test]
	#[doc = "T4 gate: bounded diff from a saved before-world: INSERTs, UPDATEs (session"]
	#[doc = "status, post status, likes, replies, follows), DELETEs (session 200, follow"]
	#[doc = "(bob,alice)); reload equals after, newest_first [500,3,2,1] (newest-first"]
	#[doc = "preserved, existing seqs untouched) and the reply's parent is still 1."]
	fn test_apply_diff() {
		let path = "/tmp/ft-apply-diff.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let before = build_world();
		let after = build_after();
		let _ok = apply(&mut conn, &before, &after);
		assert!(load_world(&mut conn) == after);
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == after);
		assert!(load_world(&mut conn).newest_first == vec!(500, 3, 2, 1));
		assert!(load_world(&mut conn).posts[3].1.parent == Some(1));
	}
	#[test]
	#[doc = "DB3a gate: a clean diff COMMITs (apply returns true) and the new rows are visible"]
	#[doc = "from a brand-new connection, so write-through really reached the DB."]
	fn test_apply_returns_true() {
		let path = "/tmp/ft-apply-true.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let before = build_world();
		let after = build_after();
		let committed = apply(&mut conn, &before, &after);
		assert!(committed);
		assert!(load_world(&mut conn) == after);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == after);
	}

	#[test]
	#[doc = "DB3a gate: the RAM cache lies (post 1 is missing from BEFORE, but the DB has it),"]
	#[doc = "so apply() re-INSERTs pid 1 and hits the PRIMARY KEY, then INSERTs its like and"]
	#[doc = "reply pairs (likes/replies have no PK, so they would leak). The batch must ROLLBACK:"]
	#[doc = "apply reports failure and the pre-state is intact on disk."]
	fn test_apply_failure_rolls_back() {
		let path = "/tmp/ft-apply-rollback.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		let pre = build_world();
		save_world(&mut conn, pre.clone());
		let mut bad_before = build_world();
		bad_before.posts.retain(|entry| entry.0 != 1);
		let committed = apply(&mut conn, &bad_before, &pre);
		assert!(!committed);
		assert!(load_world(&mut conn) == pre);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == pre);
	}
	#[test]
	/// DB3b gate: reload_accounts throws ONLY the accounts section of the RAM cache out
	/// and re-queries it, so the tampered accounts (bob dropped, alice's password is a lie)
	/// come back as the DB rows, while sessions/posts/follows/newest_first/used_* keep their
	/// cached (tampered) values: exactly one section moved.
	fn test_reload_accounts() {
		let path = "/tmp/ft-reload-accounts.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut tampered = build_world();
		let ghost = "bob".to_string();
		tampered.accounts.retain(|entry| entry.0 != ghost);
		tampered.accounts[0].1.password = "LIE".to_string();
		let mut fresh = reopen(path.to_string()).unwrap();
		let reloaded = reload_accounts(&mut fresh, tampered.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(reloaded.accounts == load_world(&mut again).accounts);
		assert!(reloaded.sessions == tampered.sessions);
		assert!(reloaded.posts == tampered.posts);
		assert!(reloaded.follows == tampered.follows);
		assert!(reloaded.newest_first == tampered.newest_first);
		assert!(reloaded.used_post_ids == tampered.used_post_ids);
		assert!(reloaded.used_session_ids == tampered.used_session_ids);
	}

	#[test]
	/// DB3b gate: reload_sessions replaces ONE section (sessions AND the derived used_session_ids
	/// together), so the tampered session list (200 dropped, 100 flipped to Unused, a ghost id)
	/// is restored from the DB while accounts/posts/follows/newest_first keep their cached values.
	fn test_reload_sessions() {
		let path = "/tmp/ft-reload-sessions.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut tampered = build_world();
		tampered.sessions.retain(|entry| entry.0 != 200);
		tampered.sessions[0].1 = SessionStatus::Unused;
		tampered.used_session_ids = vec![100, 999];
		let mut fresh = reopen(path.to_string()).unwrap();
		let reloaded = reload_sessions(&mut fresh, tampered.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		let expected = load_world(&mut again);
		assert!(reloaded.sessions == expected.sessions);
		assert!(reloaded.used_session_ids == expected.used_session_ids);
		assert!(reloaded.accounts == tampered.accounts);
		assert!(reloaded.posts == tampered.posts);
		assert!(reloaded.follows == tampered.follows);
	}

	#[test]
	/// DB3b gate: reload_follows re-queries the follows section only, so a tampered cache
	/// (the real pairs replaced by a ghost pair) comes back as the DB rows while
	/// accounts/sessions/posts/newest_first/used_* keep their cached values.
	fn test_reload_follows() {
		let path = "/tmp/ft-reload-follows.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut tampered = build_world();
		tampered.follows = vec![("ghost".to_string(), "alice".to_string())];
		let mut fresh = reopen(path.to_string()).unwrap();
		let reloaded = reload_follows(&mut fresh, tampered.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(reloaded.follows == load_world(&mut again).follows);
		assert!(reloaded.accounts == tampered.accounts);
		assert!(reloaded.sessions == tampered.sessions);
		assert!(reloaded.posts == tampered.posts);
		assert!(reloaded.newest_first == tampered.newest_first);
	}

	#[test]
	/// DB3b gate: reload_posts moves posts, newest_first and used_post_ids together (all
	/// derive from the posts tables), so a cache missing post 3 with a bogus timeline is fully
	/// restored from the DB (newest_first [3,2,1] via ORDER BY seq DESC) while accounts/sessions/
	/// used_session_ids keep their cached values.
	fn test_reload_posts() {
		let path = "/tmp/ft-reload-posts.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut tampered = build_world();
		tampered.posts.retain(|entry| entry.0 != 3);
		tampered.posts[0].1.text = "LIE".to_string();
		tampered.newest_first = vec![9, 8];
		tampered.used_post_ids = vec![9, 8];
		let mut fresh = reopen(path.to_string()).unwrap();
		let reloaded = reload_posts(&mut fresh, tampered.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		let expected = load_world(&mut again);
		assert!(reloaded.posts == expected.posts);
		assert!(reloaded.newest_first == expected.newest_first);
		assert!(reloaded.used_post_ids == expected.used_post_ids);
		assert!(reloaded.accounts == tampered.accounts);
		assert!(reloaded.sessions == tampered.sessions);
		assert!(reloaded.follows == tampered.follows);
		assert!(reloaded.used_session_ids == tampered.used_session_ids);
	}
	#[test]
	#[doc = "TB REDO perf-scale gate: 500 posts (pids 1 to 500, ids also in used_post_ids, newest_first "]
	#[doc = "reversed) round-trip via save_world (seqs stamped 1 to 500), then apply of the diff: "]
	#[doc = "delete pid 7, flip pid 11 to Deleted, insert pid 900 (seq 501). Batch COMMITS, load_world "]
	#[doc = "equals after exactly (newest_first [900,500..8,6..1]) and a reopen loads it again."]
	fn test_apply_perf_scale() {
		let path = "/tmp/ft-apply-perf-scale.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, empty_world());
		let mut before = empty_world();
		for index in 1..501 {
			let pid = index as u64;
			before.posts.push((
				pid,
				Post {
					author: "alice".to_string(),
					text: index.to_string(),
					visibility: Visibility::Everyone,
					status: PostStatus::Other,
					likes: vec![],
					replies: vec![],
					parent: None,
				},
			));
			before.newest_first.push(pid);
			before.used_post_ids.push(pid);
		}
		before.newest_first.reverse();
		let mut after = before.clone();
		after.posts.retain(|entry| entry.0 != 7);
		after.newest_first.retain(|pid| *pid != 7);
		after.used_post_ids.retain(|id| *id != 7);
		assert!(after.posts[9].0 == 11);
		after.posts[9].1.status = PostStatus::Deleted;
		after.posts.push((
			900,
			Post {
				author: "alice".to_string(),
				text: "extra".to_string(),
				visibility: Visibility::Everyone,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent: None,
			},
		));
		after.used_post_ids.push(900);
		after.newest_first.insert(0, 900);
		save_world(&mut conn, before.clone());
		let committed = apply(&mut conn, &before, &after);
		assert!(committed);
		assert!(load_world(&mut conn) == after);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == after);
	}
}
