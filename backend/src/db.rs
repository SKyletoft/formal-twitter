//! Diesel/SQLite persistence for the formal-twitter backend (task T3; no Rocket here).
//!
//! Six SQL tables mirror the DB schema note in todo.md. Encodings mirror
//! spec/Twitter.agda; the encoding pins are proved in backend/ImplStorage.agda.

#![allow(clippy::cast_lossless, clippy::cast_possible_truncation)]

use crate::model::{Account, Post, PostStatus, SessionStatus, Visibility, World};

use std::collections::HashMap;

use diesel::connection::SimpleConnection;
use diesel::delete;
use diesel::insert_into;
use diesel::prelude::*;

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


// ---- Encodings (proved pins: backend/ImplStorage.agda) ----

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


// ---- Loading World from the DB ----

/// Load every table with static typed queries. A query error (corrupt or
/// missing table) is treated as no rows: an empty World component, never a
/// panic; save_world rewrites everything regardless. Canonical row order
/// keeps World equality stable (lexicographic per table; newest_first from
/// ORDER BY seq DESC; likes/replies keep row order within a post).
pub fn load_world(conn: &mut SqliteConnection) -> World {
	let mut account_rows = accounts::dsl::accounts
		.select((accounts::dsl::username, accounts::dsl::password, accounts::dsl::visibility))
		.load::<(String, String, i32)>(conn)
		.unwrap_or_default();
	let mut session_rows = sessions::dsl::sessions
		.select((sessions::dsl::sid, sessions::dsl::status, sessions::dsl::user))
		.load::<(i64, i32, Option<String>)>(conn)
		.unwrap_or_default();
	let mut post_rows = posts::dsl::posts
		.select((
			posts::dsl::pid, posts::dsl::author, posts::dsl::text, posts::dsl::visibility,
			posts::dsl::status, posts::dsl::parent, posts::dsl::seq,
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
		.map(|(pid, author, text, vis, code, parent, _seq)| (
			pid as u64,
			Post {
				author,
				text,
				visibility: dec_vis(vis),
				status: dec_status(code),
				likes: like_rows.iter()
					.filter(|row| row.0 == pid)
					.map(|row| row.1.clone())
					.collect(),
				replies: reply_rows.iter()
					.filter(|row| row.0 == pid)
					.map(|row| row.1 as u64)
					.collect(),
				parent: parent.map(|p| p as u64),
			},
		))
		.collect();
	let used_post_ids: Vec<u64> = posts_map.iter().map(|row| row.0).collect();
	let used_session_ids: Vec<u64> = session_rows.iter().map(|row| row.0 as u64).collect();
	World {
		accounts: account_rows
			.into_iter()
			.map(|(username, password, vis)| (username, Account {password, default_visibility: dec_vis(vis)}))
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
	 let account_rows: Vec<_> = w.accounts.into_iter()
		.map(|(username, account)| (
		accounts::dsl::username.eq(username), accounts::dsl::password.eq(account.password),
				accounts::dsl::visibility.eq(enc_vis(account.default_visibility))
		))
		.collect();
	 let session_rows: Vec<_> = w.sessions.into_iter()
		.map(|(sid, st)| {
			 let (code, user) = enc_sess_row(st);
			(sessions::dsl::sid.eq(sid as i64), sessions::dsl::status.eq(code), sessions::dsl::user.eq(user))
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
		like_rows.push((likes::dsl::post_pid.eq(pid as i64), likes::dsl::user.eq(user)));
	  }
	  for reply_pid in post.replies.into_iter() {
		reply_rows.push((replies::dsl::post_pid.eq(pid as i64), replies::dsl::reply_pid.eq(reply_pid as i64)));
	  }
	 }
	 if !account_rows.is_empty() {
	  let _ = insert_into(accounts::dsl::accounts).values(&account_rows).execute(conn);
	 }
	 if !session_rows.is_empty() {
	  let _ = insert_into(sessions::dsl::sessions).values(&session_rows).execute(conn);
	 }
	 if !post_rows.is_empty() {
	  let _ = insert_into(posts::dsl::posts).values(&post_rows).execute(conn);
	 }
	 if !like_rows.is_empty() {
	  let _ = insert_into(likes::dsl::likes).values(&like_rows).execute(conn);
	 }
	 if !reply_rows.is_empty() {
	  let _ = insert_into(replies::dsl::replies).values(&reply_rows).execute(conn);
	 }
	 let follow_rows: Vec<_> = w.follows.into_iter()
		.map(|(follower, followee)| (follows::dsl::follower.eq(follower), follows::dsl::followee.eq(followee)))
		.collect();
	 if !follow_rows.is_empty() {
	  let _ = insert_into(follows::dsl::follows).values(&follow_rows).execute(conn);
	 }
	 // used_post_ids / used_session_ids are not stored: load_world derives them
	 // from the keys actually present, which keeps the DB the reentrant source of truth.
}

#[cfg(test)]
mod db_tests {
	use super::{Account, Post, PostStatus, SessionStatus, Visibility, World, init_or_open, load_world, save_world};
	use crate::model::empty_world;

	#[doc = "Canonical well-formed World for the save/load tests; rows are pre-sorted in the"]
	#[doc = "order load_world returns them, so equality holds after a full save/reopen round-trip."]
	fn build_world() -> World {
		World {
			accounts: vec!(("alice".to_string(), Account { password: "a".to_string(), default_visibility: Visibility::Everyone }),
				("bob".to_string(), Account { password: "b".to_string(), default_visibility: Visibility::FollowersOnly })),
			sessions: vec!((100, SessionStatus::Active("alice".to_string())), (200, SessionStatus::Revoked)),
			posts: vec!(				(1, Post { author: "alice".to_string(), text: "hello".to_string(), visibility: Visibility::Everyone,
				status: PostStatus::Other, likes: vec!("bob".to_string()), replies: vec!(2), parent: None }),
				(2, Post { author: "bob".to_string(), text: "reply-text".to_string(), visibility: Visibility::FollowersOnly,
					status: PostStatus::Other, likes: vec![], replies: vec![], parent: Some(1) }),
				(3, Post { author: "alice".to_string(), text: "gone".to_string(), visibility: Visibility::Everyone,
					status: PostStatus::Deleted, likes: vec![], replies: vec![], parent: None })),
			follows: vec!(("alice".to_string(), "bob".to_string()), ("bob".to_string(), "alice".to_string())),
			newest_first: vec!(3, 2, 1),
			used_post_ids: vec!(1, 2, 3),
			used_session_ids: vec!(100, 200),
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
}
