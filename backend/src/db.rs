// db.rs - persistence for World using Diesel + SQLite.
//
// Diesel 2.4 ships no schema! macro at compile time, so all SQL is raw
// `sql_query(str)` with `.bind::<SqlType,_>(value)` parameters (the bind
// collector quotes values safely; user strings never touch the grammar).
//
// Sentinels: a NULL never crosses the query boundary (Diesel's SQLite
// backend treats result columns as non-nullable), so:
//   posts.parent  : 0 means "no parent" (real pids start at 1)
//   sessions.user : "" means "no username" (only active sessions carry one)

use diesel::{
	QueryableByName, RunQueryDsl, SqliteConnection,
	connection::SimpleConnection,
	sql_query,
	sql_types::{BigInt, Text},
};

use std::collections::{HashMap, HashSet};

use crate::world::*;

#[derive(QueryableByName)]
pub struct AccountsRow {
	#[diesel(sql_type = Text)]
	username: String,
	#[diesel(sql_type = Text)]
	password: String,
	#[diesel(sql_type = Text)]
	visibility: String,
}

#[derive(QueryableByName)]
pub struct SessionsRow {
	#[diesel(sql_type = BigInt)]
	sid: i64,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Text)]
	user: String,
}

#[derive(QueryableByName)]
pub struct PostsRow {
	#[diesel(sql_type = BigInt)]
	pid: i64,
	#[diesel(sql_type = Text)]
	author: String,
	#[diesel(sql_type = Text)]
	text: String,
	#[diesel(sql_type = Text)]
	visibility: String,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = BigInt)]
	parent: i64,
}

#[derive(QueryableByName)]
pub struct LikesRow {
	#[diesel(sql_type = BigInt)]
	pid: i64,
	#[diesel(sql_type = Text)]
	user: String,
	#[diesel(sql_type = BigInt)]
	seq: i64,
}

#[derive(QueryableByName)]
pub struct RepliesRow {
	#[diesel(sql_type = BigInt)]
	ppid: i64,
	#[diesel(sql_type = BigInt)]
	cpid: i64,
	#[diesel(sql_type = BigInt)]
	seq: i64,
}

#[derive(QueryableByName)]
pub struct FollowsRow {
	#[diesel(sql_type = Text)]
	follower: String,
	#[diesel(sql_type = Text)]
	followee: String,
}

#[derive(QueryableByName)]
pub struct LogRow {
	#[diesel(sql_type = Text)]
	req: String,
	#[diesel(sql_type = Text)]
	ts: String,
}

pub const SCHEMA: &str = "
CREATE TABLE accounts (username TEXT PRIMARY KEY, password TEXT NOT NULL, visibility TEXT NOT NULL);
CREATE TABLE sessions (sid BIGINT PRIMARY KEY, status TEXT NOT NULL, user TEXT NOT NULL);
CREATE TABLE posts (pid BIGINT PRIMARY KEY, author TEXT NOT NULL, text TEXT NOT NULL, visibility TEXT NOT NULL, status TEXT NOT NULL, parent BIGINT NOT NULL);
CREATE TABLE likes (pid BIGINT NOT NULL, user TEXT NOT NULL, seq BIGINT NOT NULL);
CREATE TABLE replies (ppid BIGINT NOT NULL, cpid BIGINT NOT NULL, seq BIGINT NOT NULL);
CREATE TABLE follows (follower TEXT NOT NULL, followee TEXT NOT NULL);
CREATE TABLE log (req TEXT NOT NULL, ts TEXT NOT NULL);
";

pub fn vis_str(v: Visibility) -> String {
	if v == Visibility::Everyone {
		"everyone".to_string()
	} else {
		"followers-only".to_string()
	}
}

pub fn vis_of(s: String) -> Visibility {
	if s == "followers-only" {
		Visibility::FollowersOnly
	} else {
		Visibility::Everyone
	}
}

pub fn status_str(s: PostStatus) -> String {
	if s == PostStatus::Live {
		"live".to_string()
	} else {
		"deleted".to_string()
	}
}

pub fn status_of(s: String) -> PostStatus {
	if s == "deleted" {
		PostStatus::Deleted
	} else {
		PostStatus::Live
	}
}

pub fn init(conn: &mut SqliteConnection) {
	conn.batch_execute(SCHEMA).unwrap();
}

pub fn load_world(conn: &mut SqliteConnection) -> World {
	let mut w = World {
		account_at: HashMap::new(),
		session_at: HashMap::new(),
		post_at: HashMap::new(),
		follows: HashSet::new(),
		newest_first: Vec::new(),
	};

	let accs = sql_query("SELECT username, password, visibility FROM accounts")
		.get_results::<AccountsRow>(conn)
		.unwrap();
	for r in accs {
		w.account_at.insert(
			r.username,
			Account {
				password: r.password,
				default_visibility: vis_of(r.visibility),
			},
		);
	}

	let sess = sql_query("SELECT sid, status, user FROM sessions")
		.get_results::<SessionsRow>(conn)
		.unwrap();
	for r in sess {
		let sid = r.sid;
		let st = r.status;
		let user = r.user;
		let status = if st == "active" {
			SessionStatus::Active(user)
		} else if st == "revoked" {
			SessionStatus::Revoked
		} else {
			SessionStatus::Unused
		};
		w.session_at.insert(sid, status);
	}

	let ps = sql_query("SELECT pid, author, text, visibility, status, parent FROM posts")
		.get_results::<PostsRow>(conn)
		.unwrap();
	for r in ps {
		let pid = r.pid;
		let a = r.author;
		let t = r.text;
		let v = r.visibility;
		let s = r.status;
		let par = r.parent;
		w.post_at.insert(
			pid,
			Post {
				author: a,
				text: t,
				visibility: vis_of(v),
				status: status_of(s),
				likes: Vec::new(),
				replies: Vec::new(),
				parent: if par == 0 { None } else { Some(par) },
			},
		);
		w.newest_first.push(pid);
	}
	// newest-first = descending pid, since pids are monotonic (max+1).
	w.newest_first.sort();
	w.newest_first.reverse();

	let likes = sql_query("SELECT pid, user, seq FROM likes ORDER BY seq")
		.get_results::<LikesRow>(conn)
		.unwrap();
	for r in likes {
		w.post_at.get_mut(&r.pid).unwrap().likes.push(r.user);
	}

	let reps = sql_query("SELECT ppid, cpid, seq FROM replies ORDER BY seq")
		.get_results::<RepliesRow>(conn)
		.unwrap();
	for r in reps {
		w.post_at.get_mut(&r.ppid).unwrap().replies.push(r.cpid);
	}

	let fols = sql_query("SELECT follower, followee FROM follows")
		.get_results::<FollowsRow>(conn)
		.unwrap();
	for r in fols {
		w.follows.insert((r.follower, r.followee));
	}

	w
}

pub fn save_world(conn: &mut SqliteConnection, w: &World) {
	sql_query("DELETE FROM accounts").execute(conn).unwrap();
	sql_query("DELETE FROM sessions").execute(conn).unwrap();
	sql_query("DELETE FROM posts").execute(conn).unwrap();
	sql_query("DELETE FROM likes").execute(conn).unwrap();
	sql_query("DELETE FROM replies").execute(conn).unwrap();
	sql_query("DELETE FROM follows").execute(conn).unwrap();

	for (u, acc) in w.account_at.iter() {
		sql_query("INSERT INTO accounts (username, password, visibility) VALUES (")
			.bind::<Text, _>(u)
			.sql(", ")
			.bind::<Text, _>(acc.password.clone())
			.sql(", ")
			.bind::<Text, _>(vis_str(acc.default_visibility))
			.sql(")")
			.execute(conn)
			.unwrap();
	}

	for (sid, st) in w.session_at.iter() {
		let (status, user) = match st {
			SessionStatus::Active(u) => ("active".to_string(), u.to_string()),
			SessionStatus::Revoked => ("revoked".to_string(), "".to_string()),
			SessionStatus::Unused => ("unused".to_string(), "".to_string()),
		};
		sql_query("INSERT INTO sessions (sid, status, user) VALUES (")
			.bind::<BigInt, _>(sid)
			.sql(", ")
			.bind::<Text, _>(status)
			.sql(", ")
			.bind::<Text, _>(user)
			.sql(")")
			.execute(conn)
			.unwrap();
	}

	for (pid, p) in w.post_at.iter() {
		let par = if p.parent.is_none() {
			0
		} else {
			p.parent.unwrap()
		};
		sql_query("INSERT INTO posts (pid, author, text, visibility, status, parent) VALUES (")
			.bind::<BigInt, _>(pid)
			.sql(", ")
			.bind::<Text, _>(p.author.clone())
			.sql(", ")
			.bind::<Text, _>(p.text.clone())
			.sql(", ")
			.bind::<Text, _>(vis_str(p.visibility))
			.sql(", ")
			.bind::<Text, _>(status_str(p.status))
			.sql(", ")
			.bind::<BigInt, _>(par)
			.sql(")")
			.execute(conn)
			.unwrap();
		let mut seq: i64 = 0;
		for u in p.likes.iter() {
			sql_query("INSERT INTO likes (pid, user, seq) VALUES (")
				.bind::<BigInt, _>(pid)
				.sql(", ")
				.bind::<Text, _>(u)
				.sql(", ")
				.bind::<BigInt, _>(seq)
				.sql(")")
				.execute(conn)
				.unwrap();
			seq = seq + 1;
		}
		let mut seq: i64 = 0;
		for c in p.replies.iter() {
			sql_query("INSERT INTO replies (ppid, cpid, seq) VALUES (")
				.bind::<BigInt, _>(pid)
				.sql(", ")
				.bind::<BigInt, _>(c)
				.sql(", ")
				.bind::<BigInt, _>(seq)
				.sql(")")
				.execute(conn)
				.unwrap();
			seq = seq + 1;
		}
	}

	for (f, g) in w.follows.iter() {
		sql_query("INSERT INTO follows (follower, followee) VALUES (")
			.bind::<Text, _>(f)
			.sql(", ")
			.bind::<Text, _>(g)
			.sql(")")
			.execute(conn)
			.unwrap();
	}
}

pub fn append_log(conn: &mut SqliteConnection, req: String) {
	sql_query("INSERT INTO log (req, ts) VALUES (")
		.bind::<Text, _>(req)
		.sql(", datetime('now'))")
		.execute(conn)
		.unwrap();
}

pub fn read_log(conn: &mut SqliteConnection) -> Vec<(String, String)> {
	let rows = sql_query("SELECT req, ts FROM log ORDER BY rowid")
		.get_results::<LogRow>(conn)
		.unwrap();
	let mut out: Vec<(String, String)> = Vec::new();
	for r in rows {
		out.push((r.req.to_string(), r.ts.to_string()));
	}
	out
}

// ---- Plaintext dump for /raw ----

pub fn raw_dump(w: &World) -> String {
	let mut parts = Vec::new();
	parts.push("== accounts ==".to_string());
	for (u, acc) in w.account_at.iter() {
		parts.push(format!(
			"{} | password={} | visibility={}",
			u,
			acc.password,
			vis_str(acc.default_visibility)
		));
	}
	parts.push("== sessions ==".to_string());
	for (sid, st) in w.session_at.iter() {
		match st {
			SessionStatus::Active(u) => parts.push(format!("{} | active | user={}", sid, u)),
			SessionStatus::Revoked => parts.push(format!("{} | revoked", sid)),
			SessionStatus::Unused => parts.push(format!("{} | unused", sid)),
		}
	}
	parts.push("== posts (newest first) ==".to_string());
	for pid in w.newest_first.iter() {
		let p = w.post_at.get(&pid).unwrap();
		let par = if p.parent.is_none() {
			"-".to_string()
		} else {
			format!("{} (reply to)", p.parent.unwrap())
		};
		parts.push(format!(
			"{} | by={} | visibility={} | status={} | parent={} | likes={}",
			pid,
			p.author,
			vis_str(p.visibility),
			status_str(p.status),
			par,
			p.likes.join(", ")
		));
	}
	parts.push("== follows ==".to_string());
	for (f, g) in w.follows.iter() {
		parts.push(format!("{} follows {}", f, g));
	}
	parts.join("\n")
}
