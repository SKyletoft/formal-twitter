//! Diesel/SQLite persistence for the formal-twitter backend (task T3; no Rocket here).
//!
//! Six SQL tables mirror the DB schema note in todo.md. Encodings mirror
//! spec/Twitter.agda; the stdlib-only encoding-pin module was removed per A4
//! (recovery commit b6b868b keeps it).

#![allow(clippy::cast_lossless, clippy::cast_possible_truncation)]

use crate::model::{Account, Delta, Post, PostStatus, SessionStatus, Visibility, World};

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

/// Borrowed sibling of enc_sess_row (task TB): the status arrives by reference, so apply()'s
/// borrowed views never copy it; only the Active username is copied, where this runs.
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
	// (F7) The 4th full-table query (ORDER BY seq DESC pid re-scan) is gone: derive that
	// order by stable-sorting the already-loaded post_rows (row.6 = seq, row.0 = pid),
	// which are already pid-sorted here; stable sort keeps pid order on seq ties, matching
	// the DB scan order of the removed query (seqs are unique stamps, so ties cannot occur).
	let mut nf_pairs: Vec<(i64, i64)> = post_rows.iter().map(|row| (row.6, row.0)).collect();
	nf_pairs.sort_by(|x, y| y.0.cmp(&x.0));
	let newest_first: Vec<u64> = nf_pairs.into_iter().map(|(_, pid)| pid as u64).collect();
	// (F5) bucket the sorted row lists once, then look each post's bucket up per post.
	// (F5) keys are the u64 post ids; each Post keeps a fresh copy of its bucket.
	let like_map = bucket_like_rows(like_rows);
	let reply_map = bucket_reply_rows(reply_rows);
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
					// (F5) O(1) bucket lookup replaces the full-row-list filter;
					likes: like_map
						.get(&(pid as u64))
						.unwrap_or(&vec![])
						.iter()
						.map(|user| user.to_string())
						.collect(),
					// (F5) same for the reply buckets (u64 ids are copied).
					// (F5) deref gives the u64 id.
					replies: reply_map.get(&(pid as u64)).unwrap_or(&vec![]).to_vec(),
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

// ---- (F5) bucket likes/replies rows ONCE by post_pid (kills the P x (L + R) per-post rescans) ----
// Both row lists are loaded tuple-sorted, so equal post_pid rows are contiguous and each bucket
// keeps the query's ORDER BY order (likes asc by user, replies asc by reply_pid) - exactly the
// subsequence the previous per-post full-list filter produced, so Post.likes / Post.replies stay
// identical. Buckets are collected into a HashMap keyed by the u64 post id for O(1) lookup.
fn bucket_like_rows(rows: Vec<(i64, String)>) -> HashMap<u64, Vec<String>> {
	// (F5) one pass over the sorted rows, collecting runs of equal post_pid.
	let n = rows.len();
	// (F5) buckets keyed by the i64 post_pid, cast to u64 when collected.
	let mut out: Vec<(i64, Vec<String>)> = vec![];
	let mut i = 0;
	while i < n {
		// (F5) key of the run starting at i.
		let pid = rows[i].0;
		let mut j = i + 1;
		// (F5) rows are sorted by key, so a mismatch ends the bucket.
		while j < n && rows[j].0 == pid {
			j += 1;
		}
		// (F5) bucket keeps the row order the query gave; users clone so each Post owns its list.
		// (F5) push the (key, bucket) pair and jump past the run.
		out.push((pid, rows[i..j].iter().map(|row| row.1.clone()).collect()));
		i = j;
	}
	// (F5) collect buckets straight into the HashMap (no per-row insert loop).
	// (F5) key cast to u64.
	out.into_iter()
		.map(|(pid, users)| (pid as u64, users))
		.collect()
}

fn bucket_reply_rows(rows: Vec<(i64, i64)>) -> HashMap<u64, Vec<u64>> {
	// (F5) same contiguous-run grouping as bucket_like_rows: reply rows are tuple-sorted by
	// (post_pid, reply_pid), so each bucket is exactly the query-order reply list of a post.
	// (F5) one pass over the sorted rows.
	let n = rows.len();
	// (F5) buckets keyed by the i64 post_pid, cast later.
	let mut out: Vec<(i64, Vec<i64>)> = vec![];
	let mut i = 0;
	while i < n {
		let pid = rows[i].0;
		let mut j = i + 1;
		// (F5) run of equal post_pid rows.
		while j < n && rows[j].0 == pid {
			j += 1;
		}
		// (F5) bucket keeps ascending reply_pid order; push pair and skip the run.
		out.push((pid, rows[i..j].iter().map(|row| row.1).collect()));
		i = j;
	}
	// (F5) collect into the HashMap keyed by the u64 post id.
	// (F5) reply ids i64 -> u64, so Post.replies stays a Vec<u64>.
	// (F5) no per-row insert loop, so clippy's insert-in-loop style lint stays quiet.
	out.into_iter()
		.map(|(pid, kids)| (pid as u64, kids.into_iter().map(|k| k as u64).collect()))
		.collect()
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
	post_rows.sort();
	like_rows.sort();
	reply_rows.sort();
	// (F7) The 4th full-table query (ORDER BY seq DESC pid re-scan) is gone: derive that
	// order by stable-sorting the already-loaded post_rows (row.6 = seq, row.0 = pid);
	// seqs are unique stamps, so ties cannot occur and the order equals the query's.
	let mut nf_pairs: Vec<(i64, i64)> = post_rows.iter().map(|row| (row.6, row.0)).collect();
	nf_pairs.sort_by(|x, y| y.0.cmp(&x.0));
	let newest_first: Vec<u64> = nf_pairs.into_iter().map(|(_, pid)| pid as u64).collect();
	// (F5) bucket the sorted row lists once, then look each post's bucket up per post.
	// (F5) keys are the u64 post ids; each Post keeps a fresh copy of its bucket.
	let like_map = bucket_like_rows(like_rows);
	// (F5) reply buckets keyed the same way.
	// (F5) both built before the Post decode loop.
	let reply_map = bucket_reply_rows(reply_rows);
	// (F5) decode loop now reads buckets, never the whole row list.
	// (F5) pids iterate ascending (post_rows sorted), buckets keyed by pid.
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
					// (F5) O(1) bucket lookup replaces the full-row-list filter;
					// (F5) get borrows the bucket, so elements are copied into this Post.
					// (F5) None (no likes) falls back to an empty list.
					likes: like_map
						.get(&(pid as u64))
						.unwrap_or(&vec![])
						.iter()
						.map(|user| user.to_string())
						.collect(),
					// (F5) same for the reply buckets (u64 ids are copied).
					// (F5) deref gives the u64 id.
					// (F5) None means the post has no replies.
					replies: reply_map.get(&(pid as u64)).unwrap_or(&vec![]).to_vec(),
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
/// Lossy: pids absent from newest_first are stamped seq = 0 (seq_of.get unwrap_or),
/// so their restart order is unrecoverable; save_world is used only in tests.
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

/// (F3) ONE-SHOT launch seed for a caller's max_seq cache: the ONLY place the seq column
/// (F3) is scanned for a maximum, and it runs at server startup, never per request.
/// Returns 0 for an empty DB, which apply() reads as "stamp the first post at seq 1".
pub fn db_max_seq(conn: &mut SqliteConnection) -> u64 {
	// (F3) Bounded once-per-launch: plain load of the seq column, hand-folded for the
	// (F3) maximum (the Aggregates type soup stays out of the way).
	let seqs: Vec<i64> = posts::dsl::posts
		.select(posts::dsl::seq)
		.load::<i64>(conn)
		.unwrap_or_default();
	let mut best: u64 = 0;
	for s in seqs.into_iter() {
		// (F3) Guard before the signed-to-unsigned cast, so save_world's lossy seq = 0
		// (F3) rows and any negative stamp never raise the hint.
		if s > 0 && (s as u64) > best {
			best = s as u64;
		}
	}
	best
}

/// test-only reference: Bounded write-through: the DB must already mirror `before`; we mutate only
/// the delta to `after`. Accounts only ever get INSERTs (password/visibility of
/// an existing account never changes). Sessions UPDATE on status/user change,
/// INSERT when new, DELETE when dropped (defensive). Posts: a new pid is INSERTed
/// with seq = max_hint + 1, growing by one per insertion, so ORDER BY seq DESC keeps
/// newest_first (new posts prepend); existing seqs stay put.
/// Status flips (live<->deleted) UPDATE the row; likes/replies are pair INSERT/DELETE;
/// follows likewise. Nothing existing is rewritten, so this is O(delta).
/// (F3) max_hint is the CALLER's cached maximum seq currently stored in the DB (0 =
/// (F3) empty DB). Contract: max_hint >= every seq in the DB; the first new post is stamped
/// (F3) max_hint + 1 and successive inserts increment from there. apply() NEVER re-reads the
/// (F3) seq column (that per-request SELECT + max-fold scan was O(P) and ran on pure reads
/// (F3) too; it is gone). The caller keeps the hint exact by advancing it by the number of
/// (F3) posts a COMMITTED call INSERTed; a false return changed nothing in the DB, so the
/// (F3) caller's max_seq stays as it was. Single writer per DB file: another server opening
/// (F3) the same file reseeds its hint at startup with db_max_seq, which is the only scan.
/// The whole batch is one sqlite transaction (raw BEGIN/COMMIT or ROLLBACK pragmas);
/// the Bool reports whether the batch committed, i.e. false means the DB is unchanged.
pub fn apply(conn: &mut SqliteConnection, before: &World, after: &World, max_hint: u64) -> bool {
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
	// (F3) No DB scan at all: the stamp counter starts at the caller's hint, so the first
	// (F3) new post gets max_hint + 1 and every further INSERT increments from there.
	let mut next_seq: i64 = max_hint as i64 + 1;
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
				// (F6) membership sets built ONCE per touched post: they replace the nested
				// (F6) any() scans (O(L^2) for likes, O(R^2) for replies). Iteration below is
				// (F6) unchanged, so the INSERT/DELETE statements keep their exact order.
				// (F6) old likers keyed by reference, so no string is copied.
				let old_likes: HashSet<&String> = old.likes.iter().collect();
				// (F6) new likers likewise.
				let new_likes: HashSet<&String> = post.likes.iter().collect();
				// (F6) old reply ids keyed by u64, as next_sids does.
				// (F6) deref gives the u64.
				let old_replies: HashSet<u64> = old.replies.iter().copied().collect();
				// (F6) new reply ids likewise.
				let new_replies: HashSet<u64> = post.replies.iter().copied().collect();
				for user in post.likes.iter() {
					// (F6) O(1) probe replaces the old-likes any() scan.
					if !old_likes.contains(&user) {
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
					// (F6) O(1) probe replaces the new-likes any() scan.
					if !new_likes.contains(&user) {
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
					// (F6) O(1) probe replaces the old-replies any() scan.
					if !old_replies.contains(reply_pid) {
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
					// (F6) O(1) probe replaces the new-replies any() scan.
					if !new_replies.contains(reply_pid) {
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

// ---- Delta-driven write-through (task F2) ----

/// (F2) Delta-driven write-through: the SAME diesel statements apply() emits for one
/// (F2) Command's effect, read off the Delta payload instead of diffing two Worlds, so a
/// (F2) later load_world observes exactly what patch_world computed. Same BEGIN-first,
/// (F2) COMMIT-iff-all-Ok, else-ROLLBACK discipline as apply(): a PRIMARY KEY clash (a RAM
/// (F2) sampled id that landed on a stored one) ANDs a false into ok, ROLLBACKs the batch
/// (F2) and reports false with the DB byte-identical. max_hint is the caller's cached max
/// (F2) seq, so Publish stamps max_hint + 1 exactly as apply does; before is the caller's
/// (F2) DB-mirror cache, read ONLY for the column an UPDATE must keep (a deleted post's
/// (F2) visibility). Zero-statement batches COMMIT and report true.
pub fn apply_delta(
	conn: &mut SqliteConnection,
	before: &World,
	delta: Delta,
	max_hint: u64,
) -> bool {
	// Transactional write-through: BEGIN first; every statement's recoverable QueryResult
	// is ANDed into ok, and the batch COMMITs only if all of them (plus BEGIN) succeeded.
	let mut ok = conn.batch_execute("BEGIN TRANSACTION;").is_ok();
	// (F2) one branch per Delta constructor: the payload moves in, so its strings and
	// (F2) accounts are never copied.
	match delta {
		// (F2) None_: zero-statement transaction -> COMMIT -> true.
		Delta::None_ => {}
		Delta::Publish(pid, author, text, visibility, parent) => {
			// (F2) the caller's hint, never a DB re-scan: apply stamps its first new post
			// (F2) at max_hint + 1 and Publish INSERTs exactly one posts row.
			let next_seq: i64 = max_hint as i64 + 1;
			// (F2) apply's new-post INSERT, column for column: a fresh post is live,
			// (F2) unliked and reply-free, so apply's inner like/reply INSERT loops emit
			// (F2) nothing and used_pids/used_sids stay derived rows (no table for them).
			ok &= insert_into(posts::dsl::posts)
				.values((
					posts::dsl::pid.eq(pid as i64),
					posts::dsl::author.eq(author),
					posts::dsl::text.eq(text),
					posts::dsl::visibility.eq(enc_vis(visibility)),
					posts::dsl::status.eq(enc_status(PostStatus::Other)),
					posts::dsl::parent.eq(parent.map(|p| p as i64)),
					posts::dsl::seq.eq(next_seq),
				))
				.execute(conn)
				.is_ok();
			// (F2) the child's parent field IS the spec's reply relation, so the DB gains
			// (F2) the reply row apply's replies set-diff INSERT emits: the row keys on the PARENT's
			// (F2) post_pid and carries the new pid in reply_pid, which is what load_world
			// (F2) reads back as that parent's reply.
			if let Some(ppid) = parent {
				ok &= insert_into(replies::dsl::replies)
					.values((
						replies::dsl::post_pid.eq(ppid as i64),
						replies::dsl::reply_pid.eq(pid as i64),
					))
					.execute(conn)
					.is_ok();
			}
		}
		Delta::Delete(pid) => {
			// (F2) visibility is not part of the effect, yet apply's posts UPDATE writes that
			// (F2) exact column pair (status AND visibility), so the row's current visibility
			// (F2) comes from the caller's before-cache. pids are unique: first hit wins.
			let cur_vis: Visibility = match before.posts.iter().find(|(row_pid, _)| *row_pid == pid)
			{
				Some((_, post)) => post.visibility.clone(),
				// (F2) the cache lost the row: load's decode default, and the delta only ever
				// (F2) comes for a stored post, so the UPDATE stays total.
				None => Visibility::Everyone,
			};
			// (F2) UPDATE, never DELETE: tombstones persist (the spec's reap is commented
			// (F2) out), so likes, replies and the parent column all stay put.
			ok &= update(posts::dsl::posts)
				.filter(posts::dsl::pid.eq(pid as i64))
				.set((
					posts::dsl::status.eq(enc_status(PostStatus::Deleted)),
					posts::dsl::visibility.eq(enc_vis(cur_vis)),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::Authenticate(sid, user) => {
			// (F2) login issues a FRESH sid, so this is apply's new-session INSERT: the
			// (F2) (1, just user) Active row. A sid that is already stored clashes the
			// (F2) PRIMARY KEY and rolls the whole batch back.
			let (code, row_user) = enc_sess_row(SessionStatus::Active(user));
			ok &= insert_into(sessions::dsl::sessions)
				.values((
					sessions::dsl::sid.eq(sid as i64),
					sessions::dsl::status.eq(code),
					sessions::dsl::user.eq(row_user),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::RevokeToken(sid) => {
			// (F2) logout: apply's existing-sid session UPDATE, both columns of its set-pair
			// (F2) (status AND user) moving together.
			let (code, row_user) = enc_sess_row(SessionStatus::Revoked);
			ok &= update(sessions::dsl::sessions)
				.filter(sessions::dsl::sid.eq(sid as i64))
				.set((
					sessions::dsl::status.eq(code),
					sessions::dsl::user.eq(row_user),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::Register(user, acct) => {
			// (F2) apply's accounts INSERT: accounts never UPDATE, the spec's register rule
			// (F2) fixes password and default visibility at signup. An existing username
			// (F2) clashes the PRIMARY KEY -> ROLLBACK -> false.
			ok &= insert_into(accounts::dsl::accounts)
				.values((
					accounts::dsl::username.eq(user),
					accounts::dsl::password.eq(acct.password),
					accounts::dsl::visibility.eq(enc_vis(acct.default_visibility)),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::Follow(follower, followee) => {
			// (F2) apply's follows-branch INSERT: the pair is stored as one row.
			ok &= insert_into(follows::dsl::follows)
				.values((
					follows::dsl::follower.eq(follower),
					follows::dsl::followee.eq(followee),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::Unfollow(follower, followee) => {
			// (F2) apply's follows-branch DELETE over the exact pair, so no other edge is
			// (F2) touched and an absent pair deletes zero rows (not an error).
			ok &= delete(follows::dsl::follows)
				.filter(
					follows::dsl::follower
						.eq(follower)
						.and(follows::dsl::followee.eq(followee)),
				)
				.execute(conn)
				.is_ok();
		}
		Delta::Like(pid, user) => {
			// (F2) apply's likes INSERT for a new liker: (post_pid, user), the pair load
			// (F2) groups into Post.likes. step_d emits Like only for a non-liker, so no
			// (F2) duplicate row can appear.
			ok &= insert_into(likes::dsl::likes)
				.values((
					likes::dsl::post_pid.eq(pid as i64),
					likes::dsl::user.eq(user),
				))
				.execute(conn)
				.is_ok();
		}
		Delta::Unlike(pid, user) => {
			// (F2) apply's like-row DELETE: the same (post_pid, user) filter chain.
			ok &= delete(likes::dsl::likes)
				.filter(
					likes::dsl::post_pid
						.eq(pid as i64)
						.and(likes::dsl::user.eq(user)),
				)
				.execute(conn)
				.is_ok();
		}
		Delta::TimePasses(sids) => {
			// (F2) patch_world revokes exactly the sids the payload carries, which is
			// (F2) apply's UPDATE for every session whose status changed: ONE write per
			// (F2) sid, same set-pair as the RevokeToken branch.
			for sid in sids.into_iter() {
				let (code, row_user) = enc_sess_row(SessionStatus::Revoked);
				ok &= update(sessions::dsl::sessions)
					.filter(sessions::dsl::sid.eq(sid as i64))
					.set((
						sessions::dsl::status.eq(code),
						sessions::dsl::user.eq(row_user),
					))
					.execute(conn)
					.is_ok();
			}
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
		// (F2) apply_delta is the Delta-driven batch under test; apply stays the reference.
		Account,
		Post,
		PostStatus,
		SessionStatus,
		Visibility,
		World,
		apply,
		apply_delta,
		init_or_open,
		load_world,
		posts,
		reload_accounts,
		reload_follows,
		reload_posts,
		reload_sessions,
		reopen,
		save_world,
	};
	// (F3) The test-local (pid, seq) peek below needs the Query trait (.select), so it pulls
	// (F3) the same prelude db.rs itself opens.
	use crate::model::empty_world;
	// (F2) the Delta sum-type and patch_world pin what apply_delta must reproduce.
	use crate::model::{Delta, patch_world};
	use diesel::prelude::*;

	/// Canonical well-formed World for the save/load tests; rows are pre-sorted in the
	/// order load_world returns them, so equality holds after a full save/reopen round-trip.
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

	/// init_or_open creates the DB file; load_world on a fresh DB gives the empty World.
	#[test]
	/// T3 gate: fresh database loads as the empty World.
	fn test_db_empty() {
		let mut conn = init_or_open("/tmp/ft-db-test-empty.sqlite".to_string()).unwrap();
		assert!(load_world(&mut conn) == empty_world());
	}

	/// save_world then reopen init_or_open + load_world: loaded == w (full round-trip).
	#[test]
	/// T3 gate: save_world then load_world reproduces the World exactly.
	fn test_db_roundtrip() {
		let path = "/tmp/ft-db-test-roundtrip.sqlite";
		let w = build_world();
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, w.clone());
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == w);
	}

	/// Reopening the same file twice yields equal Worlds (reentrancy).
	#[test]
	/// T3 gate: two reopened loads agree on the same DB file.
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

	/// A Revoked session row (NULL user) survives save+load.
	#[test]
	/// T3 gate: Revoked sessions (no user) are preserved.
	fn test_db_revoked_preserved() {
		let path = "/tmp/ft-db-test-revoked.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let mut again = init_or_open(path.to_string()).unwrap();
		let loaded = load_world(&mut again);
		assert!(loaded.sessions.len() == 2);
		assert!(loaded.sessions[1] == (200, SessionStatus::Revoked));
	}

	/// The after-World for the bounded-diff test: signup zoe (INSERT),
	/// session 100 Active->Revoked (UPDATE), 200 dropped (DELETE), 300 inserted
	/// (INSERT, Unused), post 1 liked by carol and replied to by pid 500 (whose
	/// parent stays 1), post 2 flipped to deleted, follows changed. Rows stay in
	/// load_world's canonical sorted order.
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
	/// T4 gate: apply on an empty DB (before = empty) INSERTs every row of after;
	/// new pids get seq = max_hint + 1 from scratch (hint 0 = empty DB), and reload
	/// reproduces after.
	fn test_apply_inserts_all() {
		let path = "/tmp/ft-apply-empty.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// Wipe first so the test is hermetic when the file already exists from an earlier run.
		save_world(&mut conn, empty_world());
		let after = build_world();
		// (F3) hint 0: the DB is empty, so the stamps run 1, 2, 3.
		let _ok = apply(&mut conn, &empty_world(), &after, 0);
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == after);
	}

	#[test]
	/// T4 gate: bounded diff from a saved before-world: INSERTs, UPDATEs (session
	/// status, post status, likes, replies, follows), DELETEs (session 200, follow
	/// (bob,alice)); reload equals after, newest_first [500,3,2,1] (newest-first
	/// preserved, existing seqs untouched) and the reply's parent is still 1.
	fn test_apply_diff() {
		let path = "/tmp/ft-apply-diff.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let before = build_world();
		let after = build_after();
		// (F3) hint 3: save_world above stamped the three posts with seqs 1..3, so the new
		// (F3) post 500 is stamped 4 and the existing seqs stay put.
		let _ok = apply(&mut conn, &before, &after, 3);
		assert!(load_world(&mut conn) == after);
		let mut again = init_or_open(path.to_string()).unwrap();
		assert!(load_world(&mut again) == after);
		assert!(load_world(&mut conn).newest_first == vec!(500, 3, 2, 1));
		assert!(load_world(&mut conn).posts[3].1.parent == Some(1));
	}
	#[test]
	/// DB3a gate: a clean diff COMMITs (apply returns true) and the new rows are visible
	/// from a brand-new connection, so write-through really reached the DB.
	fn test_apply_returns_true() {
		let path = "/tmp/ft-apply-true.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		save_world(&mut conn, build_world());
		let before = build_world();
		let after = build_after();
		// (F3) hint 3 matches the saved DB's max seq, so the diff stamps post 500 at seq 4.
		let committed = apply(&mut conn, &before, &after, 3);
		assert!(committed);
		assert!(load_world(&mut conn) == after);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == after);
	}

	/// (F9) gate: ONE connection answers MANY apply batches - serve_command keeps a single
	/// SqliteConnection alive in Server and reuses it every request.  Here one establish
	/// runs TWO successive commits (before -> after, after -> after2) through the SAME
	/// conn with no reopen between: both must COMMIT (a rollback would poison the chain
	/// and flip these asserts), and the reused conn - plus a fresh establish - must both
	/// end at after2.
	/// (F3) hint arithmetic: save stamped before's posts 1..3, batch one stamps post 500
	/// (F3) at seq 4, and batch two adds NO posts, so the cached hint stays exactly 4.
	/// (F3) Both hints must match the DB's max or apply would over/under-stamp and the
	/// (F3) final load_world compare would flip.
	#[test]
	fn test_apply_conn_reuse() {
		// (F9) exactly ONE establish for the whole test: Server.conn's lifecycle.
		let conn_path = "/tmp/ft-apply-conn-reuse.sqlite";
		// (F9) one reopen only - the SECOND connection below is the audit, never used for
		// (F9) an apply.
		let mut conn = init_or_open(conn_path.to_string()).unwrap();
		// hermetic wipe, then the seeded BEFORE the first batch updates from
		save_world(&mut conn, empty_world());
		save_world(&mut conn, build_world());
		let before = build_world();
		let after = build_after();
		// (F3) save_world above stamped before's three posts at 1..3, so batch one's hint
		// (F3) is 3.
		// batch one: before -> after through the held conn (F9: this is request N).
		// (F3) hint 3 stamps the diff's new post 500 at seq 4.
		// (F9) the SAME conn carries both batches: nothing re-established in between.
		// (F3) batch two's hint is after's max seq: post 500 took 4, so it stays 4.
		let batch_one: bool = apply(&mut conn, &before, &after, 3);
		// (F9) FIRST commit must succeed: the held conn stays usable for batch two.
		assert!(batch_one);
		// batch two: after -> after2 through the SAME conn (F9: request N+1).  The diff is
		// a session-status UPDATE (no new posts), so the cached hint stays exactly 4.
		// (F9) no reopen here - reuse means reuse.
		// after2 is the after World with session 100 flipped to Active: a one-field UPDATE
		// diff keeps the conn chain committed.
		// (F3) new_post_count is 0 here, so max_seq (the hint) does not move at all.
		// (F9) the rollback-vs-reopen question of the old failure arm is settled by these
		// (F9) two trues: the rollback path may keep the conn, no reopen needed.
		let mut after2 = after.clone();
		// (F9) flip one session status: the second diff.
		// (F3) no posts change, so stamps stay 1..4 and the hint stays 4.
		// (F9) this is the after -> after2 half of the chain.
		// (F9) (a stale-conn bug would make THIS apply false and flip the assert below)
		// (F9) sessions[0] is (100, Revoked) in after.
		after2.sessions[0].1 = SessionStatus::Active("tok".to_string());
		// (F3) hint 4 = after's max seq: exact, so batch two stamps nothing new.
		// (F9) same conn, second apply.
		let batch_two: bool = apply(&mut conn, &after, &after2, 4);
		// (F9) SECOND commit on the reused conn.
		assert!(batch_two);
		// the reused conn's own view already equals after2: both batches landed.
		// (F9) this is serve_state reading through Server.conn, not a fresh establish.
		// (F3) stamps stay 1..4; newest_first stays [500, 3, 2, 1].
		// (F9) final audit through a fresh establish: the DB agrees with the reused conn.
		// (F9) two views, one truth.
		let after2_on_disk = load_world(&mut conn) == after2;
		assert!(after2_on_disk);
		// (F9) and the fresh establish is only an audit, never used for an apply.
		let mut audit = reopen(conn_path.to_string()).unwrap();
		// (F9) same World through the SECOND connection: source of truth, once consulted.
		assert!(load_world(&mut audit) == after2);
		// (F3) the exact stamp order survived both batches on one conn: post 500 sits at
		// (F3) seq 4, so newest_first leads with it.
		assert!(load_world(&mut audit).newest_first == vec!(500, 3, 2, 1));
		// (F3) and the existing posts' seqs stayed put behind it.
		// (F9) sessions[0] now Active: batch two's UPDATE is in the DB, visible fresh.
		assert!(load_world(&mut audit).sessions[0].1 == SessionStatus::Active("tok".to_string()));
		// (F9) end of chain: two applies, one connection, one truth.
	}

	#[test]
	/// DB3a gate: the RAM cache lies (post 1 is missing from BEFORE, but the DB has it),
	/// so apply() re-INSERTs pid 1 and hits the PRIMARY KEY, then INSERTs its like and
	/// reply pairs (likes/replies have no PK, so they would leak). The batch must ROLLBACK:
	/// apply reports failure and the pre-state is intact on disk.
	fn test_apply_failure_rolls_back() {
		let path = "/tmp/ft-apply-rollback.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		let pre = build_world();
		save_world(&mut conn, pre.clone());
		let mut bad_before = build_world();
		bad_before.posts.retain(|entry| entry.0 != 1);
		let committed = apply(&mut conn, &bad_before, &pre, 3);
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
	/// TB REDO perf-scale gate: 500 posts (pids 1 to 500, ids also in used_post_ids, newest_first
	/// reversed) round-trip via save_world (seqs stamped 1 to 500), then apply of the diff with
	/// max_hint 500: delete pid 7, flip pid 11 to Deleted, insert pid 900 (seq 501 straight from
	/// the hint, never from an O(P) re-scan). Batch COMMITS, load_world equals after exactly
	/// (newest_first [900,500..8,6..1]) and a reopen loads it again.
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
		// (F3) hint 500: the 500 saved posts hold seqs 1..500, so pid 900 must land on 501.
		let committed = apply(&mut conn, &before, &after, 500);
		assert!(committed);
		assert!(load_world(&mut conn) == after);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == after);
	}

	/// (F3) Test-only peek at the DB's (pid, seq) rows, pid-sorted: apply() must never READ the
	/// (F3) seq column, but a test still has to see the stamps the caller's hint produced.
	fn seq_pairs(conn: &mut SqliteConnection) -> Vec<(i64, i64)> {
		let mut rows: Vec<(i64, i64)> = posts::dsl::posts
			.select((posts::dsl::pid, posts::dsl::seq))
			.load::<(i64, i64)>(conn)
			.unwrap_or_default();
		// (F3) DB row order is unspecified; sort by pid (then seq) so the pin is deterministic.
		rows.sort();
		rows
	}

	#[test]
	/// F3 gate: apply() stamps a new post VERBATIM at max_hint + 1, never from a DB re-scan.
	/// The seeded DB holds posts with seqs 1..5 (max 5), yet the call passes max_hint = 42,
	/// so the inserted pid 777 lands on seq 43 (the old fold scan would have said 6) and the
	/// five existing rows keep their stamps 1..5 untouched.  The batch COMMITs, and a fresh
	/// load reproduces the whole World with 777 heading newest_first (its seq is the highest).
	fn test_apply_max_hint() {
		let path = "/tmp/ft-apply-max-hint.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// Hermetic: the file can exist from an earlier run.
		save_world(&mut conn, empty_world());
		// Seed five posts; newest_first reversed makes save_world stamp pid 1..5 with seq 1..5.
		let mut seeded: World = empty_world();
		for index in 1..6 {
			let pid: u64 = index as u64;
			seeded.posts.push((
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
			seeded.newest_first.push(pid);
			seeded.used_post_ids.push(pid);
		}
		seeded.newest_first.reverse();
		// The DB must mirror `before` before apply() runs the diff.
		save_world(&mut conn, seeded.clone());
		// The DB's real max seq is 5, so a re-scan implementation would stamp the new post 6.
		assert!(seq_pairs(&mut conn) == vec![(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]);
		let mut after: World = seeded.clone();
		after.posts.push((
			777,
			Post {
				author: "alice".to_string(),
				text: "hinted".to_string(),
				visibility: Visibility::Everyone,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent: None,
			},
		));
		after.newest_first.insert(0, 777);
		after.used_post_ids.push(777);
		// (F3) hint 42 lies far above the DB's own max: the stamp must follow the hint.
		let committed: bool = apply(&mut conn, &seeded, &after, 42);
		assert!(committed);
		// (F3) 43 = 42 + 1 pins the hint used verbatim; the five old rows are untouched.
		assert!(seq_pairs(&mut conn) == vec![(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (777, 43)]);
		let mut fresh = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut fresh) == after);
	}
	#[test]
	/// F2 gate: a parent-less Publish emits ONE posts INSERT stamped max_hint + 1 and
	/// nothing else, so a fresh load equals patch_world's after and the new pid heads
	/// newest_first.
	fn test_apply_delta_publish() {
		let path = "/tmp/ft-delta-publish.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		// (F2) the DB must already mirror before: save stamps the three posts 1..3.
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) the effect-only payload: no parent, so no reply row either.
		let fresh: Delta = Delta::Publish(
			900,
			"alice".to_string(),
			"fresh".to_string(),
			Visibility::Everyone,
			None,
		);
		// (F2) patch_world pushes the post, prepends newest_first and grows used_post_ids.
		let after: World = patch_world(before.clone(), fresh.clone());
		// (F2) the batch COMMITs: the delta's one INSERT was accepted.
		assert!(apply_delta(&mut conn, &before, fresh, 3));
		assert!(load_world(&mut conn) == after);
		let mut again = init_or_open(path.to_string()).unwrap();
		// (F2) the source of truth agrees on a SECOND connection, so the row reached disk.
		assert!(load_world(&mut again) == after);
		// (F2) the row landed on the caller's stamp: the hint, plus one.
		assert!(seq_pairs(&mut conn) == vec![(1, 1), (2, 2), (3, 3), (900, 4)]);
		// (F2) the newest-first head is the new post and the older stamps stayed put.
		assert!(load_world(&mut again).newest_first == vec![900, 3, 2, 1]);
	}

	#[test]
	/// F2 gate: a Publish with a parent gains the replies-row INSERT too, so the DB holds
	/// BOTH halves of the spec's reply invariant.  patch_world only moves the child's
	/// parent field, so the RAM cache lags by that row and load_world is the spec's
	/// after: the parent gains the child in its replies list.
	fn test_apply_delta_publish_reply() {
		let path = "/tmp/ft-delta-reply.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		// (F2) the BEFORE world: post 1 already replies to by pid 2, stamped 1..3.
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) the effect carries the parent, so the reply row must be written too.
		let reply: Delta = Delta::Publish(
			900,
			"alice".to_string(),
			"me too".to_string(),
			Visibility::Everyone,
			Some(1),
		);
		// (F2) patch_world pushes the post (its own parent field) and never touches post 1.
		let cached: World = patch_world(before.clone(), reply.clone());
		// (F2) the spec's successful-reply after: the parent's list gains the child pid.
		let mut want: World = cached.clone();
		// (F2) post 1 is the first pid-sorted entry in the cache.
		assert!(want.posts[0].0 == 1);
		want.posts[0].1.replies.push(900);
		// (F2) the batch COMMITs: the posts INSERT plus the replies-row INSERT.
		assert!(apply_delta(&mut conn, &before, reply, 3));
		// (F2) load reads the reply row back: the parent's list carries the child.
		assert!(load_world(&mut conn) == want);
		let mut again = init_or_open(path.to_string()).unwrap();
		// (F2) the same truth on a second connection: the row really is on disk.
		assert!(load_world(&mut again) == want);
		// (F2) the child's parent column is the other half of the invariant.
		assert!(load_world(&mut again).posts[3].1.parent == Some(1));
		// (F2) the row keys on the PARENT post_pid: post 1's bucket holds 2 and 900.
		// (F2) the stamp is the hint plus one, so newest_first leads with the reply.
		assert!(load_world(&mut again).newest_first == vec![900, 3, 2, 1]);
		// (F2) the RAM cache rebuilt from the DB converges on the same replies list.
		assert!(reload_posts(&mut again, cached.clone()).posts[0].1.replies == vec![2, 900]);
	}

	#[test]
	/// F2 gate: Delete emits ONE posts UPDATE over apply's exact column pair (status AND
	/// visibility), never a row DELETE: the tombstone keeps its likes, replies, parent and
	/// seq, and a second Delete of the same pid is idempotent.
	fn test_apply_delta_delete() {
		let path = "/tmp/ft-delta-delete.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		// (F2) post 1 carries a liker, a reply and Everyone visibility: all must stay put.
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) patch_world flips the status to Deleted and touches nothing else.
		let gone: Delta = Delta::Delete(1);
		let after: World = patch_world(before.clone(), gone.clone());
		// (F2) one UPDATE: the row's visibility comes from the before-cache.
		assert!(apply_delta(&mut conn, &before, gone.clone(), 3));
		// (F2) load agrees with patch: status flips, likes/replies/parent stay put.
		assert!(load_world(&mut conn) == after);
		let mut again = init_or_open(path.to_string()).unwrap();
		let loaded: World = load_world(&mut again);
		// (F2) the tombstone survives: the spec's reap is commented out, so no DELETE.
		assert!(loaded.posts[0].1.status == PostStatus::Deleted);
		// (F2) the like row and the reply row still hang off the deleted post.
		assert!(loaded.posts[0].1.likes == vec!["bob".to_string()]);
		assert!(loaded.posts[0].1.replies == vec![2]);
		// (F2) visibility survived the UPDATE: apply writes that exact column pair.
		assert!(loaded.posts[0].1.visibility == Visibility::Everyone);
		// (F2) no stamp moved: an UPDATE never re-writes seq.
		assert!(seq_pairs(&mut again) == vec![(1, 1), (2, 2), (3, 3)]);
		// (F2) the held conn stays usable: an idempotent second Delete still COMMITS.
		// (F2) patch's retain-free loop is idempotent, so after2 equals after.
		assert!(apply_delta(&mut conn, &after, gone, 3));
		assert!(load_world(&mut conn) == after);
	}

	#[test]
	/// F2 gate: Follow INSERTs one follows row and Unfollow DELETEs the exact pair, so two
	/// successive deltas through the SAME held connection keep load_world equal to the
	/// patched cache - and an Unfollow of an absent pair deletes zero rows yet COMMITs.
	fn test_apply_delta_follow_unfollow() {
		let path = "/tmp/ft-delta-follows.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) follow one NEW pair: apply's follows-branch INSERT.
		let pair: Delta = Delta::Follow("carol".to_string(), "alice".to_string());
		// (F2) patch_world pushes the pair onto the follows list.
		let followed: World = patch_world(before.clone(), pair.clone());
		// (F2) no new post here, so the caller's hint stays 3 for every batch below.
		assert!(apply_delta(&mut conn, &before, pair, 3));
		// (F2) the cache and the DB move together.
		assert!(load_world(&mut conn) == followed);
		// (F2) unfollow the SAME pair through the SAME conn: apply's follows DELETE.
		// (F2) patch_world retains the pair out of the list.
		let off: Delta = Delta::Unfollow("carol".to_string(), "alice".to_string());
		let back: World = patch_world(followed.clone(), off.clone());
		// (F2) the filter chain hits the exact (follower, followee) row only.
		assert!(apply_delta(&mut conn, &followed, off, 3));
		// (F2) back where we started: every other edge stayed put.
		assert!(load_world(&mut conn) == back);
		assert!(back.follows == before.follows);
		// (F2) an absent pair: DELETE matches zero rows, which is not an error.
		// (F2) patch_world's retain is a no-op, so the cache is unchanged too.
		let ghost: Delta = Delta::Unfollow("ghost".to_string(), "alice".to_string());
		let same: World = patch_world(before.clone(), ghost.clone());
		assert!(apply_delta(&mut conn, &before, ghost, 3));
		assert!(load_world(&mut conn) == same);
		let mut again = init_or_open(path.to_string()).unwrap();
		// (F2) the disk agrees with the cache after all three batches.
		assert!(load_world(&mut again) == same);
	}

	#[test]
	/// F2 gate: a RAM-sampled pid that hits a stored PRIMARY KEY (Publish onto pid 2) and
	/// a signup on a stored username both report false after a ROLLBACK, with the DB byte-
	/// identical to the seeded world; the held conn then still COMMITs a good batch.
	fn test_apply_delta_collision() {
		let path = "/tmp/ft-delta-clash.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) a sampled pid that lands on the stored pid 2: INSERT hits the PRIMARY KEY.
		let clash: Delta = Delta::Publish(
			2,
			"bob".to_string(),
			"clash".to_string(),
			Visibility::Everyone,
			None,
		);
		// (F2) the failed statement ANDs a false into ok, so the batch rolls back.
		assert!(!apply_delta(&mut conn, &before, clash, 3));
		// (F2) the ROLLBACK restored every row: the DB is byte-identical to before.
		assert!(load_world(&mut conn) == before);
		// (F2) a signup onto a stored username clashes accounts' PRIMARY KEY too.
		let dupe: Delta = Delta::Register(
			"alice".to_string(),
			Account {
				password: "x".to_string(),
				default_visibility: Visibility::Everyone,
			},
		);
		// (F2) patch would push the account, so the cache says alice exists twice: the DB
		// (F2) must say NO, and it must stay exactly as it was.
		assert!(!apply_delta(&mut conn, &before, dupe, 3));
		assert!(load_world(&mut conn) == before);
		let mut fresh = reopen(path.to_string()).unwrap();
		// (F2) the second connection sees the same untouched truth.
		assert!(load_world(&mut fresh) == before);
		// (F2) the conn survived both rollbacks: a good Publish COMMITS next.
		// (F2) the hint stayed 3, so the stamp is still 4.
		let good: Delta = Delta::Publish(
			900,
			"alice".to_string(),
			"fresh".to_string(),
			Visibility::Everyone,
			Some(2),
		);
		let after: World = patch_world(before.clone(), good.clone());
		assert!(apply_delta(&mut conn, &before, good, 3));
		// (F2) the parent gains the reply row again, so the spec after is expected below.
		// (F2) load equals patch plus the reply row on post 2 (apply's replies INSERT).
		let mut want = after.clone();
		// (F2) the reply row keys on the PARENT post_pid, so post 2 gains pid 900.
		// (F2) patch pushed the post onto the pid-sorted list, so 900 is last.
		assert!(want.posts[1].0 == 2);
		want.posts[1].1.replies.push(900);
		// (F2) load agrees with the spec after, including the reply row.
		assert!(load_world(&mut conn) == want);
		// (F2) the two clashes moved no stamp, so the hint plus one still holds.
		assert!(seq_pairs(&mut conn) == vec![(1, 1), (2, 2), (3, 3), (900, 4)]);
	}

	#[test]
	/// F2 bonus gate: the session and like branches.  None_ and an empty TimePasses are
	/// zero-statement batches that still COMMIT; Authenticate INSERTs the Active row,
	/// RevokeToken and TimePasses UPDATE (2, NULL) per sid, Like INSERTs a like row and
	/// Unlike DELETEs it - every step keeps load_world equal to the patched cache.
	fn test_apply_delta_sessions_and_likes() {
		let path = "/tmp/ft-delta-sessions.sqlite";
		let mut conn = init_or_open(path.to_string()).unwrap();
		// hermetic wipe: the file can exist from an earlier run
		save_world(&mut conn, empty_world());
		save_world(&mut conn, build_world());
		let before: World = build_world();
		// (F2) None_ has no effect: zero statements, so the transaction COMMITs and says true.
		assert!(apply_delta(&mut conn, &before, Delta::None_, 3));
		assert!(load_world(&mut conn) == before);
		// (F2) TimePasses with no sid in the payload: still a zero-statement batch.
		assert!(apply_delta(
			&mut conn,
			&before,
			Delta::TimePasses(vec![]),
			3
		));
		assert!(load_world(&mut conn) == before);
		// (F2) TimePasses over both sids: one session UPDATE each, mirroring apply's UPDATE.
		// (F2) patch revokes exactly the sids the payload names (200 is already Revoked).
		let revoke_all: Delta = Delta::TimePasses(vec![100, 200]);
		let revoked: World = patch_world(before.clone(), revoke_all.clone());
		assert!(apply_delta(&mut conn, &before, revoke_all, 3));
		assert!(load_world(&mut conn) == revoked);
		// (F2) the Revoked row is (2, NULL): status AND user move together.
		// (F2) the row is written, never deleted: used_session_ids stays derived.
		assert!(load_world(&mut conn).sessions[0].1 == SessionStatus::Revoked);
		// (F2) Authenticate on a FRESH sid: apply's new-session INSERT of the (1, just u) row.
		let login: Delta = Delta::Authenticate(700, "alice".to_string());
		let signed_in: World = patch_world(revoked.clone(), login.clone());
		assert!(apply_delta(&mut conn, &revoked, login, 3));
		// (F2) patch pushes the Active session and its used sid in the same order load sorts.
		assert!(load_world(&mut conn) == signed_in);
		// (F2) logout on that session: apply's existing-sid UPDATE back to (2, NULL).
		let logout: Delta = Delta::RevokeToken(700);
		let signed_out: World = patch_world(signed_in.clone(), logout.clone());
		assert!(apply_delta(&mut conn, &signed_in, logout, 3));
		// (F2) load agrees: the same truth as patch's revoke.
		assert!(load_world(&mut conn) == signed_out);
		// (F2) like post 1 by a new liker: apply's likes-row INSERT.
		// (F2) patch appends the liker since it is not one yet.
		let like: Delta = Delta::Like(1, "zed".to_string());
		let liked: World = patch_world(signed_out.clone(), like.clone());
		assert!(apply_delta(&mut conn, &signed_out, like, 3));
		// (F2) load re-buckets the like row into Post.likes, sorted by user.
		assert!(
			load_world(&mut conn).posts[0].1.likes == vec!["bob".to_string(), "zed".to_string()]
		);
		// (F2) unlike: apply's like-row DELETE over the exact (post_pid, user) pair.
		let undo: Delta = Delta::Unlike(1, "zed".to_string());
		let unliked: World = patch_world(liked.clone(), undo.clone());
		assert!(apply_delta(&mut conn, &liked, undo, 3));
		// (F2) the posts row itself stayed put: likes live in their own table.
		// (F2) the same truth through a brand-new connection: every batch reached disk.
		let mut again = reopen(path.to_string()).unwrap();
		assert!(load_world(&mut again) == unliked);
	}
}
