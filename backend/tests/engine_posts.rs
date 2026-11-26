//! Property and unit tests for the post lifecycle engine (task T2b).
//!
//! Every property below is a direct rendering of a `Step` rule of
//! `spec/Twitter.agda`; the matching Agda lemma lives in `ImplProofs.agda`.
//! P1 (`publish` without a parent) is `successful-post` (Twitter.agda:387-398);
//! P2/P3 (`publish` with a parent) are `successful-reply` (400-422) including
//! the `new-reply` visibility rule (213-217); P4 is `failed-reply` (424-430);
//! P5/P6 are `delete-post` (432-449); P7 is
//! `failed-delete-non-existant-post` / `failed-delete-not-author` (451-462);
//! P8 (`read_post` with a session) is `read-post-logged-in` (540-548) and the
//! `cant-read-post-*` rules (518-538); P9 (`read_post` anonymously) is
//! `read-post-anonymously` (550-554); P10 is `failed-access` (464-468).
//!
//! Every property asserts both halves of the spec's `Step`: the `Result`, and
//! -- for the steps that change nothing -- that the whole persisted world is
//! byte-for-byte unchanged, or that exactly the one documented row changed.
//! State is seeded through `formal_twitter::store`, never through the engine,
//! so the snapshot deltas are attributable to the command under test alone.
//!
//! `read-post nothing` is also covered on the failing side, and not by a
//! "deviation": `extract-sid (read-post msid _) = msid` (Twitter.agda:196) is
//! `nothing` here, so the premise of `failed-access` (Twitter.agda:464-468) --
//! "for every `sid`, `extract-sid cmd ≡ just sid` implies no valid session" --
//! is VACUOUS for this command, since `nothing ≢ just sid`. Hence
//! `Step before (read-post nothing pid) before expired` is derivable in every
//! world, and an anonymous read of an absent, `followers-only` or deleted post
//! answers `Expired` (proved as `read-anonymous-expired`), not `Denied`.

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Text};
use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::posts::{delete, publish, read_post};
use formal_twitter::model::{
	Account, Post, PostId, PostStatus, SessionId, SessionStatus, Visibility,
};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

// ---------------------------------------------------------------------------
// Harness: an in-memory database, plus read-only views of it.
//
// Snapshots are sorted in Rust on the *composed* line, never in SQL: `'|'`
// (0x7C) sorts after every letter and digit, so `ORDER BY` on one column and a
// sort of `a|b|c` disagree whenever one field is a prefix of another. The
// properties build their expected lines in Rust and sort them the same way.
// ---------------------------------------------------------------------------

const OTHER_PASSWORD: &str = "other-secret";

fn database() -> Db {
	Db::in_memory().expect("create in-memory database")
}

fn account_of(db: &Db, username: &str) -> Option<Account> {
	db.read(|conn| store::get_account(conn, username))
		.expect("read account")
}

fn status_of(db: &Db, sid: SessionId) -> SessionStatus {
	db.read(|conn| store::get_session(conn, sid))
		.expect("read session")
}

fn post_of(db: &Db, pid: PostId) -> Option<Post> {
	db.read(|conn| store::get_post(conn, pid))
		.expect("read post")
}

fn replies_of(db: &Db, pid: PostId) -> Vec<PostId> {
	db.read(|conn| store::replies_of(conn, pid))
		.expect("read replies")
}

fn like_count(db: &Db, pid: PostId) -> i64 {
	db.read(|conn| store::like_count(conn, pid))
		.expect("read like count")
}

/// The whole `newest-first` order of the spec (Twitter.agda:74).
fn newest_first(db: &Db) -> Vec<PostId> {
	db.read(|conn| store::newest_first(conn, u32::MAX))
		.expect("read newest-first")
}

#[derive(QueryableByName)]
struct CountRow {
	#[diesel(sql_type = BigInt)]
	count: i64,
}

fn row_count(db: &Db, table: &str) -> i64 {
	let sql = format!("SELECT COUNT(*) AS count FROM {table}");
	db.read(|conn| {
		let row: CountRow = diesel::sql_query(sql).get_result(conn)?;
		Ok(row.count)
	})
	.expect("count query")
}

#[derive(QueryableByName)]
struct LineRow {
	#[diesel(sql_type = Text)]
	line: String,
}

fn sorted_lines(db: &Db, sql: &str) -> Vec<String> {
	let mut out = db
		.read(|conn| {
			let rows: Vec<LineRow> = diesel::sql_query(sql.to_owned()).load(conn)?;
			Ok(rows
				.into_iter()
				.map(|row| row.line)
				.collect::<Vec<String>>())
		})
		.expect("dump query");
	out.sort_unstable();
	out
}

fn accounts_snapshot(db: &Db) -> Vec<String> {
	sorted_lines(
		db,
		"SELECT username || '|' || password || '|' || default_visibility AS line \
		 FROM accounts",
	)
}

fn sessions_snapshot(db: &Db) -> Vec<String> {
	sorted_lines(
		db,
		"SELECT CAST(id AS TEXT) || '|' || status || '|' || username AS line \
		 FROM sessions",
	)
}

fn posts_snapshot(db: &Db) -> Vec<String> {
	sorted_lines(
		db,
		"SELECT CAST(id AS TEXT) || '|' || author || '|' || text || '|' || visibility \
		 || '|' || status || '|' || COALESCE(CAST(parent AS TEXT), '') AS line \
		 FROM posts",
	)
}

fn follows_snapshot(db: &Db) -> Vec<String> {
	sorted_lines(
		db,
		"SELECT follower || '|' || followee AS line FROM follows",
	)
}

fn likes_snapshot(db: &Db) -> Vec<String> {
	sorted_lines(
		db,
		"SELECT CAST(pid AS TEXT) || '|' || user AS line FROM post_likes",
	)
}

/// The whole persisted world rendered as text, table groups separated by
/// markers. This is how the properties check the "everything else unchanged"
/// premises of the spec's steps (e.g. Twitter.agda:391-395).
fn world(db: &Db) -> Vec<String> {
	let mut out = accounts_snapshot(db);
	out.push("--sessions--".to_string());
	out.extend(sessions_snapshot(db));
	out.push("--posts--".to_string());
	out.extend(posts_snapshot(db));
	out.push("--follows--".to_string());
	out.extend(follows_snapshot(db));
	out.push("--likes--".to_string());
	out.extend(likes_snapshot(db));
	out
}

/// One `posts_snapshot` line.
fn post_line(
	id: PostId,
	author: &str,
	text: &str,
	visibility: Visibility,
	status: PostStatus,
	parent: Option<PostId>,
) -> String {
	let visibility = match visibility {
		Visibility::Everyone => "everyone",
		Visibility::FollowersOnly => "followers-only",
	};
	let status = match status {
		PostStatus::Live => "live",
		PostStatus::Deleted => "deleted",
	};
	let parent = parent.map(|p| p.0.to_string()).unwrap_or_default();
	format!("{}|{author}|{text}|{visibility}|{status}|{parent}", id.0)
}

// ---------------------------------------------------------------------------
// Seeding. All state goes in through `store`, never through the engine.
// ---------------------------------------------------------------------------

fn seed_account(db: &Db, name: &str) {
	assert!(
		db.write(|conn| store::create_account(conn, name, OTHER_PASSWORD))
			.expect("seed account"),
		"precondition: {name} is a free username"
	);
}

fn seed_session(db: &Db, sid: SessionId, name: &str) {
	db.write(|conn| store::activate_session(conn, sid, name))
		.expect("seed session");
}

fn seed_revoked_session(db: &Db, sid: SessionId, name: &str) {
	seed_session(db, sid, name);
	db.write(|conn| store::revoke_session(conn, sid))
		.expect("revoke seeded session");
}

fn seed_post(db: &Db, id: PostId, author: &str, text: &str, vis: Visibility) {
	db.write(|conn| store::insert_post(conn, id, author, text, vis))
		.expect("seed post");
}

fn seed_reply(db: &Db, id: PostId, author: &str, text: &str, vis: Visibility, parent: PostId) {
	db.write(|conn| store::insert_reply(conn, id, author, text, vis, parent))
		.expect("seed reply");
}

fn seed_delete(db: &Db, id: PostId) {
	db.write(|conn| store::soft_delete_post(conn, id))
		.expect("seed deletion");
}

fn seed_follow(db: &Db, follower: &str, followee: &str) {
	db.write(|conn| store::add_follow(conn, follower, followee))
		.expect("seed follow");
}

fn seed_like(db: &Db, id: PostId, user: &str) {
	db.write(|conn| store::add_like(conn, id, user))
		.expect("seed like");
}

// ---------------------------------------------------------------------------
// Generated data: small strings over a line-safe alphabet.
// ---------------------------------------------------------------------------

const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&*";

fn small_string(g: &mut Gen) -> String {
	let len = 1 + usize::arbitrary(g) % 8;
	let mut out = String::with_capacity(len);
	for _ in 0..len {
		let index = usize::arbitrary(g) % ALPHABET.len();
		out.push(ALPHABET[index] as char);
	}
	out
}

#[derive(Clone, Debug)]
struct Name(String);

#[derive(Clone, Debug)]
struct Body(String);

/// A small count, used for the number of seeded likes.
#[derive(Clone, Debug)]
struct Pad(u8);

impl Arbitrary for Name {
	fn arbitrary(g: &mut Gen) -> Self {
		Name(small_string(g))
	}
}

impl Arbitrary for Body {
	fn arbitrary(g: &mut Gen) -> Self {
		Body(small_string(g))
	}
}

impl Arbitrary for Pad {
	fn arbitrary(g: &mut Gen) -> Self {
		Pad(u8::arbitrary(g))
	}
}

// ---------------------------------------------------------------------------
// Seeded ids. Small constants keep the seeded world legible; `publish`
// allocates its own ids from the whole i64 range, so it never reuses one.
// ---------------------------------------------------------------------------

const SID: SessionId = SessionId(100);
const REVOKED_SID: SessionId = SessionId(101);
const PARENT: PostId = PostId(200);
const REPLY_1: PostId = PostId(201);
const REPLY_2: PostId = PostId(202);
const STRANGER: PostId = PostId(203);
const OWN: PostId = PostId(300);
const CHILD: PostId = PostId(301);
const ABSENT: PostId = PostId(9_000_000);

fn created(result: EngineResult) -> PostId {
	match result {
		EngineResult::CreatedPost(pid) => pid,
		other => panic!("expected CreatedPost, got {other:?}"),
	}
}

fn returned(result: EngineResult) -> (String, String, u64, Vec<PostId>) {
	match result {
		EngineResult::ReturnedPost {
			author,
			text,
			likes,
			replies,
		} => (author, text, likes, replies),
		other => panic!("expected ReturnedPost, got {other:?}"),
	}
}

// ---------------------------------------------------------------------------
// P1: publish without a parent -- `successful-post` (Twitter.agda:387-398)
// ---------------------------------------------------------------------------

/// `successful-post`: a fresh id holds `new-post username txt user` -- the
/// author's text with `default-visibility` of the session's account, `live`,
/// no parent, no likes and no replies -- that id heads `newest-first`, and
/// every account, session, post, follow and like that existed before is
/// untouched.
#[quickcheck]
fn publish_creates_post(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	// Unrelated rows the new post must not disturb.
	seed_post(&db, STRANGER, &other.0, "stranger", Visibility::Everyone);
	seed_reply(
		&db,
		REPLY_1,
		&other.0,
		"old reply",
		Visibility::Everyone,
		STRANGER,
	);
	seed_follow(&db, &other.0, &name.0);
	seed_like(&db, STRANGER, &name.0);

	let default = account_of(&db, &name.0)
		.expect("account")
		.default_visibility;
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let mut posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	let pid = created(publish(&db, SID, &body.0, None).expect("publish"));

	// PostIsNew ...
	let post = post_of(&db, pid).expect("new post is stored");
	assert_eq!(post.author, name.0);
	assert_eq!(post.text, body.0);
	assert_eq!(post.visibility, default);
	assert_eq!(post.status, PostStatus::Live);
	assert_eq!(post.parent, None);
	// `new-post` starts with empty reply and like lists.
	assert_eq!(replies_of(&db, pid), Vec::new());
	assert_eq!(like_count(&db, pid), 0);

	// ... and `pid ∷ newest-first before ≡ newest-first after`.
	let mut order_expected = vec![pid];
	order_expected.extend(order_before);
	assert_eq!(newest_first(&db), order_expected);

	// Everything else unchanged, plus exactly this one post row.
	posts_before.push(post_line(
		pid,
		&name.0,
		&body.0,
		default,
		PostStatus::Live,
		None,
	));
	posts_before.sort_unstable();
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	assert_eq!(row_count(&db, "posts"), 3);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P2/P3: publish with a parent -- `successful-reply` (Twitter.agda:400-422)
// ---------------------------------------------------------------------------

/// `successful-reply` on a public live parent: the reply takes the account's
/// `default-visibility`, points at the parent, and is prepended to the
/// parent's reply list; no other row changes.
#[quickcheck]
fn reply_to_public_parent_creates_reply(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "parent", Visibility::Everyone);
	seed_reply(&db, REPLY_1, &other.0, "one", Visibility::Everyone, PARENT);
	seed_reply(&db, REPLY_2, &other.0, "two", Visibility::Everyone, PARENT);

	let default = account_of(&db, &name.0)
		.expect("account")
		.default_visibility;
	let parent_before = post_of(&db, PARENT).expect("parent");
	// `World.newest-first` order, oldest last.
	let replies_before = vec![REPLY_2, REPLY_1];
	assert_eq!(replies_of(&db, PARENT), replies_before);
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let mut posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	let pid = created(publish(&db, SID, &body.0, Some(PARENT)).expect("publish"));
	// `successful-reply` requires a fresh post (Twitter.agda:400-422: `pid ≢ ppid`).
	assert_ne!(pid, PARENT, "a reply never reuses its parent's id");

	// `new-reply` of an `everyone` parent: the account's default visibility.
	let post = post_of(&db, pid).expect("new reply is stored");
	assert_eq!(post.author, name.0);
	assert_eq!(post.text, body.0);
	assert_eq!(post.visibility, default);
	assert_eq!(post.status, PostStatus::Live);
	assert_eq!(post.parent, Some(PARENT));
	assert_eq!(replies_of(&db, pid), Vec::new());
	assert_eq!(like_count(&db, pid), 0);

	// The parent keeps every column; only its reply rows gain `pid`.
	assert_eq!(post_of(&db, PARENT).expect("parent"), parent_before);
	let mut replies_expected = vec![pid];
	replies_expected.extend(replies_before);
	assert_eq!(replies_of(&db, PARENT), replies_expected);

	// `pid ∷ newest-first before ≡ newest-first after`.
	let mut order_expected = vec![pid];
	order_expected.extend(order_before);
	assert_eq!(newest_first(&db), order_expected);

	// Everything else unchanged, plus exactly this one post row.
	posts_before.push(post_line(
		pid,
		&name.0,
		&body.0,
		default,
		PostStatus::Live,
		Some(PARENT),
	));
	posts_before.sort_unstable();
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	TestResult::passed()
}

/// `successful-reply` on a `followers-only` live parent the author follows:
/// `new-reply` (Twitter.agda:213-217) forces `followers-only` on the reply even
/// though the account's default is `everyone`.
#[quickcheck]
fn reply_to_followed_private_parent_is_private(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "parent", Visibility::FollowersOnly);
	seed_follow(&db, &name.0, &other.0);

	// Precondition for the rule to be visible: the account default is the
	// permissive one.
	assert_eq!(
		account_of(&db, &name.0)
			.expect("account")
			.default_visibility,
		Visibility::Everyone
	);
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let mut posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	let pid = created(publish(&db, SID, &body.0, Some(PARENT)).expect("publish"));
	// `successful-reply` requires a fresh post (Twitter.agda:400-422: `pid ≢ ppid`).
	assert_ne!(pid, PARENT, "a reply never reuses its parent's id");

	let post = post_of(&db, pid).expect("new reply is stored");
	assert_eq!(post.author, name.0);
	assert_eq!(post.text, body.0);
	assert_eq!(
		post.visibility,
		Visibility::FollowersOnly,
		"a followers-only parent forces a followers-only reply"
	);
	assert_eq!(post.status, PostStatus::Live);
	assert_eq!(post.parent, Some(PARENT));
	assert_eq!(replies_of(&db, PARENT), vec![pid]);

	let mut order_expected = vec![pid];
	order_expected.extend(order_before);
	assert_eq!(newest_first(&db), order_expected);

	posts_before.push(post_line(
		pid,
		&name.0,
		&body.0,
		Visibility::FollowersOnly,
		PostStatus::Live,
		Some(PARENT),
	));
	posts_before.sort_unstable();
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P4: failed reply -- `failed-reply` (Twitter.agda:424-430)
// ---------------------------------------------------------------------------

/// `failed-reply` when the parent is absent: `denied`, world untouched.
#[quickcheck]
fn reply_to_absent_parent_is_denied(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, STRANGER, &other.0, "stranger", Visibility::Everyone);
	let before = world(&db);

	assert_eq!(
		publish(&db, SID, &body.0, Some(ABSENT)).expect("publish"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a failed reply must not change the world"
	);
	TestResult::passed()
}

/// `failed-reply` when the parent is deleted: `denied`, world untouched.
#[quickcheck]
fn reply_to_deleted_parent_is_denied(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "parent", Visibility::Everyone);
	seed_delete(&db, PARENT);
	let before = world(&db);

	assert_eq!(
		publish(&db, SID, &body.0, Some(PARENT)).expect("publish"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a failed reply must not change the world"
	);
	TestResult::passed()
}

/// `failed-reply` when the parent is `followers-only` and the author does not
/// follow the parent's author: `denied`, world untouched.
#[quickcheck]
fn reply_to_unfollowed_private_parent_is_denied(name: Name, other: Name, body: Body) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "parent", Visibility::FollowersOnly);
	// A follow in the other direction must not help.
	seed_follow(&db, &other.0, &name.0);
	let before = world(&db);

	assert_eq!(
		publish(&db, SID, &body.0, Some(PARENT)).expect("publish"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a failed reply must not change the world"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P5/P6: delete -- `delete-post` (Twitter.agda:432-449)
// ---------------------------------------------------------------------------

/// `delete-post`: the author's live post becomes `deleted`; author, text,
/// visibility, parent, likes and replies are unchanged, and so is every other
/// row. There is no `live` premise on `delete-post`, which P6 exercises.
#[quickcheck]
fn delete_own_live_post_succeeds(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, OWN, &name.0, "mine", Visibility::FollowersOnly);
	seed_reply(&db, CHILD, &other.0, "child", Visibility::Everyone, OWN);
	seed_like(&db, OWN, &other.0);
	seed_like(&db, OWN, "third-party");
	seed_follow(&db, &other.0, &name.0);

	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let mut posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(
		delete(&db, SID, OWN).expect("delete"),
		EngineResult::Success
	);

	// Only `status` changed on the post itself.
	let post = post_of(&db, OWN).expect("post row is kept");
	assert_eq!(post.id, OWN);
	assert_eq!(post.author, name.0);
	assert_eq!(post.text, "mine");
	assert_eq!(post.visibility, Visibility::FollowersOnly);
	assert_eq!(post.parent, None);
	assert_eq!(post.status, PostStatus::Deleted);
	// ... including its likes and replies.
	assert_eq!(like_count(&db, OWN), 2);
	assert_eq!(replies_of(&db, OWN), vec![CHILD]);

	let live = post_line(
		OWN,
		&name.0,
		"mine",
		Visibility::FollowersOnly,
		PostStatus::Live,
		None,
	);
	let deleted = post_line(
		OWN,
		&name.0,
		"mine",
		Visibility::FollowersOnly,
		PostStatus::Deleted,
		None,
	);
	let position = posts_before
		.iter()
		.position(|line| *line == live)
		.expect("the live row is in the snapshot");
	posts_before[position] = deleted;
	posts_before.sort_unstable();
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `delete-post` has no `live` premise, so deleting an already `deleted` post
/// by its author succeeds and changes nothing at all.
#[quickcheck]
fn delete_already_deleted_post_succeeds(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, OWN, &name.0, "mine", Visibility::Everyone);
	seed_delete(&db, OWN);
	let before = world(&db);

	assert_eq!(
		delete(&db, SID, OWN).expect("delete"),
		EngineResult::Success
	);
	assert_eq!(world(&db), before, "an idempotent delete changes nothing");
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P7: failed deletes (Twitter.agda:451-462)
// ---------------------------------------------------------------------------

/// `failed-delete-non-existant-post`: an absent post is `denied` (not an
/// error) and the world is untouched.
#[quickcheck]
fn delete_absent_post_is_denied(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, STRANGER, &other.0, "stranger", Visibility::Everyone);
	let before = world(&db);

	assert_eq!(
		delete(&db, SID, ABSENT).expect("delete"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a failed delete must not change the world"
	);
	TestResult::passed()
}

/// `failed-delete-not-author`: someone else's post is `denied` and untouched,
/// even when the author follows the deleter.
#[quickcheck]
fn delete_foreign_post_is_denied(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, STRANGER, &other.0, "stranger", Visibility::Everyone);
	seed_follow(&db, &other.0, &name.0);
	let before = world(&db);

	assert_eq!(
		delete(&db, SID, STRANGER).expect("delete"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a failed delete must not change the world"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P8: read-post with a session (Twitter.agda:518-548)
// ---------------------------------------------------------------------------

/// `read-post-logged-in` for a public live post: `returned-post author txt
/// (length likes) replies`. `likes` is the number of like rows and `replies`
/// is the parent's reply list, newest first. A read changes nothing.
#[quickcheck]
fn read_public_post_logged_in(name: Name, other: Name, pad: Pad) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "hello", Visibility::Everyone);
	seed_reply(&db, REPLY_1, &other.0, "a", Visibility::Everyone, PARENT);
	seed_reply(&db, REPLY_2, &other.0, "b", Visibility::Everyone, PARENT);
	let likes = pad.0 % 4;
	for index in 0..likes {
		seed_like(&db, PARENT, &format!("liker{index}"));
	}
	// `newest-first` order: the most recently inserted reply heads the list.
	let expected_replies = vec![REPLY_2, REPLY_1];
	assert_eq!(replies_of(&db, PARENT), expected_replies);
	assert_eq!(like_count(&db, PARENT), i64::from(likes));
	let before = world(&db);

	let (author, text, reported_likes, replies) =
		returned(read_post(&db, Some(SID), PARENT).expect("read-post"));
	assert_eq!(author, other.0);
	assert_eq!(text, "hello");
	assert_eq!(reported_likes, u64::from(likes));
	assert_eq!(replies, expected_replies);
	assert_eq!(world(&db), before, "a read must not change the world");
	TestResult::passed()
}

/// `read-post-logged-in` via `post-is-private`: a `followers-only` live post
/// is readable when the session's user follows its author, with the same
/// `returned-post` shape.
#[quickcheck]
fn read_private_post_logged_in_when_following(name: Name, other: Name, pad: Pad) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "secret", Visibility::FollowersOnly);
	seed_follow(&db, &name.0, &other.0);
	let likes = pad.0 % 3;
	for index in 0..likes {
		seed_like(&db, PARENT, &format!("liker{index}"));
	}
	let before = world(&db);

	let (author, text, reported_likes, replies) =
		returned(read_post(&db, Some(SID), PARENT).expect("read-post"));
	assert_eq!(author, other.0);
	assert_eq!(text, "secret");
	assert_eq!(reported_likes, u64::from(likes));
	assert_eq!(replies, Vec::new());
	assert_eq!(world(&db), before);
	TestResult::passed()
}

/// `cant-read-post-private`: `followers-only` and not followed -- `denied`,
/// world untouched.
#[quickcheck]
fn read_private_post_without_follow_is_denied(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "secret", Visibility::FollowersOnly);
	seed_follow(&db, &other.0, &name.0);
	let before = world(&db);

	assert_eq!(
		read_post(&db, Some(SID), PARENT).expect("read-post"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a denied read must not change the world"
	);
	TestResult::passed()
}

/// `cant-read-post-private-deleted`: a deleted post is `denied` for a logged-in
/// reader, world untouched.
#[quickcheck]
fn read_deleted_post_is_denied(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, PARENT, &other.0, "gone", Visibility::Everyone);
	seed_delete(&db, PARENT);
	let before = world(&db);

	assert_eq!(
		read_post(&db, Some(SID), PARENT).expect("read-post"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a denied read must not change the world"
	);
	TestResult::passed()
}

/// `cant-read-post-public`: an absent post is `denied` for a logged-in reader,
/// world untouched.
#[quickcheck]
fn read_absent_post_is_denied(name: Name, other: Name) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_post(&db, STRANGER, &other.0, "stranger", Visibility::Everyone);
	let before = world(&db);

	assert_eq!(
		read_post(&db, Some(SID), ABSENT).expect("read-post"),
		EngineResult::Denied
	);
	assert_eq!(
		world(&db),
		before,
		"a denied read must not change the world"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P9: read-post anonymously -- `read-post-anonymously` (Twitter.agda:550-554)
//
// The readable case is `read-post-anonymously`; the unreadable cases are
// `failed-access` (Twitter.agda:464-468), whose premise is vacuous because
// `extract-sid (read-post nothing pid) = nothing` (Twitter.agda:196). Agda:
// `read-anonymous` and `read-anonymous-expired`.
// ---------------------------------------------------------------------------

/// `read-post-anonymously`: a public live post is returned with its author,
/// text, like count and reply list, without a session and without a change.
#[quickcheck]
fn read_public_post_anonymously(name: Name, other: Name, pad: Pad) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_post(&db, PARENT, &other.0, "public", Visibility::Everyone);
	seed_reply(&db, REPLY_1, &name.0, "a", Visibility::Everyone, PARENT);
	let likes = pad.0 % 3;
	for index in 0..likes {
		seed_like(&db, PARENT, &format!("liker{index}"));
	}
	let before = world(&db);

	let (author, text, reported_likes, replies) =
		returned(read_post(&db, None, PARENT).expect("read-post"));
	assert_eq!(author, other.0);
	assert_eq!(text, "public");
	assert_eq!(reported_likes, u64::from(likes));
	assert_eq!(replies, vec![REPLY_1]);
	assert_eq!(world(&db), before);
	TestResult::passed()
}

/// Anonymous reads of an absent, `followers-only` or deleted post are
/// `Expired` and change nothing: `extract-sid (read-post nothing pid) = nothing`
/// (Twitter.agda:196), so `failed-access` (Twitter.agda:464-468) applies
/// vacuously and `Step before (read-post nothing pid) before expired` holds
/// (Agda: `read-anonymous-expired`).
#[test]
fn anonymous_reads_of_unreadable_posts_expire() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, PARENT, "ada", "secret", Visibility::FollowersOnly);
	seed_post(&db, STRANGER, "ada", "gone", Visibility::Everyone);
	seed_delete(&db, STRANGER);
	let before = world(&db);

	for pid in [ABSENT, PARENT, STRANGER] {
		assert_eq!(
			read_post(&db, None, pid).expect("read-post"),
			EngineResult::Expired,
			"anonymous read of {pid:?}"
		);
	}
	assert_eq!(
		world(&db),
		before,
		"an expired read must not change the world"
	);
}

// ---------------------------------------------------------------------------
// P10: failed-access on every post command (Twitter.agda:464-468)
// ---------------------------------------------------------------------------

/// `failed-access`: every post command that carries a session answers `expired`
/// and leaves the world untouched when its session is revoked or was never
/// issued. `publish`, `delete` and `read-post (just sid)` all extract a session
/// (Twitter.agda:181-197); `read-post nothing` has none, not even the spec.
#[quickcheck]
fn expired_session_keeps_the_world(name: Name, other: Name, body: Body, pad: Pad) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_account(&db, &name.0);
	seed_session(&db, SID, &name.0);
	seed_revoked_session(&db, REVOKED_SID, &other.0);
	seed_post(&db, PARENT, &other.0, "parent", Visibility::Everyone);
	// Outside `SID`/`REVOKED_SID`, so it is genuinely unused.
	let unused = SessionId(1 + i64::from(pad.0 % 90));
	assert_eq!(status_of(&db, unused), SessionStatus::Unused);
	let before = world(&db);

	for sid in [REVOKED_SID, unused] {
		assert_eq!(
			publish(&db, sid, &body.0, None).expect("publish"),
			EngineResult::Expired,
			"publish with {sid:?}"
		);
		assert_eq!(world(&db), before, "an expired request changes nothing");

		assert_eq!(
			delete(&db, sid, PARENT).expect("delete"),
			EngineResult::Expired,
			"delete with {sid:?}"
		);
		assert_eq!(world(&db), before, "an expired request changes nothing");

		assert_eq!(
			read_post(&db, Some(sid), PARENT).expect("read-post"),
			EngineResult::Expired,
			"read-post with {sid:?}"
		);
		assert_eq!(world(&db), before, "an expired request changes nothing");
	}
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// Deterministic unit tests: cases where generation adds nothing.
//
// `store::create_account` always stamps `default-visibility = everyone`, so the
// "an `everyone` parent yields the account default" half of `new-reply` can
// only be observed through the stored default; the discriminating half is the
// `followers-only` parent above.
// ---------------------------------------------------------------------------

/// The reply list reported by `read-post` is the parent's `newest-first`
/// order, and `likes` is a count, not the like list.
#[test]
fn read_reports_likes_as_a_count_and_replies_newest_first() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_session(&db, SID, "bob");
	seed_post(&db, PARENT, "ada", "hello", Visibility::Everyone);
	for reply in [REPLY_1, REPLY_2] {
		seed_reply(&db, reply, "ada", "reply", Visibility::Everyone, PARENT);
	}
	for liker in ["bob", "carol", "dave"] {
		seed_like(&db, PARENT, liker);
	}
	assert_eq!(
		read_post(&db, Some(SID), PARENT).unwrap(),
		EngineResult::ReturnedPost {
			author: "ada".to_string(),
			text: "hello".to_string(),
			likes: 3,
			replies: vec![REPLY_2, REPLY_1],
		}
	);
}

/// A reply is inserted at the head of the parent's reply list, in the order the
/// replies arrive.
#[test]
fn replies_are_prepended_in_arrival_order() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_session(&db, SID, "bob");
	seed_post(&db, PARENT, "ada", "hello", Visibility::Everyone);

	let first = created(publish(&db, SID, "one", Some(PARENT)).unwrap());
	let second = created(publish(&db, SID, "two", Some(PARENT)).unwrap());
	assert_ne!(first, second);
	assert_eq!(replies_of(&db, PARENT), vec![second, first]);
	assert_eq!(
		post_of(&db, first).unwrap().parent,
		Some(PARENT),
		"the reply points at its parent"
	);
}

/// A deleted post still owns its id: a fresh publish gets a different one, the
/// tombstone keeps its status and likes, and unrelated replies are untouched.
#[test]
fn delete_keeps_the_tombstone() {
	let db = database();
	seed_account(&db, "ada");
	seed_session(&db, SID, "ada");
	seed_post(&db, PARENT, "ada", "hello", Visibility::Everyone);
	seed_post(&db, OWN, "ada", "mine", Visibility::Everyone);
	seed_reply(&db, REPLY_1, "ada", "reply", Visibility::Everyone, PARENT);
	seed_like(&db, OWN, "bob");

	assert_eq!(delete(&db, SID, OWN).unwrap(), EngineResult::Success);
	let fresh = created(publish(&db, SID, "new", None).unwrap());
	assert_ne!(fresh, OWN, "a tombstone still occupies its id");
	assert_eq!(post_of(&db, OWN).unwrap().status, PostStatus::Deleted);
	assert_eq!(like_count(&db, OWN), 1);
	assert_eq!(
		replies_of(&db, PARENT),
		vec![REPLY_1],
		"a top-level publish adds no reply"
	);
}
