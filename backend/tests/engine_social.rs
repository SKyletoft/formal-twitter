//! Property tests for the social actions engine (task T3a).
//!
//! Every property below is a direct rendering of a `Step` rule of
//! `spec/Twitter.agda`; the matching Agda lemma lives in `ImplProofs.agda`
//! (P12 `follows-world`/`follow-success`/`unfollows-world`/`unfollow-success`,
//! P13 `liked-world`/`like-success`/`unliked-world`/`unlike-success` with
//! `like-denied`/`unlike-denied`, and P14's four `*-expired` lemmas):
//!
//! * S1 `follow` is `follow-user` (Twitter.agda:655-664);
//! * S2 `unfollow` is `unfollow-user` (Twitter.agda:666-675);
//! * S3 `like` is `like-post` (Twitter.agda:587-613) and `failed-like-post`
//!   (Twitter.agda:615-619);
//! * S4 `unlike` is `unlike-post` (Twitter.agda:621-647) and
//!   `failed-unlike-post` (Twitter.agda:649-653);
//! * S5 all four commands on an inactive session are `failed-access`
//!   (Twitter.agda:464-468).
//!
//! Every property asserts both halves of the spec's `Step`: the `Result`, and
//! -- for the steps that change something -- the exact row delta, or, for
//! `denied`/`expired`, that the whole persisted world is byte-for-byte
//! unchanged. State is seeded through `formal_twitter::store`, never through
//! the engine, so the deltas are attributable to the command under test alone.

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Text};
use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::social::{follow, like, unfollow, unlike};
use formal_twitter::model::{Post, PostId, SessionId, SessionStatus, Visibility};
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

fn account_is_absent(db: &Db, username: &str) -> bool {
	db.read(|conn| store::get_account(conn, username))
		.expect("read account")
		.is_none()
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

fn is_following(db: &Db, follower: &str, followee: &str) -> bool {
	db.read(|conn| store::is_following(conn, follower, followee))
		.expect("read follow")
}

fn is_liked(db: &Db, pid: PostId, user: &str) -> bool {
	db.read(|conn| store::is_liked(conn, pid, user))
		.expect("read like")
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
/// premises of the spec's steps (e.g. Twitter.agda:607-612).
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

/// A `follows_snapshot` line.
fn follow_line(follower: &str, followee: &str) -> String {
	format!("{follower}|{followee}")
}

/// A `likes_snapshot` line.
fn like_line(pid: PostId, user: &str) -> String {
	format!("{}|{user}", pid.0)
}

/// `lines`, with `line` added when it is not already there, sorted the way
/// every snapshot is sorted.
fn with_line(lines: &[String], line: &str) -> Vec<String> {
	let mut out = lines.to_vec();
	if !out.iter().any(|present| present == line) {
		out.push(line.to_string());
	}
	out.sort_unstable();
	out
}

/// `lines`, with `line` removed, sorted the way every snapshot is sorted.
fn without_line(lines: &[String], line: &str) -> Vec<String> {
	let mut out: Vec<String> = lines
		.iter()
		.filter(|present| present.as_str() != line)
		.cloned()
		.collect();
	out.sort_unstable();
	out
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

/// The shared seeded world: `user` -- with an active session `SID` and a
/// revoked session `REVOKED_SID` -- and `author`, a public `PARENT` post by
/// `author`, one reply to it and one like on it. No follow edge touches `user`
/// or `author`, so whether a `followers-only` post is readable is decided by
/// the individual test.
fn seed_world(db: &Db, user: &str, author: &str) {
	seed_account(db, user);
	seed_account(db, author);
	seed_session(db, SID, user);
	seed_revoked_session(db, REVOKED_SID, user);
	seed_post(db, PARENT, author, "parent", Visibility::Everyone);
	seed_reply(db, REPLY_1, author, "reply", Visibility::Everyone, PARENT);
	seed_like(db, PARENT, author);
}

/// The `denied` half of a `Step`: the answer, and a world that did not move.
fn assert_denied(db: &Db, result: EngineResult, before: &[String]) {
	assert_eq!(result, EngineResult::Denied);
	assert_eq!(world(db), before, "a denied command changes nothing");
}

/// The `expired` half of a `Step`: the answer, and a world that did not move.
fn assert_expired(db: &Db, result: EngineResult, before: &[String]) {
	assert_eq!(result, EngineResult::Expired);
	assert_eq!(world(db), before, "an expired command changes nothing");
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

/// A body of text, so the paths that carry one are exercised too.
#[derive(Clone, Debug)]
struct Body(String);

/// A small selector, used to pick between the two post visibilities.
#[derive(Clone, Debug)]
struct Pick(u8);

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

impl Arbitrary for Pick {
	fn arbitrary(g: &mut Gen) -> Self {
		Pick(u8::arbitrary(g))
	}
}

// ---------------------------------------------------------------------------
// Seeded ids. Small constants keep the seeded world legible; `publish`
// allocates its own ids from the whole i64 range, so it never reuses one.
// ---------------------------------------------------------------------------

const SID: SessionId = SessionId(100);
const REVOKED_SID: SessionId = SessionId(101);
const UNUSED_SID: SessionId = SessionId(102);
const PARENT: PostId = PostId(200);
const REPLY_1: PostId = PostId(201);
const REPLY_2: PostId = PostId(202);
const TARGET: PostId = PostId(300);
const ABSENT: PostId = PostId(9_000_000);

// ---------------------------------------------------------------------------
// S1: follow -- `follow-user` (Twitter.agda:655-664)
// ---------------------------------------------------------------------------

/// `follow-user`: the session must be valid, the follower is its user, and the
/// only thing that changes is `add-follower`. There is no premise on the
/// followee, so following a username with no account is `Success` too
/// (`follow_unknown_user_succeeds`). Every other follow pair, and every
/// account, session, post and `newest-first` entry, is untouched.
#[quickcheck]
fn follow_succeeds_and_sets_follow(follower: Name, followee: Name, other: Name) -> TestResult {
	if follower.0 == followee.0 || follower.0 == other.0 || followee.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &follower.0, &other.0);
	// An unrelated follow pair that must survive the command.
	seed_follow(&db, &other.0, &follower.0);

	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(
		follow(&db, SID, &followee.0).expect("follow"),
		EngineResult::Success
	);

	assert!(is_following(&db, &follower.0, &followee.0));
	assert!(is_following(&db, &other.0, &follower.0));
	// Exactly one `follows` row may appear; nothing may disappear.
	assert_eq!(row_count(&db, "follows"), 2);
	assert_eq!(
		follows_snapshot(&db),
		with_line(&follows_before, &follow_line(&follower.0, &followee.0))
	);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `add-follower` (Twitter.agda:371-375) is idempotent: following twice is
/// still `success` and sets nothing else, so the world is unchanged.
#[quickcheck]
fn follow_is_idempotent(follower: Name, followee: Name, other: Name) -> TestResult {
	if follower.0 == followee.0 || follower.0 == other.0 || followee.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &follower.0, &other.0);
	seed_follow(&db, &follower.0, &followee.0);
	// Precondition: the edge is already there.
	assert!(is_following(&db, &follower.0, &followee.0));
	let before = world(&db);
	assert_eq!(
		follow(&db, SID, &followee.0).expect("follow"),
		EngineResult::Success
	);
	assert_eq!(world(&db), before);
	TestResult::passed()
}

/// `follow-user` has no premise on the followee, so following an account that
/// does not exist is `success` and stores the edge.
#[quickcheck]
fn follow_unknown_user_succeeds(follower: Name, followee: Name) -> TestResult {
	if follower.0 == followee.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &follower.0);
	seed_session(&db, SID, &follower.0);
	// Precondition: the followee has no account.
	assert!(account_is_absent(&db, &followee.0));
	let follows_before = follows_snapshot(&db);

	assert_eq!(
		follow(&db, SID, &followee.0).expect("follow"),
		EngineResult::Success
	);

	assert!(is_following(&db, &follower.0, &followee.0));
	assert_eq!(
		follows_snapshot(&db),
		with_line(&follows_before, &follow_line(&follower.0, &followee.0))
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// S2: unfollow -- `unfollow-user` (Twitter.agda:666-675)
// ---------------------------------------------------------------------------

/// `unfollow-user` removes exactly one edge and keeps everything else -- the
/// other follow pairs, the accounts, the sessions, the posts and the
/// `newest-first` order.
#[quickcheck]
fn unfollow_succeeds_and_clears_follow(follower: Name, followee: Name, other: Name) -> TestResult {
	if follower.0 == followee.0 || follower.0 == other.0 || followee.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &follower.0, &other.0);
	seed_follow(&db, &follower.0, &followee.0);
	seed_follow(&db, &other.0, &follower.0);
	// Precondition: the edge to remove exists.
	assert!(is_following(&db, &follower.0, &followee.0));

	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(
		unfollow(&db, SID, &followee.0).expect("unfollow"),
		EngineResult::Success
	);

	assert!(!is_following(&db, &follower.0, &followee.0));
	assert!(is_following(&db, &other.0, &follower.0));
	assert_eq!(
		follows_snapshot(&db),
		without_line(&follows_before, &follow_line(&follower.0, &followee.0))
	);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(likes_snapshot(&db), likes_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `unfollow-user` has no premise that the edge existed, so unfollowing a user
/// that was never followed is `success` and changes nothing.
#[quickcheck]
fn unfollow_never_followed_succeeds(follower: Name, followee: Name, other: Name) -> TestResult {
	if follower.0 == followee.0 || follower.0 == other.0 || followee.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &follower.0, &other.0);
	// Precondition: no such edge.
	assert!(!is_following(&db, &follower.0, &followee.0));
	let before = world(&db);
	assert_eq!(
		unfollow(&db, SID, &followee.0).expect("unfollow"),
		EngineResult::Success
	);
	assert_eq!(world(&db), before);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// S3: like -- `like-post` (Twitter.agda:587-613), `failed-like-post` (615-619)
// ---------------------------------------------------------------------------

/// `like-post` on a readable post: a public `live` post, or a `followers-only`
/// `live` post the user follows the author of. The user joins the like list,
/// the like count gains exactly their contribution, the likes of every other
/// user are unchanged, the post keeps author, text, visibility, status, parent
/// and replies, and no other row of the world moves.
#[quickcheck]
fn like_readable_post_succeeds(liker: Name, author: Name, third: Name, pick: Pick) -> TestResult {
	if liker.0 == author.0 || liker.0 == third.0 || author.0 == third.0 {
		return TestResult::discard();
	}
	let private = pick.0 % 2 == 1;
	let visibility = if private {
		Visibility::FollowersOnly
	} else {
		Visibility::Everyone
	};
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_account(&db, &third.0);
	seed_post(&db, TARGET, &author.0, "target", visibility);
	seed_reply(&db, REPLY_2, &third.0, "under target", visibility, TARGET);
	seed_like(&db, TARGET, &author.0);
	seed_like(&db, TARGET, &third.0);
	if private {
		seed_follow(&db, &liker.0, &author.0);
	}
	// Precondition: `CanReadPost` (Twitter.agda:158-179) holds -- the follow
	// edge is what makes the `followers-only` case readable.
	assert_eq!(
		is_following(&db, &liker.0, &author.0),
		private,
		"the follow edge decides whether the private post is readable"
	);

	let post_before = post_of(&db, TARGET).expect("target post");
	let replies_before = replies_of(&db, TARGET);
	let count_before = like_count(&db, TARGET);
	let rows_before = row_count(&db, "post_likes");
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(like(&db, SID, TARGET).expect("like"), EngineResult::Success);

	assert!(is_liked(&db, TARGET, &liker.0));
	assert_eq!(like_count(&db, TARGET), count_before + 1);
	assert_eq!(row_count(&db, "post_likes"), rows_before + 1);
	assert_eq!(
		likes_snapshot(&db),
		with_line(&likes_before, &like_line(TARGET, &liker.0))
	);
	// The rest of the post is unchanged.
	assert_eq!(post_of(&db, TARGET).expect("target post"), post_before);
	assert_eq!(replies_of(&db, TARGET), replies_before);
	// ... and so is everything else in the world.
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `like-post` does not require the user to be absent from the like list, so
/// liking twice is `success`, adds no duplicate row and leaves the count and
/// the rest of the world as they were.
#[quickcheck]
fn like_is_idempotent(liker: Name, author: Name, third: Name) -> TestResult {
	if liker.0 == author.0 || liker.0 == third.0 || author.0 == third.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_account(&db, &third.0);
	seed_post(&db, TARGET, &author.0, "target", Visibility::Everyone);
	seed_like(&db, TARGET, &liker.0);
	seed_like(&db, TARGET, &third.0);
	// Precondition: the like is already there.
	assert!(is_liked(&db, TARGET, &liker.0));
	let count_before = like_count(&db, TARGET);
	let rows_before = row_count(&db, "post_likes");
	let before = world(&db);

	assert_eq!(like(&db, SID, TARGET).expect("like"), EngineResult::Success);

	assert_eq!(like_count(&db, TARGET), count_before);
	assert_eq!(row_count(&db, "post_likes"), rows_before);
	assert_eq!(world(&db), before);
	TestResult::passed()
}

/// `like-post` has no distinctness premise: an author may like their own post.
#[quickcheck]
fn like_own_post_succeeds(liker: Name, other: Name, body: Body) -> TestResult {
	if liker.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &liker.0);
	seed_account(&db, &other.0);
	seed_session(&db, SID, &liker.0);
	seed_post(&db, TARGET, &liker.0, &body.0, Visibility::Everyone);
	seed_like(&db, TARGET, &other.0);
	// Precondition: the post is the session user's own.
	assert_eq!(
		post_of(&db, TARGET).expect("own post").author,
		liker.0,
		"the post belongs to the session's user"
	);
	let count_before = like_count(&db, TARGET);
	let rows_before = row_count(&db, "post_likes");
	let likes_before = likes_snapshot(&db);
	let post_before = post_of(&db, TARGET).expect("own post");
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(like(&db, SID, TARGET).expect("like"), EngineResult::Success);

	assert!(is_liked(&db, TARGET, &liker.0));
	assert_eq!(like_count(&db, TARGET), count_before + 1);
	assert_eq!(row_count(&db, "post_likes"), rows_before + 1);
	assert_eq!(
		likes_snapshot(&db),
		with_line(&likes_before, &like_line(TARGET, &liker.0))
	);
	assert_eq!(post_of(&db, TARGET).expect("own post"), post_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `failed-like-post` (Twitter.agda:615-619) on a post that does not exist:
/// `denied`, and nothing at all changes.
#[quickcheck]
fn like_denied_absent(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	// Precondition: no post has that id.
	assert!(post_of(&db, ABSENT).is_none());
	let before = world(&db);
	assert_denied(&db, like(&db, SID, ABSENT).expect("like"), &before);
	TestResult::passed()
}

/// `failed-like-post` on a `deleted` post (`CanReadPost` demands `live`):
/// `denied`, and nothing at all changes.
#[quickcheck]
fn like_denied_deleted(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_post(&db, TARGET, &author.0, "gone", Visibility::Everyone);
	seed_delete(&db, TARGET);
	let before = world(&db);
	assert_denied(&db, like(&db, SID, TARGET).expect("like"), &before);
	TestResult::passed()
}

/// `failed-like-post` on a `followers-only` post the user does not follow
/// (`post-is-private`, Twitter.agda:161-170): `denied`, world unchanged.
#[quickcheck]
fn like_denied_private_not_followed(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_post(&db, TARGET, &author.0, "private", Visibility::FollowersOnly);
	// Precondition: no follow edge, so `CanReadPost` fails.
	assert!(!is_following(&db, &liker.0, &author.0));
	let before = world(&db);
	assert_denied(&db, like(&db, SID, TARGET).expect("like"), &before);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// S4: unlike -- `unlike-post` (Twitter.agda:621-647), `failed-unlike-post`
// (Twitter.agda:649-653)
// ---------------------------------------------------------------------------

/// `unlike-post`: the user leaves the like list (so the AFTER post no longer
/// lists them, Twitter.agda:625), the like count loses exactly their
/// contribution, the likes of every other user are unchanged, the post keeps
/// every other field, and no other row of the world moves.
#[quickcheck]
fn unlike_liked_post_removes_like(liker: Name, author: Name, third: Name) -> TestResult {
	if liker.0 == author.0 || liker.0 == third.0 || author.0 == third.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_account(&db, &third.0);
	seed_post(&db, TARGET, &author.0, "target", Visibility::Everyone);
	seed_reply(
		&db,
		REPLY_2,
		&third.0,
		"under target",
		Visibility::Everyone,
		TARGET,
	);
	seed_like(&db, TARGET, &liker.0);
	seed_like(&db, TARGET, &third.0);
	// Precondition: the like to remove exists.
	assert!(is_liked(&db, TARGET, &liker.0));

	let post_before = post_of(&db, TARGET).expect("target post");
	let replies_before = replies_of(&db, TARGET);
	let count_before = like_count(&db, TARGET);
	let rows_before = row_count(&db, "post_likes");
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let posts_before = posts_snapshot(&db);
	let follows_before = follows_snapshot(&db);
	let likes_before = likes_snapshot(&db);
	let order_before = newest_first(&db);

	assert_eq!(
		unlike(&db, SID, TARGET).expect("unlike"),
		EngineResult::Success
	);

	assert!(!is_liked(&db, TARGET, &liker.0));
	assert_eq!(like_count(&db, TARGET), count_before - 1);
	assert_eq!(row_count(&db, "post_likes"), rows_before - 1);
	assert_eq!(
		likes_snapshot(&db),
		without_line(&likes_before, &like_line(TARGET, &liker.0))
	);
	// The rest of the post is unchanged.
	assert_eq!(post_of(&db, TARGET).expect("target post"), post_before);
	assert_eq!(replies_of(&db, TARGET), replies_before);
	// ... and so is everything else in the world.
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	assert_eq!(posts_snapshot(&db), posts_before);
	assert_eq!(follows_snapshot(&db), follows_before);
	assert_eq!(newest_first(&db), order_before);
	TestResult::passed()
}

/// `unlike-post` has no premise that the like existed, so unliking a post the
/// user never liked is `success` and changes nothing.
#[quickcheck]
fn unlike_never_liked_succeeds(liker: Name, author: Name, third: Name) -> TestResult {
	if liker.0 == author.0 || liker.0 == third.0 || author.0 == third.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_account(&db, &third.0);
	seed_post(&db, TARGET, &author.0, "target", Visibility::Everyone);
	seed_like(&db, TARGET, &third.0);
	// Precondition: no like by `liker`.
	assert!(!is_liked(&db, TARGET, &liker.0));
	let before = world(&db);
	assert_eq!(
		unlike(&db, SID, TARGET).expect("unlike"),
		EngineResult::Success
	);
	assert_eq!(world(&db), before);
	TestResult::passed()
}

/// `failed-unlike-post` (Twitter.agda:649-653) on a post that does not exist:
/// `denied`, and nothing at all changes.
#[quickcheck]
fn unlike_denied_absent(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	assert!(post_of(&db, ABSENT).is_none());
	assert!(!is_liked(&db, ABSENT, &liker.0));
	let before = world(&db);
	assert_denied(&db, unlike(&db, SID, ABSENT).expect("unlike"), &before);
	TestResult::passed()
}

/// `failed-unlike-post` on a `deleted` post: `denied`, and even the like the
/// user holds on it stays.
#[quickcheck]
fn unlike_denied_deleted(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_post(&db, TARGET, &author.0, "gone", Visibility::Everyone);
	seed_like(&db, TARGET, &liker.0);
	seed_delete(&db, TARGET);
	let before = world(&db);
	assert_denied(&db, unlike(&db, SID, TARGET).expect("unlike"), &before);
	// The denied command did not consume the like either.
	assert!(is_liked(&db, TARGET, &liker.0));
	TestResult::passed()
}

/// `failed-unlike-post` on a `followers-only` post the user does not follow:
/// `denied`, world unchanged.
#[quickcheck]
fn unlike_denied_private_not_followed(liker: Name, author: Name) -> TestResult {
	if liker.0 == author.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	seed_post(&db, TARGET, &author.0, "private", Visibility::FollowersOnly);
	seed_like(&db, TARGET, &liker.0);
	// Precondition: no follow edge, so `CanReadPost` fails.
	assert!(!is_following(&db, &liker.0, &author.0));
	let before = world(&db);
	assert_denied(&db, unlike(&db, SID, TARGET).expect("unlike"), &before);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// S5: failed-access -- all four commands on an inactive session
// (Twitter.agda:464-468)
// ---------------------------------------------------------------------------

/// `failed-access`: the four commands extract their session
/// (`extract-sid`, Twitter.agda:203-207), so a session that is not `active` --
/// `unused` or `revoked` -- expires the request and leaves the world untouched.
/// Unlike `read-post nothing`, none of these can fire vacuously.
#[quickcheck]
fn social_commands_expire_without_valid_session(
	liker: Name,
	author: Name,
	followee: Name,
) -> TestResult {
	if liker.0 == author.0 || liker.0 == followee.0 || author.0 == followee.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_world(&db, &liker.0, &author.0);
	// The commands have something to act on, so `Success` would be tempting.
	seed_follow(&db, &liker.0, &author.0);
	seed_like(&db, PARENT, &liker.0);
	let before = world(&db);

	let inactive = [
		(UNUSED_SID, SessionStatus::Unused),
		(REVOKED_SID, SessionStatus::Revoked),
	];
	for (sid, expected) in inactive {
		// Precondition: the session is not active.
		assert_eq!(status_of(&db, sid), expected);
		assert_expired(&db, follow(&db, sid, &followee.0).expect("follow"), &before);
		assert_expired(
			&db,
			unfollow(&db, sid, &followee.0).expect("unfollow"),
			&before,
		);
		assert_expired(&db, like(&db, sid, PARENT).expect("like"), &before);
		assert_expired(&db, unlike(&db, sid, PARENT).expect("unlike"), &before);
	}
	TestResult::passed()
}
