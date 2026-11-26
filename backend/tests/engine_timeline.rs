//! Property and unit tests for the timeline engine (task T3b).
//!
//! Every property below is a direct rendering of a `Step` rule of
//! `spec/Twitter.agda`; the matching Agda lemma lives in `ImplProofs.agda`
//! (P15):
//!
//! * `personal_timeline` is `get-personal-timeline` (Twitter.agda:557-566);
//! * `global_timeline (Some sid)` is `get-private-global-timeline` (:568-576);
//! * `global_timeline None` is `get-public-global-timeline` (:578-585);
//! * both session-carrying commands expire an inactive session, which is
//!   `failed-access` (:464-468).
//!
//! The spec's answers filter the whole `World.newest-first` order and then
//! `take n`. `ImplProofs.agda` proves that those filters coincide with the
//! *simple* characterizations the engine's SQL evaluates, and the expected
//! lists below replicate exactly that simple form -- `live` plus the follow
//! table (`personal`), `live` plus `everyone` or a follow (`private global`),
//! `live` plus `everyone` (`public global`) -- over the seeded rows ordered by
//! `seq DESC`, then truncated to `n`. So the assertions and the theorems check
//! the same list, not merely the same constructor.
//!
//! State is seeded through `formal_twitter::store`, never through the engine.
//! Snapshots are sorted in Rust on the composed line, never in SQL: `'|'`
//! (0x7C) sorts after every letter and digit, so `ORDER BY` on one column and
//! a sort of `a|b|c` disagree whenever one field is a prefix of another.

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::Text;
use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::timeline::{global_timeline, personal_timeline};
use formal_twitter::model::{Post, PostId, PostStatus, SessionId, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

// ---------------------------------------------------------------------------
// Harness: an in-memory database, plus read-only views of it.
// ---------------------------------------------------------------------------

const PASSWORD: &str = "timeline-secret";

fn database() -> Db {
	Db::in_memory().expect("create in-memory database")
}

fn status_of_post(db: &Db, pid: PostId) -> PostStatus {
	post_of(db, pid).expect("seeded post").status
}

fn post_of(db: &Db, pid: PostId) -> Option<Post> {
	db.read(|conn| store::get_post(conn, pid))
		.expect("read post")
}

fn follows(db: &Db, follower: &str, followee: &str) -> bool {
	db.read(|conn| store::is_following(conn, follower, followee))
		.expect("read follow")
}

/// The whole `newest-first` order of the spec (Twitter.agda:74), i.e. the rows
/// by descending `seq`.
fn newest_first(db: &Db) -> Vec<PostId> {
	db.read(|conn| store::newest_first(conn, u32::MAX))
		.expect("read newest-first")
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
/// markers. A timeline command must never change it (Twitter.agda:557-585 all
/// have `before` as the after world).
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

// ---------------------------------------------------------------------------
// Seeding. All state goes in through `store`, never through the engine.
// ---------------------------------------------------------------------------

fn seed_account(db: &Db, name: &str) {
	assert!(
		db.write(|conn| store::create_account(conn, name, PASSWORD))
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

// ---------------------------------------------------------------------------
// The simple characterizations the engine's SQL implements (ImplProofs P15).
// ---------------------------------------------------------------------------

/// `World.newest-first` together with each row.
fn ordered_posts(db: &Db) -> Vec<(PostId, Post)> {
	newest_first(db)
		.into_iter()
		.map(|pid| {
			(
				pid,
				post_of(db, pid).expect("every newest-first pid exists"),
			)
		})
		.collect()
}

/// `personal-allowed` (ImplProofs.agda): `live` and the user follows the
/// author. `take n` is applied *after* the filter, exactly like the spec's
/// `take n ∘ filter … ∘ newest-first`.
fn expected_personal(db: &Db, user: &str, n: u32) -> Vec<PostId> {
	ordered_posts(db)
		.into_iter()
		.filter(|(_, post)| post.status == PostStatus::Live && follows(db, user, &post.author))
		.map(|(pid, _)| pid)
		.take(n as usize)
		.collect()
}

/// `global-allowed` / `public-allowed` (ImplProofs.agda): `live` and, with a
/// session, `everyone` or a follow; without one, `everyone` only.
fn expected_global(db: &Db, user: Option<&str>, n: u32) -> Vec<PostId> {
	ordered_posts(db)
		.into_iter()
		.filter(|(_, post)| {
			post.status == PostStatus::Live
				&& (post.visibility == Visibility::Everyone
					|| user.is_some_and(|follower| follows(db, follower, &post.author)))
		})
		.map(|(pid, _)| pid)
		.take(n as usize)
		.collect()
}

/// The ids of a `ReturnedTimeline` answer.
fn returned(result: EngineResult) -> Vec<PostId> {
	match result {
		EngineResult::ReturnedTimeline(ids) => ids,
		other => panic!("expected a returned timeline, got {other:?}"),
	}
}

// ---------------------------------------------------------------------------
// The seeded world of the deterministic tests.
//
// Insertion order is `seq` order, so `newest-first` is the reverse of the
// `seed_*` calls below.
// ---------------------------------------------------------------------------

const SID: SessionId = SessionId(100);
const REVOKED_SID: SessionId = SessionId(101);
const UNUSED_SID: SessionId = SessionId(102);

const ME: &str = "me";
const BOB: &str = "bob";
const CAROL: &str = "carol";

const MY_PUBLIC: PostId = PostId(200);
const MY_PRIVATE: PostId = PostId(201);
const BOB_PUBLIC: PostId = PostId(202);
const BOB_PRIVATE: PostId = PostId(203);
const CAROL_PRIVATE: PostId = PostId(204);
const CAROL_PUBLIC: PostId = PostId(205);
const CAROL_DELETED: PostId = PostId(206);
const CAROL_REPLY: PostId = PostId(207);

/// `me` with an active `SID` and a revoked `REVOKED_SID`; one `everyone` and
/// one `followers-only` post each by `me`, `bob` and `carol`; a deleted post
/// and a reply, both by `carol`; `me` follows `carol` and nobody else.
///
/// `newest-first` = 207, 206, 205, 204, 203, 202, 201, 200.
fn seed_world(db: &Db) {
	for name in [ME, BOB, CAROL] {
		seed_account(db, name);
	}
	seed_session(db, SID, ME);
	seed_revoked_session(db, REVOKED_SID, ME);
	seed_post(db, MY_PUBLIC, ME, "my public", Visibility::Everyone);
	seed_post(db, MY_PRIVATE, ME, "my private", Visibility::FollowersOnly);
	seed_post(db, BOB_PUBLIC, BOB, "bob public", Visibility::Everyone);
	seed_post(
		db,
		BOB_PRIVATE,
		BOB,
		"bob private",
		Visibility::FollowersOnly,
	);
	seed_post(
		db,
		CAROL_PRIVATE,
		CAROL,
		"carol private",
		Visibility::FollowersOnly,
	);
	seed_post(
		db,
		CAROL_PUBLIC,
		CAROL,
		"carol public",
		Visibility::Everyone,
	);
	seed_post(
		db,
		CAROL_DELETED,
		CAROL,
		"carol deleted",
		Visibility::Everyone,
	);
	seed_reply(
		db,
		CAROL_REPLY,
		CAROL,
		"carol reply",
		Visibility::Everyone,
		MY_PUBLIC,
	);
	seed_delete(db, CAROL_DELETED);
	seed_follow(db, ME, CAROL);
}

// ---------------------------------------------------------------------------
// T1: personal timeline -- `get-personal-timeline` (Twitter.agda:557-566)
// ---------------------------------------------------------------------------

/// The personal timeline is exactly the live posts of followed authors,
/// newest-first; public posts of non-followed authors are left out.
#[test]
fn personal_timeline_follows_the_characterization() {
	let db = database();
	seed_world(&db);

	let ids = returned(personal_timeline(&db, SID, 10).expect("timeline"));
	assert_eq!(ids, vec![CAROL_REPLY, CAROL_PUBLIC, CAROL_PRIVATE]);
	assert_eq!(ids, expected_personal(&db, ME, 10));
	// A `followers-only` post of a followed author is readable ...
	assert!(ids.contains(&CAROL_PRIVATE));
	// ... and a public post of a non-followed author is not.
	assert!(!ids.contains(&BOB_PUBLIC));
	assert!(!ids.contains(&BOB_PRIVATE));
	// Every entry is live and by a followed author.
	for pid in &ids {
		assert_eq!(status_of_post(&db, *pid), PostStatus::Live);
		let post = post_of(&db, *pid).expect("post");
		assert!(follows(&db, ME, &post.author));
	}
}

/// `take n` (Twitter.agda:560) bounds the answer: `0` is empty, `n` shorter
/// than the list is a prefix, `n` longer than it is the whole list.
#[test]
fn personal_timeline_takes_n_after_filtering() {
	let db = database();
	seed_world(&db);

	assert!(
		returned(personal_timeline(&db, SID, 0).expect("timeline")).is_empty(),
		"n = 0 yields the empty timeline"
	);
	assert_eq!(
		returned(personal_timeline(&db, SID, 1).expect("timeline")),
		vec![CAROL_REPLY]
	);
	assert_eq!(
		returned(personal_timeline(&db, SID, 2).expect("timeline")),
		vec![CAROL_REPLY, CAROL_PUBLIC]
	);
	let all = vec![CAROL_REPLY, CAROL_PUBLIC, CAROL_PRIVATE];
	assert_eq!(
		returned(personal_timeline(&db, SID, 3).expect("timeline")),
		all
	);
	assert_eq!(
		returned(personal_timeline(&db, SID, 4).expect("timeline")),
		all,
		"n larger than the list saturates"
	);
	assert_eq!(
		returned(personal_timeline(&db, SID, u32::MAX).expect("timeline")),
		all
	);
	// `n` bounds the answer, never the scanned prefix: the deleted and
	// unfollowed rows *before* the readable ones do not consume the budget.
	assert_eq!(
		returned(personal_timeline(&db, SID, 1).expect("timeline")),
		vec![CAROL_REPLY]
	);
}

/// A post is not special because the session's user wrote it: `follows-post-author`
/// (Twitter.agda:366-369) is consulted like for anyone else, so the own posts
/// appear only after a self-follow.
#[test]
fn personal_timeline_own_posts_need_a_self_follow() {
	let db = database();
	seed_world(&db);

	let before = returned(personal_timeline(&db, SID, 100).expect("timeline"));
	assert!(!before.contains(&MY_PUBLIC));
	assert!(!before.contains(&MY_PRIVATE));

	seed_follow(&db, ME, ME);

	let after = returned(personal_timeline(&db, SID, 100).expect("timeline"));
	assert_eq!(
		after,
		vec![
			CAROL_REPLY,
			CAROL_PUBLIC,
			CAROL_PRIVATE,
			MY_PRIVATE,
			MY_PUBLIC
		]
	);
	assert_eq!(after, expected_personal(&db, ME, 100));
}

/// Following another author brings exactly their live posts in, at their
/// `newest-first` positions.
#[test]
fn personal_timeline_following_an_author_adds_their_posts() {
	let db = database();
	seed_world(&db);

	seed_follow(&db, ME, BOB);

	let ids = returned(personal_timeline(&db, SID, 100).expect("timeline"));
	assert_eq!(
		ids,
		vec![
			CAROL_REPLY,
			CAROL_PUBLIC,
			CAROL_PRIVATE,
			BOB_PRIVATE,
			BOB_PUBLIC
		]
	);
	assert_eq!(ids, expected_personal(&db, ME, 100));
}

/// A deleted post stays out even when its author is followed, and a reply is an
/// ordinary entry (row 207, the newest one, with a parent).
#[test]
fn personal_timeline_excludes_deleted_posts_and_keeps_replies() {
	let db = database();
	seed_world(&db);
	assert!(follows(&db, ME, CAROL));
	assert_eq!(
		post_of(&db, CAROL_REPLY).expect("reply").parent,
		Some(MY_PUBLIC),
		"precondition: 207 is a reply"
	);

	let ids = returned(personal_timeline(&db, SID, 100).expect("timeline"));
	assert!(!ids.contains(&CAROL_DELETED));
	assert_eq!(ids.first(), Some(&CAROL_REPLY));
	assert_eq!(ids, expected_personal(&db, ME, 100));
}

// ---------------------------------------------------------------------------
// T2: private global timeline -- `get-private-global-timeline` (:568-576)
// ---------------------------------------------------------------------------

/// With a session, the global timeline is the `CanReadPost` set (Twitter.agda:
/// 158-179): `live` and either `everyone`, or `followers-only` and followed.
#[test]
fn private_global_timeline_includes_readable_posts() {
	let db = database();
	seed_world(&db);

	let ids = returned(global_timeline(&db, Some(SID), 100).expect("timeline"));
	assert_eq!(
		ids,
		vec![
			CAROL_REPLY,
			CAROL_PUBLIC,
			CAROL_PRIVATE,
			BOB_PUBLIC,
			MY_PUBLIC
		]
	);
	assert_eq!(ids, expected_global(&db, Some(ME), 100));
	// Own public post: readable. Own `followers-only` post: not, because the
	// user does not follow themself.
	assert!(ids.contains(&MY_PUBLIC));
	assert!(!ids.contains(&MY_PRIVATE));
	// Someone else's `followers-only` post: readable iff followed.
	assert!(ids.contains(&CAROL_PRIVATE));
	assert!(!ids.contains(&BOB_PRIVATE));
	// Deleted posts are never readable.
	assert!(!ids.contains(&CAROL_DELETED));
}

/// The own `followers-only` post becomes readable after a self-follow, and
/// nothing else moves.
#[test]
fn private_global_timeline_own_private_post_needs_a_self_follow() {
	let db = database();
	seed_world(&db);

	seed_follow(&db, ME, ME);

	let ids = returned(global_timeline(&db, Some(SID), 100).expect("timeline"));
	assert_eq!(
		ids,
		vec![
			CAROL_REPLY,
			CAROL_PUBLIC,
			CAROL_PRIVATE,
			BOB_PUBLIC,
			MY_PRIVATE,
			MY_PUBLIC
		]
	);
	assert_eq!(ids, expected_global(&db, Some(ME), 100));
}

/// `take n` on the private global timeline, after filtering.
#[test]
fn private_global_timeline_takes_n_after_filtering() {
	let db = database();
	seed_world(&db);

	assert!(
		returned(global_timeline(&db, Some(SID), 0).expect("timeline")).is_empty(),
		"n = 0 yields the empty timeline"
	);
	assert_eq!(
		returned(global_timeline(&db, Some(SID), 2).expect("timeline")),
		vec![CAROL_REPLY, CAROL_PUBLIC]
	);
	let all = vec![
		CAROL_REPLY,
		CAROL_PUBLIC,
		CAROL_PRIVATE,
		BOB_PUBLIC,
		MY_PUBLIC,
	];
	assert_eq!(
		returned(global_timeline(&db, Some(SID), 5).expect("timeline")),
		all
	);
	assert_eq!(
		returned(global_timeline(&db, Some(SID), u32::MAX).expect("timeline")),
		all
	);
}

// ---------------------------------------------------------------------------
// T3: public global timeline -- `get-public-global-timeline` (:578-585)
// ---------------------------------------------------------------------------

/// Without a session the timeline is `is-post-public` (Twitter.agda:342-357):
/// `live` and `everyone`. The follow table is irrelevant, so seeding follows in
/// every direction changes nothing.
#[test]
fn public_global_timeline_is_public_and_live_only() {
	let db = database();
	seed_world(&db);
	let before = returned(global_timeline(&db, None, 100).expect("timeline"));

	seed_follow(&db, BOB, ME);
	seed_follow(&db, ME, BOB);
	seed_follow(&db, ME, ME);
	seed_follow(&db, BOB, CAROL);

	let ids = returned(global_timeline(&db, None, 100).expect("timeline"));
	assert_eq!(ids, vec![CAROL_REPLY, CAROL_PUBLIC, BOB_PUBLIC, MY_PUBLIC]);
	assert_eq!(
		ids, before,
		"the tokenless timeline ignores the follow table"
	);
	assert_eq!(ids, expected_global(&db, None, 100));
	assert!(!ids.contains(&BOB_PRIVATE));
	assert!(!ids.contains(&CAROL_PRIVATE));
	assert!(!ids.contains(&MY_PRIVATE));
	assert!(!ids.contains(&CAROL_DELETED));
	for pid in &ids {
		let post = post_of(&db, *pid).expect("post");
		assert_eq!(post.status, PostStatus::Live);
		assert_eq!(post.visibility, Visibility::Everyone);
	}
}

/// `take n` on the tokenless timeline, after filtering.
#[test]
fn public_global_timeline_takes_n_after_filtering() {
	let db = database();
	seed_world(&db);

	assert!(
		returned(global_timeline(&db, None, 0).expect("timeline")).is_empty(),
		"n = 0 yields the empty timeline"
	);
	assert_eq!(
		returned(global_timeline(&db, None, 1).expect("timeline")),
		vec![CAROL_REPLY]
	);
	assert_eq!(
		returned(global_timeline(&db, None, 3).expect("timeline")),
		vec![CAROL_REPLY, CAROL_PUBLIC, BOB_PUBLIC]
	);
	let all = vec![CAROL_REPLY, CAROL_PUBLIC, BOB_PUBLIC, MY_PUBLIC];
	assert_eq!(
		returned(global_timeline(&db, None, u32::MAX).expect("timeline")),
		all
	);
}

/// `read-global-timeline nothing` extracts no session (`extract-sid`,
/// Twitter.agda:196), so `failed-access`'s premise is vacuous: it answers even
/// in a world with no sessions at all.
#[test]
fn public_global_timeline_works_without_any_session() {
	let db = database();
	seed_account(&db, CAROL);
	seed_post(
		&db,
		CAROL_PRIVATE,
		CAROL,
		"carol private",
		Visibility::FollowersOnly,
	);

	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		Vec::<PostId>::new(),
		"a followers-only post is not publicly readable"
	);

	seed_post(
		&db,
		CAROL_PUBLIC,
		CAROL,
		"carol public",
		Visibility::Everyone,
	);
	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		vec![CAROL_PUBLIC]
	);
}

// ---------------------------------------------------------------------------
// T4: inactive sessions -- `failed-access` (Twitter.agda:464-468)
// ---------------------------------------------------------------------------

/// Both session-carrying timelines answer `Expired` for a revoked session and
/// leave the world untouched; the tokenless one keeps answering.
#[test]
fn timelines_expire_for_a_revoked_session() {
	let db = database();
	seed_world(&db);
	let before = world(&db);

	assert_eq!(
		personal_timeline(&db, REVOKED_SID, 10).expect("timeline"),
		EngineResult::Expired
	);
	assert_eq!(
		global_timeline(&db, Some(REVOKED_SID), 10).expect("timeline"),
		EngineResult::Expired
	);
	assert_eq!(world(&db), before, "an expired command changes nothing");
	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		expected_global(&db, None, 10),
		"the tokenless timeline never expires"
	);
}

/// The same for a session that was never issued.
#[test]
fn timelines_expire_for_an_unused_session() {
	let db = database();
	seed_world(&db);
	let before = world(&db);

	assert_eq!(
		personal_timeline(&db, UNUSED_SID, 10).expect("timeline"),
		EngineResult::Expired
	);
	assert_eq!(
		global_timeline(&db, Some(UNUSED_SID), 10).expect("timeline"),
		EngineResult::Expired
	);
	assert_eq!(world(&db), before, "an expired command changes nothing");
}

// ---------------------------------------------------------------------------
// Generated worlds: arbitrary posts, authors, visibilities, statuses, follows
// and bounds. The expected list is always the simple characterization above.
// ---------------------------------------------------------------------------

const NAMES: [&str; 3] = [ME, BOB, CAROL];

#[derive(Clone, Debug)]
struct GeneratedPost {
	author: u8,
	followers_only: bool,
	deleted: bool,
	reply_to: Option<u8>,
}

#[derive(Clone, Debug)]
struct GeneratedWorld {
	posts: Vec<GeneratedPost>,
	/// `follows[f * 3 + t]` is "user `f` follows user `t`".
	follows: [bool; 9],
	n: u32,
}

impl Arbitrary for GeneratedWorld {
	fn arbitrary(g: &mut Gen) -> Self {
		let count = usize::arbitrary(g) % 7;
		let mut posts = Vec::with_capacity(count);
		for index in 0..count {
			let author = u8::arbitrary(g) % 3;
			let followers_only = bool::arbitrary(g);
			let deleted = bool::arbitrary(g);
			// A reply points at an earlier post, as `only-valid-replies`
			// (Twitter.agda:98-106) requires.
			let reply_to = if index > 0 && bool::arbitrary(g) {
				Some((usize::arbitrary(g) % index) as u8)
			} else {
				None
			};
			posts.push(GeneratedPost {
				author,
				followers_only,
				deleted,
				reply_to,
			});
		}
		let mut follows = [false; 9];
		let bits = u16::arbitrary(g);
		for (index, slot) in follows.iter_mut().enumerate() {
			*slot = (bits >> index) & 1 == 1;
		}
		// `n` may be zero, smaller than the list, or larger than it.
		let n = u32::arbitrary(g) % 9;
		GeneratedWorld { posts, follows, n }
	}
}

fn seed_generated(db: &Db, generated: &GeneratedWorld) {
	for name in NAMES {
		seed_account(db, name);
	}
	seed_session(db, SID, ME);
	let mut ids: Vec<PostId> = Vec::with_capacity(generated.posts.len());
	for (index, post) in generated.posts.iter().enumerate() {
		let pid = PostId(1_000 + index as i64);
		ids.push(pid);
		let author = NAMES[usize::from(post.author) % NAMES.len()];
		let visibility = if post.followers_only {
			Visibility::FollowersOnly
		} else {
			Visibility::Everyone
		};
		match post.reply_to {
			Some(parent) => seed_reply(
				db,
				pid,
				author,
				"text",
				visibility,
				ids[usize::from(parent)],
			),
			None => seed_post(db, pid, author, "text", visibility),
		}
		if post.deleted {
			seed_delete(db, pid);
		}
	}
	for (follower, name) in NAMES.iter().enumerate() {
		for (followee, other) in NAMES.iter().enumerate() {
			if generated.follows[follower * NAMES.len() + followee] {
				seed_follow(db, name, other);
			}
		}
	}
}

/// `get-personal-timeline` for an arbitrary world and bound: exactly the live
/// posts of followed authors, newest-first, truncated to `n`.
#[quickcheck]
fn personal_timeline_matches_the_characterization(generated: GeneratedWorld) -> TestResult {
	let db = database();
	seed_generated(&db, &generated);
	let before = world(&db);

	let ids = returned(personal_timeline(&db, SID, generated.n).expect("timeline"));
	assert_eq!(ids, expected_personal(&db, ME, generated.n));
	assert!(ids.len() as u64 <= u64::from(generated.n));
	for pid in &ids {
		let post = post_of(&db, *pid).expect("post");
		assert_eq!(post.status, PostStatus::Live);
		assert!(follows(&db, ME, &post.author));
	}
	// Longer bounds extend the answer, never reorder it.
	let all = returned(personal_timeline(&db, SID, u32::MAX).expect("timeline"));
	assert_eq!(all, expected_personal(&db, ME, u32::MAX));
	assert_eq!(ids, all[..ids.len()].to_vec());
	assert_eq!(world(&db), before, "a timeline command changes nothing");
	TestResult::passed()
}

/// `get-private-global-timeline`: exactly the readable posts, newest-first.
#[quickcheck]
fn private_global_timeline_matches_the_characterization(generated: GeneratedWorld) -> TestResult {
	let db = database();
	seed_generated(&db, &generated);
	let before = world(&db);

	let ids = returned(global_timeline(&db, Some(SID), generated.n).expect("timeline"));
	assert_eq!(ids, expected_global(&db, Some(ME), generated.n));
	assert!(ids.len() as u64 <= u64::from(generated.n));
	for pid in &ids {
		let post = post_of(&db, *pid).expect("post");
		assert_eq!(post.status, PostStatus::Live);
		assert!(
			post.visibility == Visibility::Everyone || follows(&db, ME, &post.author),
			"a readable post is public or followed"
		);
	}
	let all = returned(global_timeline(&db, Some(SID), u32::MAX).expect("timeline"));
	assert_eq!(all, expected_global(&db, Some(ME), u32::MAX));
	assert_eq!(ids, all[..ids.len()].to_vec());
	assert_eq!(world(&db), before, "a timeline command changes nothing");
	TestResult::passed()
}

/// `get-public-global-timeline`: exactly the live `everyone` posts. Follows and
/// sessions are irrelevant, and the private timeline is the public one plus the
/// readable `followers-only` posts, which is the spec's `filter` nesting.
#[quickcheck]
fn public_global_timeline_matches_the_characterization(generated: GeneratedWorld) -> TestResult {
	let db = database();
	seed_generated(&db, &generated);
	let before = world(&db);

	let ids = returned(global_timeline(&db, None, generated.n).expect("timeline"));
	assert_eq!(ids, expected_global(&db, None, generated.n));
	assert!(ids.len() as u64 <= u64::from(generated.n));
	for pid in &ids {
		let post = post_of(&db, *pid).expect("post");
		assert_eq!(post.status, PostStatus::Live);
		assert_eq!(post.visibility, Visibility::Everyone);
	}
	let public_all = returned(global_timeline(&db, None, u32::MAX).expect("timeline"));
	assert_eq!(public_all, expected_global(&db, None, u32::MAX));
	assert_eq!(ids, public_all[..ids.len()].to_vec());

	// The readable set is the public set plus the readable `followers-only`
	// posts: dropping the `followers-only` entries from the private timeline
	// leaves exactly the public one, i.e. the spec's `is-post-public` filter.
	let private_all = returned(global_timeline(&db, Some(SID), u32::MAX).expect("timeline"));
	let private_public: Vec<PostId> = private_all
		.into_iter()
		.filter(|pid| post_of(&db, *pid).expect("post").visibility == Visibility::Everyone)
		.collect();
	assert_eq!(private_public, public_all);
	assert_eq!(world(&db), before, "a timeline command changes nothing");
	TestResult::passed()
}

/// `failed-access` (Twitter.agda:464-468) for the timelines: any session that
/// is not `active` expires both session-carrying commands and changes nothing,
/// while the tokenless one keeps answering.
#[quickcheck]
fn timelines_expire_for_inactive_sessions(generated: GeneratedWorld) -> TestResult {
	let db = database();
	seed_generated(&db, &generated);
	seed_revoked_session(&db, REVOKED_SID, ME);
	let before = world(&db);

	for sid in [UNUSED_SID, REVOKED_SID] {
		assert_eq!(
			personal_timeline(&db, sid, generated.n).expect("timeline"),
			EngineResult::Expired,
			"the personal timeline expands an inactive session"
		);
		assert_eq!(
			global_timeline(&db, Some(sid), generated.n).expect("timeline"),
			EngineResult::Expired,
			"the private global timeline expands an inactive session"
		);
	}
	assert_eq!(world(&db), before, "an expired command changes nothing");
	assert_eq!(
		returned(global_timeline(&db, None, generated.n).expect("timeline")),
		expected_global(&db, None, generated.n),
		"the tokenless timeline never expires"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// Sparse-follows regression (T6c).
//
// The personal timeline used to scan `idx_posts_seq` and evaluate an
// `EXISTS(follows)` predicate once per post, which costs O(#posts) no matter
// how few authors the user follows. It is now a per-author top-n window over
// the follow join. The answer must still be exactly `get-personal-timeline`
// (Twitter.agda:557-566): `take n` of the `live` posts of followed authors,
// newest-first.
// ---------------------------------------------------------------------------

const SPARSE_POSTS: usize = 5_000;
const SPARSE_AUTHORS: usize = 50;
const SPARSE_FOLLOWED: usize = 17;
const SPARSE_BASE: i64 = 10_000;
const SPARSE_ME: &str = "me";

/// Author `i % 50` of the sparse world: `author00` .. `author49`.
fn sparse_author(i: usize) -> String {
	format!("author{:02}", i % SPARSE_AUTHORS)
}

/// Seeds ~5 000 posts across 50 authors in a single transaction, interleaving
/// `followers-only`, replies and soft-deleted posts, and makes `me` follow
/// exactly one author. Returns `(id, author, live)` per post in `seq` order.
fn seed_sparse_world(db: &Db) -> Vec<(PostId, String, bool)> {
	db.write(|conn| {
		store::create_account(conn, SPARSE_ME, PASSWORD)?;
		for a in 0..SPARSE_AUTHORS {
			store::create_account(conn, &format!("author{a:02}"), PASSWORD)?;
		}
		store::activate_session(conn, SID, SPARSE_ME)?;
		for i in 0..SPARSE_POSTS {
			let id = PostId(SPARSE_BASE + i as i64);
			let author = sparse_author(i);
			let vis = if i % 7 == 0 {
				Visibility::FollowersOnly
			} else {
				Visibility::Everyone
			};
			let text = format!("post {i}");
			if i % 13 == 0 {
				store::insert_reply(conn, id, &author, &text, vis, PostId(SPARSE_BASE))?;
			} else {
				store::insert_post(conn, id, &author, &text, vis)?;
			}
			if i % 11 == 0 {
				store::soft_delete_post(conn, id)?;
			}
		}
		store::add_follow(conn, SPARSE_ME, &sparse_author(SPARSE_FOLLOWED))?;
		Ok(())
	})
	.expect("seed sparse world");
	(0..SPARSE_POSTS)
		.map(|i| {
			(
				PostId(SPARSE_BASE + i as i64),
				sparse_author(i),
				i % 11 != 0,
			)
		})
		.collect()
}

#[test]
fn sparse_follows_personal_timeline_is_the_followed_authors_top_n() {
	let db = database();
	let seeded = seed_sparse_world(&db);
	let followed = sparse_author(SPARSE_FOLLOWED);

	// Preconditions: the world really is sparse for `me`.
	assert_eq!(seeded.len(), SPARSE_POSTS);
	let mut authors: Vec<&str> = seeded.iter().map(|(_, a, _)| a.as_str()).collect();
	authors.sort_unstable();
	authors.dedup();
	assert_eq!(authors.len(), SPARSE_AUTHORS);
	assert!(
		seeded.iter().any(|(_, _, live)| !live),
		"the world contains deleted posts"
	);
	for a in 0..SPARSE_AUTHORS {
		assert_eq!(
			follows(&db, SPARSE_ME, &format!("author{a:02}")),
			a == SPARSE_FOLLOWED,
			"`me` follows exactly one author"
		);
	}

	// The expected answer, derived from the seed alone (newest-first is the
	// reverse of insertion order because `seq` increases monotonically).
	let expected_all: Vec<PostId> = seeded
		.iter()
		.rev()
		.filter(|(_, author, live)| *live && *author == followed)
		.map(|(pid, _, _)| *pid)
		.collect();
	assert!(
		expected_all.len() > 10,
		"the followed author has more than ten live posts"
	);

	// The engine agrees with the whole characterization ...
	assert_eq!(
		returned(personal_timeline(&db, SID, u32::MAX).expect("timeline")),
		expected_all
	);
	assert_eq!(
		returned(personal_timeline(&db, SID, u32::MAX).expect("timeline")),
		expected_personal(&db, SPARSE_ME, u32::MAX),
		"the answer is `filter follows-post-author (filter live newest-first)`"
	);

	// ... and with `take n` for the interesting bounds.
	let over = expected_all.len() as u32 + 1;
	for n in [0u32, 1, 10, over, u32::MAX] {
		let ids = returned(personal_timeline(&db, SID, n).expect("timeline"));
		let want = expected_all[..expected_all.len().min(n as usize)].to_vec();
		assert_eq!(ids, want, "n = {n}");
		assert_eq!(ids, expected_personal(&db, SPARSE_ME, n), "n = {n}");
		assert!(ids.len() as u64 <= u64::from(n));
		// No post of a non-followed author, and every entry is live.
		for pid in &ids {
			let post = post_of(&db, *pid).expect("seeded post");
			assert_eq!(post.author, followed);
			assert_eq!(post.status, PostStatus::Live);
		}
	}

	// Explicitly: published-by-others posts are absent.
	let others: Vec<PostId> = seeded
		.iter()
		.filter(|(_, author, _)| *author != followed)
		.map(|(pid, _, _)| *pid)
		.collect();
	let answer = returned(personal_timeline(&db, SID, u32::MAX).expect("timeline"));
	for pid in &others {
		assert!(!answer.contains(pid), "post by a non-followed author");
	}
}
