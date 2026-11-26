//! Cache tests for task C1a: the in-memory cache of public post bodies.
//!
//! The cache adds no `Step` to `spec/Twitter.agda`. `read-post` is still
//! `read-post-logged-in` / `read-post-anonymously` (Twitter.agda:518-555) and
//! `failed-access` (464-468); the cache is only another way to reach the same
//! answer. So there is nothing new to prove in `ImplProofs.agda`, and what must
//! hold instead is the equality this file checks: a cached `read_post` always
//! agrees with the same call on a [`Db`] whose cache is disabled, and the cache
//! never holds anything the database disagrees with.

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::posts::{delete, publish, read_post};
use formal_twitter::engine::social::{follow, like, unfollow, unlike};
use formal_twitter::engine::time::time_passes;
use formal_twitter::model::{DbError, PostId, PostStatus, PublicPost, SessionId, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

const ALICE: &str = "alice";
const BOB: &str = "bob";
const PASSWORD: &str = "pw";
const ALICE_SID: SessionId = SessionId(1);
const BOB_SID: SessionId = SessionId(2);
/// A session id that was never issued.
const UNKNOWN_SID: SessionId = SessionId(999);

/// A live `everyone` post by [`ALICE`] with two likes and one reply.
const PUBLIC: PostId = PostId(11);
/// A live `followers-only` post by [`ALICE`].
const PRIVATE: PostId = PostId(12);
/// A soft-deleted `everyone` post by [`ALICE`].
const GONE: PostId = PostId(13);
/// [`BOB`]'s public reply to [`PUBLIC`].
const REPLY: PostId = PostId(14);

/// The seeded world, identical in both databases of a pair: two accounts, one
/// active session each, three posts by [`ALICE`] (public, followers-only and
/// deleted), one public reply, and two likes on [`PUBLIC`].
fn seed(db: &Db) {
	db.write(|c| {
		store::create_account(c, ALICE, PASSWORD)?;
		store::create_account(c, BOB, PASSWORD)?;
		store::activate_session(c, ALICE_SID, ALICE)?;
		store::activate_session(c, BOB_SID, BOB)?;
		store::insert_post(c, PUBLIC, ALICE, "public", Visibility::Everyone)?;
		store::insert_post(c, PRIVATE, ALICE, "private", Visibility::FollowersOnly)?;
		store::insert_post(c, GONE, ALICE, "gone", Visibility::Everyone)?;
		store::soft_delete_post(c, GONE)?;
		store::insert_reply(c, REPLY, BOB, "a reply", Visibility::Everyone, PUBLIC)?;
		store::add_like(c, PUBLIC, ALICE)?;
		store::add_like(c, PUBLIC, BOB)?;
		Ok(())
	})
	.expect("seed");
}

fn seeded() -> Db {
	let db = Db::in_memory().expect("in-memory database");
	seed(&db);
	db
}

fn read(db: &Db, session: Option<SessionId>, pid: PostId) -> EngineResult {
	read_post(db, session, pid).expect("read-post")
}

fn expect_success(result: Result<EngineResult, DbError>, what: &str) {
	assert_eq!(result.expect(what), EngineResult::Success, "{what}");
}

fn returned(result: &EngineResult) -> (&str, &str, u64, &[PostId]) {
	match result {
		EngineResult::ReturnedPost {
			author,
			text,
			likes,
			replies,
		} => (author, text, *likes, replies),
		other => panic!("expected a returned post, got {other:?}"),
	}
}

/// The body the database holds for `pid`, built the way the cache does.
fn database_body(db: &Db, pid: PostId) -> PublicPost {
	db.read(|c| {
		let post = store::get_post(c, pid)?.expect("post exists");
		Ok(PublicPost {
			author: post.author,
			text: post.text,
			likes: store::like_count(c, pid)?.max(0) as u64,
			replies: store::replies_of(c, pid)?,
		})
	})
	.expect("database body")
}

// ---------------------------------------------------------------------------
// Deterministic behaviour: hits, invalidation, and what is never cached.
// ---------------------------------------------------------------------------

#[test]
fn a_public_read_is_cached_and_repeats_identically() {
	let db = seeded();
	assert_eq!(
		db.cache_get(PUBLIC),
		None,
		"nothing is cached before a read"
	);

	let first = read(&db, Some(ALICE_SID), PUBLIC);
	assert!(
		db.cache_get(PUBLIC).is_some(),
		"a miss is inserted so the next read can hit it"
	);
	let second = read(&db, Some(ALICE_SID), PUBLIC);
	assert_eq!(first, second, "the second read is the cached answer");

	assert_eq!(
		db.cache_get(PUBLIC),
		Some(PublicPost {
			author: ALICE.to_owned(),
			text: "public".to_owned(),
			likes: 2,
			replies: vec![REPLY],
		}),
		"the cached body is the returned-post body"
	);
	assert_eq!(returned(&first), (ALICE, "public", 2, &[REPLY][..]));

	// The body is reader-independent, so every session and the anonymous
	// reader get exactly the same answer.
	assert_eq!(read(&db, Some(BOB_SID), PUBLIC), first);
	assert_eq!(read(&db, None, PUBLIC), first);
	assert_eq!(read(&db, Some(UNKNOWN_SID), PUBLIC), EngineResult::Expired);
}

#[test]
fn a_like_is_reflected_after_the_write() {
	let db = seeded();
	assert_eq!(returned(&read(&db, Some(ALICE_SID), PUBLIC)).2, 2);
	assert!(db.cache_get(PUBLIC).is_some());

	expect_success(unlike(&db, BOB_SID, PUBLIC), "unlike");
	assert_eq!(db.cache_get(PUBLIC), None, "a write drops the cached body");
	assert_eq!(returned(&read(&db, Some(ALICE_SID), PUBLIC)).2, 1);

	expect_success(like(&db, BOB_SID, PUBLIC), "like");
	assert_eq!(returned(&read(&db, Some(ALICE_SID), PUBLIC)).2, 2);
}

#[test]
fn a_reply_is_reflected_after_the_write() {
	let db = seeded();
	assert_eq!(returned(&read(&db, None, PUBLIC)).3, &[REPLY][..]);

	let created = publish(&db, BOB_SID, "second reply", Some(PUBLIC)).expect("reply");
	let EngineResult::CreatedPost(fresh) = created else {
		panic!("expected a created post, got {created:?}");
	};
	assert_eq!(
		db.cache_get(PUBLIC),
		None,
		"a reply drops the cached parent"
	);

	let after = read(&db, None, PUBLIC);
	let (_, _, _, replies) = returned(&after);
	assert_eq!(replies, &[fresh, REPLY][..], "newest reply first");
	assert_eq!(db.cache_get(PUBLIC), Some(database_body(&db, PUBLIC)));
}

#[test]
fn a_deletion_is_reflected_after_the_write() {
	let db = seeded();
	assert_eq!(returned(&read(&db, Some(ALICE_SID), PUBLIC)).1, "public");
	assert!(db.cache_get(PUBLIC).is_some());

	expect_success(delete(&db, ALICE_SID, PUBLIC), "delete");
	assert_eq!(db.cache_get(PUBLIC), None, "a delete drops the cached body");
	assert_eq!(read(&db, Some(ALICE_SID), PUBLIC), EngineResult::Denied);
	assert_eq!(read(&db, None, PUBLIC), EngineResult::Expired);
	assert_eq!(db.cache_get(PUBLIC), None, "a denial is never cached");
}

#[test]
fn time_passes_drops_the_cache_and_keeps_the_body_readable_anonymously() {
	let db = seeded();
	let before = read(&db, Some(ALICE_SID), PUBLIC);
	assert!(db.cache_get(PUBLIC).is_some());

	expect_success(time_passes(&db), "time-passes");
	assert_eq!(db.cache_get(PUBLIC), None, "time-passes is a write");
	assert_eq!(read(&db, Some(ALICE_SID), PUBLIC), EngineResult::Expired);
	assert_eq!(read(&db, None, PUBLIC), before);
}

#[test]
fn a_followers_only_post_is_never_cached() {
	let db = seeded();
	assert_eq!(read(&db, Some(BOB_SID), PRIVATE), EngineResult::Denied);
	assert_eq!(db.cache_get(PRIVATE), None);

	expect_success(follow(&db, BOB_SID, ALICE), "follow");
	let visible = read(&db, Some(BOB_SID), PRIVATE);
	assert_eq!(returned(&visible), (ALICE, "private", 0, &[][..]));
	assert_eq!(
		db.cache_get(PRIVATE),
		None,
		"a followers-only body depends on the reader and is not cached"
	);

	expect_success(unfollow(&db, BOB_SID, ALICE), "unfollow");
	assert_eq!(
		read(&db, Some(BOB_SID), PRIVATE),
		EngineResult::Denied,
		"the earlier readable answer is not served from the cache"
	);
	assert_eq!(
		read(&db, None, PRIVATE),
		EngineResult::Expired,
		"is-post-public rejects it"
	);
	assert_eq!(db.cache_get(PRIVATE), None);

	// Reads of the private post never disturb the public one.
	assert_eq!(returned(&read(&db, None, PUBLIC)).2, 2);
}

#[test]
fn anonymous_reads_cache_only_public_posts() {
	let db = seeded();
	assert_eq!(read(&db, None, GONE), EngineResult::Expired);
	assert_eq!(read(&db, None, PRIVATE), EngineResult::Expired);
	assert_eq!(read(&db, None, PostId(4242)), EngineResult::Expired);
	for pid in [GONE, PRIVATE, PostId(4242)] {
		assert_eq!(db.cache_get(pid), None, "{pid:?} must not be cached");
	}

	let public = read(&db, None, PUBLIC);
	assert_eq!(returned(&public).1, "public");
	assert_eq!(db.cache_get(PUBLIC), Some(database_body(&db, PUBLIC)));
	assert_eq!(read(&db, None, PUBLIC), public);
}

// ---------------------------------------------------------------------------
// Property: the cache never changes an answer.
// ---------------------------------------------------------------------------

/// One command of the scripted property: the kind, a selector for the post and
/// a selector for the session (`0` is the anonymous reader).
#[derive(Clone, Copy, Debug)]
struct Step {
	op: Op,
	target: u8,
	selector: u8,
}

#[derive(Clone, Copy, Debug)]
enum Op {
	Publish,
	Reply,
	Like,
	Unlike,
	Delete,
	Follow,
	Unfollow,
	Read,
}

impl Arbitrary for Step {
	fn arbitrary(g: &mut Gen) -> Self {
		let op = match u8::arbitrary(g) % 8 {
			0 => Op::Publish,
			1 => Op::Reply,
			2 => Op::Like,
			3 => Op::Unlike,
			4 => Op::Delete,
			5 => Op::Follow,
			6 => Op::Unfollow,
			_ => Op::Read,
		};
		Self {
			op,
			target: u8::arbitrary(g),
			selector: u8::arbitrary(g),
		}
	}
}

/// One database of the pair, plus every post id it holds in the order the
/// script created them. The two sides of a pair agree on that order, so a
/// position identifies a post on both.
struct Side {
	db: Db,
	posts: Vec<PostId>,
}

impl Side {
	fn new(db: Db) -> Self {
		seed(&db);
		Self {
			db,
			posts: vec![PUBLIC, PRIVATE, GONE, REPLY],
		}
	}

	fn post(&self, selector: u8) -> PostId {
		self.posts[selector as usize % self.posts.len()]
	}

	fn position(&self, pid: PostId) -> Option<usize> {
		self.posts.iter().position(|p| *p == pid)
	}
}

/// `0` is the anonymous reader, `1`/`2` the seeded sessions, `3` a session that
/// was never issued.
fn session(selector: u8) -> Option<SessionId> {
	match selector % 4 {
		0 => None,
		1 => Some(ALICE_SID),
		2 => Some(BOB_SID),
		_ => Some(UNKNOWN_SID),
	}
}

fn apply(side: &mut Side, step: Step) -> EngineResult {
	let target = side.post(step.target);
	let sid = session(step.selector).unwrap_or(ALICE_SID);
	let followee = if step.target.is_multiple_of(2) {
		ALICE
	} else {
		BOB
	};
	let result = match step.op {
		Op::Publish => publish(&side.db, sid, "published", None),
		Op::Reply => publish(&side.db, sid, "replied", Some(target)),
		Op::Like => like(&side.db, sid, target),
		Op::Unlike => unlike(&side.db, sid, target),
		Op::Delete => delete(&side.db, sid, target),
		Op::Follow => follow(&side.db, sid, followee),
		Op::Unfollow => unfollow(&side.db, sid, followee),
		Op::Read => read_post(&side.db, session(step.selector), target),
	}
	.expect("command");
	if let EngineResult::CreatedPost(pid) = &result {
		side.posts.push(*pid);
	}
	result
}

/// A command's answer with post ids replaced by positions, so the two sides of
/// a pair compare even though `publish` allocates different ids in each.
#[derive(Debug, PartialEq)]
enum Outcome {
	Success,
	Denied,
	Expired,
	LoginFailed,
	SignupFailed,
	ReturnedTimeline(Vec<Option<usize>>),
	IssuedSession,
	CreatedPost,
	ReturnedPost {
		author: String,
		text: String,
		likes: u64,
		replies: Vec<Option<usize>>,
	},
}

fn outcome(result: &EngineResult, side: &Side) -> Outcome {
	match result {
		EngineResult::Success => Outcome::Success,
		EngineResult::Denied => Outcome::Denied,
		EngineResult::Expired => Outcome::Expired,
		EngineResult::LoginFailed => Outcome::LoginFailed,
		EngineResult::SignupFailed => Outcome::SignupFailed,
		EngineResult::ReturnedTimeline(ids) => {
			Outcome::ReturnedTimeline(ids.iter().map(|pid| side.position(*pid)).collect())
		}
		EngineResult::IssuedSession(_) => Outcome::IssuedSession,
		EngineResult::CreatedPost(_) => Outcome::CreatedPost,
		EngineResult::ReturnedPost {
			author,
			text,
			likes,
			replies,
		} => Outcome::ReturnedPost {
			author: author.clone(),
			text: text.clone(),
			likes: *likes,
			replies: replies.iter().map(|pid| side.position(*pid)).collect(),
		},
	}
}

/// The whole world of `side`, post ids translated to positions.
fn world(side: &Side) -> Vec<String> {
	side.db
		.read(|c| {
			let mut out = Vec::new();
			for (index, pid) in side.posts.iter().enumerate() {
				let post = store::get_post(c, *pid)?;
				let likes = store::like_count(c, *pid)?;
				let replies = store::replies_of(c, *pid)?;
				let parent = post
					.as_ref()
					.and_then(|p| p.parent)
					.and_then(|p| side.position(p));
				let shown = post.map(|p| (p.author, p.text, p.visibility, p.status));
				out.push(format!(
					"{index}|{shown:?}|{parent:?}|{likes}|{:?}",
					replies
						.iter()
						.map(|r| side.position(*r))
						.collect::<Vec<_>>()
				));
			}
			for name in [ALICE, BOB] {
				out.push(format!("account {name} {:?}", store::get_account(c, name)?));
			}
			for sid in [ALICE_SID, BOB_SID, UNKNOWN_SID] {
				out.push(format!(
					"session {:?} {:?}",
					sid,
					store::get_session(c, sid)?
				));
			}
			for (follower, followee) in [(BOB, ALICE), (ALICE, BOB)] {
				out.push(format!(
					"follow {follower}->{followee} {}",
					store::is_following(c, follower, followee)?
				));
			}
			Ok(out)
		})
		.expect("world snapshot")
}

/// Every post, read by every kind of reader: the cached side must answer what
/// the uncached side answers. Each pair of reads is a miss followed by a hit,
/// so this also checks that a hit equals the miss it caches.
fn assert_all_reads_agree(cached: &Side, plain: &Side) {
	assert_eq!(cached.posts.len(), plain.posts.len());
	for index in 0..cached.posts.len() {
		for selector in [0u8, 1, 2, 3] {
			let got =
				read_post(&cached.db, session(selector), cached.posts[index]).expect("cached");
			let want =
				read_post(&plain.db, session(selector), plain.posts[index]).expect("uncached");
			assert_eq!(
				outcome(&got, cached),
				outcome(&want, plain),
				"post {index}, selector {selector}"
			);
			let again =
				read_post(&cached.db, session(selector), cached.posts[index]).expect("cached hit");
			assert_eq!(got, again, "post {index}, selector {selector}: hit differs");
		}
	}
}

/// Whatever the cache holds is exactly the database's current body, and only
/// `live` `everyone` posts are ever held.
fn assert_cache_matches_database(side: &Side) {
	for pid in &side.posts {
		let Some(entry) = side.db.cache_get(*pid) else {
			continue;
		};
		let post = side
			.db
			.read(|c| store::get_post(c, *pid))
			.expect("read post")
			.expect("cached post exists");
		assert_eq!(
			post.status,
			PostStatus::Live,
			"{pid:?} is cached but not live"
		);
		assert_eq!(
			post.visibility,
			Visibility::Everyone,
			"{pid:?} is cached but not public"
		);
		assert_eq!(
			entry,
			database_body(&side.db, *pid),
			"{pid:?} is cached with a stale body"
		);
	}
}

#[quickcheck]
fn cached_reads_always_match_uncached_reads(steps: Vec<Step>) -> TestResult {
	let cached = Side::new(Db::in_memory().expect("cached database"));
	let plain = Side::new(Db::in_memory_uncached().expect("uncached database"));
	let mut cached = cached;
	let mut plain = plain;
	for step in steps.into_iter().take(8) {
		let got = apply(&mut cached, step);
		let want = apply(&mut plain, step);
		assert_eq!(
			outcome(&got, &cached),
			outcome(&want, &plain),
			"{step:?} answered differently"
		);
		assert_eq!(
			world(&cached),
			world(&plain),
			"{step:?} left a different world"
		);
		assert_cache_matches_database(&cached);
		assert_all_reads_agree(&cached, &plain);
	}
	TestResult::passed()
}

// A second handle on the same file has its own cache, so the benchmarks can
// read the pre-cache path against the same data. It is only ever read from: a
// write through it would not invalidate the first handle's cache, which is why
// the server keeps exactly one `Db`.
#[test]
fn a_second_uncached_handle_reads_the_same_file_without_a_cache() {
	let dir = tempfile::tempdir().expect("temp dir");
	let path = dir.path().join("db.sqlite");
	let path = path.to_str().expect("utf-8 path");
	let db = Db::new(path).expect("cached database");
	seed(&db);
	let cached = read(&db, Some(ALICE_SID), PUBLIC);
	assert!(db.cache_get(PUBLIC).is_some(), "the first handle caches");
	let plain = Db::new_uncached(path).expect("uncached database");
	assert_eq!(read(&plain, Some(ALICE_SID), PUBLIC), cached);
	assert!(db.cache_get(PUBLIC).is_some());
	assert_eq!(read(&db, Some(ALICE_SID), PUBLIC), cached);
	assert_eq!(db.cache_get(PUBLIC), Some(database_body(&db, PUBLIC)));
}
