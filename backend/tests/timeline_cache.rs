//! Timeline id cache tests for task C1b.
//!
//! The cache adds no `Step` to `spec/Twitter.agda`. `read-personal-timeline`
//! and `read-global-timeline` are still `get-personal-timeline` /
//! `get-private-global-timeline` / `get-public-global-timeline`
//! (Twitter.agda:557-585), plus `failed-access` (464-468) for an inactive
//! supplied session. So there is nothing new to prove in `ImplProofs.agda`,
//! and what must hold instead is the equality this file checks: every cached
//! timeline answer equals the same call on a [`Db`] whose cache is disabled,
//! and no ids cached before a write are ever served after it.

use formal_twitter::db::{Db, TimelineKey};
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::auth::{authenticate, register, revoke_token};
use formal_twitter::engine::posts::{delete, publish};
use formal_twitter::engine::social::{follow, like, unfollow, unlike};
use formal_twitter::engine::time::time_passes;
use formal_twitter::engine::timeline::{global_timeline, personal_timeline};
use formal_twitter::model::{PostId, SessionId, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

const ALICE: &str = "alice";
const BOB: &str = "bob";
const CAROL: &str = "carol";
const PASSWORD: &str = "pw";
const ALICE_SID: SessionId = SessionId(1);
const BOB_SID: SessionId = SessionId(2);
/// A session id that was never issued.
const UNKNOWN_SID: SessionId = SessionId(999);

/// A live `everyone` post by [`ALICE`].
const PUBLIC: PostId = PostId(11);
/// A live `followers-only` post by [`ALICE`].
const PRIVATE: PostId = PostId(12);
/// A soft-deleted `everyone` post by [`ALICE`].
const GONE: PostId = PostId(13);
/// [`BOB`]'s public reply to [`PUBLIC`].
const REPLY: PostId = PostId(14);
/// A live `everyone` post by [`CAROL`].
const CAROL_PUBLIC: PostId = PostId(15);

/// The seeded world, identical in both databases of a pair: three accounts with
/// one active session each, five posts, and `alice -> bob` plus `bob -> alice`
/// follow edges.
fn seed(db: &Db) {
	db.write(|c| {
		store::create_account(c, ALICE, PASSWORD)?;
		store::create_account(c, BOB, PASSWORD)?;
		store::create_account(c, CAROL, PASSWORD)?;
		store::activate_session(c, ALICE_SID, ALICE)?;
		store::activate_session(c, BOB_SID, BOB)?;
		store::insert_post(c, PUBLIC, ALICE, "public", Visibility::Everyone)?;
		store::insert_post(c, PRIVATE, ALICE, "private", Visibility::FollowersOnly)?;
		store::insert_post(c, GONE, ALICE, "gone", Visibility::Everyone)?;
		store::soft_delete_post(c, GONE)?;
		store::insert_reply(c, REPLY, BOB, "a reply", Visibility::Everyone, PUBLIC)?;
		store::insert_post(c, CAROL_PUBLIC, CAROL, "carol", Visibility::Everyone)?;
		store::add_follow(c, ALICE, BOB)?;
		store::add_follow(c, BOB, ALICE)?;
		Ok(())
	})
	.expect("seed");
}

fn seeded(db: Db) -> Db {
	seed(&db);
	db
}

fn cached() -> Db {
	seeded(Db::in_memory().expect("in-memory database"))
}

fn uncached() -> Db {
	seeded(Db::in_memory_uncached().expect("in-memory database"))
}

fn ids(result: EngineResult) -> Vec<PostId> {
	match result {
		EngineResult::ReturnedTimeline(ids) => ids,
		other => panic!("expected a returned timeline, got {other:?}"),
	}
}

/// The three timeline forms of the spec, for one session and length.
fn forms(db: &Db, sid: SessionId, n: u32) -> [EngineResult; 3] {
	[
		personal_timeline(db, sid, n).expect("personal timeline"),
		global_timeline(db, Some(sid), n).expect("private global timeline"),
		global_timeline(db, None, n).expect("public global timeline"),
	]
}

fn anonymous(db: &Db, n: u32) -> Vec<PostId> {
	ids(global_timeline(db, None, n).expect("public global timeline"))
}

fn user_of(sid: SessionId) -> Option<&'static str> {
	match sid {
		ALICE_SID => Some(ALICE),
		BOB_SID => Some(BOB),
		_ => None,
	}
}

/// The keys `forms` uses for a session that is valid: `None` for an unknown
/// session, whose session-carrying forms must answer `Expired` and cache
/// nothing.
fn keys_for(sid: SessionId, n: u32) -> Vec<TimelineKey> {
	let mut keys = vec![TimelineKey::Anonymous(n)];
	if let Some(user) = user_of(sid) {
		keys.push(TimelineKey::Personal(user.to_owned(), n));
		keys.push(TimelineKey::Global(user.to_owned(), n));
	}
	keys
}

fn assert_forms_equal(cached: &Db, plain: &Db, sid: SessionId, n: u32) {
	assert_eq!(
		forms(cached, sid, n),
		forms(plain, sid, n),
		"session {sid:?}, n {n}"
	);
}

// ---------------------------------------------------------------------------
// Cold versus warm.
// ---------------------------------------------------------------------------

#[test]
fn cold_and_warm_answers_match_an_uncached_handle_for_every_length_and_session() {
	let cached = cached();
	let plain = uncached();
	for n in [0, 1, 2, 3, 5, 100] {
		for sid in [ALICE_SID, BOB_SID, UNKNOWN_SID] {
			// Cold: every entry is a miss and is inserted.
			assert_forms_equal(&cached, &plain, sid, n);
			// Warm: every entry is a hit and must answer identically.
			assert_forms_equal(&cached, &plain, sid, n);
		}
	}
}

#[test]
fn a_timeline_hit_answers_with_the_cached_ids() {
	let db = cached();
	let n = 4;
	// Seed the three keys with sentinel ids the database does not contain, so
	// a hit is recognisable from the answer alone: a store query could never
	// return them.
	let generation = db.cache_generation();
	let sentinels = [
		TimelineKey::Personal(ALICE.to_owned(), n),
		TimelineKey::Global(ALICE.to_owned(), n),
		TimelineKey::Anonymous(n),
	];
	for (index, key) in sentinels.iter().enumerate() {
		db.cache_put_timeline(generation, key.clone(), vec![PostId(9000 + index as i64)]);
	}
	// A hit returns the sentinel, so the ids cannot have come from the
	// timeline query. Only the *anonymous* form is database-free, though:
	// `personal_timeline` and `global_timeline (just sid)` run `active_user`
	// before consulting the cache, because session validity is never cached and
	// `Expired` must win over a cached list (see
	// `a_cached_list_never_makes_an_invalid_session_return_a_timeline`). So
	// this test proves id provenance for all three forms and no statement
	// count for the two session-carrying ones -- `global_timeline(db, None, n)`
	// returns before it takes the database lock at all.
	assert_eq!(
		ids(personal_timeline(&db, ALICE_SID, n).expect("personal")),
		vec![PostId(9000)]
	);
	assert_eq!(
		ids(global_timeline(&db, Some(ALICE_SID), n).expect("global")),
		vec![PostId(9001)]
	);
	assert_eq!(
		ids(global_timeline(&db, None, n).expect("anonymous")),
		vec![PostId(9002)]
	);
}

#[test]
fn a_miss_inserts_every_form_and_the_warm_read_repeats_it() {
	let db = cached();
	let n = 3;
	let cold = forms(&db, ALICE_SID, n);
	for key in keys_for(ALICE_SID, n) {
		assert!(
			db.cache_get_timeline(&key).is_some(),
			"{key:?} was not inserted by the cold read"
		);
	}
	let warm = forms(&db, ALICE_SID, n);
	assert_eq!(cold, warm, "the warm read differs from the cold one");
}

// ---------------------------------------------------------------------------
// Invalidation and reflection of writes.
// ---------------------------------------------------------------------------

/// A database and every post id it holds, in creation order, so two sides of a
/// pair can translate ids into comparable positions.
struct Side {
	db: Db,
	posts: Vec<PostId>,
}

impl Side {
	fn new(db: Db) -> Self {
		seed(&db);
		Self {
			db,
			posts: vec![PUBLIC, PRIVATE, GONE, REPLY, CAROL_PUBLIC],
		}
	}

	fn position(&self, pid: PostId) -> Option<usize> {
		self.posts.iter().position(|p| *p == pid)
	}

	fn push_created(&mut self, result: &EngineResult) {
		if let EngineResult::CreatedPost(pid) = result {
			self.posts.push(*pid);
		}
	}
}

fn expect_success(result: Result<EngineResult, formal_twitter::model::DbError>, what: &str) {
	assert_eq!(result.expect(what), EngineResult::Success, "{what}");
}

/// Warm all three forms for `sid`/`n` and return the keys they use.
fn warm(side: &mut Side, sid: SessionId, n: u32) -> Vec<TimelineKey> {
	let answers = forms(&side.db, sid, n);
	for answer in &answers {
		assert!(
			matches!(answer, EngineResult::ReturnedTimeline(_)),
			"warm read of a valid session answered {answer:?}"
		);
	}
	let keys = keys_for(sid, n);
	for key in &keys {
		assert!(
			side.db.cache_get_timeline(key).is_some(),
			"{key:?} missing after a warm read"
		);
	}
	keys
}

/// One write, applied to both sides, then the cache must be empty and a fresh
/// read must agree with the uncached side.
fn write_then_check(
	cached: &mut Side,
	plain: &mut Side,
	warm_keys: &[TimelineKey],
	write: impl Fn(&Db) -> EngineResult,
) {
	let got = write(&cached.db);
	let want = write(&plain.db);
	cached.push_created(&got);
	plain.push_created(&want);
	// The result itself may name a freshly allocated post, so compare after
	// recording it on both sides.
	assert_eq!(
		outcome(&got, cached),
		outcome(&want, plain),
		"write answered differently"
	);
	for key in warm_keys {
		assert!(
			cached.db.cache_get_timeline(key).is_none(),
			"{key:?} survived a write"
		);
	}
	// Every sample of every n the writes below use: nothing cached survives,
	// and the next reads answer like the uncached handle (ids translated to
	// positions, because `publish` allocates a different id on each side).
	assert_eq!(
		form_outcomes(cached, ALICE_SID, 50),
		form_outcomes(plain, ALICE_SID, 50),
		"reads after the write differ"
	);
	assert_eq!(world(cached), world(plain));
}

#[test]
fn every_write_invalidates_all_three_kinds_and_the_next_read_reflects_it() {
	let mut cached = Side::new(Db::in_memory().expect("cached database"));
	let mut plain = Side::new(Db::in_memory_uncached().expect("uncached database"));
	let n = 50;

	let keys = warm(&mut cached, ALICE_SID, n);
	assert_forms_equal(&cached.db, &plain.db, ALICE_SID, n);
	write_then_check(&mut cached, &mut plain, &keys, |db| {
		publish(db, ALICE_SID, "published", None).expect("publish")
	});

	let keys = warm(&mut cached, ALICE_SID, n);
	write_then_check(&mut cached, &mut plain, &keys, |db| {
		publish(db, ALICE_SID, "replied", Some(PUBLIC)).expect("reply")
	});

	let keys = warm(&mut cached, ALICE_SID, n);
	write_then_check(&mut cached, &mut plain, &keys, |db| {
		delete(db, ALICE_SID, PUBLIC).expect("delete")
	});

	let keys = warm(&mut cached, ALICE_SID, n);
	write_then_check(&mut cached, &mut plain, &keys, |db| {
		follow(db, ALICE_SID, CAROL).expect("follow")
	});

	let keys = warm(&mut cached, ALICE_SID, n);
	write_then_check(&mut cached, &mut plain, &keys, |db| {
		unfollow(db, ALICE_SID, BOB).expect("unfollow")
	});
}

#[test]
fn time_passes_invalidates_and_expires_the_session_forms() {
	let mut cached = Side::new(Db::in_memory().expect("cached database"));
	let plain = Side::new(Db::in_memory_uncached().expect("uncached database"));
	let keys = warm(&mut cached, ALICE_SID, 5);
	expect_success(time_passes(&cached.db), "time-passes");
	expect_success(time_passes(&plain.db), "time-passes");
	for key in &keys {
		assert!(
			cached.db.cache_get_timeline(key).is_none(),
			"{key:?} survived time-passes"
		);
	}
	assert_eq!(
		personal_timeline(&cached.db, ALICE_SID, 5).expect("personal"),
		EngineResult::Expired
	);
	assert_eq!(
		global_timeline(&cached.db, Some(ALICE_SID), 5).expect("global"),
		EngineResult::Expired
	);
	assert_forms_equal(&cached.db, &plain.db, ALICE_SID, 5);
}

/// Every mutating command reports through `Db::write`, so every one of them
/// must clear the whole cache -- not only the post/follow commands covered by
/// `every_write_invalidates_all_three_kinds_and_the_next_read_reflects_it`.
/// `like`, `unlike`, `register`, `login` and `logout` are checked here
/// directly, because the invalidation policy is *total*: a `like` leaves the id
/// lists themselves unchanged but drops them anyway (the stale value it must
/// prevent is the post body -- the like count -- which `tests/cache.rs`
/// covers), and the three auth commands change the session a session-carrying
/// key is named after.
#[test]
fn like_unlike_register_login_and_logout_clear_the_cache() {
	let db = cached();
	let n = 5;
	let cleared = |what: &str| {
		for key in keys_for(ALICE_SID, n) {
			assert!(
				db.cache_get_timeline(&key).is_none(),
				"{what}: {key:?} survived the write"
			);
		}
	};

	// Warm, run the command, assert the whole cache went -- one command at a
	// time, so each clearing is attributed to that command alone.
	let _ = warm_keys(&db, ALICE_SID, n);
	expect_success(like(&db, ALICE_SID, CAROL_PUBLIC), "like");
	cleared("like");

	let _ = warm_keys(&db, ALICE_SID, n);
	expect_success(unlike(&db, ALICE_SID, CAROL_PUBLIC), "unlike");
	cleared("unlike");

	let _ = warm_keys(&db, ALICE_SID, n);
	expect_success(register(&db, "dave", PASSWORD), "register");
	cleared("register");

	let _ = warm_keys(&db, ALICE_SID, n);
	assert!(
		matches!(
			authenticate(&db, CAROL, PASSWORD).expect("login"),
			EngineResult::IssuedSession(_)
		),
		"login issues a session"
	);
	cleared("login");

	let _ = warm_keys(&db, ALICE_SID, n);
	expect_success(revoke_token(&db, BOB_SID), "logout");
	cleared("logout");

	// After all of it, the cache is still an exact stand-in for the database.
	assert_forms_equal(&db, &uncached(), ALICE_SID, n);
}

// ---------------------------------------------------------------------------
// Session precedence: a cached list never outlives the session check.
// ---------------------------------------------------------------------------

#[test]
fn a_cached_list_never_makes_an_invalid_session_return_a_timeline() {
	let db = cached();
	let n = 3;
	// Warm every key, then inject entries under the users' names too: even if
	// such an entry exists, the session check must run first.
	let _ = warm_keys(&db, ALICE_SID, n);
	let generation = db.cache_generation();
	db.cache_put_timeline(
		generation,
		TimelineKey::Personal(ALICE.to_owned(), n),
		vec![PUBLIC],
	);
	db.cache_put_timeline(
		generation,
		TimelineKey::Global(ALICE.to_owned(), n),
		vec![PUBLIC],
	);
	assert_eq!(
		personal_timeline(&db, UNKNOWN_SID, n).expect("personal"),
		EngineResult::Expired
	);
	assert_eq!(
		global_timeline(&db, Some(UNKNOWN_SID), n).expect("global"),
		EngineResult::Expired
	);

	// A revoked session is likewise checked before any cached list.
	let db = cached();
	let _ = warm_keys(&db, ALICE_SID, n);
	expect_success(revoke_token(&db, ALICE_SID), "revoke-token");
	let generation = db.cache_generation();
	db.cache_put_timeline(
		generation,
		TimelineKey::Personal(ALICE.to_owned(), n),
		vec![PUBLIC],
	);
	db.cache_put_timeline(
		generation,
		TimelineKey::Global(ALICE.to_owned(), n),
		vec![PUBLIC],
	);
	// The revoked user's keys really are present: the answers below come from
	// the session check, not from an empty cache.
	assert!(
		db.cache_get_timeline(&TimelineKey::Personal(ALICE.to_owned(), n))
			.is_some()
	);
	assert!(
		db.cache_get_timeline(&TimelineKey::Global(ALICE.to_owned(), n))
			.is_some()
	);
	assert_eq!(
		personal_timeline(&db, ALICE_SID, n).expect("personal"),
		EngineResult::Expired
	);
	assert_eq!(
		global_timeline(&db, Some(ALICE_SID), n).expect("global"),
		EngineResult::Expired
	);
}

/// Warm the three forms and return their keys, without the `Side` wrapper.
fn warm_keys(db: &Db, sid: SessionId, n: u32) -> Vec<TimelineKey> {
	let answers = forms(db, sid, n);
	assert!(
		answers
			.iter()
			.all(|answer| matches!(answer, EngineResult::ReturnedTimeline(_)))
	);
	let keys = keys_for(sid, n);
	for key in &keys {
		assert!(db.cache_get_timeline(key).is_some(), "{key:?} missing");
	}
	keys
}

// ---------------------------------------------------------------------------
// Key separation and `take n`.
// ---------------------------------------------------------------------------

#[test]
fn the_three_kinds_and_distinct_lengths_are_separate_keys() {
	let db = cached();
	let n = 2;
	let generation = db.cache_generation();
	let personal = vec![PostId(101)];
	let private = vec![PostId(201), PostId(202)];
	let public = vec![PostId(301), PostId(302)];
	db.cache_put_timeline(
		generation,
		TimelineKey::Personal(ALICE.to_owned(), n),
		personal.clone(),
	);
	db.cache_put_timeline(
		generation,
		TimelineKey::Global(ALICE.to_owned(), n),
		private.clone(),
	);
	db.cache_put_timeline(generation, TimelineKey::Anonymous(n), public.clone());
	assert_eq!(
		ids(personal_timeline(&db, ALICE_SID, n).expect("personal")),
		personal
	);
	assert_eq!(
		ids(global_timeline(&db, Some(ALICE_SID), n).expect("private global")),
		private
	);
	assert_eq!(anonymous(&db, n), public);

	// A different `n` is a different key, even for the same timeline.
	db.cache_put_timeline(
		generation,
		TimelineKey::Personal(ALICE.to_owned(), 1),
		vec![PostId(401)],
	);
	assert_eq!(
		ids(personal_timeline(&db, ALICE_SID, 1).expect("personal n=1")),
		vec![PostId(401)]
	);
	assert_eq!(
		ids(personal_timeline(&db, ALICE_SID, 2).expect("personal n=2")),
		personal
	);
}

#[test]
fn take_n_saturates_and_zero_is_empty() {
	let cached = cached();
	let plain = uncached();
	for n in [0, 1, 2, 3, 1000] {
		assert_forms_equal(&cached, &plain, ALICE_SID, n);
	}
	for answer in forms(&cached, ALICE_SID, 0) {
		assert_eq!(answer, EngineResult::ReturnedTimeline(Vec::new()));
	}
	// `n` larger than the whole filtered list returns every entry: the short
	// answers are its prefixes.
	let big = forms(&cached, ALICE_SID, 1000);
	let two = forms(&cached, ALICE_SID, 2);
	for (big, two) in big.into_iter().zip(two) {
		let big = ids(big);
		let two = ids(two);
		assert_eq!(two, big[..two.len()], "n=2 is a prefix of the whole list");
	}
}

// ---------------------------------------------------------------------------
// Property: a cached handle answers exactly like an uncached one, and its
// cache reacts to every write.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Op {
	Publish,
	Reply,
	Delete,
	Follow,
	Unfollow,
	Timelines,
}

#[derive(Clone, Copy, Debug)]
struct Step {
	op: Op,
	target: u8,
	n: u8,
	session: u8,
}

impl Arbitrary for Step {
	fn arbitrary(g: &mut Gen) -> Self {
		let op = match u8::arbitrary(g) % 6 {
			0 => Op::Publish,
			1 => Op::Reply,
			2 => Op::Delete,
			3 => Op::Follow,
			4 => Op::Unfollow,
			_ => Op::Timelines,
		};
		Self {
			op,
			target: u8::arbitrary(g),
			n: u8::arbitrary(g) % 8,
			session: u8::arbitrary(g),
		}
	}
}

/// `0` alice, `1` bob, `2` an unissued session.
fn sid(selector: u8) -> SessionId {
	match selector % 3 {
		0 => ALICE_SID,
		1 => BOB_SID,
		_ => UNKNOWN_SID,
	}
}

fn apply(side: &mut Side, step: Step) -> EngineResult {
	let target = side.posts[step.target as usize % side.posts.len()];
	let followee = if step.target.is_multiple_of(2) {
		ALICE
	} else {
		BOB
	};
	let result = match step.op {
		Op::Publish => publish(&side.db, sid(step.session), "published", None),
		Op::Reply => publish(&side.db, sid(step.session), "replied", Some(target)),
		Op::Delete => delete(&side.db, sid(step.session), target),
		Op::Follow => follow(&side.db, sid(step.session), followee),
		Op::Unfollow => unfollow(&side.db, sid(step.session), followee),
		Op::Timelines => unreachable!("timelines are handled separately"),
	}
	.expect("command");
	side.push_created(&result);
	result
}

/// `true` for the operations that are one `Db::write`.
fn is_write(op: Op) -> bool {
	!matches!(op, Op::Timelines)
}

#[derive(Debug, PartialEq)]
enum Outcome {
	Success,
	Denied,
	Expired,
	ReturnedTimeline(Vec<Option<usize>>),
	CreatedPost,
}

fn outcome(result: &EngineResult, side: &Side) -> Outcome {
	match result {
		EngineResult::Success => Outcome::Success,
		EngineResult::Denied => Outcome::Denied,
		EngineResult::Expired => Outcome::Expired,
		EngineResult::CreatedPost(_) => Outcome::CreatedPost,
		EngineResult::ReturnedTimeline(ids) => {
			Outcome::ReturnedTimeline(ids.iter().map(|pid| side.position(*pid)).collect())
		}
		other => panic!("unexpected result {other:?}"),
	}
}

fn form_outcomes(side: &Side, session: SessionId, n: u32) -> [Outcome; 3] {
	forms(&side.db, session, n).map(|result| outcome(&result, side))
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
			for name in [ALICE, BOB, CAROL] {
				out.push(format!("account {name} {:?}", store::get_account(c, name)?));
			}
			for session in [ALICE_SID, BOB_SID, UNKNOWN_SID] {
				out.push(format!(
					"session {:?} {:?}",
					session,
					store::get_session(c, session)?
				));
			}
			for (follower, followee) in [(ALICE, BOB), (BOB, ALICE), (ALICE, CAROL)] {
				out.push(format!(
					"follow {follower}->{followee} {}",
					store::is_following(c, follower, followee)?
				));
			}
			Ok(out)
		})
		.expect("world snapshot")
}

#[quickcheck]
fn cached_timelines_always_match_uncached_and_react_to_writes(steps: Vec<Step>) -> TestResult {
	let mut cached = Side::new(Db::in_memory().expect("cached database"));
	let mut plain = Side::new(Db::in_memory_uncached().expect("uncached database"));
	// Every key a read has used since the last write. A write must clear them
	// all, which is what makes a disabled invalidation fail below.
	let mut used_keys: Vec<TimelineKey> = Vec::new();

	for step in steps.into_iter().take(8) {
		if is_write(step.op) {
			// Warm every kind through the cached handle first. The read is
			// asserted against the uncached handle, and makes the post-write
			// absence assertion below non-vacuous: a cache that never stored
			// anything, or that kept entries across writes, fails here.
			for key in warm(&mut cached, ALICE_SID, u32::from(step.n % 8)) {
				used_keys.push(key);
			}
			assert_eq!(
				form_outcomes(&cached, ALICE_SID, u32::from(step.n % 8)),
				form_outcomes(&plain, ALICE_SID, u32::from(step.n % 8)),
				"{step:?}: warm reads differ"
			);
			let got = apply(&mut cached, step);
			let want = apply(&mut plain, step);
			assert_eq!(
				outcome(&got, &cached),
				outcome(&want, &plain),
				"{step:?} answered differently"
			);
			for key in used_keys.drain(..) {
				assert!(
					cached.db.cache_get_timeline(&key).is_none(),
					"{step:?}: {key:?} survived a write"
				);
			}
			// The very next read reflects the write and agrees with the
			// uncached handle.
			for key in warm(&mut cached, ALICE_SID, u32::from(step.n % 8)) {
				used_keys.push(key);
			}
			assert_eq!(
				form_outcomes(&cached, ALICE_SID, u32::from(step.n % 8)),
				form_outcomes(&plain, ALICE_SID, u32::from(step.n % 8)),
				"{step:?}: reads after the write differ"
			);
		} else {
			let session = sid(step.session);
			let n = u32::from(step.n % 8);
			let got = form_outcomes(&cached, session, n);
			let want = form_outcomes(&plain, session, n);
			assert_eq!(got, want, "{step:?}: timelines differ");
			// A returned timeline is cached now. This is what a dead timeline
			// cache fails: the assertion is not about agreement, which a cache
			// that always misses would still satisfy.
			if let Some(user) = user_of(session) {
				if matches!(got[0], Outcome::ReturnedTimeline(_)) {
					let key = TimelineKey::Personal(user.to_owned(), n);
					assert!(
						cached.db.cache_get_timeline(&key).is_some(),
						"{step:?}: {key:?} missing after a hit"
					);
					used_keys.push(key);
				}
				if matches!(got[1], Outcome::ReturnedTimeline(_)) {
					let key = TimelineKey::Global(user.to_owned(), n);
					assert!(
						cached.db.cache_get_timeline(&key).is_some(),
						"{step:?}: {key:?} missing after a hit"
					);
					used_keys.push(key);
				}
			}
			let key = TimelineKey::Anonymous(n);
			assert!(
				cached.db.cache_get_timeline(&key).is_some(),
				"{step:?}: {key:?} missing after a hit"
			);
			used_keys.push(key);
		}
		assert_eq!(world(&cached), world(&plain), "{step:?}: worlds differ");
	}
	TestResult::passed()
}
