//! Property and unit tests for the timeline engine (task T3b, migrated to the
//! Q1 world-state harness by task Q1b).
//!
//! Every expected timeline is a **pure** function of the generated
//! `WorldState` -- filter `newest_first`, then `take n` -- never a database
//! query. Each property cites the `Step` rule of `spec/Twitter.agda` and the
//! `ImplProofs.agda` lemma that rewrites the spec's nested `filter`s into that
//! characterization:
//!
//! | property | rule (Twitter.agda) | Agda lemma |
//! |---|---|---|
//! | `personal_timeline_is_the_followed_authors_live_posts` | `get-personal-timeline` (:557-566) | `personal-timeline`, `personal-char` |
//! | `private_global_timeline_is_the_readable_live_posts` | `get-private-global-timeline` (:568-576) | `private-global-timeline`, `global-char` |
//! | `public_global_timeline_is_the_public_live_posts` | `get-public-global-timeline` (:578-585) | `public-global-timeline`, `public-char` |
//! | `timelines_take_n_after_filtering` | `take n` (:560, :571, :583) | `personal-timeline`, `private-global-timeline`, `public-global-timeline` |
//! | `timelines_expire_with_an_inactive_session` | `failed-access` (:464-468) | `personal-timeline-expired`, `private-global-timeline-expired` |
//! | `public_global_timeline_never_expires` | `read-global-timeline nothing` | `public-global-timeline` |
//!
//! The characterizations (ImplProofs `personal-allowed` / `global-allowed` /
//! `public-allowed`):
//!
//! * personal: `live` and the session's user follows the author
//!   (`follows-post-author`, Twitter.agda:366-369 -- the user's own posts need
//!   a self-follow, they are not special-cased);
//! * private global: `live` and (`everyone` or followed) -- `CanReadPost`,
//!   Twitter.agda:158-179;
//! * public global: `live` and `everyone` -- `is-post-public`,
//!   Twitter.agda:342-357.
//!
//! All three filter the whole list before `take n`, so `n` bounds the answer,
//! never the scanned prefix; `take` saturates, so `n` larger than the filtered
//! list yields all of it. Replies are ordinary entries.
//!
//! Harness shape (see `support`): one in-memory database per `#[test]`, created
//! outside the quickcheck cases; each case resets it, materialises the generated
//! world and asserts the round-trip before the property runs. Properties that
//! need an active session (or a session-free world) derive it purely from the
//! generated world and re-materialise through `reseed`.

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::timeline::{global_timeline, personal_timeline};
use formal_twitter::model::{PostId, PostStatus, SessionId, SessionStatus, Visibility};
use quickcheck::{Arbitrary, Gen, TestResult};

use support::{AccountState, PostState, WorldState, check, from_db, materialise, reset};

// ---------------------------------------------------------------------------
// Generated argument: a length bound.
// ---------------------------------------------------------------------------

/// A small bound, so `take n` is exercised below, at and above the length of
/// the filtered list; `u32::MAX` is asserted explicitly in every property.
#[derive(Clone, Debug)]
struct Bound(u32);

impl Arbitrary for Bound {
	fn arbitrary(g: &mut Gen) -> Self {
		Bound(u32::arbitrary(g) % 8)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
		Box::new((0..self.0).rev().map(Bound))
	}
}

// ---------------------------------------------------------------------------
// Worlds and pure expected timelines.
// ---------------------------------------------------------------------------

fn account(password: &str, visibility: Visibility) -> AccountState {
	AccountState {
		password: password.to_string(),
		visibility,
	}
}

fn post(author: &str, text: &str, visibility: Visibility) -> PostState {
	PostState {
		author: author.to_string(),
		text: text.to_string(),
		visibility,
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: None,
	}
}

fn deleted(mut post: PostState) -> PostState {
	post.status = PostStatus::Deleted;
	post
}

fn follows(world: &WorldState, follower: &str, followee: &str) -> bool {
	world
		.follows
		.contains(&(follower.to_string(), followee.to_string()))
}

/// `personal-allowed` (ImplProofs.agda): `live` and followed. `take n` comes
/// *after* the filter, exactly as in `get-personal-timeline`.
fn personal_expected(world: &WorldState, user: &str, n: u32) -> Vec<PostId> {
	world
		.newest_first
		.iter()
		.copied()
		.filter(|pid| {
			let post = &world.posts[pid];
			post.status == PostStatus::Live && follows(world, user, &post.author)
		})
		.take(n as usize)
		.collect()
}

/// `global-allowed`: `live` and (`everyone` or followed).
fn private_global_expected(world: &WorldState, user: &str, n: u32) -> Vec<PostId> {
	world
		.newest_first
		.iter()
		.copied()
		.filter(|pid| {
			let post = &world.posts[pid];
			post.status == PostStatus::Live
				&& (post.visibility == Visibility::Everyone || follows(world, user, &post.author))
		})
		.take(n as usize)
		.collect()
}

/// `public-allowed`: `live` and `everyone` (`is-post-public`).
fn public_global_expected(world: &WorldState, n: u32) -> Vec<PostId> {
	world
		.newest_first
		.iter()
		.copied()
		.filter(|pid| {
			let post = &world.posts[pid];
			post.status == PostStatus::Live && post.visibility == Visibility::Everyone
		})
		.take(n as usize)
		.collect()
}

fn empty_world() -> WorldState {
	WorldState {
		accounts: BTreeMap::new(),
		sessions: HashMap::new(),
		posts: HashMap::new(),
		follows: BTreeSet::new(),
		newest_first: Vec::new(),
	}
}

/// A session id no world uses.
fn absent_session(world: &WorldState) -> SessionId {
	let mut id = 1_000_000;
	while world.sessions.contains_key(&SessionId(id)) {
		id += 1;
	}
	SessionId(id)
}

/// The smallest session id whose status is `active`, with its user.
fn first_active(world: &WorldState) -> Option<(SessionId, String)> {
	let mut ids = world.active_sessions();
	ids.sort_unstable_by_key(|sid| sid.0);
	let sid = *ids.first()?;
	match world.session_status(sid) {
		SessionStatus::Active(user) => Some((sid, user)),
		_ => unreachable!("listed as active"),
	}
}

/// `world` with at least one `active` session, that session's id and its user.
///
/// About half the generated worlds have no active session; adding one keeps
/// every case instead of discarding it.
fn with_actor(world: &WorldState) -> (WorldState, SessionId, String) {
	if let Some((sid, user)) = first_active(world) {
		return (world.clone(), sid, user);
	}
	let mut next = world.clone();
	let user = match next.accounts.keys().next().cloned() {
		Some(user) => user,
		None => {
			next.accounts.insert(
				"actor".to_string(),
				account("pw-actor", Visibility::Everyone),
			);
			"actor".to_string()
		}
	};
	let sid = absent_session(&next);
	next.sessions
		.insert(sid, SessionStatus::Active(user.clone()));
	next.validate().expect("the world with an actor is valid");
	(next, sid, user)
}

/// `world` with at least one `revoked` session, and such a session's id.
fn with_revoked_session(world: &WorldState) -> (WorldState, SessionId) {
	let mut ids: Vec<SessionId> = world
		.sessions
		.iter()
		.filter(|(_, status)| matches!(status, SessionStatus::Revoked))
		.map(|(sid, _)| *sid)
		.collect();
	ids.sort_unstable_by_key(|sid| sid.0);
	if let Some(sid) = ids.first() {
		return (world.clone(), *sid);
	}
	let sid = absent_session(world);
	let mut next = world.clone();
	next.sessions.insert(sid, SessionStatus::Revoked);
	next.validate()
		.expect("the world with a revoked session is valid");
	(next, sid)
}

/// Materialise `seeded` when it differs from the world the harness already
/// wrote, re-asserting the round-trip. Never builds a database.
fn reseed(db: &Db, world: &WorldState, seeded: &WorldState) {
	if seeded == world {
		return;
	}
	reset(db);
	materialise(db, seeded);
	assert_eq!(
		from_db(db),
		*seeded,
		"the materialiser must round-trip the derived world"
	);
}

fn returned(result: EngineResult) -> Vec<PostId> {
	match result {
		EngineResult::ReturnedTimeline(ids) => ids,
		other => panic!("expected a returned timeline, got {other:?}"),
	}
}

// ---------------------------------------------------------------------------
// T1: personal timeline -- `get-personal-timeline` (Twitter.agda:557-566).
// Agda: `personal-timeline` over `personal-char`.
// ---------------------------------------------------------------------------

/// The personal timeline is exactly `take n` of the live posts of followed
/// authors, in `newest-first` order. The session's own posts are not special:
/// they appear only after a self-follow (`follows-post-author`).
#[test]
fn personal_timeline_is_the_followed_authors_live_posts() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		reseed(db, world, &seeded);

		let ids = returned(personal_timeline(db, sid, bound.0).expect("timeline"));
		let expected = personal_expected(&seeded, &user, bound.0);
		assert_eq!(ids, expected, "take n of the followed authors' live posts");
		assert!(
			ids.len() as u64 <= u64::from(bound.0),
			"n bounds the answer"
		);

		// Every entry is live and by an author the user follows.
		for pid in &ids {
			let post = &seeded.posts[pid];
			assert_eq!(post.status, PostStatus::Live);
			assert!(
				follows(&seeded, &user, &post.author),
				"{pid:?} is by a followed author"
			);
		}

		// A longer bound extends the answer, never reorders it.
		let all = returned(personal_timeline(db, sid, u32::MAX).expect("timeline"));
		assert_eq!(all, personal_expected(&seeded, &user, u32::MAX));
		assert_eq!(ids, all[..ids.len()].to_vec(), "a prefix of the whole list");

		// Own posts need a self-follow; deleted and unfollowed rows never show.
		for (pid, post) in &seeded.posts {
			if post.author == user && post.status == PostStatus::Live {
				assert_eq!(
					all.contains(pid),
					follows(&seeded, &user, &user),
					"own post {pid:?} needs a self-follow"
				);
			}
			if post.status == PostStatus::Deleted || !follows(&seeded, &user, &post.author) {
				assert!(!all.contains(pid), "{pid:?} is deleted or unfollowed");
			}
		}
		assert_eq!(from_db(db), seeded, "a timeline command changes nothing");
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// T2: private global timeline -- `get-private-global-timeline` (:568-576).
// Agda: `private-global-timeline` over `global-char`.
// ---------------------------------------------------------------------------

/// With a session, the global timeline is the `CanReadPost` set (Twitter.agda:
/// 158-179): `live` and either `everyone`, or `followers-only` and followed.
#[test]
fn private_global_timeline_is_the_readable_live_posts() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		reseed(db, world, &seeded);

		let ids = returned(global_timeline(db, Some(sid), bound.0).expect("timeline"));
		let expected = private_global_expected(&seeded, &user, bound.0);
		assert_eq!(ids, expected, "take n of the readable live posts");
		assert!(
			ids.len() as u64 <= u64::from(bound.0),
			"n bounds the answer"
		);

		for pid in &ids {
			let post = &seeded.posts[pid];
			assert_eq!(post.status, PostStatus::Live);
			assert!(
				post.visibility == Visibility::Everyone || follows(&seeded, &user, &post.author),
				"{pid:?} is public or followed"
			);
		}

		let all = returned(global_timeline(db, Some(sid), u32::MAX).expect("timeline"));
		assert_eq!(all, private_global_expected(&seeded, &user, u32::MAX));
		assert_eq!(ids, all[..ids.len()].to_vec(), "a prefix of the whole list");

		// Deleted and unfollowed `followers-only` posts stay out.
		for (pid, post) in &seeded.posts {
			if post.status == PostStatus::Deleted
				|| (post.visibility == Visibility::FollowersOnly
					&& !follows(&seeded, &user, &post.author))
			{
				assert!(!all.contains(pid), "{pid:?} is unreadable");
			}
		}
		assert_eq!(from_db(db), seeded, "a timeline command changes nothing");
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// T3: public global timeline -- `get-public-global-timeline` (:578-585).
// Agda: `public-global-timeline` over `public-char`.
// ---------------------------------------------------------------------------

/// Without a session the timeline is `is-post-public` (Twitter.agda:342-357):
/// `live` and `everyone`. The follow table is irrelevant.
#[test]
fn public_global_timeline_is_the_public_live_posts() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		reseed(db, world, world);

		let ids = returned(global_timeline(db, None, bound.0).expect("timeline"));
		let expected = public_global_expected(world, bound.0);
		assert_eq!(ids, expected, "take n of the public live posts");
		assert!(
			ids.len() as u64 <= u64::from(bound.0),
			"n bounds the answer"
		);

		for pid in &ids {
			let post = &world.posts[pid];
			assert_eq!(post.status, PostStatus::Live);
			assert_eq!(post.visibility, Visibility::Everyone);
		}

		let all = returned(global_timeline(db, None, u32::MAX).expect("timeline"));
		assert_eq!(all, public_global_expected(world, u32::MAX));
		assert_eq!(ids, all[..ids.len()].to_vec(), "a prefix of the whole list");

		// The tokenless timeline ignores follows and sessions: a world with the
		// same posts but no session at all answers the same list.
		let session_free = world.without_sessions();
		reset(db);
		materialise(db, &session_free);
		assert_eq!(from_db(db), session_free);
		assert_eq!(
			returned(global_timeline(db, None, u32::MAX).expect("timeline")),
			all,
			"the tokenless timeline never consults a session"
		);
		assert_eq!(
			from_db(db),
			session_free,
			"a timeline command changes nothing"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// T4: `take n` bounds -- `n = 0` empty, `n` above the list saturates.
// Agda: `take` in `personal-timeline` / `private-global-timeline` /
// `public-global-timeline`.
// ---------------------------------------------------------------------------

/// `n = 0` is empty, `n > len` is the whole list, and the three timelines agree
/// with their formulas at every bound. Replies are ordinary entries: they are
/// filtered and counted exactly like top-level posts.
#[test]
fn timelines_take_n_after_filtering() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		reseed(db, world, &seeded);

		let personal_all = personal_expected(&seeded, &user, u32::MAX);
		let private_all = private_global_expected(&seeded, &user, u32::MAX);
		let public_all = public_global_expected(&seeded, u32::MAX);

		assert!(
			returned(personal_timeline(db, sid, 0).expect("timeline")).is_empty(),
			"n = 0 yields the empty personal timeline"
		);
		assert!(
			returned(global_timeline(db, Some(sid), 0).expect("timeline")).is_empty(),
			"n = 0 yields the empty private global timeline"
		);
		assert!(
			returned(global_timeline(db, None, 0).expect("timeline")).is_empty(),
			"n = 0 yields the empty public global timeline"
		);

		for (all, n) in [
			(&personal_all, personal_all.len() as u32 + 1),
			(&private_all, private_all.len() as u32 + 1),
			(&public_all, public_all.len() as u32 + 1),
		] {
			assert_eq!(
				all.len(),
				all.len().min(n as usize),
				"precondition: n is above the list"
			);
		}

		// `n` above the length saturates on the whole filtered list.
		let over_personal = personal_all.len() as u32 + 1;
		let over_private = private_all.len() as u32 + 1;
		let over_public = public_all.len() as u32 + 1;
		assert_eq!(
			returned(personal_timeline(db, sid, over_personal).expect("timeline")),
			personal_all,
			"n above the personal list saturates"
		);
		assert_eq!(
			returned(global_timeline(db, Some(sid), over_private).expect("timeline")),
			private_all,
			"n above the private global list saturates"
		);
		assert_eq!(
			returned(global_timeline(db, None, over_public).expect("timeline")),
			public_all,
			"n above the public list saturates"
		);

		// Every bound is exactly `take n` of the filtered list.
		assert_eq!(
			returned(personal_timeline(db, sid, bound.0).expect("timeline")),
			personal_all[..personal_all.len().min(bound.0 as usize)].to_vec()
		);
		assert_eq!(
			returned(global_timeline(db, Some(sid), bound.0).expect("timeline")),
			private_all[..private_all.len().min(bound.0 as usize)].to_vec()
		);
		assert_eq!(
			returned(global_timeline(db, None, bound.0).expect("timeline")),
			public_all[..public_all.len().min(bound.0 as usize)].to_vec()
		);

		// Replies are ordinary entries: every reply that the filter admits is
		// in the unbounded answer, and it sits at its `newest-first` position.
		for (pid, post) in &seeded.posts {
			if post.parent.is_some()
				&& post.status == PostStatus::Live
				&& post.visibility == Visibility::Everyone
			{
				assert!(
					public_all.contains(pid),
					"reply {pid:?} is an ordinary timeline entry"
				);
			}
		}
		assert_eq!(from_db(db), seeded, "a timeline command changes nothing");
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// T5: failed-access -- `failed-access` (Twitter.agda:464-468).
// Agda: `personal-timeline-expired`, `private-global-timeline-expired`.
// ---------------------------------------------------------------------------

/// Any session that is not `active` expires both session-carrying timelines and
/// changes nothing, while the tokenless one keeps answering.
#[test]
fn timelines_expire_with_an_inactive_session() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		let (seeded, _, _) = with_actor(world);
		let (seeded, revoked) = with_revoked_session(&seeded);
		reseed(db, world, &seeded);
		let unused = absent_session(&seeded);
		assert_eq!(seeded.session_status(unused), SessionStatus::Unused);

		for sid in [revoked, unused] {
			assert_eq!(
				personal_timeline(db, sid, bound.0).expect("timeline"),
				EngineResult::Expired,
				"the personal timeline expires an inactive session"
			);
			assert_eq!(from_db(db), seeded, "an expired command changes nothing");

			assert_eq!(
				global_timeline(db, Some(sid), bound.0).expect("timeline"),
				EngineResult::Expired,
				"the private global timeline expires an inactive session"
			);
			assert_eq!(from_db(db), seeded, "an expired command changes nothing");
		}

		// `read-global-timeline nothing` extracts no session, so it never
		// expires.
		assert_eq!(
			returned(global_timeline(db, None, bound.0).expect("timeline")),
			public_global_expected(&seeded, bound.0),
			"the tokenless timeline never expires"
		);
		TestResult::passed()
	});
}

/// `read-global-timeline nothing` works in a world with no sessions at all: its
/// `extract-sid` is `nothing` (Twitter.agda:196), so `failed-access`'s premise
/// is vacuous.
#[test]
fn public_global_timeline_never_expires() {
	check(|db: &Db, world: &WorldState, bound: Bound| -> TestResult {
		let session_free = world.without_sessions();
		reseed(db, world, &session_free);
		assert!(session_free.active_sessions().is_empty());

		assert_eq!(
			returned(global_timeline(db, None, bound.0).expect("timeline")),
			public_global_expected(&session_free, bound.0),
			"a session-free world still answers the public timeline"
		);
		assert_eq!(
			returned(global_timeline(db, None, u32::MAX).expect("timeline")),
			public_global_expected(&session_free, u32::MAX)
		);
		assert_eq!(
			from_db(db),
			session_free,
			"a timeline command changes nothing"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// Deterministic unit tests: one database each, worlds built as data.
// ---------------------------------------------------------------------------

const SID: SessionId = SessionId(100);
const REVOKED_SID: SessionId = SessionId(101);

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

/// `me` with an active `SID` and a revoked `REVOKED_SID`; one `everyone` and one
/// `followers-only` post each by `me`, `bob` and `carol`; a deleted post and a
/// reply, both by `carol`; `me` follows `carol` and nobody else.
///
/// `newest-first` = 207, 206, 205, 204, 203, 202, 201, 200.
fn sample_world() -> WorldState {
	let mut reply = post(CAROL, "carol reply", Visibility::Everyone);
	reply.parent = Some(MY_PUBLIC);
	let mut root = post(ME, "my public", Visibility::Everyone);
	root.replies = vec![CAROL_REPLY];
	let world = WorldState {
		accounts: BTreeMap::from([
			(ME.to_string(), account("pw-me", Visibility::Everyone)),
			(BOB.to_string(), account("pw-bob", Visibility::Everyone)),
			(
				CAROL.to_string(),
				account("pw-carol", Visibility::FollowersOnly),
			),
		]),
		sessions: HashMap::from([
			(SID, SessionStatus::Active(ME.to_string())),
			(REVOKED_SID, SessionStatus::Revoked),
		]),
		posts: HashMap::from([
			(MY_PUBLIC, root),
			(
				MY_PRIVATE,
				post(ME, "my private", Visibility::FollowersOnly),
			),
			(BOB_PUBLIC, post(BOB, "bob public", Visibility::Everyone)),
			(
				BOB_PRIVATE,
				post(BOB, "bob private", Visibility::FollowersOnly),
			),
			(
				CAROL_PRIVATE,
				post(CAROL, "carol private", Visibility::FollowersOnly),
			),
			(
				CAROL_PUBLIC,
				post(CAROL, "carol public", Visibility::Everyone),
			),
			(
				CAROL_DELETED,
				deleted(post(CAROL, "carol deleted", Visibility::Everyone)),
			),
			(CAROL_REPLY, reply),
		]),
		follows: BTreeSet::from([(ME.to_string(), CAROL.to_string())]),
		newest_first: vec![
			CAROL_REPLY,
			CAROL_DELETED,
			CAROL_PUBLIC,
			CAROL_PRIVATE,
			BOB_PRIVATE,
			BOB_PUBLIC,
			MY_PRIVATE,
			MY_PUBLIC,
		],
	};
	world.validate().expect("the sample world is valid");
	world
}

/// A fresh database holding `world`.
fn seeded(world: &WorldState) -> Db {
	let db = Db::in_memory().expect("create in-memory database");
	reset(&db);
	materialise(&db, world);
	assert_eq!(from_db(&db), *world, "the fixture round-trips");
	db
}

/// The personal timeline is the live posts of followed authors; a public post of
/// a non-followed author is left out, and the reply 207 (the newest row) heads
/// the list as an ordinary entry.
#[test]
fn personal_timeline_follows_the_characterization() {
	let world = sample_world();
	let db = seeded(&world);

	let ids = returned(personal_timeline(&db, SID, 10).expect("timeline"));
	assert_eq!(ids, vec![CAROL_REPLY, CAROL_PUBLIC, CAROL_PRIVATE]);
	assert_eq!(ids, personal_expected(&world, ME, 10));
	assert!(
		ids.contains(&CAROL_PRIVATE),
		"a followers-only post of a followed author is readable"
	);
	assert!(!ids.contains(&BOB_PUBLIC), "a non-followed author is out");
	assert!(!ids.contains(&CAROL_DELETED), "a deleted post is out");
	assert_eq!(from_db(&db), world, "a timeline command changes nothing");
}

/// `take n` (Twitter.agda:560): `0` is empty, a short `n` is a prefix, a long
/// `n` saturates.
#[test]
fn personal_timeline_takes_n_after_filtering() {
	let world = sample_world();
	let db = seeded(&world);
	let all = [CAROL_REPLY, CAROL_PUBLIC, CAROL_PRIVATE];

	for n in [0u32, 1, 2, 3, 4, u32::MAX] {
		let expected = all[..all.len().min(n as usize)].to_vec();
		let ids = returned(personal_timeline(&db, SID, n).expect("timeline"));
		assert_eq!(ids, expected, "n = {n}");
		assert_eq!(ids, personal_expected(&world, ME, n), "n = {n}");
	}
}

/// Own posts appear only after a self-follow (`follows-post-author`).
#[test]
fn personal_timeline_own_posts_need_a_self_follow() {
	let world = sample_world();
	let db = seeded(&world);

	let before = returned(personal_timeline(&db, SID, u32::MAX).expect("timeline"));
	assert!(!before.contains(&MY_PUBLIC));
	assert!(!before.contains(&MY_PRIVATE));

	let mut followed = world.clone();
	followed.follows.insert((ME.to_string(), ME.to_string()));
	followed
		.validate()
		.expect("the world with a self-follow is valid");
	reset(&db);
	materialise(&db, &followed);

	let after = returned(personal_timeline(&db, SID, u32::MAX).expect("timeline"));
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
	assert_eq!(after, personal_expected(&followed, ME, u32::MAX));
}

/// The private global timeline is the `CanReadPost` set; the own
/// `followers-only` post becomes readable after a self-follow.
#[test]
fn private_global_timeline_includes_readable_posts() {
	let world = sample_world();
	let db = seeded(&world);

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
	assert_eq!(ids, private_global_expected(&world, ME, 100));
	assert!(ids.contains(&MY_PUBLIC));
	assert!(
		!ids.contains(&MY_PRIVATE),
		"no self-follow, so not readable"
	);
	assert!(!ids.contains(&BOB_PRIVATE), "not followed, so not readable");
	assert!(
		!ids.contains(&CAROL_DELETED),
		"deleted posts are never readable"
	);

	let mut followed = world.clone();
	followed.follows.insert((ME.to_string(), ME.to_string()));
	followed
		.validate()
		.expect("the world with a self-follow is valid");
	reset(&db);
	materialise(&db, &followed);

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
	assert_eq!(ids, private_global_expected(&followed, ME, 100));

	// `take n` on the private global timeline, after filtering.
	for n in [0u32, 2, 5, u32::MAX] {
		assert_eq!(
			returned(global_timeline(&db, Some(SID), n).expect("timeline")),
			private_global_expected(&followed, ME, n),
			"n = {n}"
		);
	}
}

/// The tokenless timeline is `is-post-public`: `live` and `everyone`, ignoring
/// the follow table and the session table alike.
#[test]
fn public_global_timeline_is_public_and_live_only() {
	let world = sample_world();
	let db = seeded(&world);
	let before = returned(global_timeline(&db, None, 100).expect("timeline"));

	let mut followed = world.clone();
	followed.follows.insert((BOB.to_string(), ME.to_string()));
	followed.follows.insert((ME.to_string(), BOB.to_string()));
	followed.follows.insert((ME.to_string(), ME.to_string()));
	followed
		.follows
		.insert((BOB.to_string(), CAROL.to_string()));
	followed
		.validate()
		.expect("the world with follows is valid");
	reset(&db);
	materialise(&db, &followed);

	let ids = returned(global_timeline(&db, None, 100).expect("timeline"));
	assert_eq!(ids, vec![CAROL_REPLY, CAROL_PUBLIC, BOB_PUBLIC, MY_PUBLIC]);
	assert_eq!(
		ids, before,
		"the tokenless timeline ignores the follow table"
	);
	assert_eq!(ids, public_global_expected(&followed, 100));
	assert!(!ids.contains(&BOB_PRIVATE));
	assert!(!ids.contains(&CAROL_PRIVATE));
	assert!(!ids.contains(&MY_PRIVATE));
	assert!(!ids.contains(&CAROL_DELETED));

	for n in [0u32, 1, 3, u32::MAX] {
		assert_eq!(
			returned(global_timeline(&db, None, n).expect("timeline")),
			public_global_expected(&followed, n),
			"n = {n}"
		);
	}
}

/// `read-global-timeline nothing` works in a world with no sessions.
#[test]
fn public_global_timeline_works_without_any_session() {
	let mut world = empty_world();
	world
		.accounts
		.insert(CAROL.to_string(), account("pw-carol", Visibility::Everyone));
	world.posts.insert(
		CAROL_PRIVATE,
		post(CAROL, "carol private", Visibility::FollowersOnly),
	);
	world.newest_first.push(CAROL_PRIVATE);
	let db = seeded(&world);

	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		Vec::<PostId>::new(),
		"a followers-only post is not publicly readable"
	);

	world.posts.insert(
		CAROL_PUBLIC,
		post(CAROL, "carol public", Visibility::Everyone),
	);
	world.newest_first.insert(0, CAROL_PUBLIC);
	world.validate().expect("the extended world is valid");
	reset(&db);
	materialise(&db, &world);

	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		vec![CAROL_PUBLIC]
	);
	assert_eq!(from_db(&db), world);
}

/// Both session-carrying timelines answer `Expired` for a revoked and for a
/// never-issued session and change nothing; the tokenless one keeps answering.
#[test]
fn timelines_expire_for_a_revoked_or_unused_session() {
	let world = sample_world();
	let db = seeded(&world);
	let unused = absent_session(&world);

	for sid in [REVOKED_SID, unused] {
		assert_eq!(
			personal_timeline(&db, sid, 10).expect("timeline"),
			EngineResult::Expired,
			"personal with {sid:?}"
		);
		assert_eq!(
			global_timeline(&db, Some(sid), 10).expect("timeline"),
			EngineResult::Expired,
			"private global with {sid:?}"
		);
		assert_eq!(from_db(&db), world, "an expired command changes nothing");
	}
	assert_eq!(
		returned(global_timeline(&db, None, 10).expect("timeline")),
		public_global_expected(&world, 10),
		"the tokenless timeline never expires"
	);
}

/// Following another author brings exactly their live posts in, at their
/// `newest-first` positions; nothing else moves.
#[test]
fn personal_timeline_following_an_author_adds_their_posts() {
	let world = sample_world();
	let db = seeded(&world);

	let mut followed = world.clone();
	followed.follows.insert((ME.to_string(), BOB.to_string()));
	followed
		.validate()
		.expect("the world with a follow is valid");
	reset(&db);
	materialise(&db, &followed);

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
	assert_eq!(ids, personal_expected(&followed, ME, 100));
	assert_eq!(from_db(&db), followed, "a timeline command changes nothing");
}

/// The generated worlds cover empty and post-free shapes, but the trivially
/// empty answers are worth pinning down: no posts and no follows yields three
/// empty timelines (and no session is needed for the public one).
#[test]
fn timelines_of_an_empty_world_are_empty() {
	let mut world = empty_world();
	world
		.accounts
		.insert(ME.to_string(), account("pw-me", Visibility::Everyone));
	world
		.sessions
		.insert(SID, SessionStatus::Active(ME.to_string()));
	let db = seeded(&world);

	for n in [0u32, 1, u32::MAX] {
		assert_eq!(
			returned(personal_timeline(&db, SID, n).expect("timeline")),
			Vec::<PostId>::new(),
			"personal, n = {n}"
		);
		assert_eq!(
			returned(global_timeline(&db, Some(SID), n).expect("timeline")),
			Vec::<PostId>::new(),
			"private global, n = {n}"
		);
		assert_eq!(
			returned(global_timeline(&db, None, n).expect("timeline")),
			Vec::<PostId>::new(),
			"public global, n = {n}"
		);
	}
	assert_eq!(from_db(&db), world);
}

// ---------------------------------------------------------------------------
// Sparse-follows regression (T6c).
//
// The personal timeline must not scan every post when the user follows only a
// few authors; it is a per-author top-n window over the follow join. The answer
// must still be exactly `get-personal-timeline` (Twitter.agda:557-566): `take n`
// of the `live` posts of followed authors, newest-first.
// ---------------------------------------------------------------------------

const SPARSE_POSTS: usize = 5_000;
const SPARSE_AUTHORS: usize = 50;
const SPARSE_FOLLOWED: usize = 17;
const SPARSE_BASE: i64 = 10_000;

/// Author `i % 50` of the sparse world: `author00` .. `author49`.
fn sparse_author(i: usize) -> String {
	format!("author{:02}", i % SPARSE_AUTHORS)
}

/// A ~5 000-post world across 50 authors, interleaving `followers-only` posts,
/// replies and deleted posts, where `me` follows exactly one author.
///
/// Insertion order is post `i` = id `10_000 + i`, so `newest-first` is the
/// reverse: `10_000 + 4_999` first. Every 13th post (except the root) is a reply
/// to the root `10_000`.
fn sparse_world() -> WorldState {
	let mut accounts = BTreeMap::from([(ME.to_string(), account("pw-me", Visibility::Everyone))]);
	for a in 0..SPARSE_AUTHORS {
		accounts.insert(format!("author{a:02}"), account("pw", Visibility::Everyone));
	}
	let mut posts: HashMap<PostId, PostState> = HashMap::new();
	let mut newest_first: Vec<PostId> = Vec::with_capacity(SPARSE_POSTS);
	for i in 0..SPARSE_POSTS {
		let pid = PostId(SPARSE_BASE + i as i64);
		let mut state = post(
			&sparse_author(i),
			&format!("post {i}"),
			if i % 7 == 0 {
				Visibility::FollowersOnly
			} else {
				Visibility::Everyone
			},
		);
		if i % 13 == 0 && i > 0 {
			state.parent = Some(PostId(SPARSE_BASE));
		}
		if i % 11 == 0 {
			state = deleted(state);
		}
		posts.insert(pid, state);
		newest_first.push(pid);
	}
	newest_first.sort_unstable_by_key(|pid| std::cmp::Reverse(pid.0));
	// Replies in `seq` order: rank 0 is the newest post, so ascending rank is
	// descending id.
	let mut children: Vec<PostId> = posts
		.iter()
		.filter(|(_, state)| state.parent == Some(PostId(SPARSE_BASE)))
		.map(|(pid, _)| *pid)
		.collect();
	children.sort_unstable_by_key(|pid| std::cmp::Reverse(pid.0));
	posts
		.get_mut(&PostId(SPARSE_BASE))
		.expect("the root exists")
		.replies = children;

	let world = WorldState {
		accounts,
		sessions: HashMap::from([(SID, SessionStatus::Active(ME.to_string()))]),
		posts,
		follows: BTreeSet::from([(ME.to_string(), sparse_author(SPARSE_FOLLOWED))]),
		newest_first,
	};
	world.validate().expect("the sparse world is valid");
	world
}

#[test]
fn sparse_follows_personal_timeline_is_the_followed_authors_top_n() {
	let world = sparse_world();
	let db = seeded(&world);
	let followed = sparse_author(SPARSE_FOLLOWED);

	// Preconditions: the world really is sparse for `me`.
	assert_eq!(world.posts.len(), SPARSE_POSTS);
	let mut authors: Vec<&str> = world.posts.values().map(|p| p.author.as_str()).collect();
	authors.sort_unstable();
	authors.dedup();
	assert_eq!(authors.len(), SPARSE_AUTHORS);
	assert!(
		world
			.posts
			.values()
			.any(|p| p.status == PostStatus::Deleted)
	);

	// The expected answer, derived from the world alone.
	let expected_all: Vec<PostId> = personal_expected(&world, ME, u32::MAX);
	assert!(
		expected_all.len() > 10,
		"the followed author has more than ten live posts"
	);
	assert!(expected_all.iter().all(|pid| {
		let state = &world.posts[pid];
		state.author == followed && state.status == PostStatus::Live
	}));

	assert_eq!(
		returned(personal_timeline(&db, SID, u32::MAX).expect("timeline")),
		expected_all
	);

	let over = expected_all.len() as u32 + 1;
	for n in [0u32, 1, 10, over, u32::MAX] {
		let ids = returned(personal_timeline(&db, SID, n).expect("timeline"));
		let want = expected_all[..expected_all.len().min(n as usize)].to_vec();
		assert_eq!(ids, want, "n = {n}");
		assert_eq!(ids, personal_expected(&world, ME, n), "n = {n}");
	}

	// Explicitly: posts by non-followed authors are absent.
	let others: Vec<PostId> = world
		.posts
		.iter()
		.filter(|(_, state)| state.author != followed)
		.map(|(pid, _)| *pid)
		.collect();
	let answer = returned(personal_timeline(&db, SID, u32::MAX).expect("timeline"));
	for pid in &others {
		assert!(!answer.contains(pid), "post by a non-followed author");
	}
	assert_eq!(from_db(&db), world, "a timeline command changes nothing");
}
