//! Property and unit tests for the `time-passes` engine command (task T7, Q1a
//! pilot).
//!
//! Every property is a direct rendering of the `session-timeout` Step of
//! `spec/Twitter.agda` (691-702): every `active` session becomes `revoked`,
//! every other session row is untouched, and nothing else in the world moves.
//! The matching Agda lemmas are `time-passes-success` and
//! `time-passes-idempotent` in `ImplProofs.agda`, both stated over
//! `timed-out-world` -- the world whose `session-at` is `before`'s composed
//! with `timed-out`. Both lemmas already quantify over an arbitrary `World`,
//! so this world-state-driven pilot needs no new Agda.
//!
//! Q1a harness shape (see `support`):
//!
//! * **one** in-memory sqlite database per `#[test]`, created outside the
//!   quickcheck cases by `support::check`;
//! * every case resets that database and materialises a freshly generated
//!   `WorldState`; the property body receives `&Db` and `&WorldState` and
//!   never builds a database;
//! * `WorldState` generation is constructive (always valid) and shrinking is
//!   validity-preserving, so a counterexample is a small valid world;
//! * the materialiser round-trips: the harness asserts `from_db(db) == world`
//!   on every case;
//! * assumption: `newest_first` is a permutation of **all** posts, because
//!   `store::newest_first` also lists deleted posts (the spec's
//!   `newest-first` may list only some; `only-valid-posts` is the only
//!   constraint).

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::time::time_passes;
use formal_twitter::model::{PostId, PostStatus, SessionId, SessionStatus, Visibility};
use formal_twitter::store;
use quickcheck::TestResult;

use support::{AccountState, PostState, WorldState, check, from_db, materialise, reset};

// ---------------------------------------------------------------------------
// Helpers.
// ---------------------------------------------------------------------------

fn status_in_db(db: &Db, sid: SessionId) -> SessionStatus {
	db.read(|conn| store::get_session(conn, sid))
		.expect("read session")
}

fn account(password: &str, visibility: Visibility) -> AccountState {
	AccountState {
		password: password.to_string(),
		visibility,
	}
}

fn post(author: &str, text: &str) -> PostState {
	PostState {
		author: author.to_string(),
		text: text.to_string(),
		visibility: Visibility::Everyone,
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: None,
	}
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

/// Two accounts, an `active` session per account, one `revoked` session, a
/// followers-only root with a deleted reply, a follow and a like: enough
/// unrelated rows that "everything else unchanged" is not discharged by
/// accident.
fn sample_world() -> WorldState {
	let mut root = post("grace", "first post");
	root.visibility = Visibility::FollowersOnly;
	root.likes = vec!["ada".to_string()];
	root.replies = vec![PostId(2)];
	let reply = PostState {
		parent: Some(PostId(1)),
		status: PostStatus::Deleted,
		..post("ada", "reply")
	};
	let world = WorldState {
		accounts: BTreeMap::from([
			("ada".to_string(), account("pw-ada", Visibility::Everyone)),
			(
				"grace".to_string(),
				account("pw-grace", Visibility::FollowersOnly),
			),
		]),
		sessions: HashMap::from([
			(SessionId(1), SessionStatus::Active("ada".to_string())),
			(SessionId(2), SessionStatus::Revoked),
			(SessionId(3), SessionStatus::Active("grace".to_string())),
		]),
		posts: HashMap::from([(PostId(1), root), (PostId(2), reply)]),
		follows: BTreeSet::from([("ada".to_string(), "grace".to_string())]),
		newest_first: vec![PostId(2), PostId(1)],
	};
	world.validate().expect("the sample world is valid");
	world
}

/// A session id no generated or hand-built world uses.
const ABSENT: SessionId = SessionId(9_000_000);

// ---------------------------------------------------------------------------
// P1: time-passes -- `session-timeout` (Twitter.agda:691-702).
// Agda: `time-passes-success` over `timed-out-world` / `timed-out`.
// ---------------------------------------------------------------------------

/// The first premise of `session-timeout`: every active session is `revoked`
/// afterwards. The second premise: nothing else in the world moves -- no
/// account, no post, no follow, no like, and no session row is added or
/// removed.
#[test]
fn time_passes_revokes_every_active_session() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let timed_out = world.timed_out();
		let active = world.active_sessions();

		assert_eq!(
			time_passes(db).expect("time-passes"),
			EngineResult::Success,
			"time-passes must succeed on every world"
		);

		// Every seeded session: active becomes revoked, revoked stays
		// revoked. An id that was never inserted is still unused.
		for (sid, status) in &world.sessions {
			let expected = match status {
				SessionStatus::Active(_) | SessionStatus::Revoked => SessionStatus::Revoked,
				SessionStatus::Unused => unreachable!("stored sessions are active or revoked"),
			};
			assert_eq!(
				status_in_db(db, *sid),
				expected,
				"session {sid:?} after the timeout"
			);
		}
		for sid in &active {
			assert_eq!(status_in_db(db, *sid), SessionStatus::Revoked);
		}
		assert_eq!(status_in_db(db, ABSENT), SessionStatus::Unused);

		// The whole world is `timed-out-world before`: sessions moved as
		// above and every other component copied unchanged.
		assert_eq!(
			from_db(db),
			timed_out,
			"time-passes must leave everything but the session statuses alone"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P2: idempotence. Agda: `time-passes-idempotent`.
// ---------------------------------------------------------------------------

/// A second `time-passes` also answers `success` and leaves the whole world --
/// the session table included -- exactly as the first one left it: after one
/// timeout no session is `active` any more, so the effect is already complete
/// (`timed-out` is idempotent).
#[test]
fn time_passes_is_idempotent() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		assert_eq!(time_passes(db).expect("time-passes"), EngineResult::Success);
		let once = from_db(db);
		assert_eq!(once, world.timed_out());

		assert_eq!(
			time_passes(db).expect("second time-passes"),
			EngineResult::Success,
			"a second time-passes still succeeds"
		);
		assert_eq!(from_db(db), once, "a second timeout changes nothing");
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P3: a world without sessions. Agda: `time-passes-idempotent` at a world with
// no sessions (the `session-timeout` premise is vacuous there).
// ---------------------------------------------------------------------------

/// A world with no sessions at all is already timed out: `time-passes`
/// answers `success` and changes nothing. Worlds that do have sessions are
/// discarded rather than failed -- P1 covers those.
#[test]
fn time_passes_on_empty_world_changes_nothing() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		if !world.sessions.is_empty() {
			return TestResult::discard();
		}
		assert_eq!(time_passes(db).expect("time-passes"), EngineResult::Success);
		assert_eq!(
			from_db(db),
			*world,
			"a world with no sessions is already timed out"
		);
		assert_eq!(status_in_db(db, ABSENT), SessionStatus::Unused);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// Deterministic unit tests for the same rules.
// ---------------------------------------------------------------------------

#[test]
fn time_passes_revokes_active_and_keeps_the_other_rows() {
	let db = Db::in_memory().expect("create in-memory database");
	let world = sample_world();
	reset(&db);
	materialise(&db, &world);
	assert_eq!(from_db(&db), world, "the fixture round-trips");

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(from_db(&db), world.timed_out());
	assert_eq!(status_in_db(&db, SessionId(1)), SessionStatus::Revoked);
	assert_eq!(status_in_db(&db, SessionId(2)), SessionStatus::Revoked);
	assert_eq!(status_in_db(&db, SessionId(3)), SessionStatus::Revoked);
	assert_eq!(status_in_db(&db, ABSENT), SessionStatus::Unused);
}

#[test]
fn time_passes_twice_is_still_success_and_changes_nothing() {
	let db = Db::in_memory().expect("create in-memory database");
	let world = sample_world();
	reset(&db);
	materialise(&db, &world);

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	let once = from_db(&db);
	assert_eq!(once, world.timed_out());

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(from_db(&db), once);
}

#[test]
fn time_passes_on_an_empty_database_is_success() {
	let db = Db::in_memory().expect("create in-memory database");
	let world = empty_world();
	reset(&db);
	materialise(&db, &world);

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(from_db(&db), world);
	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(from_db(&db), world);
}

#[test]
fn time_passes_keeps_a_revoked_session_revoked() {
	let db = Db::in_memory().expect("create in-memory database");
	let mut world = empty_world();
	world
		.accounts
		.insert("ada".to_string(), account("pw", Visibility::Everyone));
	world.sessions.insert(SessionId(7), SessionStatus::Revoked);
	reset(&db);
	materialise(&db, &world);

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(
		status_in_db(&db, SessionId(7)),
		SessionStatus::Revoked,
		"a revoked session stays revoked"
	);
	assert_eq!(from_db(&db), world);
}
