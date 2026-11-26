//! Property and unit tests for the authentication engine (task T2a), migrated
//! to the Q1 world-state harness (see `support`).
//!
//! Every property is a direct rendering of a `Step` rule of `spec/Twitter.agda`
//! and is paired with the Agda lemma in `ImplProofs.agda` that states the same
//! thing:
//!
//! | property                                    | spec rule               | Agda lemma               |
//! |---------------------------------------------|-------------------------|--------------------------|
//! | `register_free_username_creates_account`    | `create-account` 470-488| `register-success`       |
//! | `register_taken_username_fails`             | `failed-create-account` | `register-duplicate`     |
//! | `authenticate_correct_password_issues_...`  | `login` 490-516         | `login-success`          |
//! | `authenticate_absent_user_fails`            | `failed-login-1`        | `login-absent`           |
//! | `authenticate_wrong_password_fails`         | `failed-login-2`        | `login-wrong-password`   |
//! | `revoke_active_session_succeeds`            | `logout` 677-689        | `logout-success`         |
//! | `revoke_inactive_session_expires`           | `failed-access` 464-468 | `logout-expired`, `logout-unused` |
//! | `failed_access_expires_for_every_session_..`| `failed-access` 464-468 | `failed-access-inactive` |
//!
//! Harness shape:
//!
//! * **one** in-memory sqlite database per `#[test]`, created outside the
//!   quickcheck cases by `support::check`;
//! * every case resets it and materialises a freshly generated `WorldState`;
//!   the property body receives `&Db` and `&WorldState` and never builds a
//!   database;
//! * a property that needs a shape the generator may not produce (a taken
//!   username, an active or a revoked session) derives the world inside the
//!   body by cloning and mutating it, then re-materialises *that* world through
//!   `load` -- still no database construction;
//! * the expected world is computed from the before world, so "everything else
//!   unchanged" is asserted by whole-world equality rather than by a sample of
//!   rows.

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::auth::{authenticate, register, revoke_token};
use formal_twitter::model::{DbError, PostId, PostStatus, SessionId, SessionStatus, Visibility};
use quickcheck::{Arbitrary, Gen, TestResult};

use support::{AccountState, PostState, WorldState, check, from_db, materialise, reset};

// ---------------------------------------------------------------------------
// Arguments generated alongside the world.
// ---------------------------------------------------------------------------

const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&*";

fn small_string(g: &mut Gen) -> String {
	let len = 1 + usize::arbitrary(g) % 8;
	let mut out = String::with_capacity(len);
	for _ in 0..len {
		out.push(ALPHABET[usize::arbitrary(g) % ALPHABET.len()] as char);
	}
	out
}

/// A username or password candidate; usually made free or different before use.
#[derive(Clone, Debug)]
struct Name(String);

/// A password to try.
#[derive(Clone, Debug)]
struct Pass(String);

/// A selector into the generated world's sorted rows.
#[derive(Clone, Copy, Debug)]
struct Seed(usize);

impl Arbitrary for Name {
	fn arbitrary(g: &mut Gen) -> Self {
		Name(small_string(g))
	}
}

impl Arbitrary for Pass {
	fn arbitrary(g: &mut Gen) -> Self {
		Pass(small_string(g))
	}
}

impl Arbitrary for Seed {
	fn arbitrary(g: &mut Gen) -> Self {
		Seed(usize::arbitrary(g))
	}
}

// ---------------------------------------------------------------------------
// World helpers: deterministic selection and the derived worlds a property
// needs. All of them clone the generated world and mutate the clone.
// ---------------------------------------------------------------------------

fn pick<T>(items: &[T], seed: usize) -> Option<&T> {
	items.get(seed % items.len().max(1))
}

fn sorted_accounts(world: &WorldState) -> Vec<String> {
	world.accounts.keys().cloned().collect()
}

fn sorted_sessions(world: &WorldState) -> Vec<(SessionId, SessionStatus)> {
	let mut ids: Vec<SessionId> = world.sessions.keys().copied().collect();
	ids.sort_unstable_by_key(|sid| sid.0);
	ids.into_iter()
		.map(|sid| (sid, world.session_status(sid)))
		.collect()
}

/// `base`, with `'_'` appended until no account holds it. The premise of
/// `register-success` / `failed-login-1` is that the username is absent.
fn free_username(world: &WorldState, base: &str) -> String {
	let mut candidate = base.to_string();
	while world.accounts.contains_key(&candidate) {
		candidate.push('_');
	}
	candidate
}

/// A session id no row of `world` holds, i.e. `unused`.
fn free_session_id(world: &WorldState, seed: usize) -> SessionId {
	let mut id = 9_000_000 + (seed % 1_000) as i64;
	while world.sessions.contains_key(&SessionId(id)) {
		id += 1;
	}
	SessionId(id)
}

/// `candidate`, or `candidate` with `'x'` appended while it equals `password`:
/// the `Account.password acc ≢ passwd` premise of `failed-login-2`.
fn wrong_password(password: &str, candidate: &str) -> String {
	let mut wrong = candidate.to_string();
	while wrong == password {
		wrong.push('x');
	}
	wrong
}

/// `world` and a username it holds: the generated account at `seed` when there
/// is one, otherwise `world` plus an account named after `base`. Lets the
/// duplicate-registration and wrong-password properties run on the empty world
/// too instead of discarding it.
fn with_some_account(world: &WorldState, seed: usize, base: &str) -> (WorldState, String) {
	if let Some(name) = pick(&sorted_accounts(world), seed) {
		return (world.clone(), name.clone());
	}
	let name = free_username(world, base);
	let mut next = world.clone();
	next.accounts.insert(
		name.clone(),
		AccountState {
			password: base.to_string(),
			visibility: Visibility::Everyone,
		},
	);
	(next, name)
}

/// `world` and an active session -- the generated one at `seed`, or a fresh
/// session for an account `world` keeps or gains -- together with its user.
fn with_active_session(
	world: &WorldState,
	seed: usize,
	base: &str,
) -> (WorldState, SessionId, String) {
	let active: Vec<(SessionId, String)> = sorted_sessions(world)
		.into_iter()
		.filter_map(|(sid, status)| match status {
			SessionStatus::Active(user) => Some((sid, user)),
			_ => None,
		})
		.collect();
	if let Some((sid, user)) = pick(&active, seed) {
		return (world.clone(), *sid, user.clone());
	}
	let (mut next, name) = with_some_account(world, seed, base);
	let sid = free_session_id(&next, seed);
	next.sessions
		.insert(sid, SessionStatus::Active(name.clone()));
	(next, sid, name)
}

/// `world` and a `revoked` session -- the first one it holds, or a fresh one.
fn with_revoked_session(world: &WorldState, seed: usize) -> (WorldState, SessionId) {
	if let Some((sid, _)) = sorted_sessions(world)
		.into_iter()
		.find(|(_, status)| matches!(status, SessionStatus::Revoked))
	{
		return (world.clone(), sid);
	}
	let sid = free_session_id(world, seed);
	let mut next = world.clone();
	next.sessions.insert(sid, SessionStatus::Revoked);
	(next, sid)
}

/// Reset the shared database, materialise a world derived inside a property
/// body and check the round-trip. No database is created here.
fn load(db: &Db, world: &WorldState) {
	world.validate().expect("a derived world is valid");
	reset(db);
	materialise(db, world);
	assert_eq!(from_db(db), *world, "the derived world must round-trip");
}

fn account(password: &str, visibility: Visibility) -> AccountState {
	AccountState {
		password: password.to_string(),
		visibility,
	}
}

fn issued(result: EngineResult) -> SessionId {
	match result {
		EngineResult::IssuedSession(sid) => sid,
		other => panic!("expected IssuedSession, got {other:?}"),
	}
}

// ---------------------------------------------------------------------------
// P1: register (Twitter.agda:470-488) -- Agda `register-success`.
// ---------------------------------------------------------------------------

/// `create-account`: a free username answers `success`, the account holds the
/// given password with `default-visibility = everyone`, and every other
/// account, session, post, follow and like is copied unchanged. The expected
/// world is `registered-world`: `set-account` at the username, nothing else.
#[test]
fn register_free_username_creates_account() {
	check(
		|db: &Db, world: &WorldState, arg: (Name, Pass)| -> TestResult {
			let (name, pass) = arg;
			let username = free_username(world, &name.0);
			assert!(
				!world.accounts.contains_key(&username),
				"precondition: the username is absent"
			);
			let mut expected = world.clone();
			expected
				.accounts
				.insert(username.clone(), account(&pass.0, Visibility::Everyone));
			expected.validate().expect("the expected world is valid");

			assert_eq!(
				register(db, &username, &pass.0).expect("register"),
				EngineResult::Success
			);

			let after = from_db(db);
			assert_eq!(
				after.accounts.get(&username),
				Some(&account(&pass.0, Visibility::Everyone)),
				"the account holds the password and visibility everyone"
			);
			assert_eq!(
				after.sessions, world.sessions,
				"register must not touch sessions"
			);
			assert_eq!(after, expected, "nothing but the new account moves");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P2: duplicate registration -- Agda `register-duplicate`.
// ---------------------------------------------------------------------------

/// `failed-create-account`: a taken username answers `signup-failed` and the
/// world -- the existing password included -- is untouched (`Step before cmd
/// before signup-failed`).
#[test]
fn register_taken_username_fails() {
	check(
		|db: &Db, world: &WorldState, arg: (Name, Pass, Seed)| -> TestResult {
			let (name, pass, seed) = arg;
			let (world, taken) = with_some_account(world, seed.0, &name.0);
			load(db, &world);
			let before = from_db(db);
			let password_before = before.accounts[&taken].password.clone();

			assert_eq!(
				register(db, &taken, &pass.0).expect("register"),
				EngineResult::SignupFailed
			);

			let after = from_db(db);
			assert_eq!(
				after.accounts[&taken].password, password_before,
				"the existing password is kept"
			);
			assert_eq!(after, before, "signup failure must not change the world");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P3: login (Twitter.agda:490-516) -- Agda `login-success`.
// ---------------------------------------------------------------------------

/// `login`: the right password issues `issued-session sid` for a `sid` outside
/// `used-session-ids`, `session-at sid` becomes `active username` and the
/// account is unchanged (`ValidSession`, Twitter.agda:147-156). Every other
/// session, account, post and follow is copied unchanged.
#[test]
fn authenticate_correct_password_issues_valid_session() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name)| -> TestResult {
			let (seed, base) = arg;
			let (world, username) = with_some_account(world, seed.0, &base.0);
			let password = world.accounts[&username].password.clone();
			load(db, &world);

			let sid = issued(authenticate(db, &username, &password).expect("authenticate"));
			// `login` allocates a fresh session id, so it is not in
			// `used-session-ids`.
			assert!(
				!world.sessions.contains_key(&sid),
				"the issued session {sid:?} must be fresh"
			);

			let mut expected = world.clone();
			expected
				.sessions
				.insert(sid, SessionStatus::Active(username.clone()));
			expected.validate().expect("the expected world is valid");

			let after = from_db(db);
			// ValidSession.session-unchanged
			assert_eq!(
				after.session_status(sid),
				SessionStatus::Active(username.clone())
			);
			// ValidSession.account-unchanged
			assert_eq!(after.accounts, world.accounts, "the account is unchanged");
			assert_eq!(
				after.sessions.len(),
				world.sessions.len() + 1,
				"exactly one new session row"
			);
			assert_eq!(after, expected, "nothing but the new session moves");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P4: failed-login-1 -- Agda `login-absent`.
// ---------------------------------------------------------------------------

/// `failed-login-1`: an absent username answers `login-failed` and creates no
/// session; the whole world is unchanged.
#[test]
fn authenticate_absent_user_fails() {
	check(
		|db: &Db, world: &WorldState, arg: (Name, Pass)| -> TestResult {
			let username = free_username(world, &arg.0.0);
			assert!(
				!world.accounts.contains_key(&username),
				"precondition: the username is absent"
			);

			assert_eq!(
				authenticate(db, &username, &arg.1.0).expect("authenticate"),
				EngineResult::LoginFailed
			);

			let after = from_db(db);
			assert_eq!(
				after.sessions.len(),
				world.sessions.len(),
				"no session may be created"
			);
			assert_eq!(after, *world, "a failed login must not change the world");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P5: failed-login-2 -- Agda `login-wrong-password`.
// ---------------------------------------------------------------------------

/// `failed-login-2`: a wrong password for a taken username answers
/// `login-failed` and creates no session; the whole world is unchanged.
#[test]
fn authenticate_wrong_password_fails() {
	check(
		|db: &Db, world: &WorldState, arg: (Name, Pass, Seed)| -> TestResult {
			let (name, pass, seed) = arg;
			let (world, username) = with_some_account(world, seed.0, &name.0);
			let stored = world.accounts[&username].password.clone();
			let wrong = wrong_password(&stored, &pass.0);
			assert_ne!(wrong, stored, "precondition: the password is wrong");
			load(db, &world);

			assert_eq!(
				authenticate(db, &username, &wrong).expect("authenticate"),
				EngineResult::LoginFailed
			);

			let after = from_db(db);
			assert_eq!(
				after.sessions.len(),
				world.sessions.len(),
				"no session may be created"
			);
			assert_eq!(after, world, "a failed login must not change the world");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P6: logout (Twitter.agda:677-689) -- Agda `logout-success`.
// ---------------------------------------------------------------------------

/// `logout`: revoking an active session answers `success` and turns exactly
/// that session `revoked` (`set-session sid revoked`); every other session, and
/// the accounts, posts and follows, are copied unchanged.
#[test]
fn revoke_active_session_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name)| -> TestResult {
			let (seed, base) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			assert_eq!(
				world.session_status(sid),
				SessionStatus::Active(user.clone()),
				"precondition: the session is active"
			);
			load(db, &world);

			let mut expected = world.clone();
			expected.sessions.insert(sid, SessionStatus::Revoked);
			expected.validate().expect("the expected world is valid");

			assert_eq!(
				revoke_token(db, sid).expect("revoke-token"),
				EngineResult::Success
			);

			let after = from_db(db);
			assert_eq!(after.session_status(sid), SessionStatus::Revoked);
			assert_eq!(
				after.sessions.len(),
				world.sessions.len(),
				"logout keeps the row, it just revokes it"
			);
			assert_eq!(after, expected, "only that session's status moves");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// P7: logout on an inactive session -- Agda `logout-expired`,
// `logout-unused`, both instances of `failed-access-inactive`.
// ---------------------------------------------------------------------------

/// `failed-access`: revoking a session that is `revoked` or `unused` answers
/// `expired` and leaves the world untouched. Both branches are covered on every
/// case: the unused id is a fresh one, the revoked id comes from the world or
/// is derived.
#[test]
fn revoke_inactive_session_expires() {
	check(|db: &Db, world: &WorldState, seed: Seed| -> TestResult {
		// unused: an id no world row holds.
		let unused = free_session_id(world, seed.0);
		assert_eq!(world.session_status(unused), SessionStatus::Unused);
		assert_eq!(
			revoke_token(db, unused).expect("revoke-token"),
			EngineResult::Expired
		);
		assert_eq!(
			from_db(db),
			*world,
			"an expired request must not touch the world"
		);

		// revoked: from the world or freshly derived.
		let (world, sid) = with_revoked_session(world, seed.0);
		load(db, &world);
		assert_eq!(world.session_status(sid), SessionStatus::Revoked);

		assert_eq!(
			revoke_token(db, sid).expect("revoke-token"),
			EngineResult::Expired
		);
		assert_eq!(
			from_db(db),
			world,
			"an expired request must not touch the world"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P8: failed-access on every session-carrying command (Twitter.agda:464-468)
// -- Agda `failed-access-inactive`.
// ---------------------------------------------------------------------------

/// Every authentication command whose `extract-sid` is `just sid`
/// (Twitter.agda:203-207). `revoke-token` is the only one of this task.
type SessionCommand = fn(&Db, SessionId) -> Result<EngineResult, DbError>;

const SESSION_COMMANDS: &[(&str, SessionCommand)] = &[("revoke-token", revoke_token)];

/// `failed-access`: a command whose session is not active -- `revoked` or
/// `unused` -- answers `expired` and leaves the world exactly as it was. Unlike
/// `read-post nothing` none of these can fire vacuously.
#[test]
fn failed_access_expires_for_every_session_command() {
	check(|db: &Db, world: &WorldState, seed: Seed| -> TestResult {
		let (world, revoked) = with_revoked_session(world, seed.0);
		load(db, &world);
		let unused = free_session_id(&world, seed.0);
		assert_eq!(world.session_status(revoked), SessionStatus::Revoked);
		assert_eq!(world.session_status(unused), SessionStatus::Unused);

		for (name, command) in SESSION_COMMANDS {
			for sid in [revoked, unused] {
				assert_eq!(
					command(db, sid).expect("run the command"),
					EngineResult::Expired,
					"{name} on the inactive session {sid:?}"
				);
				assert_eq!(
					from_db(db),
					world,
					"{name} on an inactive session must not touch the world"
				);
			}
		}
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// Deterministic unit tests. Each one owns a single database, created here and
// outside any quickcheck case.
// ---------------------------------------------------------------------------

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

/// Two accounts, two active sessions, a revoked session, a followers-only post
/// with a like and a deleted reply, and a follow: enough unrelated rows that
/// "everything else unchanged" is not discharged by accident.
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

fn loaded_sample() -> (Db, WorldState) {
	let db = Db::in_memory().expect("create the in-memory database");
	let world = sample_world();
	reset(&db);
	materialise(&db, &world);
	assert_eq!(from_db(&db), world, "the fixture round-trips");
	(db, world)
}

#[test]
fn duplicate_registration_keeps_the_first_password() {
	let (db, world) = loaded_sample();

	assert_eq!(
		register(&db, "ada", "second").expect("register"),
		EngineResult::SignupFailed
	);
	assert_eq!(
		register(&db, "ada", "first").expect("register"),
		EngineResult::SignupFailed
	);

	let after = from_db(&db);
	assert_eq!(after.accounts["ada"].password, "pw-ada");
	assert_eq!(
		after.accounts["ada"].visibility,
		Visibility::Everyone,
		"a failed registration keeps the stored visibility"
	);
	assert_eq!(after, world, "a taken username is a no-op");
}

#[test]
fn two_logins_issue_distinct_sessions_and_logout_touches_one() {
	let db = Db::in_memory().expect("create the in-memory database");
	// A fresh in-memory database is the empty world.
	let world = empty_world();
	assert_eq!(from_db(&db), world);

	assert_eq!(
		register(&db, "ada", "pw").expect("register"),
		EngineResult::Success
	);
	let first = issued(authenticate(&db, "ada", "pw").expect("authenticate"));
	let second = issued(authenticate(&db, "ada", "pw").expect("authenticate"));
	assert_ne!(first, second, "each login gets a fresh session id");
	let after_logins = from_db(&db);
	assert_eq!(
		after_logins.session_status(first),
		SessionStatus::Active("ada".to_string())
	);
	assert_eq!(
		after_logins.session_status(second),
		SessionStatus::Active("ada".to_string())
	);

	assert_eq!(
		revoke_token(&db, first).expect("revoke-token"),
		EngineResult::Success
	);
	let after = from_db(&db);
	assert_eq!(after.session_status(first), SessionStatus::Revoked);
	assert_eq!(
		after.session_status(second),
		SessionStatus::Active("ada".to_string()),
		"logout only revokes the named session"
	);
	assert_eq!(after.sessions.len(), 2);
	assert_eq!(after.accounts, after_logins.accounts);
}

#[test]
fn revoke_of_never_issued_session_creates_no_row() {
	let (db, world) = loaded_sample();
	let before = from_db(&db);

	assert_eq!(
		revoke_token(&db, SessionId(7)).expect("revoke-token"),
		EngineResult::Expired
	);

	let after = from_db(&db);
	assert_eq!(after.session_status(SessionId(7)), SessionStatus::Unused);
	assert_eq!(after, world, "no row and no other change");
	assert_eq!(after, before);
}

#[test]
fn credentials_are_compared_exactly() {
	let db = Db::in_memory().expect("create the in-memory database");
	assert_eq!(
		register(&db, "ada", "Secret").expect("register"),
		EngineResult::Success
	);
	let before = from_db(&db);

	for (user, pass) in [("ada", "secret"), ("Ada", "Secret"), ("ada", "Secret ")] {
		assert_eq!(
			authenticate(&db, user, pass).expect("authenticate"),
			EngineResult::LoginFailed,
			"{user:?}/{pass:?} must not match"
		);
	}
	assert_eq!(from_db(&db), before, "no session may be created");
}

#[test]
fn accounts_store_any_string_the_spec_allows() {
	// Twitter.agda:470-488 has no premise on either string, so the engine
	// stores them verbatim (the interface is line based, so CR and LF cannot
	// appear in them).
	let db = Db::in_memory().expect("create the in-memory database");
	assert_eq!(
		register(&db, "ada lovelace", "p w\ttab").expect("register"),
		EngineResult::Success
	);

	let after = from_db(&db);
	assert_eq!(
		after.accounts.get("ada lovelace"),
		Some(&account("p w\ttab", Visibility::Everyone))
	);
	assert!(
		matches!(
			authenticate(&db, "ada lovelace", "p w\ttab").expect("authenticate"),
			EngineResult::IssuedSession(_)
		),
		"login answers issued-session, not success"
	);
}

#[test]
fn failed_login_does_not_create_a_session_row() {
	let (db, world) = loaded_sample();

	assert_eq!(
		authenticate(&db, "ada", "nope").expect("authenticate"),
		EngineResult::LoginFailed
	);
	assert_eq!(
		authenticate(&db, "bob", "pw-ada").expect("authenticate"),
		EngineResult::LoginFailed
	);
	assert_eq!(from_db(&db), world, "a failed login changes nothing");
}
