//! Property and unit tests for the authentication engine (task T2a).
//!
//! Every property below is a direct rendering of a `Step` rule of
//! `spec/Twitter.agda`; the matching Agda lemma lives in `ImplProofs.agda`.
//! P1 (`register`) is `register-success` / `register-duplicate`
//! (Twitter.agda:470-488); P2 (`authenticate`) is `login-success`,
//! `login-absent`, `login-wrong-password` (Twitter.agda:490-516); P3
//! (`revoke-token`) is `logout-success`, `logout-expired`, `logout-unused`
//! (Twitter.agda:677-689); P4 (failed access) is `logout-expired` /
//! `logout-unused` (Twitter.agda:464-468).
//!
//! The tests drive the engine exactly as the interface will: one in-memory
//! sqlite database per check, no in-process caches.

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Text};
use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::auth::{authenticate, register, revoke_token};
use formal_twitter::model::{Account, SessionId, SessionStatus, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

// ---------------------------------------------------------------------------
// Harness: an in-memory database, plus read-only views of it.
// ---------------------------------------------------------------------------

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

fn issued(result: EngineResult) -> SessionId {
	match result {
		EngineResult::IssuedSession(sid) => sid,
		other => panic!("expected IssuedSession, got {other:?}"),
	}
}

fn login(db: &Db, username: &str, password: &str) -> SessionId {
	issued(authenticate(db, username, password).expect("authenticate"))
}

#[derive(QueryableByName)]
struct CountRow {
	#[diesel(sql_type = BigInt)]
	count: i64,
}

fn count(db: &Db, sql: &str) -> i64 {
	db.read(|conn| {
		let row: CountRow = diesel::sql_query(sql.to_owned()).get_result(conn)?;
		Ok(row.count)
	})
	.expect("count query")
}

fn session_rows(db: &Db) -> i64 {
	count(db, "SELECT COUNT(*) AS count FROM sessions")
}

fn account_rows(db: &Db) -> i64 {
	count(db, "SELECT COUNT(*) AS count FROM accounts")
}

#[derive(QueryableByName)]
struct LineRow {
	#[diesel(sql_type = Text)]
	line: String,
}

fn lines(db: &Db, sql: &str) -> Vec<String> {
	db.read(|conn| {
		let rows: Vec<LineRow> = diesel::sql_query(sql.to_owned()).load(conn)?;
		Ok(rows.into_iter().map(|row| row.line).collect())
	})
	.expect("dump query")
}

/// The accounts table rendered as text.
///
/// The snapshot is sorted in Rust on the *composed* line, never on the SQL
/// columns: `'|'` (0x7C) sorts after every letter and digit, so `ORDER BY
/// username` and a sort of `username|password|visibility` disagree whenever
/// one username is a prefix of another. Properties that build the expected
/// rows in Rust sort the composed lines too, so this side must match.
fn accounts_snapshot(db: &Db) -> Vec<String> {
	let mut out = lines(
		db,
		"SELECT username || '|' || password || '|' || default_visibility AS line \
		 FROM accounts ORDER BY username",
	);
	out.sort_unstable();
	out
}

/// The sessions table rendered as text, sorted on the composed line for the
/// same reason as `accounts_snapshot`.
fn sessions_snapshot(db: &Db) -> Vec<String> {
	let mut out = lines(
		db,
		"SELECT CAST(id AS TEXT) || '|' || status || '|' || username AS line \
		 FROM sessions ORDER BY id",
	);
	out.sort_unstable();
	out
}

/// The sessions table minus the row `skip`, so a property can assert that a
/// command touched exactly one session and left the others alone. Sorted on
/// the composed line, like `sessions_snapshot`.
fn sessions_snapshot_except(db: &Db, skip: SessionId) -> Vec<String> {
	let skip = skip.0;
	let mut out = lines(
		db,
		&format!(
			"SELECT CAST(id AS TEXT) || '|' || status || '|' || username AS line \
			 FROM sessions WHERE id <> {skip} ORDER BY id"
		),
	);
	out.sort_unstable();
	out
}

/// Everything except accounts and sessions: posts, follows and likes. Each
/// table's rows are sorted on their composed line; the `--...--` markers keep
/// the three groups apart.
fn others_snapshot(db: &Db) -> Vec<String> {
	fn sorted(db: &Db, sql: &str) -> Vec<String> {
		let mut out = lines(db, sql);
		out.sort_unstable();
		out
	}
	let mut out = sorted(
		db,
		"SELECT CAST(id AS TEXT) || '|' || author || '|' || text || '|' || visibility \
		 || '|' || status AS line FROM posts ORDER BY id",
	);
	out.push("--follows--".to_string());
	out.extend(sorted(
		db,
		"SELECT follower || '|' || followee AS line FROM follows ORDER BY 1",
	));
	out.push("--likes--".to_string());
	out.extend(sorted(
		db,
		"SELECT CAST(pid AS TEXT) || '|' || user AS line FROM post_likes ORDER BY 1",
	));
	out
}

/// The whole persisted world rendered as text. This is how the properties
/// check the "everything else is unchanged" premise of `create-account`,
/// `logout`, `failed-login-*` and `failed-access`.
fn world(db: &Db) -> Vec<String> {
	let mut out = accounts_snapshot(db);
	out.push("--sessions--".to_string());
	out.extend(sessions_snapshot(db));
	out.push("--others--".to_string());
	out.extend(others_snapshot(db));
	out
}

// ---------------------------------------------------------------------------
// Unrelated rows the command under test must not touch.
//
// The spec's `create-account` (Twitter.agda:470-488), `login` (490-516) and
// `logout` (677-689) all carry an "everything else unchanged" premise. A
// database holding only the account under test discharges that premise by
// accident, so every such property seeds a second, unrelated account and a
// pre-existing session first. The rows go in through `store` so that they are
// independent of the engine code under test.
// ---------------------------------------------------------------------------

const OTHER_PASSWORD: &str = "other-secret";
const OTHER_SID: SessionId = SessionId(1_000_000);

/// A second account, registered straight into the database.
fn seed_account(db: &Db, name: &str) {
	assert!(
		db.write(|conn| store::create_account(conn, name, OTHER_PASSWORD))
			.expect("seed account"),
		"precondition: {name} is a free username"
	);
}

/// An `active` session for an account that already exists.
fn seed_session(db: &Db, sid: SessionId, name: &str) {
	db.write(|conn| store::activate_session(conn, sid, name))
		.expect("seed session");
}
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
struct Pass(String);

#[derive(Clone, Debug)]
struct Seed(u64);

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
		Seed(u64::arbitrary(g))
	}
}

/// A session id the engine never issued: `authenticate` allocates its
/// sessions itself, so a small constant id is absent from a fresh database.
fn absent_sid(seed: u64) -> SessionId {
	SessionId(1 + (seed % 1_000) as i64)
}

// ---------------------------------------------------------------------------
// P1: register (Twitter.agda:470-488)
// ---------------------------------------------------------------------------

/// `create-account`: a free username yields `success`, the account holds the
/// given password with `default-visibility = everyone`, and no other account
/// row, session row or post changes.
#[quickcheck]
fn register_free_username_creates_account(name: Name, other: Name, pass: Pass) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	// A second account and a session that `register` must not touch.
	seed_account(&db, &other.0);
	seed_session(&db, OTHER_SID, &other.0);
	let accounts_before = accounts_snapshot(&db);
	let others_before = others_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);

	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let stored = account_of(&db, &name.0).expect("account is stored");
	assert_eq!(stored.password, pass.0);
	assert_eq!(stored.default_visibility, Visibility::Everyone);
	assert_eq!(session_rows(&db), 1, "register must not touch sessions");

	// Exactly one account row was added; every other account row is unchanged
	// (`create-account`'s "everything else unchanged" premise).
	let mut expected = accounts_before;
	expected.push(format!("{}|{}|everyone", name.0, pass.0));
	expected.sort_unstable();
	assert_eq!(accounts_snapshot(&db), expected);
	assert_eq!(
		account_of(&db, &other.0).expect("other account").password,
		OTHER_PASSWORD
	);

	// Only the accounts table may change.
	assert_eq!(others_snapshot(&db), others_before);
	assert_eq!(sessions_snapshot(&db), sessions_before);
	TestResult::passed()
}

/// `failed-create-account`: a taken username yields `signup-failed` and leaves
/// the whole world — including unrelated accounts — unchanged.
#[quickcheck]
fn register_taken_username_fails(name: Name, other: Name, first: Pass, second: Pass) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	assert_eq!(
		register(&db, &name.0, &first.0).expect("register"),
		EngineResult::Success
	);
	let before = world(&db);

	assert_eq!(
		register(&db, &name.0, &second.0).expect("register"),
		EngineResult::SignupFailed
	);
	assert_eq!(
		world(&db),
		before,
		"signup failure must not change the world"
	);
	let stored = account_of(&db, &name.0).expect("account kept");
	assert_eq!(stored.password, first.0);
	assert_eq!(stored.default_visibility, Visibility::Everyone);
	assert_eq!(account_rows(&db), 2);
	assert_eq!(
		account_of(&db, &other.0).expect("other account").password,
		OTHER_PASSWORD,
		"the unrelated account must keep its password"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P2: authenticate (Twitter.agda:490-516)
// ---------------------------------------------------------------------------

/// `login`: the right password issues an active session for that username, the
/// resulting world satisfies `ValidSession` (Twitter.agda:147-156), and every
/// other account and session is unchanged (the `login` Step's "everything else
/// unchanged" premise, Twitter.agda:495-504).
#[quickcheck]
fn authenticate_correct_password_issues_valid_session(
	name: Name,
	other: Name,
	pass: Pass,
) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	// A second account with a pre-existing session: `authenticate` must not
	// touch either of them.
	seed_account(&db, &other.0);
	seed_session(&db, OTHER_SID, &other.0);
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let others_before = others_snapshot(&db);

	let sid = match authenticate(&db, &name.0, &pass.0).expect("authenticate") {
		EngineResult::IssuedSession(sid) => sid,
		other => panic!("expected IssuedSession, got {other:?}"),
	};
	assert_ne!(sid, OTHER_SID, "login must pick a fresh session id");

	// ValidSession.session-unchanged
	assert_eq!(status_of(&db, sid), SessionStatus::Active(name.0.clone()));
	// ValidSession.account-unchanged
	let stored = account_of(&db, &name.0).expect("account backing the session");
	assert_eq!(stored.password, pass.0);
	assert_eq!(stored.default_visibility, Visibility::Everyone);
	assert_eq!(session_rows(&db), 2, "exactly one new session row");

	// Everything else unchanged: the account map, every other session row and
	// the rest of the world (Twitter.agda:495-504).
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(sessions_snapshot_except(&db, sid), sessions_before);
	assert_eq!(others_snapshot(&db), others_before);
	assert_eq!(
		status_of(&db, OTHER_SID),
		SessionStatus::Active(other.0.clone()),
		"the unrelated session stays active"
	);
	TestResult::passed()
}

/// `failed-login-1`: an absent username yields `login-failed` and creates no
/// session.
#[quickcheck]
fn authenticate_absent_user_fails(name: Name, pass: Pass) -> TestResult {
	let db = database();
	let before = world(&db);
	assert_eq!(
		authenticate(&db, &name.0, &pass.0).expect("authenticate"),
		EngineResult::LoginFailed
	);
	assert_eq!(world(&db), before);
	assert_eq!(session_rows(&db), 0, "no session may be created");
	TestResult::passed()
}

/// `failed-login-2`: a wrong password yields `login-failed` and creates no
/// session.
#[quickcheck]
fn authenticate_wrong_password_fails(name: Name, pass: Pass, wrong: Pass) -> TestResult {
	if pass.0 == wrong.0 {
		return TestResult::discard();
	}
	let db = database();
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let before = world(&db);

	assert_eq!(
		authenticate(&db, &name.0, &wrong.0).expect("authenticate"),
		EngineResult::LoginFailed
	);
	assert_eq!(
		world(&db),
		before,
		"a failed login must not change the world"
	);
	assert_eq!(session_rows(&db), 0, "no session may be created");
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P3: revoke-token (Twitter.agda:677-689)
// ---------------------------------------------------------------------------

/// `logout`: revoking an active session succeeds and turns exactly that
/// session `revoked`; every other session and the whole account map are left
/// alone (the `logout` Step's "everything else unchanged" premise,
/// Twitter.agda:683-689).
#[quickcheck]
fn revoke_active_session_succeeds(name: Name, other: Name, pass: Pass) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	// An unrelated account with a pre-existing session, plus a second session
	// of the account under test: neither may be revoked.
	seed_account(&db, &other.0);
	seed_session(&db, OTHER_SID, &other.0);
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let sid = login(&db, &name.0, &pass.0);
	let second = login(&db, &name.0, &pass.0);
	assert_ne!(sid, second, "each login gets a fresh session id");
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot_except(&db, sid);
	let others_before = others_snapshot(&db);

	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Success
	);
	assert_eq!(status_of(&db, sid), SessionStatus::Revoked);
	assert_eq!(
		session_rows(&db),
		3,
		"logout keeps the row, it just revokes it"
	);
	assert_eq!(
		status_of(&db, second),
		SessionStatus::Active(name.0.clone()),
		"logout only revokes the named session"
	);
	assert_eq!(
		status_of(&db, OTHER_SID),
		SessionStatus::Active(other.0.clone()),
		"logout only revokes the named session"
	);
	assert_eq!(account_of(&db, &name.0).expect("account").password, pass.0);
	assert_eq!(
		account_of(&db, &other.0).expect("other account").password,
		OTHER_PASSWORD
	);

	// Only the `sid` row of the session table may change: `sid`, `second` and
	// the unrelated `OTHER_SID` all exist before the logout, so a snapshot that
	// skips `sid` is comparable before and after.
	assert_eq!(sessions_snapshot_except(&db, sid), sessions_before);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(others_snapshot(&db), others_before);
	TestResult::passed()
}

/// `failed-access`: revoking an already revoked session expires the request
/// and changes nothing — not even for an unrelated account and session.
#[quickcheck]
fn revoke_revoked_session_expires(name: Name, other: Name, pass: Pass) -> TestResult {
	if name.0 == other.0 {
		return TestResult::discard();
	}
	let db = database();
	seed_account(&db, &other.0);
	seed_session(&db, OTHER_SID, &other.0);
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let sid = login(&db, &name.0, &pass.0);
	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Success
	);
	let revoked = world(&db);

	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Expired
	);
	assert_eq!(status_of(&db, sid), SessionStatus::Revoked);
	assert_eq!(
		world(&db),
		revoked,
		"an expired request must not touch the world"
	);
	TestResult::passed()
}

/// `failed-access`: revoking a session that was never issued expires the
/// request and creates nothing.
#[quickcheck]
fn revoke_never_issued_session_expires(name: Name, pass: Pass, seed: Seed) -> TestResult {
	let db = database();
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let sid = absent_sid(seed.0);
	let before = world(&db);
	assert_eq!(
		status_of(&db, sid),
		SessionStatus::Unused,
		"precondition: the database has no such session"
	);

	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Expired
	);
	assert_eq!(
		world(&db),
		before,
		"an expired request must not touch the world"
	);
	assert_eq!(session_rows(&db), 0, "no session row may be created");
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P4: failed access on every token-bearing command (Twitter.agda:464-468)
// ---------------------------------------------------------------------------

/// `failed-access`: a token-bearing command whose session is not active
/// answers `expired` and leaves the world untouched. `revoke-token` is the
/// only token-bearing command of this task; the post commands join here when
/// they are implemented.
#[quickcheck]
fn failed_access_expires_and_keeps_world(name: Name, pass: Pass, seed: Seed) -> TestResult {
	let db = database();
	assert_eq!(
		register(&db, &name.0, &pass.0).expect("register"),
		EngineResult::Success
	);
	let sid = login(&db, &name.0, &pass.0);
	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Success
	);
	let snapshot = world(&db);

	// revoked session
	assert_eq!(
		revoke_token(&db, sid).expect("revoke-token"),
		EngineResult::Expired
	);
	assert_eq!(world(&db), snapshot);

	// absent session
	let absent = absent_sid(seed.0);
	if absent != sid {
		assert_eq!(
			status_of(&db, absent),
			SessionStatus::Unused,
			"precondition: the database has no such session"
		);
		assert_eq!(
			revoke_token(&db, absent).expect("revoke-token"),
			EngineResult::Expired
		);
		assert_eq!(world(&db), snapshot);
	}
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// Deterministic unit tests for the database-level edge cases.
// ---------------------------------------------------------------------------

#[test]
fn duplicate_registration_keeps_the_first_password() {
	let db = database();
	assert_eq!(
		register(&db, "ada", "first").unwrap(),
		EngineResult::Success
	);
	assert_eq!(
		register(&db, "ada", "second").unwrap(),
		EngineResult::SignupFailed
	);
	assert_eq!(
		register(&db, "ada", "first").unwrap(),
		EngineResult::SignupFailed
	);
	assert_eq!(account_of(&db, "ada").unwrap().password, "first");
	assert_eq!(account_rows(&db), 1);
}

#[test]
fn two_logins_issue_distinct_sessions_and_logout_touches_one() {
	let db = database();
	assert_eq!(register(&db, "ada", "pw").unwrap(), EngineResult::Success);
	let first = login(&db, "ada", "pw");
	let second = login(&db, "ada", "pw");
	assert_ne!(first, second, "each login gets a fresh session id");
	assert_eq!(
		status_of(&db, first),
		SessionStatus::Active("ada".to_string())
	);
	assert_eq!(
		status_of(&db, second),
		SessionStatus::Active("ada".to_string())
	);

	assert_eq!(revoke_token(&db, first).unwrap(), EngineResult::Success);
	assert_eq!(status_of(&db, first), SessionStatus::Revoked);
	assert_eq!(
		status_of(&db, second),
		SessionStatus::Active("ada".to_string()),
		"logout only revokes the named session"
	);
	assert_eq!(session_rows(&db), 2);
}

#[test]
fn revoke_of_never_issued_session_creates_no_row() {
	let db = database();
	assert_eq!(register(&db, "ada", "pw").unwrap(), EngineResult::Success);
	assert_eq!(session_rows(&db), 0);

	assert_eq!(
		revoke_token(&db, SessionId(7)).unwrap(),
		EngineResult::Expired
	);
	assert_eq!(session_rows(&db), 0);
	assert_eq!(status_of(&db, SessionId(7)), SessionStatus::Unused);
}

#[test]
fn credentials_are_compared_exactly() {
	let db = database();
	assert_eq!(
		register(&db, "ada", "Secret").unwrap(),
		EngineResult::Success
	);
	assert_eq!(
		authenticate(&db, "ada", "secret").unwrap(),
		EngineResult::LoginFailed
	);
	assert_eq!(
		authenticate(&db, "Ada", "Secret").unwrap(),
		EngineResult::LoginFailed
	);
	assert_eq!(
		authenticate(&db, "ada", "Secret ").unwrap(),
		EngineResult::LoginFailed
	);
	assert_eq!(session_rows(&db), 0);
}

#[test]
fn accounts_store_any_string_the_spec_allows() {
	// Twitter.agda:470-488 has no premise on either string, so the engine
	// stores them verbatim (the interface is line based, so CR and LF cannot
	// appear in them).
	let db = database();
	assert_eq!(
		register(&db, "ada lovelace", "p w\ttab").unwrap(),
		EngineResult::Success
	);
	let stored = account_of(&db, "ada lovelace").expect("account is stored");
	assert_eq!(stored.default_visibility, Visibility::Everyone);
	assert_eq!(stored.password, "p w\ttab");
	assert!(
		matches!(
			authenticate(&db, "ada lovelace", "p w\ttab").unwrap(),
			EngineResult::IssuedSession(_)
		),
		"login answers issued-session, not success"
	);
}

#[test]
fn failed_login_does_not_create_a_session_row() {
	let db = database();
	assert_eq!(register(&db, "ada", "pw").unwrap(), EngineResult::Success);
	let before = world(&db);
	assert_eq!(
		authenticate(&db, "ada", "nope").unwrap(),
		EngineResult::LoginFailed
	);
	assert_eq!(
		authenticate(&db, "bob", "pw").unwrap(),
		EngineResult::LoginFailed
	);
	assert_eq!(world(&db), before);
	assert_eq!(session_rows(&db), 0);
}
