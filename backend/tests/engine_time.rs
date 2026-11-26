//! Property and unit tests for the `time-passes` engine command (task T7).
//!
//! Every property is a direct rendering of the `session-timeout` Step of
//! `spec/Twitter.agda` (691-702): every `active` session becomes `revoked`,
//! every other session row is untouched, and nothing else in the world moves.
//! The matching Agda lemmas are `time-passes-success` and
//! `time-passes-idempotent` in `ImplProofs.agda`, both stated over
//! `timed-out-world` -- the world whose `session-at` is `before`'s composed
//! with `timed-out`.
//!
//! The tests drive the engine exactly as the interface will: one in-memory
//! sqlite database per check, seeded through `store`/`ids` only, no caches.

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::Text;
use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::time::time_passes;
use formal_twitter::ids;
use formal_twitter::model::{PostId, SessionId, SessionStatus, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

// ---------------------------------------------------------------------------
// Harness: an in-memory database, plus read-only views of it.
// ---------------------------------------------------------------------------

fn database() -> Db {
	Db::in_memory().expect("create in-memory database")
}

fn status_of(db: &Db, sid: SessionId) -> SessionStatus {
	db.read(|conn| store::get_session(conn, sid))
		.expect("read session")
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
/// one username is a prefix of another.
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

/// The whole persisted world rendered as text.
fn world(db: &Db) -> Vec<String> {
	let mut out = accounts_snapshot(db);
	out.push("--sessions--".to_string());
	out.extend(sessions_snapshot(db));
	out.push("--others--".to_string());
	out.extend(others_snapshot(db));
	out
}

/// The sessions snapshot `time-passes` must produce from `before`: every
/// `active` row keeps its id and username and becomes `revoked`, every other
/// row is copied unchanged. This is `timed-out` (ImplProofs.agda) applied
/// row-wise -- a session that is already `revoked` stays `revoked`, and an
/// `unused` session has no row at all.
fn revoked_rows(before: &[String]) -> Vec<String> {
	let mut out: Vec<String> = before
		.iter()
		.map(|line| {
			let (id, rest) = line.split_once('|').expect("id|status|username");
			let (status, user) = rest.split_once('|').expect("status|username");
			let status = if status == "active" {
				"revoked"
			} else {
				status
			};
			format!("{id}|{status}|{user}")
		})
		.collect();
	out.sort_unstable();
	out
}

// ---------------------------------------------------------------------------
// Seeding. Everything goes in through `store`/`ids`, never through the engine,
// so the fixture cannot be influenced by the code under test.
// ---------------------------------------------------------------------------

const PASSWORD: &str = "seed-pw";

/// What `seed` put into the database, so a property can name the rows it
/// expects to see afterwards.
struct Seeded {
	/// Sessions that were `active` before the timeout.
	active: Vec<SessionId>,
	/// A session that was already `revoked`.
	revoked: SessionId,
	/// A session id that was never inserted into the sessions table.
	unused: SessionId,
	/// A post by the second account, followed and liked by the first.
	post: PostId,
}

fn seed_account(db: &Db, name: &str) {
	assert!(
		db.write(|conn| store::create_account(conn, name, PASSWORD))
			.expect("seed account"),
		"precondition: {name} is a free username"
	);
}

fn issue_session(db: &Db, name: &str) -> SessionId {
	db.write(|conn| {
		let sid = ids::allocate_session_id(conn)?;
		store::activate_session(conn, sid, name)?;
		Ok(sid)
	})
	.expect("issue session")
}

/// Two accounts, one `active` session per account (two for `first`), a second
/// `revoked` session, a post by `second` that `first` follows and likes, and a
/// session id that was never inserted.
///
/// The unrelated rows matter: `session-timeout` carries an "everything else
/// unchanged" premise, and a database holding only the sessions under test
/// would discharge it by accident.
fn seed(db: &Db, first: &str, second: &str, text: &str, unused: SessionId) -> Seeded {
	for name in [first, second] {
		seed_account(db, name);
	}
	let active = vec![
		issue_session(db, first),
		issue_session(db, second),
		issue_session(db, first),
	];
	let revoked = issue_session(db, second);
	db.write(|conn| store::revoke_session(conn, revoked))
		.expect("seed revoked session");
	let post = db
		.write(|conn| {
			let pid = ids::allocate_post_id(conn)?;
			store::insert_post(conn, pid, second, text, Visibility::Everyone)?;
			store::add_follow(conn, first, second)?;
			store::add_like(conn, pid, first)?;
			Ok(pid)
		})
		.expect("seed post");
	assert_eq!(
		status_of(db, unused),
		SessionStatus::Unused,
		"precondition: no session was ever inserted under {unused:?}"
	);
	Seeded {
		active,
		revoked,
		unused,
		post,
	}
}

// ---------------------------------------------------------------------------
// Generators.
// ---------------------------------------------------------------------------

// `|` is left out so that the `id|status|username` snapshot lines stay
// unambiguous.
const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&* ";

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

#[derive(Clone, Debug)]
struct SeedValue(u64);

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

impl Arbitrary for SeedValue {
	fn arbitrary(g: &mut Gen) -> Self {
		SeedValue(u64::arbitrary(g))
	}
}

/// A session id no allocated session can plausibly have: `allocate_session_id`
/// draws at random from `1..=i64::MAX`, so a small constant derived from the
/// quickcheck seed is absent from a fresh database. `seed` asserts that
/// precondition on every use.
fn absent_sid(seed: u64) -> SessionId {
	SessionId(1_000_000 + (seed % 1_000) as i64)
}

// ---------------------------------------------------------------------------
// P1: time-passes -- `session-timeout` (Twitter.agda:691-702).
// Agda: `time-passes-success` over `timed-out-world` / `timed-out`.
// ---------------------------------------------------------------------------

/// The first premise of `session-timeout`: every active session is `revoked`
/// afterwards. The second premise: nothing else in the world moves -- no
/// account, no post, no follow, no like, and no session row is added or
/// removed.
#[quickcheck]
fn time_passes_revokes_every_active_session(
	first: Name,
	second: Name,
	text: Body,
	seed_value: SeedValue,
) -> TestResult {
	if first.0 == second.0 {
		return TestResult::discard();
	}
	let db = database();
	let seeded = seed(&db, &first.0, &second.0, &text.0, absent_sid(seed_value.0));
	let accounts_before = accounts_snapshot(&db);
	let sessions_before = sessions_snapshot(&db);
	let others_before = others_snapshot(&db);

	assert_eq!(
		time_passes(&db).expect("time-passes"),
		EngineResult::Success
	);

	// The sessions of this world: seeded `active` ones, a seeded `revoked` one
	// and a session id that was never inserted.
	for sid in &seeded.active {
		assert_eq!(status_of(&db, *sid), SessionStatus::Revoked);
	}
	assert_eq!(status_of(&db, seeded.revoked), SessionStatus::Revoked);
	assert_eq!(status_of(&db, seeded.unused), SessionStatus::Unused);

	// No row was added or removed and the only column that moved is `status`.
	assert_eq!(
		sessions_snapshot(&db),
		revoked_rows(&sessions_before),
		"every active session becomes revoked; no other session row moves"
	);
	assert_eq!(accounts_snapshot(&db), accounts_before);
	assert_eq!(others_snapshot(&db), others_before);

	// ... and the post, the follow and the like really are still there.
	assert!(
		db.read(|conn| store::get_post(conn, seeded.post))
			.expect("read post")
			.is_some(),
		"the post survives the timeout"
	);
	assert!(
		db.read(|conn| store::is_following(conn, &first.0, &second.0))
			.expect("read follow"),
		"the follow survives the timeout"
	);
	assert_eq!(
		db.read(|conn| store::like_count(conn, seeded.post))
			.expect("read likes"),
		1,
		"the like survives the timeout"
	);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P2: idempotence. Agda: `time-passes-idempotent`.
// ---------------------------------------------------------------------------

/// A second `time-passes` also answers `success` and leaves the whole world --
/// the session table included -- exactly as the first one left it: after one
/// timeout no session is `active` any more, so the effect is already complete
/// (`timed-out` is idempotent).
#[quickcheck]
fn time_passes_is_idempotent(
	first: Name,
	second: Name,
	text: Body,
	seed_value: SeedValue,
) -> TestResult {
	if first.0 == second.0 {
		return TestResult::discard();
	}
	let db = database();
	seed(&db, &first.0, &second.0, &text.0, absent_sid(seed_value.0));

	assert_eq!(
		time_passes(&db).expect("time-passes"),
		EngineResult::Success
	);
	let sessions_once = sessions_snapshot(&db);
	let world_once = world(&db);

	assert_eq!(
		time_passes(&db).expect("second time-passes"),
		EngineResult::Success
	);
	assert_eq!(
		sessions_snapshot(&db),
		sessions_once,
		"a second timeout changes no session row"
	);
	assert_eq!(world(&db), world_once, "a second timeout changes nothing");
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// P3: the empty world. Agda: `time-passes-idempotent` at a world with no
// sessions (the `session-timeout` premise is vacuous there).
// ---------------------------------------------------------------------------

/// A world with no accounts and no sessions is already timed out:
/// `time-passes` answers `success` and changes nothing.
#[quickcheck]
fn time_passes_on_empty_world_changes_nothing(seed_value: SeedValue) -> TestResult {
	let db = database();
	let before = world(&db);
	let sid = absent_sid(seed_value.0);

	assert_eq!(
		time_passes(&db).expect("time-passes"),
		EngineResult::Success
	);
	assert_eq!(world(&db), before, "the empty world is already timed out");
	assert_eq!(sessions_snapshot(&db), Vec::<String>::new());
	assert_eq!(status_of(&db, sid), SessionStatus::Unused);
	TestResult::passed()
}

// ---------------------------------------------------------------------------
// Deterministic unit tests for the same rules.
// ---------------------------------------------------------------------------

#[test]
fn time_passes_revokes_active_and_keeps_the_other_rows() {
	let db = database();
	let seeded = seed(&db, "ada", "grace", "first post", SessionId(1_000_000));
	let sessions_before = sessions_snapshot(&db);

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(sessions_snapshot(&db), revoked_rows(&sessions_before));
	assert_eq!(status_of(&db, seeded.revoked), SessionStatus::Revoked);
	assert_eq!(status_of(&db, seeded.unused), SessionStatus::Unused);
}

#[test]
fn time_passes_twice_is_still_success_and_changes_nothing() {
	let db = database();
	seed(&db, "ada", "grace", "first post", SessionId(1_000_000));

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	let sessions_once = sessions_snapshot(&db);
	let world_once = world(&db);

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(sessions_snapshot(&db), sessions_once);
	assert_eq!(world(&db), world_once);
}

#[test]
fn time_passes_on_an_empty_database_is_success() {
	let db = database();
	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert!(sessions_snapshot(&db).is_empty());
	assert!(accounts_snapshot(&db).is_empty());
	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
}

#[test]
fn time_passes_keeps_a_revoked_session_revoked() {
	let db = database();
	seed_account(&db, "ada");
	let revoked = issue_session(&db, "ada");
	db.write(|conn| store::revoke_session(conn, revoked))
		.expect("revoke seeded session");
	let id = revoked.0;

	assert_eq!(time_passes(&db).unwrap(), EngineResult::Success);
	assert_eq!(status_of(&db, revoked), SessionStatus::Revoked);
	assert_eq!(sessions_snapshot(&db), vec![format!("{id}|revoked|ada")]);
}
