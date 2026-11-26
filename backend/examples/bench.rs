//! Benchmark harness for the engine and the HTTP surface.
//!
//! Two things are measured, both only through the public API of the crate:
//!
//! * the engine commands of `spec/Twitter.agda:111-125` over a file-backed,
//!   realistically sized database (2 000 accounts, 20 000 posts, 2 000 follow
//!   edges, 100 000 likes, 100 replies), with warmup and repetitions, reporting
//!   median, p95 and throughput (operations per second);
//! * the routes of `spec/Interface.agda:52-200` through Rocket's local blocking
//!   client, over a fresh in-memory database with 500 posts, reporting the same
//!   statistics per request.
//!
//! A third section reports how the timeline and `read-post` queries scale with
//! the number of posts (1 000 / 20 000 / 100 000), and a fourth how the public
//! post cache changes `read-post`: cache disabled (the pre-cache path), cold
//! (dropped before every measured call) and warm (filled by the previous call),
//! for one `get-tweet` and for a 21-read timeline render burst.
//!
//! Seeding goes through `store` and `ids` exactly like the integration tests do,
//! in a single `db.write` transaction, so every row is committed before the
//! first measurement. Every measured call asserts the answer the spec gives for
//! the state it runs in, so a scenario never silently measures an error path.
//!
//! Run with:
//!
//! ```text
//! nix develop --command bash -c 'cd backend && cargo run --release --example bench'
//! ```

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use diesel::SqliteConnection;
use diesel::connection::{Instrumentation, InstrumentationEvent};

use formal_twitter::db::Db;
use formal_twitter::engine::{EngineResult, auth, posts, social, timeline};
use formal_twitter::ids;
use formal_twitter::model::{DbError, PostId, SessionId, Visibility};
use formal_twitter::server;
use formal_twitter::store;
use rocket::http::ContentType;
use rocket::local::blocking::Client;

/// Every seeded account has this password.
const PASSWORD: &str = "pw";
/// Accounts of the main, file-backed database.
const USERS: usize = 2_000;
/// Posts of the main, file-backed database.
const POSTS: usize = 20_000;
/// Likes of the main, file-backed database.
const LIKES: usize = 100_000;
/// Replies to the single target post.
const REPLIES: usize = 100;
/// Each follow-edge owner follows this many following authors...
const FOLLOWEES: usize = 20;
/// ... and this many accounts own such edges (2 000 follow edges in total).
const FOLLOWERS: usize = 100;
/// Timeline length of every timeline scenario.
const TIMELINE_LENGTH: u32 = 20;
/// Requests per HTTP scenario.
const HTTP_SAMPLES: usize = 200;
/// Post counts of the scaling section.
const SCALING: [usize; 3] = [1_000, 20_000, 100_000];
/// `get-tweet` reads in one render burst: the up-to-20 tweets of a timeline.
const RENDER_GET_TWEETS: usize = 20;

fn username(index: usize) -> String {
	format!("u{index:04}")
}

/* ---------- statement counting ---------- */

/// Whether [`StatementCounter`] is collecting; `false` outside a counted call,
/// so the timing sections pay one relaxed load per statement and nothing else.
static COUNTING: AtomicBool = AtomicBool::new(false);
/// Statements seen while [`COUNTING`] was set.
static STATEMENTS: AtomicUsize = AtomicUsize::new(0);

/// A diesel [`Instrumentation`] that counts the SQL statements a command issues.
///
/// Only `StartQuery` events for `SELECT`/`INSERT`/`UPDATE`/`DELETE` are counted:
/// the transaction frames (`BEGIN`/`COMMIT`) and the connection's `PRAGMA`s are
/// counted out, so the number reported is the number of round trips the command
/// makes to the database, not the transaction overhead around them.
#[derive(Debug)]
struct StatementCounter;

impl Instrumentation for StatementCounter {
	fn on_connection_event(&mut self, event: InstrumentationEvent<'_>) {
		if !COUNTING.load(Ordering::Relaxed) {
			return;
		}
		if let InstrumentationEvent::StartQuery { query, .. } = event {
			let sql = query.to_string();
			let sql = sql.trim_start();
			let counted = ["SELECT", "INSERT", "UPDATE", "DELETE"].iter().any(|verb| {
				sql.len() >= verb.len() && sql[..verb.len()].eq_ignore_ascii_case(verb)
			});
			if counted {
				STATEMENTS.fetch_add(1, Ordering::Relaxed);
			}
		}
	}
}

/// Installs [`StatementCounter`] on the connection behind `db`.
fn count_statements(db: &Db) {
	db.read::<()>(|c| {
		diesel::Connection::set_instrumentation(c, StatementCounter);
		Ok(())
	})
	.expect("install statement counter");
}

/// The statements `op` issues, on a connection [`count_statements`] instrumented.
fn counted<T>(op: impl FnOnce() -> T) -> (T, usize) {
	STATEMENTS.store(0, Ordering::SeqCst);
	COUNTING.store(true, Ordering::SeqCst);
	let value = op();
	COUNTING.store(false, Ordering::SeqCst);
	(value, STATEMENTS.load(Ordering::SeqCst))
}

fn print_statements(title: &str, rows: &[(String, usize)]) {
	println!("\n{title}");
	println!("{:<36} {:>6}", "scenario", "stmts");
	for (scenario, statements) in rows {
		println!("{scenario:<36} {statements:>6}");
	}
}

/* ---------- seeding ---------- */

/// The handles the measurements need after seeding.
struct Seeded {
	/// The acting user is `u0000`, reached through this active session.
	session: SessionId,
	/// The post the reply and `read-post` scenarios use: live and `everyone`,
	/// with `REPLIES` replies.
	target: PostId,
	/// A second live `everyone` post the acting user does not like, for the
	/// like/unlike scenarios.
	spare: PostId,
}

/// A post index whose post is `live` and `everyone` (`insert_scripted` leaves
/// every tenth post `followers-only` and every post with `index % 20 == 5`
/// `deleted`).
fn readable_index(mut index: usize) -> usize {
	while index.is_multiple_of(10) || index % 20 == 5 {
		index += 1;
	}
	index
}

/// Inserts one post with the seeded mix: ~10% `followers-only`, and 5%
/// soft-deleted.
fn insert_scripted(
	c: &mut SqliteConnection,
	index: usize,
	users: usize,
) -> Result<PostId, DbError> {
	let pid = ids::allocate_post_id(c)?;
	let visibility = if index.is_multiple_of(10) {
		Visibility::FollowersOnly
	} else {
		Visibility::Everyone
	};
	store::insert_post(
		c,
		pid,
		&username(index % users),
		&format!("post {index}"),
		visibility,
	)?;
	if index % 20 == 5 {
		store::soft_delete_post(c, pid)?;
	}
	Ok(pid)
}

/// Seeds `db` in one transaction and returns the handles the measurements use.
fn seed(db: &Db, users: usize, post_count: usize, like_count: usize, reply_count: usize) -> Seeded {
	db.write(|c| {
		for index in 0..users {
			store::create_account(c, &username(index), PASSWORD)?;
		}
		let mut session = None;
		for index in 0..FOLLOWERS.min(users) {
			let sid = ids::allocate_session_id(c)?;
			store::activate_session(c, sid, &username(index))?;
			if index == 0 {
				session = Some(sid);
			}
		}
		let session = session.expect("at least one seeded session");
		let mut post_ids = Vec::with_capacity(post_count);
		for index in 0..post_count {
			post_ids.push(insert_scripted(c, index, users)?);
		}
		let target_index = readable_index(post_count * 2 / 3).min(post_count - 1);
		let spare_index = readable_index(target_index + 1).min(post_count - 1);
		let target = post_ids[target_index];
		let spare = post_ids[spare_index];
		// Every post gets `like_count / post_count` distinct likers.
		for like in 0..like_count {
			let index = like % post_count;
			let liker = (like / post_count) * 7 + index;
			store::add_like(c, post_ids[index], &username(liker % users))?;
		}
		for reply in 0..reply_count {
			let pid = ids::allocate_post_id(c)?;
			store::insert_reply(
				c,
				pid,
				&username((reply + 1) % users),
				&format!("reply {reply}"),
				Visibility::Everyone,
				target,
			)?;
		}
		for follower in 0..FOLLOWERS.min(users) {
			for step in 1..=FOLLOWEES {
				store::add_follow(c, &username(follower), &username((follower + step) % users))?;
			}
		}
		// The like/unlike scenarios need a post the acting user does not like.
		store::remove_like(c, spare, &username(0))?;
		Ok(Seeded {
			session,
			target,
			spare,
		})
	})
	.expect("seed the database")
}

/// Appends `count` more scripted posts, continuing the index sequence.
fn append_posts(db: &Db, users: usize, offset: usize, count: usize) {
	db.write(|c| {
		for index in offset..offset + count {
			insert_scripted(c, index, users)?;
		}
		Ok(())
	})
	.expect("append posts")
}

/* ---------- measurement ---------- */

struct Stats {
	median: Duration,
	p95: Duration,
	throughput: f64,
	operations: usize,
}

fn percentile(sorted: &[Duration], q: f64) -> Duration {
	if sorted.is_empty() {
		return Duration::ZERO;
	}
	let index = ((sorted.len() - 1) as f64 * q).round() as usize;
	sorted[index.min(sorted.len() - 1)]
}

fn summarise(mut per_op: Vec<Duration>) -> Stats {
	let operations = per_op.len();
	per_op.sort();
	let median = percentile(&per_op, 0.5);
	Stats {
		median,
		p95: percentile(&per_op, 0.95),
		throughput: 1.0 / median.as_secs_f64(),
		operations,
	}
}

/// Measures `op` after a fixed warmup, in batches sized to at least 2 ms, and
/// reports the median and p95 of the per-operation time over 15 samples.
fn measure(mut op: impl FnMut()) -> Stats {
	let warmup = Instant::now();
	while warmup.elapsed() < Duration::from_millis(50) {
		op();
	}
	let mut iters = 1usize;
	loop {
		let start = Instant::now();
		for _ in 0..iters {
			op();
		}
		if start.elapsed() >= Duration::from_millis(2) || iters >= 1 << 13 {
			break;
		}
		iters *= 2;
	}
	let mut per_op = Vec::with_capacity(15);
	for _ in 0..15 {
		let start = Instant::now();
		for _ in 0..iters {
			op();
		}
		per_op.push(start.elapsed() / iters as u32);
	}
	summarise(per_op)
}

/// Measures `op` one call at a time, running `reset` between calls outside the
/// timed region, so the timed work never accumulates state.
fn measure_with_reset(mut op: impl FnMut(), mut reset: impl FnMut()) -> Stats {
	for _ in 0..5 {
		op();
		reset();
	}
	let mut iters = 1usize;
	loop {
		let start = Instant::now();
		for _ in 0..iters {
			reset();
			op();
		}
		if start.elapsed() >= Duration::from_millis(2) || iters >= 1 << 13 {
			break;
		}
		iters *= 2;
	}
	let mut per_op = Vec::with_capacity(15 * iters);
	for _ in 0..15 {
		for _ in 0..iters {
			reset();
			let start = Instant::now();
			op();
			per_op.push(start.elapsed());
		}
	}
	summarise(per_op)
}

/// Measures `op` one call at a time over `samples` calls: the HTTP shape, where
/// a request is never repeated inside one timed region.
fn measure_each(mut op: impl FnMut(), samples: usize) -> Stats {
	for _ in 0..samples / 8 + 1 {
		op();
	}
	let mut per_op = Vec::with_capacity(samples);
	for _ in 0..samples {
		let start = Instant::now();
		op();
		per_op.push(start.elapsed());
	}
	summarise(per_op)
}

/* ---------- reporting ---------- */

struct Row {
	scenario: String,
	stats: Stats,
}

impl Row {
	fn new(scenario: impl Into<String>, stats: Stats) -> Self {
		Self {
			scenario: scenario.into(),
			stats,
		}
	}
}

fn fmt_duration(value: Duration) -> String {
	let nanos = value.as_nanos();
	if nanos < 1_000 {
		format!("{nanos} ns")
	} else if nanos < 1_000_000 {
		format!("{:.2} us", nanos as f64 / 1e3)
	} else if nanos < 1_000_000_000 {
		format!("{:.2} ms", nanos as f64 / 1e6)
	} else {
		format!("{:.3} s", nanos as f64 / 1e9)
	}
}

fn print_table(title: &str, rows: &[Row]) {
	println!("\n{title}");
	println!(
		"{:<30} {:>7} {:>12} {:>12} {:>12}",
		"scenario", "ops", "median", "ops/sec", "p95"
	);
	for row in rows {
		println!(
			"{:<30} {:>7} {:>12} {:>12} {:>12}",
			row.scenario,
			row.stats.operations,
			fmt_duration(row.stats.median),
			format!("{:.0}", row.stats.throughput),
			fmt_duration(row.stats.p95)
		);
	}
}

/* ---------- engine scenarios ---------- */

fn expect_success(result: Result<EngineResult, DbError>, what: &str) {
	match result {
		Ok(EngineResult::Success) => {}
		other => panic!("{what}: {other:?}"),
	}
}

fn expect_created(result: Result<EngineResult, DbError>, what: &str) {
	match result {
		Ok(EngineResult::CreatedPost(_)) => {}
		other => panic!("{what}: {other:?}"),
	}
}

fn expect_timeline(result: Result<EngineResult, DbError>, what: &str) {
	match result {
		Ok(EngineResult::ReturnedTimeline(ids)) => {
			assert_eq!(
				ids.len(),
				TIMELINE_LENGTH as usize,
				"{what}: expected a full timeline"
			);
		}
		other => panic!("{what}: {other:?}"),
	}
}

fn expect_post(result: Result<EngineResult, DbError>, what: &str) {
	match result {
		Ok(EngineResult::ReturnedPost { replies, .. }) => {
			assert!(!replies.is_empty(), "{what}: expected replies");
		}
		other => panic!("{what}: {other:?}"),
	}
}

/// A `returned-post` answer of a post that need not have replies, for the
/// timeline-sized pool of public posts the render burst reads.
fn expect_returned(result: Result<EngineResult, DbError>, what: &str) {
	match result {
		Ok(EngineResult::ReturnedPost { .. }) => {}
		other => panic!("{what}: expected a returned post, got {other:?}"),
	}
}

fn engine_report(db: &Db, seeded: &Seeded) -> Vec<Row> {
	let session = seeded.session;
	let actor = username(0);
	let mut rows = Vec::new();

	// Reads first: the reply scenario below adds posts to the target.
	rows.push(Row::new(
		"engine: get-tweet (session)",
		measure(|| {
			expect_post(
				posts::read_post(db, Some(session), seeded.target),
				"get-tweet",
			)
		}),
	));
	rows.push(Row::new(
		"engine: get-tweet (anonymous)",
		measure(|| expect_post(posts::read_post(db, None, seeded.target), "get-tweet-anon")),
	));
	rows.push(Row::new(
		"engine: personal timeline n=20",
		measure(|| {
			expect_timeline(
				timeline::personal_timeline(db, session, TIMELINE_LENGTH),
				"personal",
			)
		}),
	));
	rows.push(Row::new(
		"engine: private global n=20",
		measure(|| {
			expect_timeline(
				timeline::global_timeline(db, Some(session), TIMELINE_LENGTH),
				"private-global",
			)
		}),
	));
	rows.push(Row::new(
		"engine: anonymous global n=20",
		measure(|| {
			expect_timeline(
				timeline::global_timeline(db, None, TIMELINE_LENGTH),
				"anon-global",
			)
		}),
	));

	// The empty transactions decompose the write path: what a `db.write` costs
	// with no statement at all is `BEGIN` + `COMMIT` (i.e. the WAL fsync).
	rows.push(Row::new(
		"engine: no-op read txn",
		measure(|| {
			db.read::<()>(|_| Ok(())).expect("read transaction");
		}),
	));
	rows.push(Row::new(
		"engine: no-op write txn",
		measure(|| {
			db.write::<()>(|_| Ok(())).expect("write transaction");
		}),
	));

	let mut registrations = 0u64;
	rows.push(Row::new(
		"engine: register",
		measure(|| {
			registrations += 1;
			expect_success(
				auth::register(db, &format!("bench{registrations}"), PASSWORD),
				"register",
			);
		}),
	));
	rows.push(Row::new(
		"engine: login",
		measure(|| match auth::authenticate(db, &actor, PASSWORD) {
			Ok(EngineResult::IssuedSession(_)) => {}
			other => panic!("login: {other:?}"),
		}),
	));
	rows.push(Row::new(
		"engine: publish",
		measure(|| {
			expect_created(
				posts::publish(db, session, "benchmark post", None),
				"publish",
			);
		}),
	));
	rows.push(Row::new(
		"engine: publish reply",
		measure(|| {
			expect_created(
				posts::publish(db, session, "benchmark reply", Some(seeded.target)),
				"publish-reply",
			);
		}),
	));
	rows.push(Row::new(
		"engine: like",
		measure_with_reset(
			|| expect_success(social::like(db, session, seeded.spare), "like"),
			|| {
				social::unlike(db, session, seeded.spare).expect("unlike reset");
			},
		),
	));
	rows.push(Row::new(
		"engine: unlike",
		measure_with_reset(
			|| expect_success(social::unlike(db, session, seeded.spare), "unlike"),
			|| {
				social::like(db, session, seeded.spare).expect("like reset");
			},
		),
	));
	let followee = username(500);
	rows.push(Row::new(
		"engine: follow",
		measure_with_reset(
			|| expect_success(social::follow(db, session, &followee), "follow"),
			|| {
				social::unfollow(db, session, &followee).expect("unfollow reset");
			},
		),
	));
	rows.push(Row::new(
		"engine: unfollow",
		measure_with_reset(
			|| expect_success(social::unfollow(db, session, &followee), "unfollow"),
			|| {
				social::follow(db, session, &followee).expect("follow reset");
			},
		),
	));
	rows
}

/* ---------- cache scenarios ---------- */

/// The `n` newest public (`live`, `everyone`) posts: the tweets a timeline
/// render fetches one `get-tweet` at a time.
fn public_posts(db: &Db, n: usize) -> Vec<PostId> {
	db.read(|c| {
		let mut out = Vec::new();
		for pid in store::newest_first(c, u32::MAX)? {
			if store::can_read_anonymous(c, pid)? {
				out.push(pid);
				if out.len() == n {
					break;
				}
			}
		}
		Ok(out)
	})
	.expect("public posts")
}

/// One timeline render: the timeline of `spec/Interface.agda` plus one
/// `get-tweet` per tweet it shows.
fn render_burst(db: &Db, session: Option<SessionId>, tweets: &[PostId]) {
	expect_timeline(
		timeline::global_timeline(db, session, TIMELINE_LENGTH),
		"burst-timeline",
	);
	for pid in tweets {
		expect_returned(posts::read_post(db, session, *pid), "burst-get-tweet");
	}
}

/// The cache scenarios, measured on the same file-backed database and the same
/// data as the engine table above:
///
/// * `no cache` -- a second handle on the same file with
///   [`Db::new_uncached`], i.e. exactly the pre-cache read path;
/// * `cold` -- the cache is dropped outside the timed region, so each call pays
///   the database read plus one insertion;
/// * `warm` -- the cache was filled by the immediately preceding call.
fn cache_report(db: &Db, uncached: &Db, seeded: &Seeded) -> Vec<Row> {
	let session = seeded.session;
	let target = seeded.target;
	let tweets = public_posts(db, RENDER_GET_TWEETS);
	assert_eq!(tweets.len(), RENDER_GET_TWEETS, "not enough public posts");
	let mut rows = Vec::new();

	rows.push(Row::new(
		"cache: get-tweet session (no cache)",
		measure(|| {
			expect_post(
				posts::read_post(uncached, Some(session), target),
				"get-tweet-no-cache",
			)
		}),
	));
	rows.push(Row::new(
		"cache: get-tweet session (cold)",
		measure_with_reset(
			|| {
				expect_post(
					posts::read_post(db, Some(session), target),
					"get-tweet-cold",
				)
			},
			|| db.clear_cache_for_tests(),
		),
	));
	rows.push(Row::new(
		"cache: get-tweet session (warm)",
		measure(|| {
			expect_post(
				posts::read_post(db, Some(session), target),
				"get-tweet-warm",
			)
		}),
	));
	rows.push(Row::new(
		"cache: get-tweet anonymous (no cache)",
		measure(|| {
			expect_post(
				posts::read_post(uncached, None, target),
				"get-tweet-anon-no-cache",
			)
		}),
	));
	rows.push(Row::new(
		"cache: get-tweet anonymous (cold)",
		measure_with_reset(
			|| expect_post(posts::read_post(db, None, target), "get-tweet-anon-cold"),
			|| db.clear_cache_for_tests(),
		),
	));
	rows.push(Row::new(
		"cache: get-tweet anonymous (warm)",
		measure(|| expect_post(posts::read_post(db, None, target), "get-tweet-anon-warm")),
	));
	rows.push(Row::new(
		"cache: render burst 1+20 (no cache)",
		measure(|| render_burst(uncached, Some(session), &tweets)),
	));
	rows.push(Row::new(
		"cache: render burst 1+20 (cold)",
		measure_with_reset(
			|| render_burst(db, Some(session), &tweets),
			|| db.clear_cache_for_tests(),
		),
	));
	rows.push(Row::new(
		"cache: render burst 1+20 (warm)",
		measure(|| render_burst(db, Some(session), &tweets)),
	));
	rows
}

/* ---------- statement counts ---------- */

/// The database round trips each command makes, counted from diesel's
/// [`InstrumentationEvent::StartQuery`] events on the same database and data.
///
/// Runs after the timing tables because it writes (`publish`, `like`, `follow`)
/// and would otherwise disturb them.
fn statement_report(db: &Db, seeded: &Seeded) -> Vec<(String, usize)> {
	let session = seeded.session;
	let target = seeded.target;
	let spare = seeded.spare;
	let mut rows: Vec<(String, usize)> = Vec::new();

	// `read-post`, cold and warm, with and without a session. The spare post is
	// used rather than the target: `engine_report`'s reply scenario can push the
	// target past `CACHE_MAX_REPLIES`, after which its body is deliberately not
	// cached and the warm rows would not be warm.
	db.clear_cache_for_tests();
	let (_, cold) = counted(|| {
		expect_returned(posts::read_post(db, Some(session), spare), "stmt-get-tweet");
	});
	rows.push(("get-tweet session (cold)".to_owned(), cold));
	let (_, warm) = counted(|| {
		expect_returned(posts::read_post(db, Some(session), spare), "stmt-get-tweet");
	});
	rows.push(("get-tweet session (warm)".to_owned(), warm));

	db.clear_cache_for_tests();
	let (_, cold) = counted(|| {
		expect_returned(posts::read_post(db, None, spare), "stmt-get-tweet-anon");
	});
	rows.push(("get-tweet anonymous (cold)".to_owned(), cold));
	let (_, warm) = counted(|| {
		expect_returned(posts::read_post(db, None, spare), "stmt-get-tweet-anon");
	});
	rows.push(("get-tweet anonymous (warm)".to_owned(), warm));

	let (_, count) = counted(|| {
		expect_created(
			posts::publish(db, session, "statement-count post", None),
			"stmt-publish",
		);
	});
	rows.push(("publish".to_owned(), count));
	let (_, count) = counted(|| {
		expect_created(
			posts::publish(db, session, "statement-count reply", Some(target)),
			"stmt-publish-reply",
		);
	});
	rows.push(("publish reply".to_owned(), count));

	social::unlike(db, session, spare).expect("reset unlike");
	let (_, count) = counted(|| expect_success(social::like(db, session, spare), "stmt-like"));
	rows.push(("like".to_owned(), count));
	let (_, count) = counted(|| expect_success(social::unlike(db, session, spare), "stmt-unlike"));
	rows.push(("unlike".to_owned(), count));

	let followee = username(500);
	social::unfollow(db, session, &followee).expect("reset unfollow");
	let (_, count) =
		counted(|| expect_success(social::follow(db, session, &followee), "stmt-follow"));
	rows.push(("follow".to_owned(), count));
	let (_, count) = counted(|| {
		expect_success(social::unfollow(db, session, &followee), "stmt-unfollow");
	});
	rows.push(("unfollow".to_owned(), count));

	let (_, count) = counted(|| {
		expect_timeline(
			timeline::personal_timeline(db, session, TIMELINE_LENGTH),
			"stmt-personal",
		);
	});
	rows.push(("personal timeline n=20".to_owned(), count));
	let (_, count) = counted(|| {
		expect_timeline(
			timeline::global_timeline(db, Some(session), TIMELINE_LENGTH),
			"stmt-private-global",
		);
	});
	rows.push(("private global n=20".to_owned(), count));
	let (_, count) = counted(|| {
		expect_timeline(
			timeline::global_timeline(db, None, TIMELINE_LENGTH),
			"stmt-anon-global",
		);
	});
	rows.push(("anonymous global n=20".to_owned(), count));

	rows
}

/* ---------- HTTP scenarios ---------- */

fn request_body(lines: &[&str]) -> String {
	let mut body = lines.join("\r\n");
	body.push_str("\r\n");
	body
}

fn http_request(client: &Client, action: &str, body: &str) {
	let response = client
		.post(format!("/api/{action}"))
		.header(ContentType::new("text", "plain").with_params(("charset", "utf-8")))
		.body(body)
		.dispatch();
	let status = response.status().code;
	let bytes = response.into_bytes().unwrap_or_default();
	assert_eq!(status, 200, "{action}: {}", String::from_utf8_lossy(&bytes));
}

fn http_report() -> Vec<Row> {
	let db = Db::in_memory().expect("in-memory database");
	let seeded = seed(&db, 200, 500, 500, REPLIES);
	let session = seeded.session.0.to_string();
	let target = seeded.target.0.to_string();
	let client = Client::tracked(server::build(db)).expect("rocket local client");
	let mut rows = Vec::new();

	let mut signups = 0u64;
	rows.push(Row::new(
		"http: signup",
		measure_each(
			|| {
				signups += 1;
				let body = request_body(&[&format!("http{signups}"), PASSWORD]);
				http_request(&client, "signup", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows.push(Row::new(
		"http: login",
		measure_each(
			|| {
				let body = request_body(&[&username(0), PASSWORD]);
				http_request(&client, "login", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows.push(Row::new(
		"http: post-tweet",
		measure_each(
			|| {
				let body = request_body(&[&session, "hello from the bench"]);
				http_request(&client, "post-tweet", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows.push(Row::new(
		"http: get-tweet",
		measure_each(
			|| {
				let body = request_body(&[&session, &target]);
				http_request(&client, "get-tweet", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows.push(Row::new(
		"http: private-timeline",
		measure_each(
			|| {
				let body = request_body(&[&session, "20"]);
				http_request(&client, "private-timeline", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows.push(Row::new(
		"http: global-timeline",
		measure_each(
			|| {
				let body = request_body(&["20"]);
				http_request(&client, "global-timeline", &body);
			},
			HTTP_SAMPLES,
		),
	));
	rows
}

/* ---------- scaling ---------- */

/// One row of the scaling table: the total number of posts, and the median of
/// each scenario at that size.
struct ScalingRow {
	posts: usize,
	cells: [Duration; 4],
}

const SCALING_HEADERS: [&str; 4] = [
	"personal-tl",
	"private-global",
	"anon-global",
	"get-tweet-cold",
];

fn scaling_measure(db: &Db, session: SessionId, target: PostId) -> [Duration; 4] {
	[
		measure(|| {
			expect_timeline(
				timeline::personal_timeline(db, session, TIMELINE_LENGTH),
				"scaling-personal",
			)
		})
		.median,
		measure(|| {
			expect_timeline(
				timeline::global_timeline(db, Some(session), TIMELINE_LENGTH),
				"scaling-private",
			)
		})
		.median,
		measure(|| {
			expect_timeline(
				timeline::global_timeline(db, None, TIMELINE_LENGTH),
				"scaling-anon",
			)
		})
		.median,
		// The cache is dropped outside the timed region, so the column keeps
		// measuring the database path rather than a warm cache hit.
		measure_with_reset(
			|| expect_post(posts::read_post(db, None, target), "scaling-get-tweet"),
			|| db.clear_cache_for_tests(),
		)
		.median,
	]
}

fn scaling_report() -> Vec<ScalingRow> {
	let path = format!("/tmp/formal-twitter-bench-scale-{}.db", std::process::id());
	let clean = |path: &str| {
		for suffix in ["", "-wal", "-shm"] {
			let _ = std::fs::remove_file(format!("{path}{suffix}"));
		}
	};
	clean(&path);
	let db = Db::new(&path).expect("scaling database");
	let seeded = seed(&db, USERS, SCALING[0], 5_000, 20);
	let mut rows = Vec::new();
	let mut seeded_posts = SCALING[0];
	rows.push(ScalingRow {
		posts: seeded_posts,
		cells: scaling_measure(&db, seeded.session, seeded.target),
	});
	for total in SCALING.iter().skip(1) {
		append_posts(&db, USERS, seeded_posts, total - seeded_posts);
		seeded_posts = *total;
		rows.push(ScalingRow {
			posts: seeded_posts,
			cells: scaling_measure(&db, seeded.session, seeded.target),
		});
	}
	drop(db);
	clean(&path);
	rows
}

fn print_scaling(rows: &[ScalingRow]) {
	println!("\nscaling: median per operation, by total number of posts");
	print!("{:>10}", "posts");
	for header in SCALING_HEADERS {
		print!(" {header:>16}");
	}
	println!();
	for row in rows {
		print!("{:>10}", row.posts);
		for cell in row.cells {
			print!(" {:>16}", fmt_duration(cell));
		}
		println!();
	}
}

/* ---------- main ---------- */

fn main() {
	let path = format!("/tmp/formal-twitter-bench-{}.db", std::process::id());
	let clean = |path: &str| {
		for suffix in ["", "-wal", "-shm"] {
			let _ = std::fs::remove_file(format!("{path}{suffix}"));
		}
	};
	clean(&path);
	let db = Db::new(&path).expect("file-backed database");

	let started = Instant::now();
	let seeded = seed(&db, USERS, POSTS, LIKES, REPLIES);
	let seed_time = started.elapsed();
	println!(
		"seeded {} accounts, {} posts, {} follow edges, {} likes, {} replies in {}",
		USERS,
		POSTS,
		FOLLOWERS * FOLLOWEES,
		LIKES,
		REPLIES,
		fmt_duration(seed_time)
	);
	println!("database: {path} (WAL), engine in-process, HTTP via Rocket's local client");

	// The cache table is measured first, on the freshly seeded databases: later
	// sections mutate the shared target post (the reply benchmark adds hundreds
	// of replies, past the per-entry reply cap).
	// A second handle on the same file with the cache disabled: the "before"
	// column of the cache table. Reads only, so it never needs to invalidate.
	let uncached = Db::new_uncached(&path).expect("uncached handle to the same database");
	let cache = cache_report(&db, &uncached, &seeded);
	let engine = engine_report(&db, &seeded);
	count_statements(&db);
	let statements = statement_report(&db, &seeded);
	let http = http_report();
	let scaling = scaling_report();

	print_table(
		"cache: same database and data, cache disabled / cold / warm",
		&cache,
	);
	print_table("engine (warmup + 15 samples, adaptive batch)", &engine);
	print_statements(
		"statements per command (SELECT/INSERT/UPDATE/DELETE, cache dropped before cold rows)",
		&statements,
	);
	print_table(
		&format!("http ({HTTP_SAMPLES} requests per scenario, in-memory db, 500 posts)"),
		&http,
	);
	print_scaling(&scaling);
	print_hotspots();

	drop(db);
	clean(&path);
}

/// The structural costs that explain the measurements above.
fn print_hotspots() {
	println!("\nhotspots");
	println!("  1. One `Mutex<SqliteConnection>` in `Db` serialises every request: reads and");
	println!("     writes queue on one connection, so throughput is one core's SQL at best.");
	println!("     Rocket's handlers are synchronous, so each request also parks a worker.");
	println!("  2. Every engine command opens a transaction (`BEGIN`/`COMMIT`): the statement");
	println!("     counts above are the round trips on top of that, 1-3 each after the query");
	println!("     fusion, so the transaction frames are a large share of a short command.");
	println!("  3. `insert_post`/`insert_reply` compute `COALESCE(MAX(seq),0)+1` per insert: a");
	println!("     unique-index seek plus one write per row, so bulk seeding is O(n log n).");
	println!("  4. `ids::allocate` draws a random i64 and probes `EXISTS` until free: one extra");
	println!("     query per publish, and per login for the session id.");
	println!("  5. Timelines filter the whole seq-ordered list until `n` matches survive: the");
	println!("     personal timeline scans ~users/followed-authors posts per answer through a");
	println!("     correlated `EXISTS`, so cost tracks match density, not `n`.");
	println!("  6. `post_view_for`/`post_view_anonymous` LEFT-JOIN `post_likes` and group, so a");
	println!("     cold `read-post` is the fused view (body, likes and `CanReadPost` in one");
	println!("     row) plus the session probe and `replies_of`; the SQL is a fixed string");
	println!("     with bound parameters, not `format!`ed. A live `everyone` tweet answers");
	println!("     from the warm cache instead, which is why the warm rows are one session");
	println!("     probe and nothing else; any write drops the whole map, so a cold row pays");
	println!("     the full database path plus the insertion.");
	println!("  7. The rest is fixed overhead: `rand` for ids, `serde_json` for escaping,");
	println!("     `format!`/`Vec` per body, and a formatted `Date` header on every response.");
}
