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
//! the number of posts (1 000 / 20 000 / 100 000).
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

use std::time::{Duration, Instant};

use diesel::SqliteConnection;

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

fn username(index: usize) -> String {
	format!("u{index:04}")
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

const SCALING_HEADERS: [&str; 4] = ["personal-tl", "private-global", "anon-global", "get-tweet"];

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
		measure(|| expect_post(posts::read_post(db, None, target), "scaling-get-tweet")).median,
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

	let engine = engine_report(&db, &seeded);
	let http = http_report();
	let scaling = scaling_report();

	print_table("engine (warmup + 15 samples, adaptive batch)", &engine);
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
	println!("  2. Every engine command opens a transaction (`BEGIN`/`COMMIT`) and is 2-4 round");
	println!("     trips: `active_user` + the work. `publish` adds `get_account`, and a reply");
	println!("     adds `get_post` + `is_following`: one post costs 3-5 queries plus an id probe.");
	println!("  3. `insert_post`/`insert_reply` compute `COALESCE(MAX(seq),0)+1` per insert: a");
	println!("     unique-index seek plus one write per row, so bulk seeding is O(n log n).");
	println!("  4. `ids::allocate` draws a random i64 and probes `EXISTS` until free: one extra");
	println!("     query per publish, and per login for the session id.");
	println!("  5. Timelines filter the whole seq-ordered list until `n` matches survive: the");
	println!("     personal timeline scans ~users/followed-authors posts per answer through a");
	println!("     correlated `EXISTS`, so cost tracks match density, not `n`.");
	println!("  6. `post_view` LEFT-JOINs `post_likes` and groups; `read_post` runs it plus");
	println!("     `can_read_post` and `replies_of`, i.e. three queries for one tweet, each");
	println!("     rebuilding a `format!`ed SQL string.");
	println!("  7. The rest is fixed overhead: `rand` for ids, `serde_json` for escaping,");
	println!("     `format!`/`Vec` per body, and a formatted `Date` header on every response.");
}
