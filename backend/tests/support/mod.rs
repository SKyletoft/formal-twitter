//! Shared quickcheck infrastructure: a valid, shrinkable `WorldState` and a
//! one-database-per-test harness.
//!
//! `WorldState` mirrors the `World` record of `spec/Twitter.agda:65-109`; it
//! carries no database concerns. Two differences from the record are forced
//! by the model types we may not change:
//!
//! * `PostId`/`SessionId` do not implement `Ord` in `backend/src/model.rs`, so
//!   the id-keyed maps are `HashMap` (both ids are `Hash + Eq`). Anything that
//!   needs a stable order sorts on the raw `i64` first.
//! * `newest-first` in the spec may list only *some* posts (the field is a
//!   `List PostId` with `only-valid-posts`). Our store's
//!   `store::newest_first` lists every row, deleted posts included, so
//!   `newest_first` here is a permutation of `posts` -- that is the invariant
//!   `validate` checks and the one the materialiser round-trips.
//!
//! A `WorldState` is *constructive*: `Arbitrary::arbitrary` only builds worlds
//! that pass `validate`, and the `Arbitrary::shrink` method only yields worlds
//! that pass `validate` and strictly decrease `measure`, so shrinking always
//! terminates.
//!
//! The harness creates **one** `Db` per `#[test]`, outside the quickcheck
//! cases; each case resets it and materialises the generated world. Properties
//! therefore take a `&Db` and a `&WorldState` and never build a database.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::marker::PhantomData;

use diesel::QueryableByName;
use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Nullable, Text};
use formal_twitter::db::Db;
use formal_twitter::model::{DbError, PostId, PostStatus, SessionId, SessionStatus, Visibility};
use formal_twitter::store;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult, Testable};

// ---------------------------------------------------------------------------
// The world.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountState {
	pub password: String,
	pub visibility: Visibility,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PostState {
	pub author: String,
	pub text: String,
	pub visibility: Visibility,
	pub status: PostStatus,
	/// Users who liked the post, sorted, duplicate-free.
	pub likes: Vec<String>,
	/// Direct replies, ascending by `PostId`, duplicate-free.
	pub replies: Vec<PostId>,
	pub parent: Option<PostId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorldState {
	pub accounts: BTreeMap<String, AccountState>,
	/// Only `Active`/`Revoked`; an absent id is `unused`.
	pub sessions: HashMap<SessionId, SessionStatus>,
	pub posts: HashMap<PostId, PostState>,
	pub follows: BTreeSet<(String, String)>,
	/// A permutation of `posts.keys()`: every row, deleted posts included,
	/// newest first.
	pub newest_first: Vec<PostId>,
}

impl WorldState {
	/// The invariants `spec/Twitter.agda:65-109` puts on a `World`, restricted
	/// to the parts a database can hold.
	pub fn validate(&self) -> Result<(), String> {
		if self.newest_first.len() != self.posts.len() {
			return Err(format!(
				"newest_first has {} entries but there are {} posts",
				self.newest_first.len(),
				self.posts.len()
			));
		}
		let mut seen = HashSet::new();
		for pid in &self.newest_first {
			if !seen.insert(*pid) {
				return Err(format!("duplicate post {pid:?} in newest_first"));
			}
			if !self.posts.contains_key(pid) {
				return Err(format!("newest_first names missing post {pid:?}"));
			}
		}
		for (sid, status) in &self.sessions {
			match status {
				SessionStatus::Active(user) => {
					if !self.accounts.contains_key(user) {
						return Err(format!(
							"active session {sid:?} names missing account {user:?}"
						));
					}
				}
				SessionStatus::Revoked => {}
				SessionStatus::Unused => {
					return Err(format!("session {sid:?} is stored as unused"));
				}
			}
		}
		for (pid, post) in &self.posts {
			let mut replies = HashSet::new();
			for child in &post.replies {
				if child == pid {
					return Err(format!("post {pid:?} replies to itself"));
				}
				if !replies.insert(*child) {
					return Err(format!("duplicate reply {child:?} on {pid:?}"));
				}
				let Some(reply) = self.posts.get(child) else {
					return Err(format!("post {pid:?} has missing reply {child:?}"));
				};
				if reply.parent != Some(*pid) {
					return Err(format!(
						"reply {child:?} of {pid:?} has parent {:?}",
						reply.parent
					));
				}
			}
			let mut likes = HashSet::new();
			for user in &post.likes {
				if !likes.insert(user.as_str()) {
					return Err(format!("duplicate like by {user:?} on {pid:?}"));
				}
			}
		}
		Ok(())
	}

	/// The world after `time-passes`: every `active` session becomes
	/// `revoked`, every other component -- and every other session status --
	/// is copied (`timed-out` in `ImplProofs.agda`).
	pub fn timed_out(&self) -> WorldState {
		let mut next = self.clone();
		for status in next.sessions.values_mut() {
			if matches!(status, SessionStatus::Active(_)) {
				*status = SessionStatus::Revoked;
			}
		}
		next
	}

	/// The status of a session in this world; an absent id is `unused`.
	pub fn session_status(&self, sid: SessionId) -> SessionStatus {
		self.sessions
			.get(&sid)
			.cloned()
			.unwrap_or(SessionStatus::Unused)
	}

	/// Ids of the sessions that are `active`.
	pub fn active_sessions(&self) -> Vec<SessionId> {
		let mut ids: Vec<SessionId> = self
			.sessions
			.iter()
			.filter(|(_, status)| matches!(status, SessionStatus::Active(_)))
			.map(|(sid, _)| *sid)
			.collect();
		ids.sort_unstable_by_key(|sid| sid.0);
		ids
	}

	/// A total order on the world used to bound shrinking: any shrink
	/// candidate must be strictly smaller.
	fn measure(&self) -> usize {
		self.accounts.len()
			+ self.sessions.len()
			+ self.posts.len()
			+ self.follows.len()
			+ self
				.accounts
				.values()
				.map(|account| account.password.chars().count())
				.sum::<usize>()
			+ self
				.posts
				.values()
				.map(|post| post.text.chars().count() + post.likes.len() + post.replies.len())
				.sum::<usize>()
	}

	/// `self` with `root` and everything that hangs off it removed, keeping
	/// `replies`, `newest_first` and the parent links consistent.
	fn without_post_subtree(&self, root: PostId) -> WorldState {
		let mut removed: HashSet<PostId> = HashSet::new();
		if !self.posts.contains_key(&root) {
			return self.clone();
		}
		removed.insert(root);
		loop {
			let mut changed = false;
			let snapshot: Vec<PostId> = removed.iter().copied().collect();
			for pid in snapshot {
				if let Some(post) = self.posts.get(&pid) {
					for child in &post.replies {
						changed |= removed.insert(*child);
					}
				}
			}
			for (pid, post) in &self.posts {
				if removed.contains(pid) {
					continue;
				}
				if let Some(parent) = post.parent
					&& removed.contains(&parent)
				{
					changed |= removed.insert(*pid);
				}
			}
			if !changed {
				break;
			}
		}
		let mut next = self.clone();
		next.posts.retain(|pid, _| !removed.contains(pid));
		next.newest_first.retain(|pid| !removed.contains(pid));
		for post in next.posts.values_mut() {
			post.replies.retain(|pid| !removed.contains(pid));
		}
		next
	}

	fn has_active_session(&self, username: &str) -> bool {
		self.sessions
			.values()
			.any(|status| matches!(status, SessionStatus::Active(user) if user == username))
	}

	/// `self` with the last character of `password` dropped.
	fn truncated_password(&self, username: &str) -> WorldState {
		let mut next = self.clone();
		if let Some(account) = next.accounts.get_mut(username) {
			let _ = account.password.pop();
		}
		next
	}

	/// `self` with the last character of a post's text dropped.
	fn truncated_text(&self, pid: PostId) -> WorldState {
		let mut next = self.clone();
		if let Some(post) = next.posts.get_mut(&pid) {
			let _ = post.text.pop();
		}
		next
	}
}

// ---------------------------------------------------------------------------
// Generation.
// ---------------------------------------------------------------------------

/// Line-safe, `|`-free so the tests may also render rows as text.
const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&* ";

fn pick(g: &mut Gen, bound: usize) -> usize {
	if bound == 0 {
		0
	} else {
		usize::arbitrary(g) % bound
	}
}

fn flag(g: &mut Gen) -> bool {
	usize::arbitrary(g) % 2 == 0
}

fn string(g: &mut Gen, min_len: usize, max_len: usize) -> String {
	let len = min_len + pick(g, max_len - min_len + 1);
	let mut out = String::with_capacity(len);
	for _ in 0..len {
		out.push(ALPHABET[pick(g, ALPHABET.len())] as char);
	}
	out
}

fn visibility(g: &mut Gen) -> Visibility {
	if flag(g) {
		Visibility::Everyone
	} else {
		Visibility::FollowersOnly
	}
}

fn distinct_usernames(g: &mut Gen, count: usize) -> Vec<String> {
	let mut names: Vec<String> = Vec::new();
	for _ in 0..200 {
		if names.len() == count {
			break;
		}
		let candidate = string(g, 1, 8);
		if !names.contains(&candidate) {
			names.push(candidate);
		}
	}
	let mut filler = 0;
	while names.len() < count {
		let candidate = format!("user{filler}");
		if !names.contains(&candidate) {
			names.push(candidate);
		}
		filler += 1;
	}
	names
}

fn shuffle(g: &mut Gen, values: &mut [PostId]) {
	for i in (1..values.len()).rev() {
		let j = pick(g, i + 1);
		values.swap(i, j);
	}
}

impl Arbitrary for WorldState {
	fn arbitrary(g: &mut Gen) -> Self {
		// 0-3 distinct accounts.
		let n_accounts = pick(g, 4);
		let names = distinct_usernames(g, n_accounts);
		let accounts: BTreeMap<String, AccountState> = names
			.iter()
			.map(|name| {
				(
					name.clone(),
					AccountState {
						password: string(g, 0, 16),
						visibility: visibility(g),
					},
				)
			})
			.collect();

		// 0-4 sessions; a fifth of the worlds are empty and a quarter are
		// revoked-only, so those shapes are covered deliberately.
		let n_sessions = if pick(g, 5) == 0 { 0 } else { pick(g, 5) };
		let revoked_only = pick(g, 4) == 0;
		let base = pick(g, 10) as i64;
		let mut sessions = HashMap::new();
		for i in 0..n_sessions {
			let sid = SessionId(base + 1 + i as i64);
			let status = if !revoked_only && !names.is_empty() && flag(g) {
				SessionStatus::Active(names[pick(g, names.len())].clone())
			} else {
				SessionStatus::Revoked
			};
			sessions.insert(sid, status);
		}

		// 0-5 posts with increasing ids; a post may answer an earlier one.
		let n_posts = pick(g, 6);
		let mut posts: HashMap<PostId, PostState> = HashMap::new();
		for index in 0..n_posts {
			let id = PostId(1 + index as i64);
			let author = if names.is_empty() {
				string(g, 1, 8)
			} else {
				names[pick(g, names.len())].clone()
			};
			let parent = if index > 0 && pick(g, 5) < 2 {
				Some(PostId(1 + pick(g, index) as i64))
			} else {
				None
			};
			let mut likes: Vec<String> =
				names.iter().filter(|_| pick(g, 3) == 0).cloned().collect();
			likes.sort();
			let status = if pick(g, 4) == 0 {
				PostStatus::Deleted
			} else {
				PostStatus::Live
			};
			posts.insert(
				id,
				PostState {
					author,
					text: string(g, 0, 16),
					visibility: visibility(g),
					status,
					likes,
					replies: Vec::new(),
					parent,
				},
			);
			if let Some(parent) = parent
				&& let Some(post) = posts.get_mut(&parent)
			{
				post.replies.push(id);
			}
		}

		// `newest_first` is a permutation of every post id: creation order,
		// reverse creation order, or a random shuffle.
		let mut newest_first: Vec<PostId> = posts.keys().copied().collect();
		newest_first.sort_unstable_by_key(|pid| pid.0);
		match pick(g, 3) {
			0 => {}
			1 => newest_first.reverse(),
			_ => shuffle(g, &mut newest_first),
		}

		let mut follows = BTreeSet::new();
		for follower in &names {
			for followee in &names {
				if pick(g, 3) == 0 {
					follows.insert((follower.clone(), followee.clone()));
				}
			}
		}

		let world = WorldState {
			accounts,
			sessions,
			posts,
			follows,
			newest_first,
		};
		debug_assert_eq!(world.validate(), Ok(()), "generated an invalid world");
		world
	}

	/// Validity-preserving shrinking. Every candidate passes `validate` and
	/// strictly decreases `measure`, so the shrinks terminate. The candidate
	/// list is linear in the size of the world, never exponential.
	fn shrink(&self) -> Box<dyn Iterator<Item = WorldState>> {
		let mut candidates: Vec<WorldState> = Vec::new();

		let mut post_ids: Vec<PostId> = self.posts.keys().copied().collect();
		post_ids.sort_unstable_by_key(|pid| pid.0);

		// Drop one post, with everything that hangs off it.
		for pid in &post_ids {
			candidates.push(self.without_post_subtree(*pid));
		}

		// Drop one like.
		for pid in &post_ids {
			if let Some(post) = self.posts.get(pid) {
				for index in 0..post.likes.len() {
					let mut next = self.clone();
					if let Some(post) = next.posts.get_mut(pid) {
						post.likes.remove(index);
					}
					candidates.push(next);
				}
			}
		}

		// Drop one follow.
		for pair in &self.follows {
			let mut next = self.clone();
			next.follows.remove(pair);
			candidates.push(next);
		}

		// Drop one session; the account it named stays.
		let mut session_ids: Vec<SessionId> = self.sessions.keys().copied().collect();
		session_ids.sort_unstable_by_key(|sid| sid.0);
		for sid in &session_ids {
			let mut next = self.clone();
			next.sessions.remove(sid);
			candidates.push(next);
		}

		// Drop one account, but only when no active session still names it.
		for name in self.accounts.keys() {
			if self.has_active_session(name) {
				continue;
			}
			let mut next = self.clone();
			next.accounts.remove(name);
			candidates.push(next);
		}

		// Truncate one password or one post text by one character.
		for (name, account) in &self.accounts {
			if !account.password.is_empty() {
				candidates.push(self.truncated_password(name));
			}
		}
		for pid in &post_ids {
			if let Some(post) = self.posts.get(pid)
				&& !post.text.is_empty()
			{
				candidates.push(self.truncated_text(*pid));
			}
		}

		let current = self.measure();
		Box::new(
			candidates
				.into_iter()
				.filter(move |world| world.measure() < current && world.validate().is_ok()),
		)
	}
}

// ---------------------------------------------------------------------------
// Materialisation: world -> database (one transaction), database -> world.
// ---------------------------------------------------------------------------

fn visibility_str(visibility: Visibility) -> &'static str {
	match visibility {
		Visibility::Everyone => "everyone",
		Visibility::FollowersOnly => "followers-only",
	}
}

fn visibility_of(value: &str) -> Visibility {
	match value {
		"everyone" => Visibility::Everyone,
		"followers-only" => Visibility::FollowersOnly,
		other => panic!("invalid visibility in the database: {other}"),
	}
}

fn post_status_of(value: &str) -> PostStatus {
	match value {
		"live" => PostStatus::Live,
		"deleted" => PostStatus::Deleted,
		other => panic!("invalid post status in the database: {other}"),
	}
}

/// Empty every table the tests write. One transaction, no foreign keys.
pub fn reset(db: &Db) {
	db.write(|conn| {
		for table in ["post_likes", "follows", "posts", "sessions", "accounts"] {
			diesel::sql_query(format!("DELETE FROM {table}")).execute(conn)?;
		}
		Ok(())
	})
	.expect("reset the database");
}

/// Write `world` into an empty database in one transaction.
///
/// `posts.seq` is assigned explicitly (`len - index`) so that
/// `ORDER BY seq DESC` reproduces `newest_first` exactly.
pub fn materialise(db: &Db, world: &WorldState) {
	world.validate().expect("materialise a valid world");
	db.write(|conn| {
		for (name, account) in &world.accounts {
			diesel::sql_query(
				"INSERT INTO accounts (username, password, default_visibility) VALUES (?, ?, ?)",
			)
			.bind::<Text, _>(name)
			.bind::<Text, _>(&account.password)
			.bind::<Text, _>(visibility_str(account.visibility))
			.execute(conn)?;
		}
		for (sid, status) in &world.sessions {
			let (status, username) = match status {
				SessionStatus::Active(user) => ("active", user.as_str()),
				SessionStatus::Revoked => ("revoked", ""),
				SessionStatus::Unused => panic!("unused sessions are not stored"),
			};
			diesel::sql_query("INSERT INTO sessions (id, status, username) VALUES (?, ?, ?)")
				.bind::<BigInt, _>(sid.0)
				.bind::<Text, _>(status)
				.bind::<Text, _>(username)
				.execute(conn)?;
		}
		let count = world.newest_first.len();
		for (index, pid) in world.newest_first.iter().enumerate() {
			let post = world
				.posts
				.get(pid)
				.expect("newest_first names an existing post");
			diesel::sql_query(
				"INSERT INTO posts (id, seq, author, text, visibility, status, parent) \
				VALUES (?, ?, ?, ?, ?, ?, ?)",
			)
			.bind::<BigInt, _>(pid.0)
			.bind::<BigInt, _>((count - index) as i64)
			.bind::<Text, _>(&post.author)
			.bind::<Text, _>(&post.text)
			.bind::<Text, _>(visibility_str(post.visibility))
			.bind::<Text, _>(match post.status {
				PostStatus::Live => "live",
				PostStatus::Deleted => "deleted",
			})
			.bind::<Nullable<BigInt>, _>(post.parent.map(|parent| parent.0))
			.execute(conn)?;
			for user in &post.likes {
				diesel::sql_query("INSERT INTO post_likes (pid, user) VALUES (?, ?)")
					.bind::<BigInt, _>(pid.0)
					.bind::<Text, _>(user)
					.execute(conn)?;
			}
		}
		for (follower, followee) in &world.follows {
			diesel::sql_query("INSERT INTO follows (follower, followee) VALUES (?, ?)")
				.bind::<Text, _>(follower)
				.bind::<Text, _>(followee)
				.execute(conn)?;
		}
		Ok(())
	})
	.expect("materialise the world");
}

#[derive(QueryableByName)]
struct AccountRow {
	#[diesel(sql_type = Text)]
	username: String,
	#[diesel(sql_type = Text)]
	password: String,
	#[diesel(sql_type = Text)]
	default_visibility: String,
}

#[derive(QueryableByName)]
struct SessionRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Text)]
	username: String,
}

#[derive(QueryableByName)]
struct PostRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
	#[diesel(sql_type = Text)]
	author: String,
	#[diesel(sql_type = Text)]
	text: String,
	#[diesel(sql_type = Text)]
	visibility: String,
	#[diesel(sql_type = Text)]
	status: String,
	#[diesel(sql_type = Nullable<BigInt>)]
	parent: Option<i64>,
}

#[derive(QueryableByName)]
struct LikeRow {
	#[diesel(sql_type = BigInt)]
	pid: i64,
	#[diesel(sql_type = Text)]
	user: String,
}

#[derive(QueryableByName)]
struct FollowRow {
	#[diesel(sql_type = Text)]
	follower: String,
	#[diesel(sql_type = Text)]
	followee: String,
}

#[derive(QueryableByName)]
struct ReplyRow {
	#[diesel(sql_type = BigInt)]
	id: i64,
	#[diesel(sql_type = Nullable<BigInt>)]
	parent: Option<i64>,
}

/// Read the whole database back as a `WorldState`.
///
/// Replies are derived from the `parent` column (the database has no replies
/// table), ordered by `id`; likes are ordered by `user`. The generator and the
/// shrinker keep both orders, so `from_db(materialise(w)) == w` for every
/// generated world -- asserted by the harness on every case.
pub fn from_db(db: &Db) -> WorldState {
	db.read(|conn| -> Result<WorldState, DbError> {
		let account_rows: Vec<AccountRow> = diesel::sql_query(
			"SELECT username, password, default_visibility FROM accounts ORDER BY username",
		)
		.load(conn)?;
		let accounts: BTreeMap<String, AccountState> = account_rows
			.into_iter()
			.map(|row| {
				(
					row.username,
					AccountState {
						password: row.password,
						visibility: visibility_of(&row.default_visibility),
					},
				)
			})
			.collect();

		let session_rows: Vec<SessionRow> =
			diesel::sql_query("SELECT id, status, username FROM sessions ORDER BY id")
				.load(conn)?;
		let mut sessions = HashMap::new();
		for row in session_rows {
			let status = match row.status.as_str() {
				"active" => SessionStatus::Active(row.username),
				"revoked" => SessionStatus::Revoked,
				other => panic!("invalid session status in the database: {other}"),
			};
			sessions.insert(SessionId(row.id), status);
		}

		let post_rows: Vec<PostRow> = diesel::sql_query(
			"SELECT id, author, text, visibility, status, parent FROM posts ORDER BY id",
		)
		.load(conn)?;
		let mut posts: HashMap<PostId, PostState> = HashMap::new();
		for row in post_rows {
			posts.insert(
				PostId(row.id),
				PostState {
					author: row.author,
					text: row.text,
					visibility: visibility_of(&row.visibility),
					status: post_status_of(&row.status),
					likes: Vec::new(),
					replies: Vec::new(),
					parent: row.parent.map(PostId),
				},
			);
		}

		let like_rows: Vec<LikeRow> =
			diesel::sql_query("SELECT pid, user FROM post_likes ORDER BY pid, user").load(conn)?;
		for row in like_rows {
			posts
				.get_mut(&PostId(row.pid))
				.expect("a like names an existing post")
				.likes
				.push(row.user);
		}

		let reply_rows: Vec<ReplyRow> = diesel::sql_query(
			"SELECT id, parent FROM posts WHERE parent IS NOT NULL ORDER BY parent, id",
		)
		.load(conn)?;
		for row in reply_rows {
			let parent = row.parent.expect("filtered by parent IS NOT NULL");
			posts
				.get_mut(&PostId(parent))
				.expect("a reply names an existing parent")
				.replies
				.push(PostId(row.id));
		}

		let follow_rows: Vec<FollowRow> =
			diesel::sql_query("SELECT follower, followee FROM follows").load(conn)?;
		let follows: BTreeSet<(String, String)> = follow_rows
			.into_iter()
			.map(|row| (row.follower, row.followee))
			.collect();

		let newest_first = store::newest_first(conn, u32::MAX)?;

		Ok(WorldState {
			accounts,
			sessions,
			posts,
			follows,
			newest_first,
		})
	})
	.expect("read the world back")
}

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

/// One database per test, shared by every case; each case resets it and
/// materialises the generated world, then checks the round-trip before running
/// the property. `QuickCheck::new()` honours `QUICKCHECK_TESTS` (default 100).
///
/// The property rides in a small `Testable` adapter: quickcheck 1.1 only
/// implements `Testable` for `fn` pointers, so a capturing closure cannot be
/// handed to `QuickCheck` directly. The adapter also shrinks through the
/// validity-preserving `WorldState::shrink` and reports the minimal failing
/// world in the panic message.
pub fn check<A>(prop: impl Fn(&Db, &WorldState, A) -> TestResult + 'static)
where
	A: Arbitrary + std::fmt::Debug + 'static,
{
	let property = WorldProperty {
		db: Db::in_memory().expect("create the in-memory database"),
		prop,
		marker: PhantomData,
	};
	QuickCheck::new().quickcheck(property);
}

struct WorldProperty<F, A> {
	db: Db,
	prop: F,
	marker: PhantomData<fn() -> A>,
}

impl<F, A> WorldProperty<F, A>
where
	A: Arbitrary + std::fmt::Debug + 'static,
	F: Fn(&Db, &WorldState, A) -> TestResult,
{
	/// Reset the shared database, materialise `world`, verify the round-trip
	/// and run the property. No database is created here.
	fn run(&self, world: &WorldState, arg: &A) -> TestResult {
		reset(&self.db);
		materialise(&self.db, world);
		assert_eq!(
			from_db(&self.db),
			*world,
			"the materialiser must round-trip every generated world"
		);
		(self.prop)(&self.db, world, arg.clone())
	}

	/// Greedily shrink the world, then the argument, while the property still
	/// fails. Every step strictly decreases `WorldState::measure` or the
	/// argument's own measure, so this terminates.
	fn minimal_failure(&self, world: &WorldState, arg: &A) -> (WorldState, A) {
		let mut world = world.clone();
		let mut arg = arg.clone();
		loop {
			if let Some(smaller) = world
				.shrink()
				.find(|candidate| self.run(candidate, &arg).is_failure())
			{
				world = smaller;
				continue;
			}
			if let Some(smaller) = arg
				.shrink()
				.find(|candidate| self.run(&world, candidate).is_failure())
			{
				arg = smaller;
				continue;
			}
			return (world, arg);
		}
	}
}

impl<F, A> Testable for WorldProperty<F, A>
where
	A: Arbitrary + std::fmt::Debug + 'static,
	F: Fn(&Db, &WorldState, A) -> TestResult + 'static,
{
	fn result(&self, g: &mut Gen) -> TestResult {
		let (world, arg): (WorldState, A) = Arbitrary::arbitrary(g);
		let first = self.run(&world, &arg);
		if !first.is_failure() {
			return first;
		}
		let (world, arg) = self.minimal_failure(&world, &arg);
		TestResult::error(format!(
			"property failed; minimal world: {world:?}\nminimal argument: {arg:?}"
		))
	}
}
