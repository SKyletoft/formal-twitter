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
//! * `Post.replies` is stored in `seq` order, not id order: the materialiser
//!   gives index `i` of `newest_first` the seq `len - i`, and the engine
//!   answers `read-post` with `store::replies_of`, which is
//!   `ORDER BY seq DESC` (`backend/src/store.rs:388`). A reply list is
//!   therefore its children sorted by *ascending rank* in `newest_first`
//!   (rank 0 = newest = highest seq), and `from_db` reads replies the same
//!   way. `likes` is canonical too: lexicographic by user, duplicate-free
//!   (`from_db` reads `ORDER BY pid, user`). `validate` requires both orders,
//!   so a world that names the right children in the wrong order is rejected
//!   rather than silently round-tripped into a different one.
//! * `replies` must be *exactly* the set of children whose `parent` names the
//!   post -- no missing child, no extra entry, no duplicate -- which closes
//!   the "parent set but child not listed in `replies`" gap.
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
	/// Users who liked the post, sorted lexicographically, duplicate-free.
	pub likes: Vec<String>,
	/// Direct replies in `seq` order (newest first), duplicate-free: exactly
	/// the children of this post, sorted by ascending rank in `newest_first`.
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
		let rank = self.rank_map();
		for (pid, post) in &self.posts {
			if post.parent == Some(*pid) {
				return Err(format!("post {pid:?} replies to itself"));
			}
			// Exactly the children of `pid`, in `seq` order: rank 0 in
			// `newest_first` gets the highest seq, so sorting by ascending
			// rank reproduces `store::replies_of`'s `ORDER BY seq DESC`.
			let mut expected: Vec<PostId> = self
				.posts
				.iter()
				.filter(|(_, child)| child.parent == Some(*pid))
				.map(|(child, _)| *child)
				.collect();
			expected.sort_unstable_by_key(|child| rank[child]);
			if post.replies != expected {
				return Err(format!(
					"post {pid:?} lists replies {:?}, but its children in seq order are {expected:?}",
					post.replies
				));
			}
			for (index, user) in post.likes.iter().enumerate() {
				if index > 0 && post.likes[index - 1] >= *user {
					return Err(format!(
						"likes of {pid:?} are not strictly lexicographic: {:?}",
						post.likes
					));
				}
			}
		}
		Ok(())
	}

	/// `PostId ->` its index in `newest_first`, i.e. its `len - seq`. Every
	/// post has a rank once `newest_first` has passed the permutation check.
	fn rank_map(&self) -> HashMap<PostId, usize> {
		self.newest_first
			.iter()
			.enumerate()
			.map(|(rank, pid)| (*pid, rank))
			.collect()
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

	/// `self` with every session dropped and nothing else touched. Already
	/// timed out (`timed_out`), since a session-free world has no `active`
	/// session left to revoke.
	pub fn without_sessions(&self) -> WorldState {
		let mut next = self.clone();
		next.sessions.clear();
		next
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

		// `replies` is stored in `seq` order, so reorder every reply list to
		// ascending rank in the `newest_first` just chosen (`validate` requires
		// that order and `store::replies_of` answers `ORDER BY seq DESC`).
		let rank: HashMap<PostId, usize> = newest_first
			.iter()
			.enumerate()
			.map(|(rank, pid)| (*pid, rank))
			.collect();
		for post in posts.values_mut() {
			post.replies.sort_unstable_by_key(|child| rank[child]);
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
/// table), ordered by `parent, seq DESC` -- the same order the engine serves
/// through `store::replies_of`; likes are ordered lexicographically by `user`.
/// The generator and the shrinker keep both orders, so
/// `from_db(materialise(w)) == w` for every generated world -- asserted by the
/// harness on every case.
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
			"SELECT id, parent FROM posts WHERE parent IS NOT NULL ORDER BY parent, seq DESC",
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
/// world together with the failure's own message.
///
/// quickcheck 1.1 calls `Testable::result` without `catch_unwind`, and Q1b
/// properties assert, so a failing assertion would unwind straight out of the
/// harness: no `TestResult` comes back, `first.is_failure()` is never reached
/// and nothing shrinks. `WorldProperty::run` therefore wraps the case in
/// `catch_unwind` and turns a panic into a failing `Outcome`, so panicking
/// properties shrink like ordinary failures.
///
/// A failure is an [`Outcome`], not a bare `TestResult`, because the harness
/// has to tell two very different bugs apart and keep the message of the first:
///
/// * a **property** failure -- the assertion the property author wrote;
/// * a **harness** failure -- `materialise` or the round-trip check panicked,
///   i.e. a bug in this module, never in the property.
///
/// Only the property's message is worth appending to the minimal-world report;
/// a harness panic is reported under its own label so it cannot be misread as a
/// failing property.
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

/// The human-readable half of a caught panic payload. `assert!` and
/// `panic!` carry a `&str` or a `String`; anything else is described
/// generically.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
	if let Some(message) = payload.downcast_ref::<&str>() {
		(*message).to_string()
	} else if let Some(message) = payload.downcast_ref::<String>() {
		message.clone()
	} else {
		"panicked with a non-string payload".to_string()
	}
}

/// What one harness case did.
///
/// The variant is the label of the failure: only `Property*` is a property
/// bug, `HarnessPanic` is a bug in this module.
enum Outcome {
	/// The case did not fail; the `TestResult` is passed through unchanged
	/// (it may be a discard).
	NotFailed(TestResult),
	/// The property returned a failing `TestResult` without panicking.
	/// quickcheck keeps `TestResult`'s fields private, so its message is not
	/// retrievable here; a panicking `assert!` is the usual shape anyway.
	PropertyFailed,
	/// The property panicked (an `assert!` or `panic!`): the assertion text.
	PropertyPanic(String),
	/// `materialise` or the round-trip check panicked: the harness is broken.
	HarnessPanic(String),
}

impl Outcome {
	fn is_failure(&self) -> bool {
		!matches!(self, Outcome::NotFailed(_))
	}
}

/// A failing case: which side failed and the message to report.
///
/// The harness folds every failing probe of the shrink loop into one of these.
/// A harness panic always wins (it makes the whole shrink meaningless);
/// otherwise the *first* message that carried one is kept, so the original
/// assertion text survives probes that fail without a message.
struct Failure {
	harness: bool,
	message: Option<String>,
}

impl Failure {
	fn of(outcome: &Outcome) -> Self {
		let mut failure = Self {
			harness: false,
			message: None,
		};
		failure.absorb(outcome);
		failure
	}

	fn absorb(&mut self, outcome: &Outcome) {
		match outcome {
			Outcome::HarnessPanic(message) => {
				self.harness = true;
				self.message = Some(message.clone());
			}
			Outcome::PropertyPanic(message) => {
				if self.message.is_none() {
					self.message = Some(message.clone());
				}
			}
			Outcome::PropertyFailed => {}
			Outcome::NotFailed(_) => {}
		}
	}

	/// The failure report: the message first, then the minimal world, so a
	/// shrunken failure still says what broke.
	fn report(&self, world: &WorldState, arg: &dyn std::fmt::Debug) -> String {
		let message = self
			.message
			.as_deref()
			.unwrap_or("no assertion message (the property returned a failing TestResult)");
		if self.harness {
			format!(
				"harness error (materialiser or round-trip check panicked, \
				not a property failure): {message}; world: {world:?}\nargument: {arg:?}"
			)
		} else {
			format!(
				"property failed: {message}; minimal world: {world:?}\nminimal argument: {arg:?}"
			)
		}
	}
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
	///
	/// The two halves are contained separately, so a panic can be attributed:
	/// a panic while setting up is a harness bug, a panic in the property is
	/// the property's own assertion.
	fn run(&self, world: &WorldState, arg: &A) -> Outcome {
		let prepared = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			reset(&self.db);
			materialise(&self.db, world);
			assert_eq!(
				from_db(&self.db),
				*world,
				"the materialiser must round-trip every generated world"
			);
		}));
		if let Err(payload) = prepared {
			return Outcome::HarnessPanic(panic_message(payload.as_ref()));
		}
		match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			(self.prop)(&self.db, world, arg.clone())
		})) {
			Ok(result) if result.is_failure() => Outcome::PropertyFailed,
			Ok(result) => Outcome::NotFailed(result),
			Err(payload) => Outcome::PropertyPanic(panic_message(payload.as_ref())),
		}
	}

	/// Greedily shrink the world, then the argument, while the case still
	/// fails. Every step strictly decreases `WorldState::measure` or the
	/// argument's own measure, so this terminates. Returns the minimal failing
	/// case and the folded [`Failure`] (original message included).
	fn minimal_failure(&self, world: &WorldState, arg: &A) -> (WorldState, A, Failure) {
		let mut world = world.clone();
		let mut arg = arg.clone();
		let mut failure = Failure::of(&self.run(&world, &arg));
		loop {
			let mut shrunk = None;
			for candidate in world.shrink() {
				let outcome = self.run(&candidate, &arg);
				if outcome.is_failure() {
					failure.absorb(&outcome);
					shrunk = Some(candidate);
					break;
				}
			}
			if let Some(smaller) = shrunk {
				world = smaller;
				continue;
			}
			let mut shrunk = None;
			for candidate in arg.shrink() {
				let outcome = self.run(&world, &candidate);
				if outcome.is_failure() {
					failure.absorb(&outcome);
					shrunk = Some(candidate);
					break;
				}
			}
			if let Some(smaller) = shrunk {
				arg = smaller;
				continue;
			}
			return (world, arg, failure);
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
		match self.run(&world, &arg) {
			Outcome::NotFailed(result) => result,
			_ => {
				let (world, arg, failure) = self.minimal_failure(&world, &arg);
				TestResult::error(failure.report(&world, &arg))
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Regression: reply order.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
	use super::*;

	fn post(author: &str, parent: Option<PostId>) -> PostState {
		PostState {
			author: author.to_string(),
			text: "text".to_string(),
			visibility: Visibility::Everyone,
			status: PostStatus::Live,
			likes: Vec::new(),
			replies: Vec::new(),
			parent,
		}
	}

	/// The Q1a blocker: `Post.replies` is `seq`-descending, *not* id order, so
	/// a parent with several children whose `newest_first` is not id-sorted
	/// must list its children in rank order, round-trip through the
	/// materialiser, and agree with `store::replies_of` (the order the engine
	/// serves). `validate` must also reject the id-ordered (wrong) list.
	#[test]
	fn replies_are_seq_ordered_and_match_the_store() {
		let mut root = post("ada", None);
		// newest_first is [2, 4, 1, 3], so ranks (and seqs) are post 2 at
		// rank 0 (seq 4), post 4 at rank 1 (seq 3), post 1 at rank 2 (seq 2)
		// and post 3 at rank 3 (seq 1). The children of post 1 are therefore
		// 2, 4 and 3, and seq-descending order is [2, 4, 3].
		root.replies = vec![PostId(2), PostId(4), PostId(3)];
		let world = WorldState {
			accounts: BTreeMap::from([(
				"ada".to_string(),
				AccountState {
					password: "pw".to_string(),
					visibility: Visibility::Everyone,
				},
			)]),
			sessions: HashMap::new(),
			posts: std::iter::once((PostId(1), root))
				.chain(
					[2, 3, 4]
						.into_iter()
						.map(|id| (PostId(id), post("ada", Some(PostId(1))))),
				)
				.collect(),
			follows: BTreeSet::new(),
			newest_first: vec![PostId(2), PostId(4), PostId(1), PostId(3)],
		};
		world.validate().expect("seq-ordered replies are valid");

		let db = Db::in_memory().expect("create the in-memory database");
		reset(&db);
		materialise(&db, &world);
		assert_eq!(from_db(&db), world, "the world round-trips");
		let replies = db
			.read(|conn| store::replies_of(conn, PostId(1)))
			.expect("read the replies");
		assert_eq!(replies, vec![PostId(2), PostId(4), PostId(3)]);
		assert_eq!(
			replies,
			world.posts[&PostId(1)].replies,
			"the engine's reply order is the world's reply order"
		);

		// Id order (or any other order) is not the stored order: `validate`
		// must say so instead of letting the round-trip paper over it.
		let mut id_ordered = world.clone();
		id_ordered
			.posts
			.get_mut(&PostId(1))
			.expect("the root exists")
			.replies = vec![PostId(2), PostId(3), PostId(4)];
		assert!(
			id_ordered.validate().is_err(),
			"replies out of seq order must be rejected"
		);

		// And a parent whose child forgot to list it is caught as well.
		let mut orphan = world.clone();
		orphan
			.posts
			.get_mut(&PostId(1))
			.expect("the root exists")
			.replies = vec![PostId(2), PostId(4)];
		assert!(
			orphan.validate().is_err(),
			"a missing reply must be rejected"
		);
	}
}

// ---------------------------------------------------------------------------
// Harness regression (Q1): a property must fail *through* the harness.
//
// quickcheck 1.1 hands `Testable::result` no `catch_unwind`, and every Q1b
// property asserts, so before the fix a failing assertion unwound out of the
// harness: `first.is_failure()` and `minimal_failure` never ran, so nothing
// shrank and no minimal world was reported. `WorldProperty::run` now catches
// the panic and reports a failing `TestResult`, which makes both reachable.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod harness_tests {
	use super::*;

	type Unit = ();

	fn harness<F>(prop: F) -> WorldProperty<F, Unit>
	where
		F: Fn(&Db, &WorldState, Unit) -> TestResult + 'static,
	{
		WorldProperty {
			db: Db::in_memory().expect("create the in-memory database"),
			prop,
			marker: PhantomData,
		}
	}

	/// A *generated* world with at least `min_posts` posts. `Gen` is seeded
	/// explicitly, so the same seed always regenerates the same world and the
	/// tests are deterministic.
	fn generated_world(min_posts: usize) -> (u64, WorldState) {
		for seed in 0..400 {
			let mut g = Gen::from_size_and_seed(6, seed);
			let world = WorldState::arbitrary(&mut g);
			if world.posts.len() >= min_posts {
				return (seed, world);
			}
		}
		panic!("the generator never produced {min_posts} posts");
	}

	fn payload_message(payload: Box<dyn std::any::Any + Send>) -> String {
		if let Some(message) = payload.downcast_ref::<String>() {
			message.clone()
		} else if let Some(message) = payload.downcast_ref::<&str>() {
			(*message).to_string()
		} else {
			panic!("unexpected panic payload");
		}
	}

	/// A property that panics on any non-empty world (the Q1b `assert!` shape).
	fn posts_must_be_empty(_db: &Db, world: &WorldState, _: Unit) -> TestResult {
		assert!(world.posts.is_empty(), "expected a world without posts");
		TestResult::passed()
	}

	/// (a) Panic containment: the assertion panic is turned into a failing
	/// `TestResult` instead of unwinding out of `run`/`result`, and QuickCheck
	/// reports the harness's minimal-world message rather than the raw panic.
	#[test]
	fn a_panicking_property_is_contained() {
		// Through `run` on a world we know is non-empty.
		let property = harness(posts_must_be_empty);
		let (_, world) = generated_world(1);
		let first =
			std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| property.run(&world, &())))
				.expect("the property panic must not leave `run`");
		assert!(first.is_failure(), "a panic is reported as a failure");

		// Through `Testable::result`: same seed, same world, panic contained
		// and reported as a failure of the case.
		let (seed, _) = generated_world(1);
		let mut g = Gen::from_size_and_seed(6, seed);
		let result =
			std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| property.result(&mut g)))
				.expect("the property panic must not leave `result`");
		assert!(result.is_failure());

		// Through `QuickCheck`: the only panic that escapes is quickcheck's
		// own failure report, carrying the shrunken world. The property panics
		// unconditionally, so the case fails whatever world is generated.
		let property = harness(|_db: &Db, _world: &WorldState, _: Unit| -> TestResult {
			panic!("boom");
		});
		let message = payload_message(
			std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
				QuickCheck::new().tests(1).quickcheck(property);
			}))
			.expect_err("quickcheck reports the failure"),
		);
		assert!(
			message.contains("property failed: boom; minimal world:"),
			"quickcheck must report the assertion text and the minimal world, got: {message}"
		);
	}

	/// (a) Message fidelity: the report of a *shrunk* failure still carries the
	/// original assertion text, not just the minimal world -- otherwise a
	/// failing property says where it broke but never what it expected.
	///
	/// The property asserts a fixed, always-false equality so the case fails on
	/// *every* generated world: the point is the report, not the world, and
	/// `QUICKCHECK_TESTS` only changes how many cases QuickCheck runs.
	#[test]
	fn a_minimal_world_report_keeps_the_assertion_text() {
		let property = harness(|_db: &Db, world: &WorldState, _: Unit| -> TestResult {
			assert_eq!(
				world.posts.len(),
				usize::MAX,
				"expected a world without posts"
			);
			TestResult::passed()
		});
		let message = payload_message(
			std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
				QuickCheck::new().tests(1).quickcheck(property);
			}))
			.expect_err("quickcheck reports the failure"),
		);
		assert!(
			message.contains("expected a world without posts"),
			"the assertion text is lost, got: {message}"
		);
		assert!(
			message.contains("; minimal world: "),
			"the minimal world is missing, got: {message}"
		);
	}

	/// (a) Attribution: a world the materialiser cannot round-trip is a harness
	/// bug, labelled as such, never reported as a failing property.
	#[test]
	fn a_broken_round_trip_is_labelled_a_harness_error() {
		let property = harness(|_db: &Db, _world: &WorldState, _: Unit| -> TestResult {
			panic!("the property must not run on a world that does not round-trip");
		});
		let (_, mut world) = generated_world(2);
		// No longer a permutation of `posts`, so `validate` refuses it inside
		// `materialise`: a harness bug, not a property one.
		world.newest_first.pop();
		assert!(matches!(
			property.run(&world, &()),
			Outcome::HarnessPanic(_)
		));

		let (_, _, failure) = property.minimal_failure(&world, &());
		assert!(failure.harness, "a materialiser panic is a harness error");
		let report = failure.report(&world, &());
		assert!(
			report.contains("harness error") && !report.contains("property failed"),
			"a harness bug must not read as a property failure, got: {report}"
		);
	}

	/// (b) Shrinking, panicking property: fails iff `posts` is non-empty, so
	/// the minimal counterexample is exactly one post.
	#[test]
	fn b_panicking_property_shrinks_to_one_post() {
		let property = harness(posts_must_be_empty);
		let (_, world) = generated_world(2);
		let (minimal, (), failure) = property.minimal_failure(&world, &());
		assert!(!failure.harness, "a property failure is not a harness one");

		assert_eq!(minimal.validate(), Ok(()), "shrinks stay valid");
		assert_eq!(minimal.posts.len(), 1, "minimal world: {minimal:?}");
		assert!(minimal.accounts.is_empty(), "minimal world: {minimal:?}");
		assert!(minimal.sessions.is_empty(), "minimal world: {minimal:?}");
		assert!(minimal.follows.is_empty(), "minimal world: {minimal:?}");
		assert!(
			property.run(&minimal, &()).is_failure(),
			"the minimal world still fails: {minimal:?}"
		);
	}

	/// (b) Shrinking, non-panicking property: a property that fails on any
	/// world shrinks all the way to the empty world.
	#[test]
	fn b_always_failing_property_shrinks_to_the_empty_world() {
		let property = harness(|_db: &Db, _world: &WorldState, _: Unit| TestResult::failed());
		let (_, world) = generated_world(1);
		let (minimal, (), _) = property.minimal_failure(&world, &());

		assert_eq!(minimal.validate(), Ok(()), "shrinks stay valid");
		assert!(minimal.accounts.is_empty(), "minimal world: {minimal:?}");
		assert!(minimal.sessions.is_empty(), "minimal world: {minimal:?}");
		assert!(minimal.posts.is_empty(), "minimal world: {minimal:?}");
		assert!(minimal.follows.is_empty(), "minimal world: {minimal:?}");
		assert!(
			minimal.newest_first.is_empty(),
			"minimal world: {minimal:?}"
		);
		assert!(
			property.run(&minimal, &()).is_failure(),
			"the minimal world still fails: {minimal:?}"
		);
	}
}
