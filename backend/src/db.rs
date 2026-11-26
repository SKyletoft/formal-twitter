use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use diesel::connection::SimpleConnection;
use diesel::{Connection, SqliteConnection};
use diesel_migrations::{EmbeddedMigrations, MigrationHarness, embed_migrations};

use crate::model::{DbError, PostId, PublicPost};

#[allow(dead_code)]
pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!("migrations");

/// The most public post bodies the cache keeps. Beyond this the map is dropped
/// wholesale: the cache is an optimisation, never a source of truth, so
/// dropping it costs at most one re-read per entry.
pub const CACHE_CAPACITY: usize = 10_000;

/// Posts with more replies than this are not cached: their body is a large
/// `Vec` and re-reading it costs little relative to holding it resident.
pub const CACHE_MAX_REPLIES: usize = 1_024;

pub fn establish(url: &str) -> Result<SqliteConnection, DbError> {
	SqliteConnection::establish(url)
		.map_err(|error| DbError(diesel::result::Error::QueryBuilderError(Box::new(error))))
}

pub fn configure(conn: &mut SqliteConnection) -> Result<(), DbError> {
	// `synchronous = NORMAL` under WAL fsyncs on checkpoint rather than on every
	// commit: a commit is durable in the OS page cache and reaches the disk
	// before the next checkpoint, so it is complete -- and readable by every
	// later transaction -- before any response is served. The only thing lost on
	// an OS crash or power failure is the tail of transactions not yet
	// checkpointed; the database file itself stays consistent (no corruption),
	// because WAL frames are checksummed and replay either stops at the first
	// torn frame or recovers a complete prefix. That is the standard tradeoff
	// (SQLite docs, "WAL mode: 2.1 Performance considerations") and it removes
	// one fsync -- ~1.8 ms on this host -- from every write transaction.
	conn.batch_execute(
		"PRAGMA foreign_keys = ON; PRAGMA busy_timeout = 5000; \
		PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;",
	)?;
	Ok(())
}

pub fn run_migrations(conn: &mut SqliteConnection) -> Result<(), DbError> {
	conn.run_pending_migrations(MIGRATIONS)
		.map(|_| ())
		.map_err(|error| DbError(diesel::result::Error::QueryBuilderError(error)))
}

/// The mutable half of [`Cache`], behind its mutex.
struct CacheState {
	/// Bumped on every successful write. A reader samples it before its
	/// database read and only publishes a body if it is unchanged afterwards,
	/// which is what makes a stale entry impossible.
	generation: u64,
	map: HashMap<PostId, PublicPost>,
}

/// The process-wide cache of public post bodies.
///
/// It never holds a value the database disagrees with, because every mutating
/// command -- including `time-passes` (Twitter.agda:691-702) -- reports through
/// [`Db::write`], which clears the map after its transaction commits.
///
/// Lock order: the database mutex of [`Db`] may be held while taking the cache
/// mutex, but the cache mutex is never held across database I/O. Every method
/// here takes and releases the cache mutex on its own, so there is only ever
/// one order and no deadlock.
///
/// Correctness rests on the existing `read-post` theorems, not on a new `Step`:
/// the cache introduces no command and no state of the spec's world. The answer
/// is still `read-post-logged-in` / `read-post-anonymously`
/// (Twitter.agda:518-555); the cache is only an alternative way to compute it,
/// and `tests/cache.rs` checks that it computes the same thing as the database.
pub struct Cache {
	/// `false` for the test-only uncached handles: every operation is then a
	/// no-op, so those handles behave exactly like the pre-cache code.
	enabled: bool,
	state: Mutex<CacheState>,
}

impl Cache {
	fn new(enabled: bool) -> Self {
		Self {
			enabled,
			state: Mutex::new(CacheState {
				generation: 0,
				map: HashMap::new(),
			}),
		}
	}

	fn get(&self, pid: PostId) -> Option<PublicPost> {
		if !self.enabled {
			return None;
		}
		// A poisoned cache is only ever a cache: fall back to the database.
		match self.state.lock() {
			Ok(state) => state.map.get(&pid).cloned(),
			Err(_) => None,
		}
	}

	/// Inserts `view` for `pid` iff no write completed since `sampled` was read.
	fn put(&self, sampled: u64, pid: PostId, view: PublicPost) {
		if !self.enabled || view.replies.len() > CACHE_MAX_REPLIES {
			return;
		}
		let Ok(mut state) = self.state.lock() else {
			return;
		};
		if state.generation != sampled {
			return;
		}
		if state.map.len() >= CACHE_CAPACITY {
			state.map.clear();
		}
		state.map.insert(pid, view);
	}

	fn generation(&self) -> u64 {
		if !self.enabled {
			return 0;
		}
		match self.state.lock() {
			Ok(state) => state.generation,
			Err(_) => 0,
		}
	}

	/// Drops every entry and moves to the next generation.
	fn invalidate(&self) {
		if !self.enabled {
			return;
		}
		if let Ok(mut state) = self.state.lock() {
			state.map.clear();
			state.generation = state.generation.wrapping_add(1);
		}
	}
}

/// A handle to the sqlite database.
///
/// The connection lives behind an `Arc` so the handle is cheap to clone: the
/// server can hand a copy to a background task (the `time-passes` timer) while
/// keeping its own. Clones share one connection and therefore one lock, which
/// keeps every transaction serialised as before. Clones also share one
/// [`Cache`], so a write through any handle invalidates what every handle sees.
#[derive(Clone)]
pub struct Db {
	conn: Arc<Mutex<SqliteConnection>>,
	cache: Arc<Cache>,
}

impl Db {
	/// An in-memory database. For tests only; production uses a file.
	pub fn in_memory() -> Result<Self, DbError> {
		Self::new(":memory:")
	}

	/// An in-memory database with the cache disabled, for the equivalence
	/// tests. Never used by the server.
	pub fn in_memory_uncached() -> Result<Self, DbError> {
		Self::new_uncached(":memory:")
	}

	pub fn new(url: &str) -> Result<Self, DbError> {
		Self::open(url, true)
	}

	/// `new` with every cache operation a no-op: the pre-cache behaviour. For
	/// tests and benchmarks; never used by the server.
	pub fn new_uncached(url: &str) -> Result<Self, DbError> {
		Self::open(url, false)
	}

	fn open(url: &str, cache: bool) -> Result<Self, DbError> {
		let mut conn = establish(url)?;
		configure(&mut conn)?;
		run_migrations(&mut conn)?;
		Ok(Self {
			conn: Arc::new(Mutex::new(conn)),
			cache: Arc::new(Cache::new(cache)),
		})
	}

	/// The body cached for `pid`, if any. Never touches the database.
	pub fn cache_get(&self, pid: PostId) -> Option<PublicPost> {
		self.cache.get(pid)
	}

	/// The current cache generation: sample it before a database read and pass
	/// it to [`Db::cache_put`], so a write racing in between wins.
	pub fn cache_generation(&self) -> u64 {
		self.cache.generation()
	}

	/// Caches `view` for `pid`, unless a write completed since `sampled`.
	pub fn cache_put(&self, sampled: u64, pid: PostId, view: PublicPost) {
		self.cache.put(sampled, pid, view);
	}

	/// Drops every cached body. For tests and benchmarks that need the cold
	/// path; production only ever drops the cache through [`Db::write`].
	#[doc(hidden)]
	pub fn clear_cache_for_tests(&self) {
		self.cache.invalidate();
	}

	pub fn write<T>(
		&self,
		f: impl FnOnce(&mut SqliteConnection) -> Result<T, DbError>,
	) -> Result<T, DbError> {
		let mut guard = self
			.conn
			.lock()
			.map_err(|_| DbError(diesel::result::Error::RollbackTransaction))?;
		let result = guard.transaction(|conn| f(conn));
		// Still under the database mutex, so no reader can publish a body of the
		// world we have just replaced. A failed transaction rolled back and
		// changed nothing, so it needs no invalidation.
		if result.is_ok() {
			self.cache.invalidate();
		}
		result
	}

	pub fn read<T>(
		&self,
		f: impl FnOnce(&mut SqliteConnection) -> Result<T, DbError>,
	) -> Result<T, DbError> {
		let mut guard = self
			.conn
			.lock()
			.map_err(|_| DbError(diesel::result::Error::RollbackTransaction))?;
		guard.transaction(|conn| f(conn))
	}
}

#[cfg(test)]
mod tests {
	use super::{CACHE_CAPACITY, CACHE_MAX_REPLIES, Db};
	use crate::model::{DbError, PostId, PublicPost};

	fn body(text: &str) -> PublicPost {
		PublicPost {
			author: "u".to_owned(),
			text: text.to_owned(),
			likes: 0,
			replies: Vec::new(),
		}
	}

	fn cache_sample(db: &Db, pid: PostId) {
		let generation = db.cache_generation();
		db.cache_put(generation, pid, body("cached"));
	}

	#[test]
	fn a_put_before_any_write_is_visible() {
		let db = Db::in_memory().expect("database");
		assert_eq!(db.cache_get(PostId(1)), None);
		cache_sample(&db, PostId(1));
		assert_eq!(db.cache_get(PostId(1)), Some(body("cached")));
	}

	#[test]
	fn every_successful_write_drops_the_cache() {
		let db = Db::in_memory().expect("database");
		cache_sample(&db, PostId(1));
		db.write(|_| Ok(())).expect("write");
		assert_eq!(db.cache_get(PostId(1)), None);
	}

	#[test]
	fn a_failed_write_keeps_the_cache() {
		let db = Db::in_memory().expect("database");
		cache_sample(&db, PostId(1));
		assert!(
			db.write(|_| Err::<(), _>(DbError(diesel::result::Error::NotFound)))
				.is_err()
		);
		assert_eq!(db.cache_get(PostId(1)), Some(body("cached")));
	}

	#[test]
	fn a_put_sampled_before_a_write_is_discarded() {
		let db = Db::in_memory().expect("database");
		let stale = db.cache_generation();
		db.write(|_| Ok(())).expect("write");
		db.cache_put(stale, PostId(1), body("stale"));
		assert_eq!(db.cache_get(PostId(1)), None);
	}

	#[test]
	fn posts_with_too_many_replies_are_not_cached() {
		let db = Db::in_memory().expect("database");
		let many = PublicPost {
			replies: (0..=CACHE_MAX_REPLIES as i64).map(PostId).collect(),
			..body("many")
		};
		let generation = db.cache_generation();
		db.cache_put(generation, PostId(1), many);
		assert_eq!(db.cache_get(PostId(1)), None);
	}

	#[test]
	fn the_capacity_is_bounded() {
		let db = Db::in_memory().expect("database");
		for id in 0..CACHE_CAPACITY as i64 {
			cache_sample(&db, PostId(id));
		}
		assert_eq!(db.cache_get(PostId(0)), Some(body("cached")));
		cache_sample(&db, PostId(CACHE_CAPACITY as i64));
		// The map was dropped wholesale to stay inside its budget.
		assert_eq!(db.cache_get(PostId(0)), None);
		assert_eq!(
			db.cache_get(PostId(CACHE_CAPACITY as i64)),
			Some(body("cached"))
		);
	}

	#[test]
	fn an_uncached_handle_never_keeps_anything() {
		let db = Db::in_memory_uncached().expect("database");
		cache_sample(&db, PostId(1));
		assert_eq!(db.cache_get(PostId(1)), None);
	}

	#[test]
	fn clones_share_one_cache() {
		let db = Db::in_memory().expect("database");
		let other = db.clone();
		cache_sample(&db, PostId(1));
		assert_eq!(other.cache_get(PostId(1)), Some(body("cached")));
		other.write(|_| Ok(())).expect("write");
		assert_eq!(db.cache_get(PostId(1)), None);
	}
}
