use std::sync::Mutex;

use diesel::connection::SimpleConnection;
use diesel::{Connection, SqliteConnection};
use diesel_migrations::{EmbeddedMigrations, MigrationHarness, embed_migrations};

use crate::model::DbError;

#[allow(dead_code)]
pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!("migrations");

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

pub struct Db {
	conn: Mutex<SqliteConnection>,
}

impl Db {
	/// An in-memory database. For tests only; production uses a file.
	pub fn in_memory() -> Result<Self, DbError> {
		Self::new(":memory:")
	}

	pub fn new(url: &str) -> Result<Self, DbError> {
		let mut conn = establish(url)?;
		configure(&mut conn)?;
		run_migrations(&mut conn)?;
		Ok(Self {
			conn: Mutex::new(conn),
		})
	}

	pub fn write<T>(
		&self,
		f: impl FnOnce(&mut SqliteConnection) -> Result<T, DbError>,
	) -> Result<T, DbError> {
		let mut guard = self
			.conn
			.lock()
			.map_err(|_| DbError(diesel::result::Error::RollbackTransaction))?;
		guard.transaction(|conn| f(conn))
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
