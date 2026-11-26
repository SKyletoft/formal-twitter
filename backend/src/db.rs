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
	conn.batch_execute(
		"PRAGMA foreign_keys = ON; PRAGMA busy_timeout = 5000; PRAGMA journal_mode = WAL;",
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
