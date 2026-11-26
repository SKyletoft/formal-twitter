use std::sync::Mutex;

use diesel::SqliteConnection;
use diesel_migrations::{EmbeddedMigrations, embed_migrations};

use crate::model::DbError;

#[allow(dead_code)]
pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!("migrations");

pub fn establish(_url: &str) -> Result<SqliteConnection, DbError> {
	unimplemented!()
}

pub fn configure(_conn: &mut SqliteConnection) -> Result<(), DbError> {
	unimplemented!()
}

pub fn run_migrations(_conn: &mut SqliteConnection) -> Result<(), DbError> {
	unimplemented!()
}

#[allow(dead_code)]
pub struct Db {
	conn: Mutex<SqliteConnection>,
}

impl Db {
	pub fn new(_url: &str) -> Result<Self, DbError> {
		unimplemented!()
	}

	pub fn write<T>(
		&self,
		_f: impl FnOnce(&mut SqliteConnection) -> Result<T, DbError>,
	) -> Result<T, DbError> {
		unimplemented!()
	}

	pub fn read<T>(
		&self,
		_f: impl FnOnce(&mut SqliteConnection) -> Result<T, DbError>,
	) -> Result<T, DbError> {
		unimplemented!()
	}
}
