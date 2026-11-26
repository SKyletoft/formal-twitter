use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Integer};
use diesel::{QueryableByName, SqliteConnection};
use rand::RngExt;

use crate::model::{DbError, PostId, SessionId};

/// Bounded number of random candidates tried before giving up.
const MAX_ATTEMPTS: usize = 100;

#[derive(QueryableByName)]
struct ExistsRow {
	#[diesel(sql_type = Integer)]
	present: i32,
}

fn id_in_use(
	c: &mut SqliteConnection,
	table: &'static str,
	candidate: i64,
) -> Result<bool, DbError> {
	let query = format!("SELECT EXISTS(SELECT 1 FROM {table} WHERE id = ?) AS present");
	let row: ExistsRow = diesel::sql_query(query)
		.bind::<BigInt, _>(candidate)
		.get_result(c)?;
	Ok(row.present != 0)
}

fn allocate(c: &mut SqliteConnection, table: &'static str) -> Result<i64, DbError> {
	let mut rng = rand::rng();
	for _ in 0..MAX_ATTEMPTS {
		let candidate = rng.random_range(1..=i64::MAX);
		if !id_in_use(c, table, candidate)? {
			return Ok(candidate);
		}
	}
	Err(DbError(diesel::result::Error::QueryBuilderError(Box::new(
		std::io::Error::other(format!(
			"could not allocate a free id in {table} after {MAX_ATTEMPTS} attempts"
		)),
	))))
}

pub fn allocate_post_id(c: &mut SqliteConnection) -> Result<PostId, DbError> {
	allocate(c, "posts").map(PostId)
}

pub fn allocate_session_id(c: &mut SqliteConnection) -> Result<SessionId, DbError> {
	allocate(c, "sessions").map(SessionId)
}
