use diesel::RunQueryDsl;
use diesel::sql_types::{BigInt, Integer};
use diesel::{QueryableByName, SqliteConnection};
use rand::RngExt;

use crate::model::{DbError, PostId, SessionId};

/// Bounded number of random candidates tried before giving up.
const MAX_ATTEMPTS: usize = 100;

/// Largest id the API may write into a bare JSON number: 2^53 - 1.
///
/// `show-tweets` (Interface.agda:219-222) writes timeline and reply ids as
/// unquoted JSON numbers. JSON numbers above 2^53 are not exactly
/// representable by JavaScript clients (`JSON.parse` silently rounds them), so
/// such an id could not be round-tripped by the frontend. `CreateNew` only
/// asks for a *fresh* id, never for the whole `Nat` range, so drawing from the
/// exactly representable range costs nothing.
const MAX_SAFE_ID: i64 = (1 << 53) - 1;

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
		let candidate = rng.random_range(1..=MAX_SAFE_ID);
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
