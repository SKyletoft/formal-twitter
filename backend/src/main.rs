//! The server binary: a database of the `FORMAL_TWITTER_DB` (or
//! `DATABASE_URL`, or `formal-twitter.db`) file, served over HTTP.

use std::time::Duration;

use formal_twitter::db::Db;
use formal_twitter::engine::time;
use formal_twitter::server;

/// The interval between `time-passes` ticks when
/// `FORMAL_TWITTER_TIME_PASSES_SECS` is unset, in seconds (two minutes).
const DEFAULT_TIME_PASSES_SECS: u64 = 120;

/// `None` (env unset) -> 120 s; "0" -> disabled; positive integer -> that many
/// seconds; invalid -> 120.
fn parse_interval(value: Option<&str>) -> Option<u64> {
	let secs = match value {
		None => DEFAULT_TIME_PASSES_SECS,
		Some(raw) => match raw.trim().parse::<u64>() {
			Ok(0) => return None,
			Ok(secs) => secs,
			Err(_) => DEFAULT_TIME_PASSES_SECS,
		},
	};
	Some(secs)
}

#[rocket::main]
async fn main() -> Result<(), Box<rocket::Error>> {
	let url = std::env::var("FORMAL_TWITTER_DB")
		.or_else(|_| std::env::var("DATABASE_URL"))
		.unwrap_or_else(|_| "formal-twitter.db".to_owned());
	let db = match Db::new(&url) {
		Ok(db) => db,
		Err(error) => {
			eprintln!("could not open the database at {url}: {error}");
			std::process::exit(1);
		}
	};
	// The `time-passes` timer lives here and not in `server::build`, so the
	// test-suite's rockets never start a background task that would race its
	// assertions. Only the real binary schedules timeouts.
	let interval = parse_interval(
		std::env::var("FORMAL_TWITTER_TIME_PASSES_SECS")
			.ok()
			.as_deref(),
	);
	if let Some(secs) = interval {
		let timer_db = db.clone();
		rocket::tokio::spawn(async move {
			let period = Duration::from_secs(secs);
			loop {
				// Sleep first: a fresh server never times out the sessions it
				// has just handed out before it has served anything.
				rocket::tokio::time::sleep(period).await;
				if let Err(error) = time::time_passes(&timer_db) {
					eprintln!("time-passes failed: {error}");
				}
			}
		});
	}
	server::build(db).launch().await?;
	Ok(())
}

#[cfg(test)]
mod tests {
	use super::{DEFAULT_TIME_PASSES_SECS, parse_interval};

	#[test]
	fn unset_interval_is_the_default() {
		assert_eq!(parse_interval(None), Some(DEFAULT_TIME_PASSES_SECS));
		assert_eq!(parse_interval(None), Some(120));
	}

	#[test]
	fn zero_disables_the_timer() {
		assert_eq!(parse_interval(Some("0")), None);
		assert_eq!(parse_interval(Some(" 0 ")), None);
	}

	#[test]
	fn positive_integers_are_taken_verbatim() {
		assert_eq!(parse_interval(Some("5")), Some(5));
		assert_eq!(parse_interval(Some("1")), Some(1));
		assert_eq!(parse_interval(Some("86400")), Some(86400));
	}

	#[test]
	fn invalid_values_fall_back_to_the_default() {
		assert_eq!(parse_interval(Some("abc")), Some(120));
		assert_eq!(parse_interval(Some("")), Some(120));
		assert_eq!(parse_interval(Some("-5")), Some(120));
		assert_eq!(parse_interval(Some("1.5")), Some(120));
	}

	#[test]
	fn surrounding_whitespace_is_trimmed() {
		assert_eq!(parse_interval(Some("  7\n")), Some(7));
		assert_eq!(parse_interval(Some("\t42 ")), Some(42));
	}
}
