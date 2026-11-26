//! The server binary: a database of the `FORMAL_TWITTER_DB` (or
//! `DATABASE_URL`, or `formal-twitter.db`) file, served over HTTP.

use formal_twitter::db::Db;
use formal_twitter::server;

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
	server::build(db).launch().await?;
	Ok(())
}
