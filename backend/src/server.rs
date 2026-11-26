//! HTTP surface: Rocket routes for `spec/Interface.agda`'s `Action`s.
//!
//! Every route is a `POST` whose body is `unlines-crlf` of the action's
//! arguments (`to-request`, Interface.agda:52-200), answered with
//! `to-response` of `to-output` of the engine's `Result`
//! (Interface.agda:224-344).

use std::time::SystemTime;

use httpdate::fmt_http_date;
use rocket::config::Config;
use rocket::data::{Limits, ToByteUnit};
use rocket::fairing::{Fairing, Info, Kind};
use rocket::http::Header;
use rocket::request::Request;
use rocket::response::Response;
use rocket::{Build, Rocket, routes};

use crate::api::routes;
use crate::assets;
use crate::db::Db;

/// `to-request` bodies are `unlines-crlf` of arbitrary `String`s, so the data
/// guard's 8 KiB default is far too small.
const STRING_LIMIT: u32 = 16;

/// Adds the `Date` header every response of the spec carries
/// (Interface.agda:227), on every response that does not already have one.
struct DateHeader;

#[rocket::async_trait]
impl Fairing for DateHeader {
	fn info(&self) -> Info {
		Info {
			name: "Date",
			kind: Kind::Response,
		}
	}

	async fn on_response<'r>(&self, _request: &'r Request<'_>, response: &mut Response<'r>) {
		if response.headers().get_one("Date").is_none() {
			let date = fmt_http_date(SystemTime::now());
			response.set_header(Header::new("Date", date));
		}
	}
}

/// The server over `db`: the API under `/api`, the frontend at `/`.
pub fn build(db: Db) -> Rocket<Build> {
	let limits = Limits::default().limit("string", STRING_LIMIT.mebibytes());
	rocket::custom(Config::figment().merge(("limits", limits)))
		.manage(db)
		.attach(DateHeader)
		.mount(
			"/api",
			routes![
				routes::post_tweet,
				routes::post_reply,
				routes::delete_tweet,
				routes::like_tweet,
				routes::unlike_tweet,
				routes::follow_user,
				routes::unfollow_user,
				routes::get_tweet,
				routes::global_timeline,
				routes::private_timeline,
				routes::login,
				routes::logout,
				routes::signup,
			],
		)
		.mount(
			"/",
			routes![
				assets::index,
				assets::index_page,
				assets::script,
				assets::stylesheet,
			],
		)
}
