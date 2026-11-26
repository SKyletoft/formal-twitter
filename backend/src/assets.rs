//! The embedded frontend, served exactly as the page needs it.
//!
//! The site is three files: the page, its script and its stylesheet.
//! `frontend/prompt` lives in the same directory but is the operator's, not
//! the browser's, so only the three named assets are ever served.

use std::io::Cursor;

use rocket::get;
use rocket::http::Header;
use rocket::request::Request;
use rocket::response::{Responder, Response, Result as ResponseResult};

/// The page, embedded at compile time.
static INDEX: &[u8] = include_bytes!("../../frontend/index.html");

/// The page's script, embedded at compile time.
static APP_JS: &[u8] = include_bytes!("../../frontend/app.js");

/// The page's stylesheet, embedded at compile time.
static STYLE_CSS: &[u8] = include_bytes!("../../frontend/style.css");

/// One of the served files.
pub struct Asset {
	contents: &'static [u8],
	content_type: &'static str,
}

impl<'r> Responder<'r, 'static> for Asset {
	fn respond_to(self, _request: &'r Request<'_>) -> ResponseResult<'static> {
		let mut response = Response::new();
		response.set_header(Header::new("Content-Type", self.content_type));
		response.set_header(Header::new(
			"Content-Length",
			self.contents.len().to_string(),
		));
		response.set_sized_body(self.contents.len(), Cursor::new(self.contents));
		Ok(response)
	}
}

/// The asset called `name`, if it is one of the served three.
fn asset(name: &str) -> Option<Asset> {
	let (contents, content_type) = match name {
		"index.html" => (INDEX, "text/html"),
		"app.js" => (APP_JS, "text/javascript"),
		"style.css" => (STYLE_CSS, "text/css"),
		_ => return None,
	};
	Some(Asset {
		contents,
		content_type,
	})
}

/// The page, at the site root.
#[get("/")]
pub fn index() -> Option<Asset> {
	asset("index.html")
}

/// The page, at its own name.
#[get("/index.html")]
pub fn index_page() -> Option<Asset> {
	asset("index.html")
}

/// The page's script.
#[get("/app.js")]
pub fn script() -> Option<Asset> {
	asset("app.js")
}

/// The page's stylesheet.
#[get("/style.css")]
pub fn stylesheet() -> Option<Asset> {
	asset("style.css")
}
