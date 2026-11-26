//! Static-asset contract for task T4.
//!
//! The frontend (`frontend/app.js:100` posts to `/api/<action>`) must be
//! served, and nothing else: in particular `frontend/prompt`, the operator
//! prompt, must never be reachable over HTTP.

use formal_twitter::db::Db;
use formal_twitter::server;
use rocket::local::blocking::{Client, LocalResponse};

fn harness() -> Client {
	Client::tracked(server::build(Db::in_memory().unwrap())).unwrap()
}

/// The media type of `Content-Type`, with its parameters stripped.
fn mime(response: &LocalResponse<'_>) -> String {
	response
		.headers()
		.get_one("Content-Type")
		.expect("a served asset carries a Content-Type")
		.split(';')
		.next()
		.unwrap_or_default()
		.trim()
		.to_string()
}

fn assert_present(response: &LocalResponse<'_>, path: &str) {
	assert!(
		response.headers().get_one("Content-Length").is_some(),
		"GET {path} carries a Content-Length"
	);
}

/// The `index.html` page, at both of its paths.
fn html(client: &Client, path: &str) -> String {
	let response = client.get(path).dispatch();
	assert_eq!(response.status().code, 200, "GET {path}");
	assert_eq!(mime(&response), "text/html", "GET {path}");
	assert_present(&response, path);
	response.into_string().expect("index.html is UTF-8")
}

#[test]
fn serves_frontend_assets() {
	let client = harness();

	for path in ["/", "/index.html"] {
		let body = html(&client, path);
		assert!(
			body.contains("<title>Formal Twitter</title>"),
			"GET {path} serves index.html"
		);
	}

	let javascript = client.get("/app.js").dispatch();
	assert_eq!(javascript.status().code, 200);
	assert!(
		matches!(
			mime(&javascript).as_str(),
			"text/javascript" | "application/javascript"
		),
		"unexpected JavaScript media type: {:?}",
		mime(&javascript)
	);
	assert_present(&javascript, "/app.js");
	let body = javascript.into_string().expect("app.js is UTF-8");
	assert!(body.contains("/api/"), "/app.js posts to the API");

	let stylesheet = client.get("/style.css").dispatch();
	assert_eq!(stylesheet.status().code, 200);
	assert_eq!(mime(&stylesheet), "text/css");
	assert_present(&stylesheet, "/style.css");
	let body = stylesheet.into_string().expect("style.css is UTF-8");
	assert!(!body.is_empty(), "/style.css is not empty");
}

#[test]
fn unknown_paths_are_not_served() {
	let client = harness();

	// `frontend/prompt` lives next to the assets but is not one of them.
	for path in [
		"/prompt",
		"/nope",
		"/frontend/prompt",
		"/api",
		"/style.css.map",
	] {
		let response = client.get(path).dispatch();
		assert_eq!(response.status().code, 404, "GET {path}");
	}

	// Only the three assets exist; the API routes are POST-only.
	let response = client.get("/api/signup").dispatch();
	assert_eq!(response.status().code, 404, "GET /api/signup");
}
