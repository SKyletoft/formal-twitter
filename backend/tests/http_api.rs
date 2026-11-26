//! HTTP-level integration tests for the public API of `spec/Interface.agda`.
//!
//! Every test drives the server through Rocket's local `Client`, sends what
//! `to-request` sends (Interface.agda:52-200) and asserts exactly what
//! `to-response` answers (Interface.agda:224-309) for the `Result` that
//! `to-output` maps (Interface.agda:335-344): status, body bytes,
//! `Content-Type`, `Content-Length`, `Cache-Control` and `Date`.
//!
//! These tests define the HTTP contract of task T4. They panic on the
//! `todo!()` skeleton until the routes exist.

use formal_twitter::db::Db;
use formal_twitter::ids::allocate_post_id;
use formal_twitter::model::Visibility;
use formal_twitter::server;
use formal_twitter::store;
use rocket::http::ContentType;
use rocket::local::blocking::{Client, LocalResponse};

/// `to-response permission-error` (Interface.agda:231).
const ACCESS_DENIED: &str = "{\"error\": \"access_denied\"}";
/// `to-response outdated-login-token` (Interface.agda:240).
const SESSION_EXPIRED: &str = "{\"error\": \"session_expired\"}";
/// `to-response login-error` (Interface.agda:278).
const LOGIN_FAILED: &str = "{\"error\": \"login_failed\"}";
/// `to-response signup-error` (Interface.agda:287).
const SIGNUP_FAILED: &str = "{\"error\": \"signup_failed\"}";
/// A body the spec cannot parse has no `Response`, so `to-response` says
/// nothing about it. The tests fix one consistent choice for it: `400` with an
/// `application/json` error body, like the other error replies.
const BAD_REQUEST: &str = "{\"error\": \"bad_request\"}";

/// `new-sid` only ever draws from `1..`, so `0` was never issued and never
/// extracts a valid session.
const NEVER_ISSUED_TOKEN: &str = "0";

/// `new-pid` only ever draws from `1..`, so `0` is `unused` in every world a
/// test builds.
const ABSENT_POST: &str = "0";

/* ---------- harness ---------- */

/// The parts of a response the contract fixes, captured eagerly so no
/// assertion depends on header order.
struct Resp {
	status: u16,
	body: String,
	content_type: Option<String>,
	content_length: Option<String>,
	cache_control: Option<String>,
	date: Option<String>,
}

fn header(response: &LocalResponse<'_>, name: &str) -> Option<String> {
	response.headers().get_one(name).map(str::to_string)
}

fn record(response: LocalResponse<'_>) -> Resp {
	let status = response.status().code;
	let content_type = header(&response, "Content-Type");
	let content_length = header(&response, "Content-Length");
	let cache_control = header(&response, "Cache-Control");
	let date = header(&response, "Date");
	let body = String::from_utf8(response.into_bytes().unwrap_or_default())
		.expect("response bodies are UTF-8");
	Resp {
		status,
		body,
		content_type,
		content_length,
		cache_control,
		date,
	}
}

fn harness() -> Client {
	Client::tracked(server::build(Db::in_memory().unwrap())).unwrap()
}

/// A harness over a database that was seeded before the server started.
fn harness_with(db: Db) -> Client {
	Client::tracked(server::build(db)).unwrap()
}

/// `unlines-crlf` of the action's arguments (Interface.agda:52-200).
fn request_body(lines: &[&str]) -> String {
	let mut body = lines.join("\r\n");
	body.push_str("\r\n");
	body
}

fn request_raw(client: &Client, action: &str, body: &str) -> Resp {
	let response = client
		.post(format!("/api/{action}"))
		.header(ContentType::new("text", "plain").with_params(("charset", "utf-8")))
		.body(body)
		.dispatch();
	record(response)
}

fn request(client: &Client, action: &str, lines: &[&str]) -> Resp {
	request_raw(client, action, &request_body(lines))
}

/* ---------- assertions ---------- */

fn assert_date(resp: &Resp) {
	assert!(
		resp.date.is_some(),
		"every API response carries a Date header (Interface.agda:227)"
	);
}

fn assert_status(resp: &Resp, status: u16) {
	assert_eq!(
		resp.status, status,
		"unexpected status; body {:?}",
		resp.body
	);
}

/// Every JSON reply: `Content-Type: application/json` with no charset, a
/// `Content-Length` equal to the exact UTF-8 byte length of the body, a
/// `Date`, and `Cache-Control: no-store` exactly where the spec sets it.
fn assert_json_headers(resp: &Resp, no_store: bool) {
	assert_eq!(
		resp.content_type.as_deref(),
		Some("application/json"),
		"body {:?}",
		resp.body
	);
	let length = resp.body.len().to_string();
	assert_eq!(
		resp.content_length.as_deref(),
		Some(length.as_str()),
		"body {:?}",
		resp.body
	);
	assert_date(resp);
	if no_store {
		assert_eq!(resp.cache_control.as_deref(), Some("no-store"));
	} else {
		assert!(
			resp.cache_control.is_none(),
			"unexpected Cache-Control: {:?}",
			resp.cache_control
		);
	}
}

/// `to-response ok`: `200`, an empty body, `Content-Length: 0`, no
/// `Content-Type` and no `Cache-Control` (Interface.agda:225-230).
fn assert_ok(resp: &Resp) {
	assert_status(resp, 200);
	assert_eq!(resp.body, "");
	assert_eq!(resp.content_length.as_deref(), Some("0"));
	assert!(
		resp.content_type.is_none(),
		"ok has no body, so it has no Content-Type"
	);
	assert!(resp.cache_control.is_none(), "ok is not a no-store reply");
	assert_date(resp);
}

fn assert_json_error(resp: &Resp, status: u16, body: &str) {
	assert_status(resp, status);
	assert_eq!(resp.body, body);
	assert_json_headers(resp, false);
}

fn assert_json_ok(resp: &Resp, body: &str, no_store: bool) {
	assert_status(resp, 200);
	assert_eq!(resp.body, body);
	assert_json_headers(resp, no_store);
}

/// A JSON reply whose body is only known once its single natural-number field
/// has been parsed (`tweet-id`, `session-token`).
fn assert_json_field_ok(resp: &Resp, no_store: bool) {
	assert_status(resp, 200);
	assert_json_headers(resp, no_store);
}

fn assert_bad_request(resp: &Resp) {
	assert_status(resp, 400);
	assert_eq!(resp.body, BAD_REQUEST);
	assert_eq!(resp.content_type.as_deref(), Some("application/json"));
	let length = resp.body.len().to_string();
	assert_eq!(resp.content_length.as_deref(), Some(length.as_str()));
	assert_date(resp);
}

/// Reads the single natural-number field `key` of a reply of the shape
/// `{"key": "<n>"}`, checking the exact surrounding bytes.
fn digits(resp: &Resp, key: &str) -> String {
	let prefix = format!("{{\"{key}\": \"");
	let rest = resp
		.body
		.strip_prefix(&prefix)
		.unwrap_or_else(|| panic!("body {:?} does not open with {prefix:?}", resp.body));
	let inner = rest
		.strip_suffix("\"}")
		.unwrap_or_else(|| panic!("body {:?} does not close with \"}}\"", resp.body));
	assert!(!inner.is_empty(), "empty {key} in {:?}", resp.body);
	assert!(
		inner.bytes().all(|byte| byte.is_ascii_digit()),
		"{key} is not a natural: {inner:?}"
	);
	assert!(
		inner.parse::<i64>().is_ok(),
		"{key} does not fit in 64 bits: {inner:?}"
	);
	inner.to_string()
}

/// `to-response (tweet-id _)`: `{"tweet_id": "<n>"}`, without `no-store`
/// (Interface.agda:249-257). Returns the id.
fn created(resp: &Resp) -> String {
	assert_json_field_ok(resp, false);
	let id = digits(resp, "tweet_id");
	assert_eq!(resp.body, format!("{{\"tweet_id\": \"{id}\"}}"));
	id
}

/// `to-response (session-token _)`: `{"session_token": "<n>"}` with
/// `Cache-Control: no-store` (Interface.agda:268-277). Returns the token.
fn session(resp: &Resp) -> String {
	assert_json_field_ok(resp, true);
	let token = digits(resp, "session_token");
	assert_eq!(resp.body, format!("{{\"session_token\": \"{token}\"}}"));
	token
}

/* ---------- bodies ---------- */

/// `to-response (tweet username txt likes replies)` (Interface.agda:296-309).
/// `username` and `text` must already be escaped the way the spec escapes.
fn tweet_body(username: &str, text: &str, likes: u64, replies: &[&str]) -> String {
	format!(
		"{{\"username\": \"{username}\", \"text\": \"{text}\", \"likes\": {likes}, \"replies\": [{}]}}",
		replies.join(", ")
	)
}

/// `to-response (timeline xs)`; `show-tweets` separates ids with `", "`
/// (Interface.agda:219-222, 258-267).
fn timeline_body(ids: &[&str]) -> String {
	format!("{{\"timeline\": [{}]}}", ids.join(", "))
}

/* ---------- actions ---------- */

fn signup(client: &Client, username: &str, password: &str) -> Resp {
	request(client, "signup", &[username, password])
}

fn login(client: &Client, username: &str, password: &str) -> Resp {
	request(client, "login", &[username, password])
}

/// Signs `username` up and returns a fresh session token for it.
fn account(client: &Client, username: &str, password: &str) -> String {
	assert_ok(&signup(client, username, password));
	session(&login(client, username, password))
}

/// `post-tweet`; returns the fresh post id.
fn publish(client: &Client, token: &str, text: &str) -> String {
	created(&request(client, "post-tweet", &[token, text]))
}

/// `post-reply`; returns the fresh reply id.
fn reply(client: &Client, token: &str, text: &str, parent: &str) -> String {
	created(&request(client, "post-reply", &[token, text, parent]))
}

fn read_post(client: &Client, session: Option<&str>, post: &str) -> Resp {
	match session {
		Some(token) => request(client, "get-tweet", &[token, post]),
		None => request(client, "get-tweet", &[post]),
	}
}

/// An account `bob`/`pw` with one `followers-only` post, seeded before the
/// server is built: `register` always gives an account
/// `default-visibility = everyone` (Twitter.agda:470-488), so the API alone
/// cannot create a `followers-only` post. Returns the database to hand to
/// `harness_with`, and the post id.
fn seed_private_post(text: &str) -> (Db, String) {
	let db = Db::in_memory().unwrap();
	let id = db
		.write(|c| {
			store::create_account(c, "bob", "pw")?;
			let pid = allocate_post_id(c)?;
			store::insert_post(c, pid, "bob", text, Visibility::FollowersOnly)?;
			Ok(pid)
		})
		.unwrap();
	(db, id.0.to_string())
}

/* ---------- 1. signup, login ---------- */

#[test]
fn signup_login_and_auth_failures() {
	let client = harness();

	// create-account (Twitter.agda:470-488) answers `success`.
	assert_ok(&signup(&client, "alice", "pw"));
	// A taken username is `signup-failed` -> 400 (Interface.agda:287-295).
	assert_json_error(&signup(&client, "alice", "other"), 400, SIGNUP_FAILED);
	// failed-login-1 / failed-login-2 (Twitter.agda:490-516).
	assert_json_error(&login(&client, "alice", "wrong"), 401, LOGIN_FAILED);
	assert_json_error(&login(&client, "nobody", "pw"), 401, LOGIN_FAILED);

	// login answers `issued-session`: exact body, no-store, and a natural id.
	let token = session(&login(&client, "alice", "pw"));
	assert!(token.parse::<i64>().unwrap() > 0);
	assert_ne!(token, NEVER_ISSUED_TOKEN);
	// Logging in again issues a distinct token.
	let again = session(&login(&client, "alice", "pw"));
	assert_ne!(token, again);
}

/* ---------- 2. posts and replies ---------- */

#[test]
fn post_reply_and_read_post() {
	let client = harness();
	let token = account(&client, "alice", "pw");

	let post = publish(&client, &token, "first post");
	// successful-reply (Twitter.agda:400-422).
	let first = reply(&client, &token, "first reply", &post);
	let second = reply(&client, &token, "second reply", &post);
	// failed-reply: the parent must be readable (Twitter.agda:424-430).
	assert_json_error(
		&request(&client, "post-reply", &[&token, "orphan", ABSENT_POST]),
		403,
		ACCESS_DENIED,
	);

	// `replies` is newest-first, so the later reply comes first.
	let expected = tweet_body("alice", "first post", 0, &[&second, &first]);
	assert_json_ok(&read_post(&client, Some(&token), &post), &expected, true);
	// read-post-anonymously: a `live` `everyone` post (Twitter.agda:550-554).
	assert_json_ok(&read_post(&client, None, &post), &expected, true);
	// cant-read-post-public (Twitter.agda:518-522): a valid session reading a
	// post that never existed answers `denied`.
	assert_json_error(
		&read_post(&client, Some(&token), ABSENT_POST),
		403,
		ACCESS_DENIED,
	);
	// The reply is itself a post and reads back as one.
	assert_json_ok(
		&read_post(&client, Some(&token), &first),
		&tweet_body("alice", "first reply", 0, &[]),
		true,
	);
}

/* ---------- 3. likes ---------- */

#[test]
fn like_and_unlike() {
	let client = harness();
	let alice = account(&client, "alice", "pw");
	let bob = account(&client, "bob", "pw");
	let post = publish(&client, &alice, "likeable");

	// like-post (Twitter.agda:587-613) answers `success`.
	assert_ok(&request(&client, "like-tweet", &[&bob, &post]));
	let liked = tweet_body("alice", "likeable", 1, &[]);
	assert_json_ok(&read_post(&client, None, &post), &liked, true);

	// `add-like` is idempotent: liking twice leaves the like list alone.
	assert_ok(&request(&client, "like-tweet", &[&bob, &post]));
	assert_json_ok(&read_post(&client, None, &post), &liked, true);

	// unlike-post (Twitter.agda:621-647) answers `success`.
	assert_ok(&request(&client, "unlike-tweet", &[&bob, &post]));
	assert_json_ok(
		&read_post(&client, None, &post),
		&tweet_body("alice", "likeable", 0, &[]),
		true,
	);
	// Unliking again is also `success`, and still changes nothing.
	assert_ok(&request(&client, "unlike-tweet", &[&bob, &post]));
	assert_json_ok(
		&read_post(&client, None, &post),
		&tweet_body("alice", "likeable", 0, &[]),
		true,
	);

	// failed-like-post (Twitter.agda:615-619).
	assert_json_error(
		&request(&client, "like-tweet", &[&bob, ABSENT_POST]),
		403,
		ACCESS_DENIED,
	);
	// failed-unlike-post (Twitter.agda:649-653) shares the same readability
	// premise: an absent post is `denied` for a valid session.
	assert_json_error(
		&request(&client, "unlike-tweet", &[&bob, ABSENT_POST]),
		403,
		ACCESS_DENIED,
	);
}

/* ---------- 4. follows ---------- */

#[test]
fn follow_unfollow_and_private_visibility() {
	let (db, private_id) = seed_private_post("bob private");
	let client = harness_with(db);
	let alice = account(&client, "alice", "pw");
	assert_ok(&login(&client, "bob", "pw"));

	// follow-user has no premise on the followee existing (Twitter.agda:655-664):
	// following an unknown username is `success`, not a failure.
	assert_ok(&request(&client, "follow-user", &[&alice, "nobody"]));

	// cant-read-post-followers-only (Twitter.agda:518-538).
	assert_json_error(
		&read_post(&client, Some(&alice), &private_id),
		403,
		ACCESS_DENIED,
	);

	assert_ok(&request(&client, "follow-user", &[&alice, "bob"]));
	assert_json_ok(
		&read_post(&client, Some(&alice), &private_id),
		&tweet_body("bob", "bob private", 0, &[]),
		true,
	);

	// unfollow-user (Twitter.agda:666-675).
	assert_ok(&request(&client, "unfollow-user", &[&alice, "bob"]));
	assert_json_error(
		&read_post(&client, Some(&alice), &private_id),
		403,
		ACCESS_DENIED,
	);
	// Unfollowing again is `success` and changes nothing.
	assert_ok(&request(&client, "unfollow-user", &[&alice, "bob"]));
	assert_json_error(
		&read_post(&client, Some(&alice), &private_id),
		403,
		ACCESS_DENIED,
	);
}

/* ---------- 5. delete ---------- */

#[test]
fn delete_post_lifecycle() {
	let client = harness();
	let alice = account(&client, "alice", "pw");
	let bob = account(&client, "bob", "pw");
	let post = publish(&client, &alice, "to delete");
	let kept = publish(&client, &alice, "kept");

	// delete-post (Twitter.agda:432-449).
	assert_ok(&request(&client, "delete-tweet", &[&alice, &post]));
	assert_json_error(&read_post(&client, Some(&alice), &post), 403, ACCESS_DENIED);

	// failed-delete-not-author (Twitter.agda:451-462).
	assert_json_error(
		&request(&client, "delete-tweet", &[&bob, &kept]),
		403,
		ACCESS_DENIED,
	);
	// failed-delete-non-existant-post.
	assert_json_error(
		&request(&client, "delete-tweet", &[&alice, ABSENT_POST]),
		403,
		ACCESS_DENIED,
	);
	// `delete-post` has no `live` premise: deleting an already deleted own
	// post is still `success` and changes nothing (a tombstone).
	assert_ok(&request(&client, "delete-tweet", &[&alice, &post]));
	assert_json_error(&read_post(&client, Some(&alice), &post), 403, ACCESS_DENIED);

	// The failed deletes left `kept` untouched.
	assert_json_ok(
		&read_post(&client, None, &kept),
		&tweet_body("alice", "kept", 0, &[]),
		true,
	);
}

/* ---------- 6. timelines ---------- */

#[test]
fn timelines_are_exact_newest_first_and_filtered() {
	let (db, private_id) = seed_private_post("bob private");
	let client = harness_with(db);
	let alice = account(&client, "alice", "pw");
	// `seed_private_post` already registered bob, so signing him up again would
	// be `signup-failed`: log in to the seeded account instead.
	let bob = session(&login(&client, "bob", "pw"));

	let first = publish(&client, &alice, "alice one");
	let bob_post = publish(&client, &bob, "bob one");
	let last = publish(&client, &alice, "alice two");
	assert_ok(&request(&client, "delete-tweet", &[&bob, &bob_post]));
	// The seeded private post is the oldest entry, and stays unreadable for
	// alice, who follows nobody yet.
	let newest_first = [last.as_str(), first.as_str()];

	// get-public-global-timeline (Twitter.agda:578-585): `live` and
	// `everyone` only, newest-first.
	assert_json_ok(
		&request(&client, "global-timeline", &["100"]),
		&timeline_body(&newest_first),
		true,
	);
	// `len` bounds the answer.
	assert_json_ok(
		&request(&client, "global-timeline", &["1"]),
		&timeline_body(&[&last]),
		true,
	);
	assert_json_ok(
		&request(&client, "global-timeline", &["0"]),
		&timeline_body(&[]),
		true,
	);
	// get-private-global-timeline (Twitter.agda:568-576), following nobody:
	// bob's private post is out of reach.
	assert_json_ok(
		&request(&client, "global-timeline", &[&alice, "100"]),
		&timeline_body(&newest_first),
		true,
	);
	// get-personal-timeline (Twitter.agda:557-566) filters by followee.
	assert_json_ok(
		&request(&client, "private-timeline", &[&alice, "100"]),
		&timeline_body(&[]),
		true,
	);

	// After following bob both timelines pick his private post up, still
	// newest-first, and the personal timeline holds only his posts.
	assert_ok(&request(&client, "follow-user", &[&alice, "bob"]));
	assert_json_ok(
		&request(&client, "global-timeline", &[&alice, "100"]),
		&timeline_body(&[&last, &first, &private_id]),
		true,
	);
	assert_json_ok(
		&request(&client, "private-timeline", &[&alice, "100"]),
		&timeline_body(&[&private_id]),
		true,
	);
	// Following is different from authoring: alice's own posts are not in her
	// personal timeline unless she follows herself.
	assert_json_ok(
		&request(&client, "private-timeline", &[&alice, "1"]),
		&timeline_body(&[&private_id]),
		true,
	);

	// private-timeline always takes a token: a tokenless body is a
	// two-line action, so one line is malformed.
	assert_bad_request(&request(&client, "private-timeline", &["100"]));

	// An inactive session answers `expired` (Twitter.agda:464-468).
	let token = session(&login(&client, "alice", "pw"));
	assert_ok(&request(&client, "logout", &[&token]));
	assert_json_error(
		&request(&client, "private-timeline", &[&token, "100"]),
		401,
		SESSION_EXPIRED,
	);
	assert_json_error(
		&request(&client, "global-timeline", &[&token, "100"]),
		401,
		SESSION_EXPIRED,
	);
}

/* ---------- 7. escaping ---------- */

#[test]
fn json_escaping_and_utf8_content_length() {
	let client = harness();
	let token = account(&client, "alice", "pw");

	// `"` and `\` are escaped; nothing else in this text needs escaping.
	let quoted = publish(&client, &token, "he said \"hi\" \\ there");
	let escaped = "he said \\\"hi\\\" \\\\ there";
	assert_json_ok(
		&read_post(&client, None, &quoted),
		&tweet_body("alice", escaped, 0, &[]),
		true,
	);

	// Multi-byte text: `Content-Length` counts octets, not characters.
	let unicode = "héllo ☃";
	let post = publish(&client, &token, unicode);
	let expected = tweet_body("alice", unicode, 0, &[]);
	let resp = read_post(&client, None, &post);
	assert_json_ok(&resp, &expected, true);
	let length = resp.body.len().to_string();
	assert_eq!(resp.content_length.as_deref(), Some(length.as_str()));
	// "é" costs 2 octets and "☃" costs 3, so the two counts differ by 3.
	assert_eq!(expected.len() - expected.chars().count(), 3);
}

/* ---------- 8. expiry ---------- */

#[test]
fn expired_sessions_and_anonymous_unreadable_posts() {
	let (db, private_id) = seed_private_post("bob private");
	let client = harness_with(db);
	let alice = account(&client, "alice", "pw");
	let post = publish(&client, &alice, "alive");
	let doomed = publish(&client, &alice, "doomed");

	// logout (Twitter.agda:677-689) revokes the session.
	let token = session(&login(&client, "alice", "pw"));
	assert_ok(&request(&client, "logout", &[&token]));

	// failed-access (Twitter.agda:464-468) covers every session-carrying
	// command -- including a second logout.
	assert_json_error(
		&request(&client, "post-tweet", &[&token, "text"]),
		401,
		SESSION_EXPIRED,
	);
	assert_json_error(
		&read_post(&client, Some(&token), &post),
		401,
		SESSION_EXPIRED,
	);
	assert_json_error(&request(&client, "logout", &[&token]), 401, SESSION_EXPIRED);
	assert_json_error(
		&read_post(&client, Some(NEVER_ISSUED_TOKEN), &post),
		401,
		SESSION_EXPIRED,
	);
	assert_json_error(
		&request(&client, "global-timeline", &[NEVER_ISSUED_TOKEN, "10"]),
		401,
		SESSION_EXPIRED,
	);
	// The same `failed-access` covers the mutating commands, which leave the
	// world untouched; `doomed` is still alice's to delete below.
	assert_json_error(
		&request(&client, "delete-tweet", &[&token, &doomed]),
		401,
		SESSION_EXPIRED,
	);
	assert_json_error(
		&request(&client, "like-tweet", &[&token, &post]),
		401,
		SESSION_EXPIRED,
	);

	// `extract-sid (read-post nothing _)` is `nothing`, so `failed-access` is
	// vacuous for an anonymous read: an unreadable post answers `expired`,
	// never `denied`.
	assert_json_error(&read_post(&client, None, ABSENT_POST), 401, SESSION_EXPIRED);
	assert_json_error(&read_post(&client, None, &private_id), 401, SESSION_EXPIRED);
	assert_ok(&request(&client, "delete-tweet", &[&alice, &doomed]));
	assert_json_error(&read_post(&client, None, &doomed), 401, SESSION_EXPIRED);

	// A readable anonymous post still answers `returned-post`.
	assert_json_ok(
		&read_post(&client, None, &post),
		&tweet_body("alice", "alive", 0, &[]),
		true,
	);
}

/* ---------- 9. persistence ---------- */

#[test]
fn state_is_persisted_before_serving() {
	let dir = tempfile::tempdir().unwrap();
	let path = dir.path().join("formal-twitter.sqlite3");
	let url = path.to_str().unwrap();

	// First process: everything goes to the database before it is served.
	let client = harness_with(Db::new(url).unwrap());
	let token = account(&client, "carol", "pw");
	let post = publish(&client, &token, "persisted");
	assert_json_ok(
		&read_post(&client, None, &post),
		&tweet_body("carol", "persisted", 0, &[]),
		true,
	);
	drop(client);

	// A fresh server over the same file still knows the account and the post.
	let client = harness_with(Db::new(url).unwrap());
	assert_json_error(&login(&client, "carol", "wrong"), 401, LOGIN_FAILED);
	let token = session(&login(&client, "carol", "pw"));
	assert_json_ok(
		&read_post(&client, Some(&token), &post),
		&tweet_body("carol", "persisted", 0, &[]),
		true,
	);
	assert_json_ok(
		&request(&client, "global-timeline", &["10"]),
		&timeline_body(&[&post]),
		true,
	);
	drop(client);
}

/* ---------- 10. malformed requests ---------- */

#[test]
fn malformed_requests_are_bad_request() {
	let client = harness();
	let token = account(&client, "alice", "pw");
	let post = publish(&client, &token, "a post");

	// Wrong number of lines: `post-tweet` takes two, `post-reply` three,
	// `get-tweet` one or two, `signup` two.
	assert_bad_request(&request_raw(&client, "post-tweet", ""));
	assert_bad_request(&request(&client, "post-tweet", &[&token]));
	assert_bad_request(&request(&client, "post-tweet", &[&token, "text", "extra"]));
	assert_bad_request(&request(&client, "get-tweet", &[]));
	assert_bad_request(&request(&client, "signup", &["a", "b", "c"]));
	assert_bad_request(&request(&client, "post-reply", &[&token, "reply"]));

	// Missing the trailing CRLF, and bare LF line separators.
	assert_bad_request(&request_raw(
		&client,
		"post-tweet",
		&format!("{token}\r\ntext"),
	));
	assert_bad_request(&request_raw(
		&client,
		"post-tweet",
		&format!("{token}\ntext\n"),
	));

	// A token, id or length that is not a natural number.
	assert_bad_request(&request(&client, "post-tweet", &["token", "text"]));
	assert_bad_request(&request(&client, "get-tweet", &["not-a-number"]));
	assert_bad_request(&request(&client, "global-timeline", &["-1"]));
	assert_bad_request(&request(&client, "global-timeline", &["1_000"]));
	assert_bad_request(&request(&client, "like-tweet", &[&token, "1e3"]));
	assert_bad_request(&request(&client, "get-tweet", &[""]));

	// Unparseable: wider than 64 bits, so not a `Nat` the request can carry.
	assert_bad_request(&request(&client, "get-tweet", &["99999999999999999999999"]));
	assert_bad_request(&request(
		&client,
		"get-tweet",
		&[&token, "99999999999999999999999"],
	));
	assert_bad_request(&request(
		&client,
		"global-timeline",
		&["99999999999999999999999"],
	));

	// A timeline length is an unbounded `Nat` and `take n` is defined for every
	// `n` (Twitter.agda:557-585), so a length far past the 32-bit range is not
	// malformed: it returns the whole timeline. Alice follows only herself here,
	// which is enough for both timelines to hold her single post.
	assert_ok(&request(&client, "follow-user", &[&token, "alice"]));
	assert_json_ok(
		&request(&client, "global-timeline", &["4294967296"]),
		&timeline_body(&[&post]),
		true,
	);
	assert_json_ok(
		&request(&client, "private-timeline", &[&token, "4294967296"]),
		&timeline_body(&[&post]),
		true,
	);

	// Empty username, password and text are valid: `""` is a `String`.
	assert_ok(&signup(&client, "", ""));
	let empty = session(&login(&client, "", ""));
	let blank = publish(&client, &empty, "");
	assert_json_ok(
		&read_post(&client, None, &blank),
		&tweet_body("", "", 0, &[]),
		true,
	);
	// The earlier post is untouched.
	assert_json_ok(
		&read_post(&client, Some(&token), &post),
		&tweet_body("alice", "a post", 0, &[]),
		true,
	);
}
