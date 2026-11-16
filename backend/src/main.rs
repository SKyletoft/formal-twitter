// main.rs - Rocket server implementing spec/Interface.agda over the world
// model, persisting everything through Diesel+SQLite.
//
// Request encoding (from to-request, adapted for browsers: GET args travel
// as query params since fetch cannot send a GET body):
//   POST /api/login           body: username \n passwd \n
//   POST /api/signup          body: username \n passwd \n
//   POST /api/post-tweet      body: token \n text \n
//   POST /api/post-reply      body: token \n text \n parent-id \n
//   POST /api/delete-tweet    body: token \n tweet-id \n
//   POST /api/like-tweet      body: token \n tweet-id \n
//   POST /api/unlike-tweet    body: token \n tweet-id \n
//   POST /api/follow-user     body: token \n username \n
//   POST /api/unfollow-user   body: token \n username \n
//   POST /api/logout          body: token \n
//   GET  /api/get-tweet       ?id= | ?token=&id=
//   GET  /api/global-timeline ?len= | ?token=&len=
//   GET  /api/private-timeline ?token=&len=
//
// Responses follow to-response exactly (single-quoted JSON bodies).
// Every request commits the new world to SQLite before the response is
// served, and appends a timestamped row to the log (viewable at /log).
// / dumps the current world as plaintext.

mod db;
mod world;

use db::*;
use world::*;

use diesel::Connection;
use diesel::SqliteConnection;
use rocket::Build;
use rocket::Rocket;
use rocket::get;
use rocket::http::Status;
use rocket::launch;
use rocket::post;
use rocket::request::Request;
use rocket::response::Responder;
use rocket::response::Response;
use rocket::routes;
use std::io::Cursor;
use std::sync::Mutex;

const DB_PATH: &str = "twitter.db";
const FRONTEND: &str = "/home/u3836/git/formal-twitter/frontend";

type Db = Mutex<SqliteConnection>;

// ---- helpers ----

pub fn arg(ls: &[String], i: usize) -> String {
	if i < ls.len() {
		ls[i].clone()
	} else {
		"".to_string()
	}
}

pub fn argi(ls: &[String], i: usize) -> i64 {
	parse_i64(arg(&ls, i))
}

pub fn parse_i64(s: String) -> i64 {
	s.parse::<i64>().unwrap_or(-1)
}

pub fn join_lines(v: &[String]) -> String {
	v.join("\n")
}

pub fn join_rest(ls: &[String], from: usize, to: usize) -> String {
	if from < to {
		join_lines(&ls[from..to])
	} else {
		"".to_string()
	}
}

pub fn split_lines(s: String) -> Vec<String> {
	let parts = s
		.split('\n')
		.map(|x| x.to_string())
		.collect::<Vec<String>>();
	if !parts.is_empty() && parts[parts.len() - 1] == "".to_string() {
		parts[..parts.len() - 1].to_vec()
	} else {
		parts
	}
}

pub fn join_ids(xs: Vec<i64>) -> String {
	xs.into_iter()
		.map(|x| x.to_string())
		.collect::<Vec<String>>()
		.join(", ")
}

pub fn to_http(r: Result) -> Http {
	let (code, body) = match r {
		Result::Success => (Status::Ok, None),
		Result::Denied => (
			Status::Forbidden,
			Some("{'error': 'access_denied'}".to_string()),
		),
		Result::Expired => (
			Status::Unauthorized,
			Some("{'error': 'session_expired'}".to_string()),
		),
		Result::LoginFailed => (
			Status::Unauthorized,
			Some("{'error': 'login_failed'}".to_string()),
		),
		Result::SignupFailed => (
			Status::BadRequest,
			Some("{'error': 'signup_failed'}".to_string()),
		),
		Result::IssuedSession(sid) => (Status::Ok, Some(format!("{{'session_token': '{}'}}", sid))),
		Result::CreatedPost(pid) => (Status::Ok, Some(format!("{{'tweet_id': '{}'}}", pid))),
		Result::ReturnedTimeline(xs) => (
			Status::Ok,
			Some(format!("{{'timeline': [{}]}}", join_ids(xs))),
		),
		Result::ReturnedPost(a, t, l, rs) => (
			Status::Ok,
			Some(format!(
				"{{'username': '{}', 'text': '{}', 'likes': {}, 'replies': [{}]}}",
				a,
				t,
				l,
				join_ids(rs)
			)),
		),
	};

	let mut rb = Response::build();
	let b0 = rb.status(code);
	let b = match body {
		Some(s) => b0
			.raw_header("Content-Type", "application/json")
			.sized_body(s.len(), Cursor::new(s)),
		None => b0,
	};
	Http { resp: b.finalize() }
}

// Apply one Command: load world, step, commit, log, render response.
pub fn run(conn: &mut SqliteConnection, cmd: Command, desc: String) -> Http {
	let w = load_world(conn);
	let (w2, r) = step(w, cmd);
	save_world(conn, &w2);
	append_log(conn, desc);
	to_http(r)
}

pub fn read_frontend(name: String) -> String {
	String::from_utf8(std::fs::read(format!("{}/{}", FRONTEND, name)).unwrap()).unwrap()
}

// Build a Response with an explicit content type and body (avoids generic
// rocket content wrappers).
pub fn send_content(ctype: String, s: String) -> Http {
	Http {
		resp: Response::build()
			.raw_header("Content-Type", ctype)
			.sized_body(s.len(), Cursor::new(s))
			.finalize(),
	}
}

// Response is not itself a Responder in Rocket 0.5; route handlers return this
// wrapper, which hands back the prebuilt Response.
pub struct Http {
	pub resp: Response<'static>,
}

impl<'r> Responder<'r, 'static> for Http {
	fn respond_to(self, _: &'r Request<'_>) -> rocket::response::Result<'static> {
		Ok(self.resp)
	}
}

// ---- API routes ----

#[post("/api/login", data = "<body>")]
pub fn api_login(body: String) -> Http {
	let ls = split_lines(body);
	let username = arg(&ls, 0);
	let passwd = arg(&ls, 1);
	let desc = format!("login {}", username);
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Authenticate(username, passwd), desc)
}

#[post("/api/signup", data = "<body>")]
pub fn api_signup(body: String) -> Http {
	let ls = split_lines(body);
	let username = arg(&ls, 0);
	let passwd = arg(&ls, 1);
	let desc = format!("signup {}", username);
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Register(username, passwd), desc)
}

#[post("/api/post-tweet", data = "<body>")]
pub fn api_post_tweet(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let text = join_rest(&ls, 1, ls.len());
	let desc = format!("post-tweet {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Publish(token, text, None), desc)
}

#[post("/api/post-reply", data = "<body>")]
pub fn api_post_reply(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let last = if ls.len() > 0 { ls.len() - 1 } else { 0 };
	let text = join_rest(&ls, 1, last);
	let parent = argi(&ls, last);
	let desc = format!("post-reply {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Publish(token, text, Some(parent)), desc)
}

#[post("/api/delete-tweet", data = "<body>")]
pub fn api_delete_tweet(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let tweet_id = argi(&ls, 1);
	let desc = format!("delete-tweet {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Delete(token, tweet_id), desc)
}

#[post("/api/like-tweet", data = "<body>")]
pub fn api_like_tweet(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let tweet_id = argi(&ls, 1);
	let desc = format!("like-tweet {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Like(token, tweet_id), desc)
}

#[post("/api/unlike-tweet", data = "<body>")]
pub fn api_unlike_tweet(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let tweet_id = argi(&ls, 1);
	let desc = format!("unlike-tweet {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Unlike(token, tweet_id), desc)
}

#[post("/api/follow-user", data = "<body>")]
pub fn api_follow_user(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let username = join_rest(&ls, 1, ls.len());
	let desc = format!("follow-user {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Follow(token, username), desc)
}

#[post("/api/unfollow-user", data = "<body>")]
pub fn api_unfollow_user(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let username = join_rest(&ls, 1, ls.len());
	let desc = format!("unfollow-user {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::Unfollow(token, username), desc)
}

#[post("/api/logout", data = "<body>")]
pub fn api_logout(body: String) -> Http {
	let ls = split_lines(body);
	let token = argi(&ls, 0);
	let desc = format!("logout {}", arg(&ls, 0));
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(&mut conn, Command::RevokeToken(token), desc)
}

#[get("/api/get-tweet?<token>&<id>")]
pub fn get_tweet(token: String, id: String) -> Http {
	let desc = format!("get-tweet {}", token);
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	let msid = if token == "" {
		None
	} else {
		Some(parse_i64(token))
	};
	run(&mut conn, Command::ReadPost(msid, parse_i64(id)), desc)
}

#[get("/api/global-timeline?<token>&<len>")]
pub fn global_timeline(token: String, len: String) -> Http {
	let desc = format!("global-timeline {}", token);
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	let msid = if token == "" {
		None
	} else {
		Some(parse_i64(token))
	};
	run(
		&mut conn,
		Command::ReadGlobalTimeline(msid, parse_i64(len)),
		desc,
	)
}

#[get("/api/private-timeline?<token>&<len>")]
pub fn private_timeline(token: String, len: String) -> Http {
	let desc = format!("private-timeline {}", token);
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	run(
		&mut conn,
		Command::ReadPersonalTimeline(parse_i64(token), parse_i64(len)),
		desc,
	)
}

// ---- dumps ----

#[get("/raw")]
pub fn raw() -> Http {
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	send_content("text/plain".to_string(), raw_dump(&load_world(&mut conn)))
}

#[get("/log")]
pub fn request_log() -> Http {
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	let mut parts = Vec::new();
	for (req, ts) in read_log(&mut conn) {
		parts.push(format!("{} @ {}", req, ts));
	}
	send_content("text/plain".to_string(), parts.join("\n"))
}

// ---- static frontend ----

#[get("/")]
pub fn index() -> Http {
	send_content(
		"text/html".to_string(),
		read_frontend("index.html".to_string()),
	)
}

#[get("/style.css")]
pub fn style() -> Http {
	send_content(
		"text/css".to_string(),
		read_frontend("style.css".to_string()),
	)
}

#[get("/app.js")]
pub fn app_js() -> Http {
	send_content(
		"text/javascript".to_string(),
		read_frontend("app.js".to_string()),
	)
}

// ---- launch ----

#[launch]
pub fn rocket() -> Rocket<Build> {
	let mut conn = SqliteConnection::establish(DB_PATH).unwrap();
	init(&mut conn);
	rocket::build().mount(
		"/",
		routes![
			api_login,
			api_signup,
			api_post_tweet,
			api_post_reply,
			api_delete_tweet,
			api_like_tweet,
			api_unlike_tweet,
			api_follow_user,
			api_unfollow_user,
			api_logout,
			get_tweet,
			global_timeline,
			private_timeline,
			raw,
			request_log,
			index,
			style,
			app_js,
		],
	)
}
