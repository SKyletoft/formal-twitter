//! The executable server layer: glue between the model, the wire codec and rocket.
//!
//! Part 1 of this layer is pure helpers: a std-only IMF `Date` header
//! (`http_date`), the from-output map of spec/Interface.agda taking a model
//! `Result` to a wire `ApiResponse` (`to_output`), cryptographic `u64`
//! randomness from `/dev/urandom` (`random_u64`) and the spec's fresh-id sampler
//! (`sample_id`).  `to_http` lifts a rendered `WireResponse` into a rocket
//! `Response`, headers in the order the spec fixes.  The routes, state and
//! launch come in part 2; nothing here talks to a server or to the DB.
use formal_twitter::model::{Result, World};
use formal_twitter::wire::{ApiResponse, WireResponse};
use rocket::Response;
use rocket::http::{Header, Status};
use std::io::Cursor;
use std::time::{SystemTime, UNIX_EPOCH};

#[doc = "Two-digit decimal, zero-padded (as the IMF-date needs dd, HH, mm, ss)."]
fn two(v: u64) -> String {
	if v < 10 {
		"0".to_string() + &v.to_string()
	} else {
		v.to_string()
	}
}

#[doc = "Gregorian leap-year test."]
fn leap(y: u64) -> bool {
	y.is_multiple_of(4) && (!y.is_multiple_of(100) || y.is_multiple_of(400))
}

#[doc = "The current moment rendered as an IMF date: \"Thu, 01 Jan 1970 00:00:00 GMT\"."]
pub fn http_date() -> String {
	let secs: u64 = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.unwrap_or_default()
		.as_secs();
	let day: u64 = secs / 86_400;
	let rest: u64 = secs % 86_400;
	let hour: u64 = rest / 3_600;
	let minute: u64 = (rest % 3_600) / 60;
	let second: u64 = rest % 60;
	let mut year: u64 = 1_970;
	let mut year_start: u64 = 0;
	loop {
		let len: u64 = if leap(year) { 366 } else { 365 };
		if day - year_start < len {
			break;
		}
		year += 1;
		year_start += len;
	}
	let month_len: [u64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
	let month_names: [&str; 12] = [
		"Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
	];
	let day_of_year: u64 = day - year_start;
	let mut month: u64 = 0;
	let mut month_start: u64 = 0;
	loop {
		let len: u64 = month_len[month as usize] + (if month == 1 && leap(year) { 1 } else { 0 });
		if day_of_year - month_start < len {
			break;
		}
		month += 1;
		month_start += len;
	}
	let day_of_month: u64 = day_of_year - month_start + 1;
	// 1970-01-01 (day 0) was a Thursday, so day counts step forward from Thu.
	let weekdays: [&str; 7] = ["Thu", "Fri", "Sat", "Sun", "Mon", "Tue", "Wed"];
	format!(
		"{}, {} {} {} {}:{}:{} GMT",
		weekdays[(day % 7) as usize],
		two(day_of_month),
		month_names[month as usize],
		year,
		two(hour),
		two(minute),
		two(second)
	)
}

#[doc = "from-output of Interface.agda: a model Result rendered as a wire ApiResponse."]
pub fn to_output(r: Result) -> ApiResponse {
	match r {
		Result::Success => ApiResponse::Ok,
		Result::Denied => ApiResponse::PermissionError,
		Result::Expired => ApiResponse::OutdatedLoginToken,
		Result::LoginFailed => ApiResponse::LoginError,
		Result::SignupFailed => ApiResponse::SignupError,
		Result::ReturnedTimeline(ids) => ApiResponse::Timeline(ids),
		Result::IssuedSession(sid) => ApiResponse::SessionToken(sid),
		Result::CreatedPost(pid) => ApiResponse::TweetId(pid),
		Result::ReturnedPost(text, author, pid, ats) => ApiResponse::Tweet(text, author, pid, ats),
	}
}

#[doc = "Eight bytes read from /dev/urandom as a big-endian u64; zero on any failure."]
pub fn random_u64() -> u64 {
	// Qualified std paths keep the top-level import list minimal.
	match std::fs::File::open("/dev/urandom") {
		Err(_) => 0,
		Ok(mut file) => {
			let mut bytes: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
			if std::io::Read::read_exact(&mut file, &mut bytes).is_err() {
				0
			} else {
				u64::from_be_bytes(bytes)
			}
		}
	}
}

#[doc = "The spec's fresh-id sampler: loop until a nonzero id is free."]
pub fn sample_id(w: World, taken: fn(&World, u64) -> bool) -> u64 {
	loop {
		let r = random_u64();
		if r != 0 && !taken(&w, r) {
			return r;
		}
	}
}

#[doc = "Lift a rendered WireResponse into a rocket Response, headers in the order the spec fixes."]
pub fn to_http(reply: WireResponse) -> Response<'static> {
	// Fold the spec's wire headers, in order, onto an empty rocket Response.
	let mut built = Response::build();
	for (name, value) in reply.headers {
		built.header(Header::new(name, value));
	}
	// All respond codes are valid; None falls back to Status::new(code).
	match Status::from_code(reply.status_code) {
		Some(status) => built.status(status),
		None => built.status(Status::new(reply.status_code)),
	};
	// The body is a fixed-size cursor over the rendered octets.
	built.sized_body(reply.body.len(), Cursor::new(reply.body));
	built.finalize()
}

#[doc = "Placeholder entry point; the server (state, routes, launch) comes in part 2."]
fn main() {
	println!("formal-twitter: server pending (task T4b-2)")
}
