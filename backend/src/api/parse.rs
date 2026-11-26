//! The request bodies that `to-request` writes (`spec/Interface.agda:52-200`).
//!
//! Every request body is `unlines-crlf` of the action's arguments (Helpers.agda),
//! so it is a non-empty sequence of lines, each terminated by `\r\n`, with the
//! last line terminated like the others. Numbers are `show`n `Nat`s, i.e.
//! decimal digits only.

/// Splits a request body into its lines.
///
/// The body must end with a trailing `\r\n` and every line must be free of
/// `\r` and `\n`, so a missing terminator, a bare `\n` separator or a stray
/// `\r` all fail to parse.
pub fn lines(body: &str) -> Option<Vec<&str>> {
	let rest = body.strip_suffix("\r\n")?;
	let lines: Vec<&str> = rest.split("\r\n").collect();
	if lines.iter().any(|line| line.contains(['\r', '\n'])) {
		return None;
	}
	Some(lines)
}

/// A body of exactly one line.
pub fn one(body: &str) -> Option<&str> {
	match lines(body)?.as_slice() {
		&[line] => Some(line),
		_ => None,
	}
}

/// A body of exactly two lines.
pub fn two(body: &str) -> Option<(&str, &str)> {
	match lines(body)?.as_slice() {
		&[first, second] => Some((first, second)),
		_ => None,
	}
}

/// A body of exactly three lines.
pub fn three(body: &str) -> Option<(&str, &str, &str)> {
	match lines(body)?.as_slice() {
		&[first, second, third] => Some((first, second, third)),
		_ => None,
	}
}

/// True when `field` is a number as `to-request` writes it: one or more ASCII
/// decimal digits, with no sign, separator or exponent.
fn is_digits(field: &str) -> bool {
	!field.is_empty() && field.bytes().all(|byte| byte.is_ascii_digit())
}

/// A `TweetId` or `LoginToken` as `to-request` writes it: a `Nat` that fits in
/// a non-negative `i64` (`new-pid` and `new-sid` draw from `1..`).
///
/// Empty, signed, padded or 64-bit-overflowing numerals fail, since none of
/// them is the `show` of a token or id this implementation can represent.
pub fn natural(field: &str) -> Option<i64> {
	if !is_digits(field) {
		return None;
	}
	field.parse().ok()
}

/// A timeline length: an unbounded `Nat` (`take n` is total, Twitter.agda:557-585).
///
/// Parsed as 64 bits and clamped to `u32::MAX`, the widest length the engine
/// takes; a length beyond 64 bits is malformed.
pub fn length(field: &str) -> Option<u32> {
	if !is_digits(field) {
		return None;
	}
	let n: u64 = field.parse().ok()?;
	Some(n.min(u64::from(u32::MAX)) as u32)
}
