//! The request bodies that `to-request` writes (`spec/Interface.agda:52-200`).
//!
//! Every request body is `unlines-crlf` of the action's arguments (Helpers.agda),
//! so it is a non-empty sequence of lines, each terminated by `\r\n`, with the
//! last line terminated like the others. Numbers are `show`n `Nat`s, i.e.
//! decimal digits only.
//!
//! Parsing never collects the whole body: the `\r\n`-separated fields are read
//! lazily, and only the `n` a body is allowed to have are ever touched.

/// The exactly-`N` fields of `body`, in order.
///
/// The body must end with a trailing `\r\n` and every field must be free of
/// `\r` and `\n`, so a missing terminator, a bare `\n` separator or a stray
/// `\r` all fail to parse. At most `N + 1` fields are ever read: the `N` kept
/// and one to detect a body that carries more fields than the action takes.
fn fields<const N: usize>(body: &str) -> Option<[&str; N]> {
	let rest = body.strip_suffix("\r\n")?;
	let mut fields = rest.split("\r\n");
	let mut out = [""; N];
	for field in &mut out {
		let next = fields.next()?;
		if next.contains(['\r', '\n']) {
			return None;
		}
		*field = next;
	}
	if fields.next().is_some() {
		return None;
	}
	Some(out)
}

/// A body of exactly one field.
pub fn one(body: &str) -> Option<&str> {
	Some(fields::<1>(body)?[0])
}

/// A body of exactly two fields.
pub fn two(body: &str) -> Option<(&str, &str)> {
	let [first, second] = fields::<2>(body)?;
	Some((first, second))
}

/// A body of exactly three fields.
pub fn three(body: &str) -> Option<(&str, &str, &str)> {
	let [first, second, third] = fields::<3>(body)?;
	Some((first, second, third))
}

/// True when `field` is a number as `to-request` writes it: one or more ASCII
/// decimal digits, with no sign, separator or exponent.
fn is_digits(field: &str) -> bool {
	!field.is_empty() && field.bytes().all(|byte| byte.is_ascii_digit())
}

/// A `TweetId` or `LoginToken` as `to-request` writes it: a `Nat` that fits in
/// a non-negative `i64` (`new-pid` and `new-sid` draw from `1..`).
///
/// Empty, signed or 64-bit-overflowing numerals fail, since none of them is the
/// `show` of a token or id this implementation can represent. Leading zeros are
/// accepted: `"007"` denotes the `Nat` 7, exactly as `show 7` would be read back.
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
