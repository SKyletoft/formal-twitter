// World model: mirrors spec/Twitter.agda (STATE TYPES / PREDICATES / TRANSITIONS).
//
// Records are encoded as structs, indexed fields as HashMaps,
// the follows relation as a set of pairs (default false),
// PostId/SessionId as monotonic integers (next_pid = max+1, next_sid = least unused).

use std::collections::{HashMap, HashSet};

#[derive(Copy, Clone, PartialEq)]
pub enum Visibility {
	Everyone,
	FollowersOnly,
}

#[derive(Copy, Clone, PartialEq)]
pub enum PostStatus {
	Live,
	Deleted,
}

#[derive(Clone, PartialEq)]
pub struct Account {
	pub password: String,
	pub default_visibility: Visibility,
}

#[derive(Clone, PartialEq)]
pub struct Post {
	pub author: String,
	pub text: String,
	pub visibility: Visibility,
	pub status: PostStatus,
	pub likes: Vec<String>,
	pub replies: Vec<i64>,
	pub parent: Option<i64>,
}

#[derive(Clone, PartialEq)]
pub enum SessionStatus {
	Unused,
	Active(String),
	Revoked,
}

#[derive(Clone, PartialEq)]
pub struct World {
	pub account_at: HashMap<String, Account>,
	pub session_at: HashMap<i64, SessionStatus>,
	pub post_at: HashMap<i64, Post>,
	pub follows: HashSet<(String, String)>,
	pub newest_first: Vec<i64>,
}

#[derive(Clone, PartialEq)]
pub enum Command {
	Publish(i64, String, Option<i64>),
	Delete(i64, i64),
	ReadPost(Option<i64>, i64),
	ReadPersonalTimeline(i64, i64),
	ReadGlobalTimeline(Option<i64>, i64),
	Authenticate(String, String),
	RevokeToken(i64),
	Register(String, String),
	Follow(i64, String),
	Unfollow(i64, String),
	Like(i64, i64),
	Unlike(i64, i64),
	TimePasses,
}

#[derive(Clone, PartialEq)]
pub enum Result {
	Success,
	Denied,
	Expired,
	LoginFailed,
	SignupFailed,
	IssuedSession(i64),
	CreatedPost(i64),
	ReturnedTimeline(Vec<i64>),
	ReturnedPost(String, String, usize, Vec<i64>),
}

// ---- PREDICATES / HELPERS (mirrors the Agda predicates) ----

pub fn valid_session(w: &World, sid: i64) -> Option<(Account, String)> {
	if let Some(SessionStatus::Active(user)) = w.session_at.get(&sid) {
		let u = user.to_string();
		if let Some(acc) = w.account_at.get(&u) {
			return Some((acc.clone(), u));
		}
	}
	return None;
}

pub fn can_have_valid_session(w: &World, sid: i64) -> bool {
	let vs = valid_session(w, sid);
	vs != None
}

pub fn next_pid(w: &World) -> i64 {
	let mut m: i64 = 0;
	for (pid, _) in w.post_at.iter() {
		if *pid > m {
			m = *pid;
		}
	}
	return m + 1;
}

pub fn next_sid(w: &World) -> i64 {
	let mut sid: i64 = 0;
	while w.session_at.contains_key(&sid) {
		sid = sid + 1;
	}
	return sid;
}

pub fn new_post(username: String, txt: String, acc: &Account) -> Post {
	return Post {
		author: username,
		text: txt,
		visibility: acc.default_visibility.clone(),
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: None,
	};
}

pub fn new_reply(username: String, txt: String, acc: &Account, ppid: i64, parent: &Post) -> Post {
	let vis = if parent.visibility == Visibility::Everyone {
		acc.default_visibility.clone()
	} else {
		Visibility::FollowersOnly
	};
	return Post {
		author: username,
		text: txt,
		visibility: vis,
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: Some(ppid),
	};
}

pub fn follows_post_author(w: &World, user: String, pid: i64) -> bool {
	if let Some(p) = w.post_at.get(&pid) {
		for (f, g) in w.follows.iter() {
			if *f == user && *g == p.author {
				return true;
			}
		}
	}
	return false;
}

pub fn can_read_post(w: &World, sid: i64, pid: i64) -> Option<Post> {
	if let Some((_acc, user)) = valid_session(w, sid) {
		if let Some(post) = w.post_at.get(&pid) {
			let ok = post.status == PostStatus::Live
				&& (post.visibility == Visibility::Everyone
					|| (post.visibility == Visibility::FollowersOnly
						&& follows_post_author(w, user, pid)));
			if ok {
				return Some(post.clone());
			}
		}
	}
	return None;
}

pub fn is_post_public(w: &World, pid: i64) -> Option<Post> {
	if let Some(p) = w.post_at.get(&pid) {
		if p.visibility == Visibility::Everyone && p.status == PostStatus::Live {
			return Some(p.clone());
		}
	}
	return None;
}

pub fn returned_post(p: &Post) -> Result {
	return Result::ReturnedPost(
		p.author.clone(),
		p.text.clone(),
		p.likes.len(),
		p.replies.clone(),
	);
}

pub fn take_n(xs: Vec<i64>, n: i64) -> Vec<i64> {
	let mut out: Vec<i64> = Vec::new();
	let k = if n <= 0 {
		0
	} else {
		let u = n as usize;
		if u < xs.len() { u } else { xs.len() }
	};
	for i in 0..k {
		out.push(xs[i]);
	}
	return out;
}

// ---- TRANSITIONS (mirrors the Step constructors in Twitter.agda) ----

pub fn step(w: World, cmd: Command) -> (World, Result) {
	match cmd {
		Command::Register(u, p) => {
			if w.account_at.contains_key(&u) {
				return (w.clone(), Result::SignupFailed);
			}
			let mut w2 = w.clone();
			w2.account_at.insert(
				u,
				Account {
					password: p,
					default_visibility: Visibility::Everyone,
				},
			);
			return (w2, Result::Success);
		}

		Command::Authenticate(u, p) => match w.account_at.get(&u) {
			Some(acc) => {
				if acc.password != p {
					return (w.clone(), Result::LoginFailed);
				}
				let sid = next_sid(&w);
				let mut w2 = w.clone();
				w2.session_at.insert(sid, SessionStatus::Active(u));
				return (w2, Result::IssuedSession(sid));
			}
			_ => return (w.clone(), Result::LoginFailed),
		},

		Command::Publish(sid, txt, None) => match valid_session(&w, sid) {
			Some((acc, user)) => {
				let pid = next_pid(&w);
				let mut w2 = w.clone();
				w2.post_at.insert(pid, new_post(user, txt, &acc));
				w2.newest_first.insert(0, pid);
				return (w2, Result::CreatedPost(pid));
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::Publish(sid, txt, Some(ppid)) => match valid_session(&w, sid) {
			Some((acc, user)) => match can_read_post(&w, sid, ppid) {
				Some(parent) => {
					let pid = next_pid(&w);
					let mut w2 = w.clone();
					w2.post_at
						.insert(pid, new_reply(user, txt, &acc, ppid, &parent));
					w2.post_at.get_mut(&ppid).unwrap().replies.insert(0, pid);
					w2.newest_first.insert(0, pid);
					return (w2, Result::CreatedPost(pid));
				}
				_ => return (w.clone(), Result::Denied),
			},
			_ => return (w.clone(), Result::Expired),
		},

		Command::Delete(sid, pid) => match valid_session(&w, sid) {
			Some((_acc, user)) => match w.post_at.get(&pid) {
				Some(post) => {
					if post.author == user {
						let mut w2 = w.clone();
						w2.post_at.get_mut(&pid).unwrap().status = PostStatus::Deleted;
						return (w2, Result::Success);
					}
					return (w.clone(), Result::Denied);
				}
				_ => return (w.clone(), Result::Denied),
			},
			_ => return (w.clone(), Result::Expired),
		},

		Command::ReadPost(msid, pid) => match msid {
			Some(sid) => match can_read_post(&w, sid, pid) {
				Some(p) => return (w.clone(), returned_post(&p)),
				_ => return (w.clone(), Result::Denied),
			},
			None => match is_post_public(&w, pid) {
				Some(p) => return (w.clone(), returned_post(&p)),
				_ => return (w.clone(), Result::Expired),
			},
		},

		Command::ReadPersonalTimeline(sid, n) => match valid_session(&w, sid) {
			Some((_acc, user)) => {
				let items = w
					.newest_first
					.iter()
					.filter(|pid| can_read_post(&w, sid, **pid).is_some())
					.filter(|pid| follows_post_author(&w, user.clone(), **pid))
					.map(|pid| *pid)
					.collect();
				return (w.clone(), Result::ReturnedTimeline(take_n(items, n)));
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::ReadGlobalTimeline(msid, n) => match msid {
			Some(sid) => {
				if can_have_valid_session(&w, sid) {
					let items = w
						.newest_first
						.iter()
						.filter(|pid| can_read_post(&w, sid, **pid).is_some())
						.map(|pid| *pid)
						.collect();
					return (w.clone(), Result::ReturnedTimeline(take_n(items, n)));
				}
				return (w.clone(), Result::Expired);
			}
			None => {
				let items = w
					.newest_first
					.iter()
					.filter(|pid| is_post_public(&w, **pid).is_some())
					.map(|pid| *pid)
					.collect();
				return (w.clone(), Result::ReturnedTimeline(take_n(items, n)));
			}
		},

		Command::RevokeToken(sid) => match w.session_at.get(&sid) {
			Some(SessionStatus::Active(_)) => {
				let mut w2 = w.clone();
				w2.session_at.insert(sid, SessionStatus::Revoked);
				return (w2, Result::Success);
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::Follow(sid, who) => match valid_session(&w, sid) {
			Some((_acc, follower)) => {
				let mut w2 = w.clone();
				w2.follows.insert((follower, who));
				return (w2, Result::Success);
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::Unfollow(sid, who) => match valid_session(&w, sid) {
			Some((_acc, follower)) => {
				let mut w2 = w.clone();
				w2.follows.remove(&(follower, who));
				return (w2, Result::Success);
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::Like(sid, pid) => match valid_session(&w, sid) {
			Some((_acc, user)) => {
				if can_read_post(&w, sid, pid).is_some() {
					let mut w2 = w.clone();
					if let Some(p) = w2.post_at.get_mut(&pid) {
						if !p.likes.contains(&user) {
							p.likes.push(user);
						}
					}
					return (w2, Result::Success);
				}
				return (w.clone(), Result::Denied);
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::Unlike(sid, pid) => match valid_session(&w, sid) {
			Some((_acc, user)) => {
				if can_read_post(&w, sid, pid).is_some() {
					let mut w2 = w.clone();
					if let Some(p) = w2.post_at.get_mut(&pid) {
						let mut idx = p.likes.len();
						for i in 0..p.likes.len() {
							if p.likes[i] == user {
								idx = i;
							}
						}
						if idx < p.likes.len() {
							p.likes.remove(idx);
						}
					}
					return (w2, Result::Success);
				}
				return (w.clone(), Result::Denied);
			}
			_ => return (w.clone(), Result::Expired),
		},

		Command::TimePasses => {
			let mut w2 = w.clone();
			let mut timed_out: Vec<i64> = Vec::new();
			for (sid, st) in w.session_at.iter() {
				match st {
					SessionStatus::Active(_) => timed_out.push(*sid),
					_ => (),
				}
			}
			for s in timed_out.iter() {
				w2.session_at.insert(*s, SessionStatus::Revoked);
			}
			return (w2, Result::Success);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn empty_world() -> World {
		World {
			account_at: HashMap::new(),
			session_at: HashMap::new(),
			post_at: HashMap::new(),
			follows: HashSet::new(),
			newest_first: Vec::new(),
		}
	}

	#[test]
	fn register_then_login_then_publish() {
		let w0 = empty_world();
		let (w1, r1) = step(
			w0,
			Command::Register("alice".to_string(), "s3cret".to_string()),
		);
		assert!(r1 == Result::Success, "register on a fresh world succeeds");
		assert!(w1.account_at.contains_key(&"alice".to_string()));

		let (w2, r2) = step(
			w1,
			Command::Authenticate("alice".to_string(), "s3cret".to_string()),
		);
		assert!(
			matches!(r2, Result::IssuedSession(_)),
			"login issues a session"
		);
		let sid = match r2 {
			Result::IssuedSession(s) => s,
			_ => 0,
		};

		let (w3, r3) = step(w2, Command::Publish(sid, "hello".to_string(), None));
		assert!(
			matches!(r3, Result::CreatedPost(_)),
			"publish creates a post"
		);
		assert!(w3.post_at.contains_key(&1), "the fresh pid is max+1");
	}

	#[test]
	fn login_requires_account_and_password() {
		let w = empty_world();
		let (_w1, r) = step(
			w,
			Command::Authenticate("ghost".to_string(), "x".to_string()),
		);
		assert!(r == Result::LoginFailed, "login on no account fails");
	}

	// ---- QuickCheck harness: forall worlds/commands ----

	struct Rng {
		s: u64,
	}

	fn next_u64(r: &mut Rng) -> u64 {
		r.s = r.s.wrapping_add(0x9E3779B97F4A7C15u64);
		let mut z = r.s;
		z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9u64);
		z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EBu64);
		z ^ (z >> 31)
	}

	fn users() -> Vec<String> {
		let mut v = Vec::new();
		v.push("alice".to_string());
		v.push("bob".to_string());
		v.push("carol".to_string());
		v
	}

	fn pick_user(r: &mut Rng) -> String {
		users()[(next_u64(r) % 3u64) as usize].clone()
	}

	fn pick_txt(r: &mut Rng) -> String {
		let c = next_u64(r) % 3u64;
		if c == 0u64 {
			"hi".to_string()
		} else if c == 1u64 {
			"yo".to_string()
		} else {
			"re".to_string()
		}
	}

	fn gen_sid(r: &mut Rng) -> i64 {
		(next_u64(r) % 4u64) as i64
	}

	fn gen_pid(r: &mut Rng) -> i64 {
		1i64 + (next_u64(r) % 4u64) as i64
	}

	fn pick_vis(r: &mut Rng) -> Visibility {
		if next_u64(r) % 2u64 == 0u64 {
			Visibility::Everyone
		} else {
			Visibility::FollowersOnly
		}
	}

	fn pick_status(r: &mut Rng) -> PostStatus {
		if next_u64(r) % 3u64 == 0u64 {
			PostStatus::Deleted
		} else {
			PostStatus::Live
		}
	}

	fn gen_world(r: &mut Rng) -> World {
		let mut w = World {
			account_at: HashMap::new(),
			session_at: HashMap::new(),
			post_at: HashMap::new(),
			follows: HashSet::new(),
			newest_first: Vec::new(),
		};
		for u in users().iter() {
			if next_u64(r) % 2u64 == 0u64 {
				w.account_at.insert(
					u.to_string(),
					Account {
						password: "pw".to_string(),
						default_visibility: pick_vis(r),
					},
				);
			}
		}
		let mut present_users: Vec<String> = Vec::new();
		for (u, _) in w.account_at.iter() {
			present_users.push(u.to_string());
		}
		for s in 0i64..4i64 {
			let c = next_u64(r) % 4u64;
			if c == 0u64 || c == 1u64 {
				if !present_users.is_empty() {
					let u =
						present_users[(next_u64(r) % present_users.len() as u64) as usize].clone();
					w.session_at.insert(s, SessionStatus::Active(u));
				}
			} else if c == 2u64 {
				w.session_at.insert(s, SessionStatus::Revoked);
			}
		}
		let mut present_pids: Vec<i64> = Vec::new();
		for p in 1i64..5i64 {
			if next_u64(r) % 5u64 != 4u64 {
				let author = if next_u64(r) % 3u64 == 0u64 && !present_users.is_empty() {
					present_users[(next_u64(r) % present_users.len() as u64) as usize].clone()
				} else {
					pick_user(r)
				};
				let mut parent: Option<i64> = None;
				if !present_pids.is_empty() && next_u64(r) % 2u64 == 0u64 {
					parent = Some(present_pids[(next_u64(r) % present_pids.len() as u64) as usize]);
				}
				let p0 = Post {
					author,
					text: pick_txt(r),
					visibility: pick_vis(r),
					status: pick_status(r),
					likes: Vec::new(),
					replies: Vec::new(),
					parent,
				};
				w.post_at.insert(p, p0);
				if let Some(pp) = parent {
					if let Some(q) = w.post_at.get_mut(&pp) {
						q.replies.insert(0, p);
					}
				}
				let pos = (next_u64(r) % (w.newest_first.len() as u64 + 1u64)) as usize;
				w.newest_first.insert(pos, p);
				present_pids.push(p);
			}
		}
		for u in users().iter() {
			for v in users().iter() {
				if u != v && next_u64(r) % 3u64 == 0u64 {
					w.follows.insert((u.to_string(), v.to_string()));
				}
			}
		}
		w
	}

	fn vec_cons(x: i64, xs: &[i64]) -> Vec<i64> {
		let mut out: Vec<i64> = Vec::new();
		out.push(x);
		for y in xs.iter() {
			out.push(*y);
		}
		out
	}

	#[test]
	fn qc_publish_toplevel() {
		let mut r = Rng { s: 1u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let txt = pick_txt(&mut r);
			let (w2, res) = step(w.clone(), Command::Publish(sid, txt.clone(), None));
			match valid_session(&w, sid) {
				Some((acc, user)) => {
					let pid = next_pid(&w);
					assert!(res == Result::CreatedPost(pid), "successful-post");
					assert!(!w.post_at.contains_key(&pid), "was-absent");
					assert!(
						w2.post_at.get(&pid) == Some(&new_post(user, txt, &acc)),
						"is-present"
					);
					assert!(
						w2.newest_first == vec_cons(pid, &w.newest_first),
						"newest-first"
					);
					assert!(
						w2.session_at == w.session_at
							&& w2.account_at == w.account_at
							&& w2.follows == w.follows,
						"everything else unchanged"
					);
					for (k, v) in w.post_at.iter() {
						if *k != pid {
							assert!(w2.post_at.get(k) == Some(&v.clone()));
						}
					}
				}
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_publish_reply() {
		let mut r = Rng { s: 2u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let txt = pick_txt(&mut r);
			let ppid = gen_pid(&mut r);
			let (w2, res) = step(w.clone(), Command::Publish(sid, txt.clone(), Some(ppid)));
			match valid_session(&w, sid) {
				Some((acc, user)) => match can_read_post(&w, sid, ppid) {
					Some(parent) => {
						let pid = next_pid(&w);
						assert!(res == Result::CreatedPost(pid), "successful-reply");
						assert!(pid != ppid, "reply pid differs from parent");
						assert!(
							w2.post_at.get(&pid)
								== Some(&new_reply(user, txt, &acc, ppid, &parent)),
							"post-is-new"
						);
						let mut pp = parent.clone();
						pp.replies.insert(0, pid);
						assert!(w2.post_at.get(&ppid) == Some(&pp), "parent gains reply");
						assert!(w2.newest_first == vec_cons(pid, &w.newest_first));
						for (k, v) in w.post_at.iter() {
							if *k != pid && *k != ppid {
								assert!(w2.post_at.get(k) == Some(&v.clone()));
							}
						}
						assert!(
							w2.session_at == w.session_at
								&& w2.account_at == w.account_at
								&& w2.follows == w.follows
						);
					}
					_ => {
						assert!(res == Result::Denied, "failed-reply");
						assert!(w2 == w);
					}
				},
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_delete() {
		let mut r = Rng { s: 3u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let pid = gen_pid(&mut r);
			let (w2, res) = step(w.clone(), Command::Delete(sid, pid));
			match valid_session(&w, sid) {
				Some((_acc, user)) => match w.post_at.get(&pid) {
					Some(post) => {
						if post.author == user {
							assert!(res == Result::Success, "delete-post");
							let mut q = post.clone();
							q.status = PostStatus::Deleted;
							assert!(w2.post_at.get(&pid) == Some(&q));
							assert!(
								w2.session_at == w.session_at
									&& w2.account_at == w.account_at
									&& w2.follows == w.follows && w2.newest_first == w.newest_first
							);
							for (k, v) in w.post_at.iter() {
								if *k != pid {
									assert!(w2.post_at.get(k) == Some(&v.clone()));
								}
							}
						} else {
							assert!(res == Result::Denied, "failed-delete-not-author");
							assert!(w2 == w);
						}
					}
					_ => {
						assert!(res == Result::Denied, "failed-delete-non-existant-post");
						assert!(w2 == w);
					}
				},
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_read_post() {
		let mut r = Rng { s: 4u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let pid = gen_pid(&mut r);
			let msid = if next_u64(&mut r) % 2u64 == 0u64 {
				Some(gen_sid(&mut r))
			} else {
				None
			};
			let (w2, res) = step(w.clone(), Command::ReadPost(msid, pid));
			assert!(w2 == w, "read does not change the world");
			match msid {
				Some(sid) => match can_read_post(&w, sid, pid) {
					Some(p) => assert!(res == returned_post(&p), "read-post-logged-in"),
					_ => assert!(res == Result::Denied, "cant-read-post"),
				},
				None => match is_post_public(&w, pid) {
					Some(p) => assert!(res == returned_post(&p), "read-post-anonymously"),
					_ => assert!(res == Result::Expired, "cant-read-post-anonymously"),
				},
			}
		}
	}

	#[test]
	fn qc_personal_timeline() {
		let mut r = Rng { s: 5u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let n = (next_u64(&mut r) % 6u64) as i64;
			let (w2, res) = step(w.clone(), Command::ReadPersonalTimeline(sid, n));
			match valid_session(&w, sid) {
				Some((_acc, user)) => {
					assert!(w2 == w);
					let items = w
						.newest_first
						.iter()
						.filter(|pid| can_read_post(&w, sid, **pid).is_some())
						.filter(|pid| follows_post_author(&w, user.clone(), **pid))
						.map(|pid| *pid)
						.collect();
					assert!(
						res == Result::ReturnedTimeline(take_n(items, n)),
						"get-personal-timeline"
					);
				}
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_global_timeline() {
		let mut r = Rng { s: 6u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let msid = if next_u64(&mut r) % 2u64 == 0u64 {
				Some(gen_sid(&mut r))
			} else {
				None
			};
			let n = (next_u64(&mut r) % 6u64) as i64;
			let (w2, res) = step(w.clone(), Command::ReadGlobalTimeline(msid, n));
			assert!(w2 == w);
			match msid {
				Some(sid) => {
					if can_have_valid_session(&w, sid) {
						let items = w
							.newest_first
							.iter()
							.filter(|pid| can_read_post(&w, sid, **pid).is_some())
							.map(|pid| *pid)
							.collect();
						assert!(
							res == Result::ReturnedTimeline(take_n(items, n)),
							"get-private-global-timeline"
						);
					} else {
						assert!(res == Result::Expired, "failed-access");
					}
				}
				None => {
					let items = w
						.newest_first
						.iter()
						.filter(|pid| is_post_public(&w, **pid).is_some())
						.map(|pid| *pid)
						.collect();
					assert!(
						res == Result::ReturnedTimeline(take_n(items, n)),
						"get-public-global-timeline"
					);
				}
			}
		}
	}

	#[test]
	fn qc_authenticate() {
		let mut r = Rng { s: 7u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let u = pick_user(&mut r);
			let p = if next_u64(&mut r) % 2u64 == 0u64 {
				"pw".to_string()
			} else {
				"bad".to_string()
			};
			let (w2, res) = step(w.clone(), Command::Authenticate(u.clone(), p.clone()));
			match w.account_at.get(&u) {
				None => {
					assert!(res == Result::LoginFailed, "failed-login-1");
					assert!(w2 == w);
				}
				Some(acc) => {
					if acc.password != p {
						assert!(res == Result::LoginFailed, "failed-login-2");
						assert!(w2 == w);
					} else {
						let sid = next_sid(&w);
						match res {
							Result::IssuedSession(s) => {
								assert!(s == sid, "login issues the least unused sid")
							}
							_ => assert!(false, "login must issue a session"),
						}
						let mut expect = w.session_at.clone();
						expect.insert(sid, SessionStatus::Active(u));
						assert!(w2.session_at == expect, "login constructor");
						assert!(
							w2.account_at == w.account_at
								&& w2.post_at == w.post_at
								&& w2.follows == w.follows
								&& w2.newest_first == w.newest_first
						);
					}
				}
			}
		}
	}

	#[test]
	fn qc_revoke_token() {
		let mut r = Rng { s: 8u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let (w2, res) = step(w.clone(), Command::RevokeToken(sid));
			match w.session_at.get(&sid) {
				Some(SessionStatus::Active(_)) => {
					assert!(res == Result::Success, "logout");
					let mut expect = w.session_at.clone();
					expect.insert(sid, SessionStatus::Revoked);
					assert!(w2.session_at == expect);
					assert!(
						w2.account_at == w.account_at
							&& w2.post_at == w.post_at
							&& w2.follows == w.follows
							&& w2.newest_first == w.newest_first
					);
				}
				_ => {
					assert!(res == Result::Expired, "revoke needs an active session");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_register() {
		let mut r = Rng { s: 9u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let u = pick_user(&mut r);
			let p = pick_txt(&mut r);
			let (w2, res) = step(w.clone(), Command::Register(u.clone(), p.clone()));
			if w.account_at.contains_key(&u) {
				assert!(res == Result::SignupFailed, "failed-create-account");
				assert!(w2 == w);
			} else {
				assert!(res == Result::Success, "create-account");
				let mut expect = w.account_at.clone();
				expect.insert(
					u,
					Account {
						password: p,
						default_visibility: Visibility::Everyone,
					},
				);
				assert!(w2.account_at == expect);
				assert!(
					w2.session_at == w.session_at
						&& w2.post_at == w.post_at
						&& w2.follows == w.follows
						&& w2.newest_first == w.newest_first
				);
			}
		}
	}

	#[test]
	fn qc_follow_unfollow() {
		let mut r = Rng { s: 10u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let who = pick_user(&mut r);
			let is_follow = next_u64(&mut r) % 2u64 == 0u64;
			let cmd = if is_follow {
				Command::Follow(sid, who.clone())
			} else {
				Command::Unfollow(sid, who.clone())
			};
			let (w2, res) = step(w.clone(), cmd);
			match valid_session(&w, sid) {
				Some((_acc, follower)) => {
					assert!(res == Result::Success, "follow-user / unfollow-user");
					assert!(
						w2.account_at == w.account_at
							&& w2.session_at == w.session_at
							&& w2.post_at == w.post_at
							&& w2.newest_first == w.newest_first
					);
					let mut expect = w.follows.clone();
					let key = (follower, who);
					if is_follow {
						expect.insert(key);
					} else {
						expect.remove(&key);
					}
					assert!(w2.follows == expect);
				}
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_like_unlike() {
		let mut r = Rng { s: 11u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let sid = gen_sid(&mut r);
			let pid = gen_pid(&mut r);
			let like = next_u64(&mut r) % 2u64 == 0u64;
			let cmd = if like {
				Command::Like(sid, pid)
			} else {
				Command::Unlike(sid, pid)
			};
			let (w2, res) = step(w.clone(), cmd);
			match valid_session(&w, sid) {
				Some((_acc, user)) => match can_read_post(&w, sid, pid) {
					Some(post) => {
						assert!(res == Result::Success, "like-post / unlike-post");
						assert!(
							w2.session_at == w.session_at
								&& w2.account_at == w.account_at
								&& w2.follows == w.follows
								&& w2.newest_first == w.newest_first
						);
						for (k, v) in w.post_at.iter() {
							if *k != pid {
								assert!(w2.post_at.get(k) == Some(&v.clone()));
							}
						}
						let q = w2.post_at.get(&pid).unwrap();
						assert!(
							q.author == post.author
								&& q.text == post.text && q.visibility == post.visibility
								&& q.status == post.status
								&& q.replies == post.replies
								&& q.parent == post.parent,
							"rest of post unchanged"
						);
						if like {
							assert!(q.likes.contains(&user), "user liked");
							for u in post.likes.iter() {
								assert!(q.likes.contains(u));
							}
							assert!(
								q.likes.len() == post.likes.len()
									|| q.likes.len() == post.likes.len() + 1
							);
						} else {
							assert!(!q.likes.contains(&user), "user unliked");
							for u in post.likes.iter() {
								if *u != user {
									assert!(q.likes.contains(u));
								}
							}
							assert!(
								q.likes.len() + (if post.likes.contains(&user) { 1 } else { 0 })
									== post.likes.len()
							);
						}
					}
					_ => {
						assert!(
							res == Result::Denied,
							"failed-like-post / failed-unlike-post"
						);
						assert!(w2 == w);
					}
				},
				_ => {
					assert!(res == Result::Expired, "failed-access");
					assert!(w2 == w);
				}
			}
		}
	}

	#[test]
	fn qc_time_passes() {
		let mut r = Rng { s: 12u64 };
		for _ in 0..300 {
			let w = gen_world(&mut r);
			let (w2, res) = step(w.clone(), Command::TimePasses);
			assert!(res == Result::Success, "session-timeout");
			assert!(
				w2.account_at == w.account_at
					&& w2.post_at == w.post_at
					&& w2.follows == w.follows
					&& w2.newest_first == w.newest_first
			);
			for (sid, st) in w.session_at.iter() {
				match st {
					SessionStatus::Active(_) => assert!(
						w2.session_at.get(sid) == Some(&SessionStatus::Revoked),
						"timeout revokes"
					),
					_ => assert!(
						w2.session_at.get(sid) == Some(&st.clone()),
						"other sessions unchanged"
					),
				}
			}
		}
	}
}
