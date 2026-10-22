//! The state machine of the public API, a translation of the
//! `event-loop` in spec/Twitter.agda. All responses are `Response`
//! constructors; the wire format is applied in response.rs.

use std::collections::HashMap;

use crate::response::Response;

pub type UserId = u64;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Privacy {
	Everyone,
	// No action currently produces these; Like/DeleteTweet are still
	// commented out in the spec.
	#[allow(dead_code)]
	FollowersOnly,
	#[allow(dead_code)]
	Removed,
}

#[derive(Debug)]
pub struct User {
	pub name: String,
	pub privacy: Privacy,
	// `follows` is managed in the Agda spec but no follow action exists
	// yet (`delete-tweet`/`logout`-style commented-out constructors).
	#[allow(dead_code)]
	pub follows: Vec<UserId>,
	pub followers: Vec<UserId>,
}

#[derive(Debug)]
pub struct Tweet {
	pub id: u64,
	pub poster: UserId,
	pub text: String,
	pub visibility: Privacy,
	pub replies: Vec<u64>,
	pub liked_by: Vec<UserId>,
}

#[derive(Debug)]
pub struct ServerState {
	users: Vec<User>,
	tweets: Vec<Tweet>,
	running_tweet_count: u64,
	running_login_token_count: u64,
	active_logins: HashMap<u64, UserId>,
	credentials: HashMap<String, (String, UserId)>,
}

impl ServerState {
	pub fn new() -> Self {
		ServerState {
			users: Vec::new(),
			tweets: Vec::new(),
			running_tweet_count: 0,
			running_login_token_count: 0,
			active_logins: HashMap::new(),
			credentials: HashMap::new(),
		}
	}

	/// `s with-login-token-for u`: bump the counter, remember the login.
	fn with_login_token_for(&mut self, u: UserId) -> u64 {
		let token = self.running_login_token_count;
		self.running_login_token_count += 1;
		self.active_logins.insert(token, u);
		token
	}

	fn lookup_token(&self, token: u64) -> Option<UserId> {
		self.active_logins.get(&token).copied()
	}

	pub fn user(&self, id: UserId) -> Option<&User> {
		self.users.get(id as usize)
	}

	#[allow(dead_code)]
	pub fn tweet_count(&self) -> u64 {
		self.running_tweet_count
	}

	/// event-loop s (post-tweet token text)
	pub fn post_tweet(&mut self, token: Option<u64>, text: String) -> Response {
		let Some(poster) = token.and_then(|t| self.lookup_token(t)) else {
			return Response::OutdatedLoginToken;
		};
		let privacy = self
			.user(poster)
			.map(|u| u.privacy)
			.unwrap_or(Privacy::Everyone);
		let id = self.running_tweet_count;
		self.tweets.push(Tweet {
			id,
			poster,
			text,
			visibility: privacy,
			replies: Vec::new(),
			liked_by: Vec::new(),
		});
		self.running_tweet_count += 1;
		Response::TweetId(id)
	}

	/// event-loop s (get-tweet tk twt). As in the spec comment, an
	/// explicit not-found is omitted; out-of-range leaks nothing and
	/// is answered with permission-error.
	pub fn get_tweet(&self, token: Option<u64>, id: u64) -> Response {
		let Some(t) = self.tweets.get(id as usize) else {
			return Response::PermissionError;
		};
		let viewer = token.and_then(|t| self.lookup_token(t));
		let visible = match t.visibility {
			Privacy::Everyone => true,
			Privacy::Removed => false,
			Privacy::FollowersOnly => match viewer {
				Some(v) => self
					.user(t.poster)
					.map(|u| u.followers.contains(&v))
					.unwrap_or(false),
				None => false,
			},
		};
		if !visible {
			return Response::PermissionError;
		}
		// NB: spec/Twitter.agda line 194 uses the outer scope's tweet
		// count as the like count, which reads like a typo; the
		// Interface comment names this field Likes, so the tweet's own
		// list of likers is used.
		Response::Tweet {
			username: self
				.user(t.poster)
				.map(|u| u.name.clone())
				.unwrap_or_default(),
			text: t.text.clone(),
			likes: t.liked_by.len() as u64,
			replies: t.replies.clone(),
		}
	}

	/// event-loop s (timeline tk len)
	pub fn timeline(&self, token: Option<u64>, len: u64) -> Response {
		let Some(token) = token else {
			let ids = self
				.tweets
				.iter()
				.filter(|t| t.visibility == Privacy::Everyone)
				.map(|t| t.id)
				.take(len as usize)
				.collect();
			return Response::Timeline(ids);
		};
		let Some(viewer) = self.lookup_token(token) else {
			return Response::OutdatedLoginToken;
		};
		let ids = self
			.tweets
			.iter()
			.filter(|t| match t.visibility {
				Privacy::Everyone => true,
				Privacy::Removed => false,
				Privacy::FollowersOnly => self
					.user(t.poster)
					.map(|u| u.followers.contains(&viewer))
					.unwrap_or(false),
			})
			.map(|t| t.id)
			.take(len as usize)
			.collect();
		Response::Timeline(ids)
	}

	/// event-loop s (login username passwd)
	pub fn login(&mut self, username: &str, passwd: &str) -> Response {
		match self.credentials.get(username) {
			Some((correct_passwd, uid)) if correct_passwd == passwd => {
				Response::SessionToken(self.with_login_token_for(*uid))
			}
			_ => Response::LoginError,
		}
	}

	/// event-loop s (signup username passwd)
	pub fn signup(&mut self, username: &str, passwd: &str) -> Response {
		if self.credentials.contains_key(username) {
			return Response::SignupError;
		}
		let uid = self.users.len() as UserId;
		self.users.push(User {
			name: username.to_string(),
			privacy: Privacy::Everyone,
			follows: Vec::new(),
			followers: Vec::new(),
		});
		self.credentials
			.insert(username.to_string(), (passwd.to_string(), uid));
		Response::SessionToken(self.with_login_token_for(uid))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn signup_login_post(s: &mut ServerState, user: &str, text: &str) -> Response {
		let tk = match s.signup(user, "pw") {
			Response::SessionToken(t) => t,
			r => return r,
		};
		s.post_tweet(Some(tk), text.to_string())
	}

	fn expect_tweet_id(r: Response) -> u64 {
		match r {
			Response::TweetId(t) => t,
			other => panic!("expected TweetId, got {other:?}"),
		}
	}

	fn expect_session_token(r: Response) -> u64 {
		match r {
			Response::SessionToken(t) => t,
			other => panic!("expected SessionToken, got {other:?}"),
		}
	}

	#[test]
	fn signup_then_login() {
		let mut s = ServerState::new();
		let t0 = expect_session_token(s.signup("alice", "secret"));
		assert_eq!(t0, 0);
		expect_session_token(s.signup("bob", "pw"));
		// Existing username
		assert!(matches!(s.signup("alice", "x"), Response::SignupError));
		// Wrong password
		assert!(matches!(s.login("alice", "wrong"), Response::LoginError));
		// Unknown user
		assert!(matches!(s.login("eve", "x"), Response::LoginError));
		expect_session_token(s.login("alice", "secret"));
		// Token counter was already at 2 after two signups
		expect_session_token(s.login("bob", "pw"));
	}

	#[test]
	fn post_tweet_requires_valid_token() {
		let mut s = ServerState::new();
		assert!(matches!(
			s.post_tweet(None, "hi".into()),
			Response::OutdatedLoginToken
		));
		assert!(matches!(
			s.post_tweet(Some(42), "hi".into()),
			Response::OutdatedLoginToken
		));
	}

	#[test]
	fn posted_tweets_are_public_by_default() {
		let mut s = ServerState::new();
		assert_eq!(expect_tweet_id(signup_login_post(&mut s, "alice", "hi")), 0);
		assert_eq!(expect_tweet_id(signup_login_post(&mut s, "bob", "yo")), 1);
		let ids = match s.timeline(None, 10) {
			Response::Timeline(ids) => ids,
			other => panic!("expected Timeline, got {other:?}"),
		};
		assert_eq!(ids, vec![0, 1]);
		// Everyone can read a public tweet
		assert!(matches!(s.get_tweet(None, 0), Response::Tweet { .. }));
	}

	#[test]
	fn get_tweet_out_of_range_is_permission_error() {
		let s = ServerState::new();
		assert!(matches!(s.get_tweet(None, 99), Response::PermissionError));
	}

	#[test]
	fn timeline_len_caps_results() {
		let mut s = ServerState::new();
		let _ = expect_tweet_id(signup_login_post(&mut s, "alice", "a"));
		let _ = expect_tweet_id(signup_login_post(&mut s, "bob", "b"));
		let _ = expect_tweet_id(signup_login_post(&mut s, "carol", "c"));
		assert_eq!(
			match s.timeline(None, 2) {
				Response::Timeline(ids) => ids,
				other => panic!("{other:?}"),
			},
			vec![0, 1]
		);
		assert_eq!(
			match s.timeline(None, 0) {
				Response::Timeline(ids) => ids,
				other => panic!("{other:?}"),
			},
			Vec::<u64>::new()
		);
	}

	#[test]
	fn timeline_with_bad_token_is_outdated() {
		let mut s = ServerState::new();
		let _ = expect_tweet_id(signup_login_post(&mut s, "alice", "a"));
		assert!(matches!(
			s.timeline(Some(99), 5),
			Response::OutdatedLoginToken
		));
	}

	#[test]
	fn followers_only_visibility() {
		// Users created by the public API are always 'everyone', but the
		// state machine still handles followers-only and removed tweets;
		// exercise it by hand so the semantics are pinned down.
		let mut s = ServerState::new();
		s.users.push(User {
			name: "alice".into(),
			privacy: Privacy::Everyone,
			follows: vec![],
			followers: vec![1],
		});
		s.users.push(User {
			name: "bob".into(),
			privacy: Privacy::Everyone,
			follows: vec![0],
			followers: vec![],
		});
		s.credentials.insert("alice".into(), ("pw".into(), 0));
		s.credentials.insert("bob".into(), ("pw".into(), 1));
		let token_alice = expect_session_token(s.login("alice", "pw"));
		let token_bob = expect_session_token(s.login("bob", "pw"));
		s.tweets.push(Tweet {
			id: 0,
			poster: 0,
			text: "secret".into(),
			visibility: Privacy::FollowersOnly,
			replies: vec![],
			liked_by: vec![],
		});
		s.running_tweet_count = 1;

		// Not logged in: not allowed
		assert!(matches!(s.get_tweet(None, 0), Response::PermissionError));
		// bob follows alice and alice has bob as a follower: visible
		assert!(matches!(
			s.get_tweet(Some(token_bob), 0),
			Response::Tweet { .. }
		));
		// alice, logged in, is not on her own follower list
		assert!(matches!(
			s.get_tweet(Some(token_alice), 0),
			Response::PermissionError
		));
		// removed tweets are gone for everyone
		s.tweets[0].visibility = Privacy::Removed;
		assert!(matches!(
			s.get_tweet(Some(token_bob), 0),
			Response::PermissionError
		));
		// timeline follows the same rules
		s.tweets[0].visibility = Privacy::FollowersOnly;
		assert!(matches!(
			s.timeline(Some(token_alice), 1),
			Response::Timeline(ids) if ids.is_empty()
		));
		assert!(matches!(
			s.timeline(Some(token_bob), 1),
			Response::Timeline(ids) if ids == vec![0]
		));
	}
}
