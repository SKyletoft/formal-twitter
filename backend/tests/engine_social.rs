//! Property and unit tests for the social actions engine (task T3a), migrated
//! to the Q1 world-state harness (see `support`).
//!
//! Every property is a direct rendering of a `Step` rule of `spec/Twitter.agda`
//! and is paired with the Agda lemma in `ImplProofs.agda` that states the same
//! thing:
//!
//! | property                                      | spec rule                    | Agda lemma        |
//! |-----------------------------------------------|------------------------------|-------------------|
//! | `follow_succeeds_and_sets_follow`             | `follow-user` 655-664        | `follow-success`  |
//! | `follow_is_idempotent`                        | `add-follower` 371-375       | `follow-success`  |
//! | `follow_unknown_user_succeeds`                | `follow-user` (no premise)   | `follow-success`  |
//! | `unfollow_succeeds_and_clears_follow`         | `unfollow-user` 666-675      | `unfollow-success`|
//! | `unfollow_never_followed_succeeds`            | `unfollow-user` (no premise) | `unfollow-success`|
//! | `like_readable_post_succeeds`                 | `like-post` 587-613          | `like-success`    |
//! | `like_already_liked_is_idempotent`            | `like-post` (no premise)     | `like-success`    |
//! | `like_own_post_succeeds`                      | `like-post` (no premise)     | `like-success`    |
//! | `like_{absent,deleted,private}_post_is_denied`| `failed-like-post` 615-619   | `like-denied`     |
//! | `unlike_liked_post_succeeds`                  | `unlike-post` 621-647        | `unlike-success`  |
//! | `unlike_never_liked_succeeds`                 | `unlike-post` (no premise)   | `unlike-success`  |
//! | `unlike_{absent,deleted,private}_post_is_...` | `failed-unlike-post` 649-653 | `unlike-denied`   |
//! | `social_commands_expire_without_valid_session`| `failed-access` 464-468      | `follow-expired`,
//! |                                               |                              | `unfollow-expired`,
//! |                                               |                              | `like-expired`,
//! |                                               |                              | `unlike-expired`  |
//!
//! Harness shape:
//!
//! * **one** in-memory sqlite database per `#[test]`, created outside the
//!   quickcheck cases by `support::check`;
//! * every case resets it and materialises a freshly generated `WorldState`;
//!   the property body receives `&Db` and `&WorldState` and never builds a
//!   database;
//! * a property that needs a shape the generator may not produce (an active
//!   session, a readable post, a post that is already liked) derives the world
//!   inside the body by cloning and mutating it, then re-materialises *that*
//!   world through `load` -- still no database construction. No generated
//!   world is discarded;
//! * the expected world is computed from the before world, so "everything else
//!   unchanged" is asserted by whole-world equality, and the per-post premises
//!   of `like-post`/`unlike-post` by `assert_like_delta`.

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::social::{follow, like, unfollow, unlike};
use formal_twitter::model::{PostId, PostStatus, SessionId, SessionStatus, Visibility};
use quickcheck::{Arbitrary, Gen, TestResult};

use support::{AccountState, PostState, WorldState, check, from_db, materialise, reset};

// ---------------------------------------------------------------------------
// Arguments generated alongside the world.
// ---------------------------------------------------------------------------

const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&*";

fn small_string(g: &mut Gen) -> String {
	let len = 1 + usize::arbitrary(g) % 8;
	let mut out = String::with_capacity(len);
	for _ in 0..len {
		out.push(ALPHABET[usize::arbitrary(g) % ALPHABET.len()] as char);
	}
	out
}

/// A username candidate: made taken or free by the property.
#[derive(Clone, Debug)]
struct Name(String);

/// A post body, so the paths that carry text are exercised too.
#[derive(Clone, Debug)]
struct Body(String);

/// A selector into the generated world's sorted rows.
#[derive(Clone, Copy, Debug)]
struct Seed(usize);

impl Arbitrary for Name {
	fn arbitrary(g: &mut Gen) -> Self {
		Name(small_string(g))
	}
}

impl Arbitrary for Body {
	fn arbitrary(g: &mut Gen) -> Self {
		Body(small_string(g))
	}
}

impl Arbitrary for Seed {
	fn arbitrary(g: &mut Gen) -> Self {
		Seed(usize::arbitrary(g))
	}
}

// ---------------------------------------------------------------------------
// World helpers: deterministic selection and the derived worlds a property
// needs. All of them clone the generated world and mutate the clone.
// ---------------------------------------------------------------------------

fn pick<T>(items: &[T], seed: usize) -> Option<&T> {
	items.get(seed % items.len().max(1))
}

fn sorted_accounts(world: &WorldState) -> Vec<String> {
	world.accounts.keys().cloned().collect()
}

fn sorted_posts(world: &WorldState) -> Vec<PostId> {
	let mut ids: Vec<PostId> = world.posts.keys().copied().collect();
	ids.sort_unstable_by_key(|pid| pid.0);
	ids
}

fn sorted_sessions(world: &WorldState) -> Vec<(SessionId, SessionStatus)> {
	let mut ids: Vec<SessionId> = world.sessions.keys().copied().collect();
	ids.sort_unstable_by_key(|sid| sid.0);
	ids.into_iter()
		.map(|sid| (sid, world.session_status(sid)))
		.collect()
}

/// `base`, with `'_'` appended until no account holds it: a followee or a
/// follower that is a name no account has.
fn free_username(world: &WorldState, base: &str) -> String {
	let mut candidate = base.to_string();
	while world.accounts.contains_key(&candidate) {
		candidate.push('_');
	}
	candidate
}

/// A session id no row of `world` holds, i.e. `unused`.
fn free_session_id(world: &WorldState, seed: usize) -> SessionId {
	let mut id = 9_000_000 + (seed % 1_000) as i64;
	while world.sessions.contains_key(&SessionId(id)) {
		id += 1;
	}
	SessionId(id)
}

/// A post id no row of `world` holds.
fn free_post_id(world: &WorldState, seed: usize) -> PostId {
	let mut id = 9_000_000 + (seed % 1_000) as i64;
	while world.posts.contains_key(&PostId(id)) {
		id += 1;
	}
	PostId(id)
}

/// `world` and a username it holds: the generated account at `seed` when there
/// is one, otherwise `world` plus an account named after `base`.
fn with_some_account(world: &WorldState, seed: usize, base: &str) -> (WorldState, String) {
	if let Some(name) = pick(&sorted_accounts(world), seed) {
		return (world.clone(), name.clone());
	}
	let name = free_username(world, base);
	let mut next = world.clone();
	next.accounts.insert(
		name.clone(),
		AccountState {
			password: base.to_string(),
			visibility: Visibility::Everyone,
		},
	);
	(next, name)
}

/// `world` and an active session -- the generated one at `seed`, or a fresh
/// session for an account `world` keeps or gains -- together with its user.
fn with_active_session(
	world: &WorldState,
	seed: usize,
	base: &str,
) -> (WorldState, SessionId, String) {
	let active: Vec<(SessionId, String)> = sorted_sessions(world)
		.into_iter()
		.filter_map(|(sid, status)| match status {
			SessionStatus::Active(user) => Some((sid, user)),
			_ => None,
		})
		.collect();
	if let Some((sid, user)) = pick(&active, seed) {
		return (world.clone(), *sid, user.clone());
	}
	let (mut next, name) = with_some_account(world, seed, base);
	let sid = free_session_id(&next, seed);
	next.sessions
		.insert(sid, SessionStatus::Active(name.clone()));
	(next, sid, name)
}

/// `world` and a `revoked` session -- the first one it holds, or a fresh one.
fn with_revoked_session(world: &WorldState, seed: usize) -> (WorldState, SessionId) {
	if let Some((sid, _)) = sorted_sessions(world)
		.into_iter()
		.find(|(_, status)| matches!(status, SessionStatus::Revoked))
	{
		return (world.clone(), sid);
	}
	let sid = free_session_id(world, seed);
	let mut next = world.clone();
	next.sessions.insert(sid, SessionStatus::Revoked);
	(next, sid)
}

/// Reset the shared database, materialise a world derived inside a property
/// body and check the round-trip. No database is created here.
fn load(db: &Db, world: &WorldState) {
	world.validate().expect("a derived world is valid");
	reset(db);
	materialise(db, world);
	assert_eq!(from_db(db), *world, "the derived world must round-trip");
}

fn account(password: &str, visibility: Visibility) -> AccountState {
	AccountState {
		password: password.to_string(),
		visibility,
	}
}

fn post(author: &str, text: &str) -> PostState {
	PostState {
		author: author.to_string(),
		text: text.to_string(),
		visibility: Visibility::Everyone,
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: None,
	}
}

/// `world` plus a fresh public `live` post by `author`.
fn add_post(world: &WorldState, pid: PostId, author: &str, text: &str) -> WorldState {
	let mut next = world.clone();
	next.posts.insert(pid, post(author, text));
	next.newest_first.push(pid);
	next
}

/// Spec `CanReadPost` (Twitter.agda:158-179), read over `world`.
fn readable_by(world: &WorldState, user: &str, pid: PostId) -> bool {
	match world.posts.get(&pid) {
		None => false,
		Some(post) => {
			post.status == PostStatus::Live
				&& (post.visibility == Visibility::Everyone
					|| world
						.follows
						.contains(&(user.to_string(), post.author.clone())))
		}
	}
}

/// `world` and a post the session's user can read: a generated readable post
/// when there is one, otherwise a fresh public `live` post by the user.
fn readable_post(world: &WorldState, seed: usize, user: &str, text: &str) -> (WorldState, PostId) {
	let posts = sorted_posts(world);
	if !posts.is_empty() {
		let base = seed % posts.len();
		for offset in 0..posts.len() {
			let pid = posts[(base + offset) % posts.len()];
			if readable_by(world, user, pid) {
				return (world.clone(), pid);
			}
		}
	}
	let pid = free_post_id(world, seed);
	(add_post(world, pid, user, text), pid)
}

/// `world` and a post that exists -- the generated one at `seed`, or a fresh
/// public `live` post by `user`. The target of the mutating `unreadable` shapes.
fn target_post(world: &WorldState, seed: usize, user: &str, text: &str) -> (WorldState, PostId) {
	let posts = sorted_posts(world);
	if let Some(pid) = pick(&posts, seed) {
		return (world.clone(), *pid);
	}
	let pid = free_post_id(world, seed);
	(add_post(world, pid, user, text), pid)
}

/// The three ways `CanReadPost` (Twitter.agda:158-179) fails.
#[derive(Clone, Copy, Debug)]
enum Unreadable {
	/// No post with that id (`can-read-absent`).
	Absent,
	/// A `deleted` post (`can-read-deleted`).
	Deleted,
	/// A `live` `followers-only` post the user does not follow the author of
	/// (`post-is-private` fails).
	Private,
}

/// `world` and a post `user` cannot read, in the given shape.
fn unreadable_post(
	world: &WorldState,
	seed: usize,
	user: &str,
	text: &str,
	shape: Unreadable,
) -> (WorldState, PostId) {
	match shape {
		Unreadable::Absent => (world.clone(), free_post_id(world, seed)),
		Unreadable::Deleted => {
			let (mut world, pid) = target_post(world, seed, user, text);
			{
				let post = world.posts.get_mut(&pid).expect("the target post exists");
				post.status = PostStatus::Deleted;
				post.visibility = Visibility::Everyone;
			}
			(world, pid)
		}
		Unreadable::Private => {
			let (mut world, pid) = target_post(world, seed, user, text);
			let author = world.posts[&pid].author.clone();
			{
				let post = world.posts.get_mut(&pid).expect("the target post exists");
				post.status = PostStatus::Live;
				post.visibility = Visibility::FollowersOnly;
			}
			world.follows.remove(&(user.to_string(), author));
			(world, pid)
		}
	}
}

/// `likes` with `user` added, keeping the canonical (sorted, duplicate-free)
/// order `Post.likes` has in the world and `like-add` produces.
fn with_like(likes: &[String], user: &str) -> Vec<String> {
	let mut out = likes.to_vec();
	if let Err(index) = out.binary_search_by(|present| present.as_str().cmp(user)) {
		out.insert(index, user.to_string());
	}
	out
}

/// `likes` with `user` removed, keeping the canonical order.
fn without_like(likes: &[String], user: &str) -> Vec<String> {
	likes
		.iter()
		.filter(|present| present.as_str() != user)
		.cloned()
		.collect()
}

/// The `like-post`/`unlike-post` premises that concern the world
/// (Twitter.agda:601-612, 633-646): the target post keeps every field but its
/// like list, `user`'s membership becomes `liked`, every other user's
/// membership is unchanged, and no other post, account, session, follow or
/// `newest-first` entry moves.
fn assert_like_delta(
	before: &WorldState,
	after: &WorldState,
	pid: PostId,
	user: &str,
	liked: bool,
) {
	let old = before
		.posts
		.get(&pid)
		.expect("the target post exists before");
	let new = after.posts.get(&pid).expect("the target post exists after");
	assert_eq!(new.author, old.author, "the author is unchanged");
	assert_eq!(new.text, old.text, "the text is unchanged");
	assert_eq!(
		new.visibility, old.visibility,
		"the visibility is unchanged"
	);
	assert_eq!(new.status, old.status, "the status is unchanged");
	assert_eq!(new.replies, old.replies, "the replies are unchanged");
	assert_eq!(new.parent, old.parent, "the parent is unchanged");
	assert_eq!(
		new.likes.contains(&user.to_string()),
		liked,
		"the user's membership must be {liked}"
	);
	let mut members: BTreeSet<String> = old.likes.iter().cloned().collect();
	members.extend(new.likes.iter().cloned());
	for other in &members {
		if other.as_str() == user {
			continue;
		}
		assert_eq!(
			old.likes.contains(other),
			new.likes.contains(other),
			"the membership of {other:?} is unchanged"
		);
	}
	let expected = if liked {
		with_like(&old.likes, user)
	} else {
		without_like(&old.likes, user)
	};
	assert_eq!(
		new.likes, expected,
		"the like list stays canonical (sorted, duplicate-free)"
	);
	assert_eq!(
		after.accounts, before.accounts,
		"the accounts are unchanged"
	);
	assert_eq!(
		after.sessions, before.sessions,
		"the sessions are unchanged"
	);
	assert_eq!(after.follows, before.follows, "the follows are unchanged");
	assert_eq!(
		after.newest_first, before.newest_first,
		"newest-first is unchanged"
	);
	assert_eq!(
		after.posts.len(),
		before.posts.len(),
		"no post was added or removed"
	);
	for (other_pid, post) in &before.posts {
		if *other_pid != pid {
			assert_eq!(
				after.posts.get(other_pid),
				Some(post),
				"post {other_pid:?} is unchanged"
			);
		}
	}
}

// ---------------------------------------------------------------------------
// S1: follow -- `follow-user` (Twitter.agda:655-664) -- Agda `follow-success`.
// ---------------------------------------------------------------------------

/// `follow-user`: the follower is the session's user, `follows` gains exactly
/// `(follower, followee)`, and every account, session, post, like and
/// `newest-first` entry is copied unchanged. There is no premise on the
/// followee, so a name with no account works too; half the cases follow an
/// existing account and half a fresh name.
#[test]
fn follow_succeeds_and_sets_follow() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Name)| -> TestResult {
			let (seed, base, candidate) = arg;
			let (world, sid, follower) = with_active_session(world, seed.0, &base.0);
			let accounts = sorted_accounts(&world);
			let followee = if seed.0 % 2 == 0 {
				pick(&accounts, seed.0)
					.cloned()
					.unwrap_or_else(|| free_username(&world, &candidate.0))
			} else {
				free_username(&world, &candidate.0)
			};
			load(db, &world);

			let mut expected = world.clone();
			expected
				.follows
				.insert((follower.clone(), followee.clone()));
			expected.validate().expect("the expected world is valid");

			assert_eq!(
				follow(db, sid, &followee).expect("follow"),
				EngineResult::Success
			);

			let after = from_db(db);
			assert!(
				after
					.follows
					.contains(&(follower.clone(), followee.clone())),
				"the follow edge is set"
			);
			assert_eq!(after.accounts, world.accounts, "follow creates no account");
			assert_eq!(
				after.sessions, world.sessions,
				"follow touches no session row"
			);
			assert_eq!(after, expected, "only the follows set moves");
			TestResult::passed()
		},
	);
}

/// `add-follower` (Twitter.agda:371-375) is idempotent: following a user that
/// is already followed is still `success` and changes nothing. The edge is
/// forced into the derived world so the case is exercised on every run.
#[test]
fn follow_is_idempotent() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name)| -> TestResult {
			let (seed, base) = arg;
			let (mut world, sid, follower) = with_active_session(world, seed.0, &base.0);
			let accounts = sorted_accounts(&world);
			let followee = pick(&accounts, seed.0)
				.cloned()
				.unwrap_or_else(|| free_username(&world, &base.0));
			world.follows.insert((follower.clone(), followee.clone()));
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				world
					.follows
					.contains(&(follower.clone(), followee.clone())),
				"precondition: the edge is already there"
			);

			assert_eq!(
				follow(db, sid, &followee).expect("follow"),
				EngineResult::Success
			);
			assert_eq!(from_db(db), world, "following twice changes nothing");
			TestResult::passed()
		},
	);
}

/// `follow-user` has no premise on the followee, so following a username with
/// no account is `success`, stores the edge and creates no account.
#[test]
fn follow_unknown_user_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Name)| -> TestResult {
			let (seed, base, candidate) = arg;
			let (world, sid, follower) = with_active_session(world, seed.0, &base.0);
			let followee = free_username(&world, &candidate.0);
			assert!(
				!world.accounts.contains_key(&followee),
				"precondition: the followee has no account"
			);
			load(db, &world);

			let mut expected = world.clone();
			expected
				.follows
				.insert((follower.clone(), followee.clone()));
			expected.validate().expect("the expected world is valid");

			assert_eq!(
				follow(db, sid, &followee).expect("follow"),
				EngineResult::Success
			);

			let after = from_db(db);
			assert!(
				after.follows.contains(&(follower, followee.clone())),
				"the follow edge is set"
			);
			assert_eq!(
				after.accounts, world.accounts,
				"no account is created for the followee"
			);
			assert_eq!(after, expected);
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// S2: unfollow -- `unfollow-user` (Twitter.agda:666-675) -- Agda
// `unfollow-success`.
// ---------------------------------------------------------------------------

/// `unfollow-user` removes exactly one edge (`remove-follower`) and keeps every
/// other follow pair, account, session, post and `newest-first` entry.
#[test]
fn unfollow_succeeds_and_clears_follow() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Name)| -> TestResult {
			let (seed, base, candidate) = arg;
			let (mut world, sid, follower) = with_active_session(world, seed.0, &base.0);
			let accounts = sorted_accounts(&world);
			let followee = if seed.0 % 2 == 0 {
				pick(&accounts, seed.0)
					.cloned()
					.unwrap_or_else(|| free_username(&world, &candidate.0))
			} else {
				free_username(&world, &candidate.0)
			};
			world.follows.insert((follower.clone(), followee.clone()));
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				world
					.follows
					.contains(&(follower.clone(), followee.clone())),
				"precondition: the edge exists"
			);

			let mut expected = world.clone();
			expected
				.follows
				.remove(&(follower.clone(), followee.clone()));

			assert_eq!(
				unfollow(db, sid, &followee).expect("unfollow"),
				EngineResult::Success
			);

			let after = from_db(db);
			assert!(
				!after.follows.contains(&(follower, followee.clone())),
				"the edge is removed"
			);
			assert_eq!(after, expected, "only the follows set moves");
			TestResult::passed()
		},
	);
}

/// `unfollow-user` has no premise that the edge existed, so unfollowing a user
/// that was never followed is `success` and changes nothing.
#[test]
fn unfollow_never_followed_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Name)| -> TestResult {
			let (seed, base, candidate) = arg;
			let (mut world, sid, follower) = with_active_session(world, seed.0, &base.0);
			let accounts = sorted_accounts(&world);
			let followee = if seed.0 % 2 == 0 {
				pick(&accounts, seed.0)
					.cloned()
					.unwrap_or_else(|| free_username(&world, &candidate.0))
			} else {
				free_username(&world, &candidate.0)
			};
			world.follows.remove(&(follower.clone(), followee.clone()));
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				!world.follows.contains(&(follower, followee.clone())),
				"precondition: the edge is absent"
			);

			assert_eq!(
				unfollow(db, sid, &followee).expect("unfollow"),
				EngineResult::Success
			);
			assert_eq!(from_db(db), world, "unfollowing nothing changes nothing");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// S3: like -- `like-post` (Twitter.agda:587-613), `failed-like-post`
// (615-619) -- Agda `like-success`, `like-denied`.
// ---------------------------------------------------------------------------

/// `like-post` on a readable post: a public `live` post, or a `followers-only`
/// `live` post the user follows the author of (`CanReadPost`,
/// Twitter.agda:158-179). The user joins the like list, every other user's
/// membership is unchanged, the post keeps author, text, visibility, status,
/// parent and replies, and no other row of the world moves.
#[test]
fn like_readable_post_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (world, pid) = readable_post(&world, seed.0, &user, &body.0);
			load(db, &world);
			assert!(
				readable_by(&world, &user, pid),
				"precondition: CanReadPost holds before the command"
			);

			let mut expected = world.clone();
			let liked = with_like(&world.posts[&pid].likes, &user);
			expected.posts.get_mut(&pid).expect("the target post").likes = liked;
			expected.validate().expect("the expected world is valid");

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Success);

			let after = from_db(db);
			assert_like_delta(&world, &after, pid, &user, true);
			assert_eq!(after, expected, "nothing but the like list moves");
			TestResult::passed()
		},
	);
}

/// `like-post` has no premise that the user is absent from the like list, so
/// liking twice is `success`, adds no duplicate and leaves the world as it was.
#[test]
fn like_already_liked_is_idempotent() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) = readable_post(&world, seed.0, &user, &body.0);
			let liked = with_like(&world.posts[&pid].likes, &user);
			world.posts.get_mut(&pid).expect("the target post").likes = liked;
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				world.posts[&pid].likes.contains(&user),
				"precondition: the user already likes the post"
			);

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Success);

			let after = from_db(db);
			assert_like_delta(&world, &after, pid, &user, true);
			assert_eq!(after, world, "liking twice changes nothing");
			TestResult::passed()
		},
	);
}

/// `like-post` has no distinctness premise on the author, so the session's user
/// may like their own post.
#[test]
fn like_own_post_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let pid = free_post_id(&world, seed.0);
			let world = add_post(&world, pid, &user, &body.0);
			load(db, &world);
			assert_eq!(
				world.posts[&pid].author, user,
				"precondition: the post is the session user's own"
			);
			assert!(readable_by(&world, &user, pid));

			let mut expected = world.clone();
			let liked = with_like(&world.posts[&pid].likes, &user);
			expected.posts.get_mut(&pid).expect("the target post").likes = liked;
			expected.validate().expect("the expected world is valid");

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Success);

			let after = from_db(db);
			assert_like_delta(&world, &after, pid, &user, true);
			assert_eq!(after, expected);
			TestResult::passed()
		},
	);
}

/// `failed-like-post` on a post that does not exist (`can-read-absent`):
/// `denied`, and the whole world is unchanged.
#[test]
fn like_absent_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name)| -> TestResult {
			let (seed, base) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (world, pid) = unreadable_post(&world, seed.0, &user, "gone", Unreadable::Absent);
			load(db, &world);
			assert!(
				!world.posts.contains_key(&pid),
				"precondition: the post is absent"
			);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied like changes nothing");
			TestResult::passed()
		},
	);
}

/// `failed-like-post` on a `deleted` post (`CanReadPost` demands `live`,
/// `can-read-deleted`): `denied`, world unchanged.
#[test]
fn like_deleted_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (world, pid) = unreadable_post(&world, seed.0, &user, &body.0, Unreadable::Deleted);
			load(db, &world);
			assert_eq!(world.posts[&pid].status, PostStatus::Deleted);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied like changes nothing");
			TestResult::passed()
		},
	);
}

/// `failed-like-post` on a `live` `followers-only` post the user does not
/// follow the author of (`post-is-private` fails): `denied`, world unchanged.
#[test]
fn like_private_unfollowed_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (world, pid) = unreadable_post(&world, seed.0, &user, &body.0, Unreadable::Private);
			load(db, &world);
			assert_eq!(
				world.posts[&pid].visibility,
				Visibility::FollowersOnly,
				"precondition: the post is followers-only"
			);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(like(db, sid, pid).expect("like"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied like changes nothing");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// S4: unlike -- `unlike-post` (Twitter.agda:621-647), `failed-unlike-post`
// (649-653) -- Agda `unlike-success`, `unlike-denied`.
// ---------------------------------------------------------------------------

/// `unlike-post`: the user leaves the like list (`user ∉ Post.likes post`,
/// Twitter.agda:625), every other user's membership is unchanged, the post
/// keeps its other fields, and no other row of the world moves.
#[test]
fn unlike_liked_post_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) = readable_post(&world, seed.0, &user, &body.0);
			let liked = with_like(&world.posts[&pid].likes, &user);
			world.posts.get_mut(&pid).expect("the target post").likes = liked;
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				world.posts[&pid].likes.contains(&user),
				"precondition: the like exists"
			);

			let mut expected = world.clone();
			let unliked = without_like(&world.posts[&pid].likes, &user);
			expected.posts.get_mut(&pid).expect("the target post").likes = unliked;

			assert_eq!(unlike(db, sid, pid).expect("unlike"), EngineResult::Success);

			let after = from_db(db);
			assert_like_delta(&world, &after, pid, &user, false);
			assert_eq!(after, expected, "nothing but the like list moves");
			TestResult::passed()
		},
	);
}

/// `unlike-post` has no premise that the like existed, so unliking a post the
/// user never liked is `success` and changes nothing.
#[test]
fn unlike_never_liked_succeeds() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) = readable_post(&world, seed.0, &user, &body.0);
			let stripped = without_like(&world.posts[&pid].likes, &user);
			world.posts.get_mut(&pid).expect("the target post").likes = stripped;
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(
				!world.posts[&pid].likes.contains(&user),
				"precondition: the user does not like the post"
			);

			assert_eq!(unlike(db, sid, pid).expect("unlike"), EngineResult::Success);
			assert_eq!(from_db(db), world, "unliking nothing changes nothing");
			TestResult::passed()
		},
	);
}

/// `failed-unlike-post` on a post that does not exist: `denied`, and nothing at
/// all changes.
#[test]
fn unlike_absent_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name)| -> TestResult {
			let (seed, base) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (world, pid) = unreadable_post(&world, seed.0, &user, "gone", Unreadable::Absent);
			load(db, &world);
			assert!(
				!world.posts.contains_key(&pid),
				"precondition: the post is absent"
			);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(unlike(db, sid, pid).expect("unlike"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied unlike changes nothing");
			TestResult::passed()
		},
	);
}

/// `failed-unlike-post` on a `deleted` post: `denied`, and even the like the
/// user holds on it stays.
#[test]
fn unlike_deleted_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) = target_post(&world, seed.0, &user, &body.0);
			let liked = with_like(&world.posts[&pid].likes, &user);
			{
				let post = world.posts.get_mut(&pid).expect("the target post");
				post.likes = liked;
				post.status = PostStatus::Deleted;
			}
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(unlike(db, sid, pid).expect("unlike"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied unlike changes nothing");
			assert!(
				from_db(db).posts[&pid].likes.contains(&user),
				"the denied command did not consume the like"
			);
			TestResult::passed()
		},
	);
}

/// `failed-unlike-post` on a `live` `followers-only` post the user does not
/// follow the author of: `denied`, world unchanged.
#[test]
fn unlike_private_unfollowed_post_is_denied() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Body)| -> TestResult {
			let (seed, base, body) = arg;
			let (world, sid, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) =
				unreadable_post(&world, seed.0, &user, &body.0, Unreadable::Private);
			let liked = with_like(&world.posts[&pid].likes, &user);
			world.posts.get_mut(&pid).expect("the target post").likes = liked;
			world.validate().expect("the derived world is valid");
			load(db, &world);
			assert!(!readable_by(&world, &user, pid));

			assert_eq!(unlike(db, sid, pid).expect("unlike"), EngineResult::Denied);
			assert_eq!(from_db(db), world, "a denied unlike changes nothing");
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// S5: failed-access -- all four commands on an inactive session
// (Twitter.agda:464-468) -- Agda `follow-expired`, `unfollow-expired`,
// `like-expired`, `unlike-expired`.
// ---------------------------------------------------------------------------

/// `failed-access`: the four commands extract their session (`extract-sid`,
/// Twitter.agda:203-207), so a session that is not `active` -- `revoked` or
/// `unused` -- expires the request and leaves the world untouched. The derived
/// world keeps a readable post and a follow edge, so `success` would be
/// tempting; unlike `read-post nothing` none of these can fire vacuously.
#[test]
fn social_commands_expire_without_valid_session() {
	check(
		|db: &Db, world: &WorldState, arg: (Seed, Name, Name)| -> TestResult {
			let (seed, base, candidate) = arg;
			let (world, _active, user) = with_active_session(world, seed.0, &base.0);
			let (mut world, pid) = readable_post(&world, seed.0, &user, "target");
			let followee = free_username(&world, &candidate.0);
			world.follows.insert((user.clone(), followee.clone()));
			let (world, revoked) = with_revoked_session(&world, seed.0);
			world.validate().expect("the derived world is valid");
			load(db, &world);
			let unused = free_session_id(&world, seed.0);
			assert_eq!(world.session_status(revoked), SessionStatus::Revoked);
			assert_eq!(world.session_status(unused), SessionStatus::Unused);

			for sid in [revoked, unused] {
				assert_eq!(
					follow(db, sid, &followee).expect("follow"),
					EngineResult::Expired,
					"follow-expired on {sid:?}"
				);
				assert_eq!(from_db(db), world, "an expired follow changes nothing");
				assert_eq!(
					unfollow(db, sid, &followee).expect("unfollow"),
					EngineResult::Expired,
					"unfollow-expired on {sid:?}"
				);
				assert_eq!(from_db(db), world, "an expired unfollow changes nothing");
				assert_eq!(
					like(db, sid, pid).expect("like"),
					EngineResult::Expired,
					"like-expired on {sid:?}"
				);
				assert_eq!(from_db(db), world, "an expired like changes nothing");
				assert_eq!(
					unlike(db, sid, pid).expect("unlike"),
					EngineResult::Expired,
					"unlike-expired on {sid:?}"
				);
				assert_eq!(from_db(db), world, "an expired unlike changes nothing");
			}
			TestResult::passed()
		},
	);
}

// ---------------------------------------------------------------------------
// Deterministic unit tests. Each one owns a single database, created here and
// outside any quickcheck case.
// ---------------------------------------------------------------------------

/// Two accounts, an active and a revoked session, a public post with a like, a
/// followers-only post by the same author, a deleted post, and one follow edge
/// (ada -> grace) that makes the followers-only post readable.
fn sample_world() -> WorldState {
	let mut public = post("grace", "public post");
	public.likes = vec!["grace".to_string()];
	let private = PostState {
		visibility: Visibility::FollowersOnly,
		..post("grace", "private post")
	};
	let deleted = PostState {
		status: PostStatus::Deleted,
		..post("ada", "deleted post")
	};
	let world = WorldState {
		accounts: BTreeMap::from([
			("ada".to_string(), account("pw-ada", Visibility::Everyone)),
			(
				"grace".to_string(),
				account("pw-grace", Visibility::Everyone),
			),
		]),
		sessions: HashMap::from([
			(SessionId(7), SessionStatus::Active("ada".to_string())),
			(SessionId(8), SessionStatus::Revoked),
		]),
		posts: HashMap::from([
			(PostId(1), public),
			(PostId(2), private),
			(PostId(3), deleted),
		]),
		follows: BTreeSet::from([("ada".to_string(), "grace".to_string())]),
		newest_first: vec![PostId(3), PostId(2), PostId(1)],
	};
	world.validate().expect("the sample world is valid");
	world
}

const ADA_SESSION: SessionId = SessionId(7);
const REVOKED_SESSION: SessionId = SessionId(8);
const PUBLIC: PostId = PostId(1);
const PRIVATE: PostId = PostId(2);
const DELETED: PostId = PostId(3);

fn loaded_sample() -> (Db, WorldState) {
	let db = Db::in_memory().expect("create the in-memory database");
	let world = sample_world();
	reset(&db);
	materialise(&db, &world);
	assert_eq!(from_db(&db), world, "the fixture round-trips");
	(db, world)
}

#[test]
fn follow_and_unfollow_move_exactly_one_edge() {
	let (db, world) = loaded_sample();
	let mut following = world.clone();
	following
		.follows
		.insert(("ada".to_string(), "bob".to_string()));

	assert_eq!(
		follow(&db, ADA_SESSION, "bob").expect("follow"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), following, "follow adds exactly one edge");

	assert_eq!(
		unfollow(&db, ADA_SESSION, "bob").expect("unfollow"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), world, "unfollow takes it back");

	assert_eq!(
		unfollow(&db, ADA_SESSION, "carol").expect("unfollow"),
		EngineResult::Success,
		"unfollowing a user that was never followed is still success"
	);
	assert_eq!(from_db(&db), world);
}

#[test]
fn like_and_unlike_a_public_post() {
	let (db, world) = loaded_sample();
	let mut liked = world.clone();
	let likes = with_like(&world.posts[&PUBLIC].likes, "ada");
	liked.posts.get_mut(&PUBLIC).expect("post 1").likes = likes;
	assert_eq!(
		liked.posts[&PUBLIC].likes,
		vec!["ada".to_string(), "grace".to_string()],
		"the like list is canonical"
	);

	assert_eq!(
		like(&db, ADA_SESSION, PUBLIC).expect("like"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), liked);

	assert_eq!(
		unlike(&db, ADA_SESSION, PUBLIC).expect("unlike"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), world);
}

#[test]
fn like_a_followers_only_post_needs_the_follow_edge() {
	let (db, world) = loaded_sample();
	// ada follows grace, so the followers-only post is readable.
	assert_eq!(
		like(&db, ADA_SESSION, PRIVATE).expect("like"),
		EngineResult::Success
	);
	let mut liked = world.clone();
	liked.posts.get_mut(&PRIVATE).expect("post 2").likes = vec!["ada".to_string()];
	assert_eq!(from_db(&db), liked);

	// Without the edge the very same post is unreadable: denied, unchanged.
	let mut unfollowed = liked.clone();
	unfollowed.follows.clear();
	reset(&db);
	materialise(&db, &unfollowed);
	assert_eq!(
		like(&db, ADA_SESSION, PRIVATE).expect("like"),
		EngineResult::Denied
	);
	assert_eq!(
		unlike(&db, ADA_SESSION, PRIVATE).expect("unlike"),
		EngineResult::Denied
	);
	assert_eq!(from_db(&db), unfollowed, "denied commands change nothing");
}

#[test]
fn like_is_idempotent_and_counts_once() {
	let (db, _world) = loaded_sample();
	assert_eq!(
		like(&db, ADA_SESSION, PUBLIC).expect("like"),
		EngineResult::Success
	);
	let once = from_db(&db);
	assert_eq!(
		once.posts[&PUBLIC].likes,
		vec!["ada".to_string(), "grace".to_string()]
	);

	assert_eq!(
		like(&db, ADA_SESSION, PUBLIC).expect("like"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), once, "a second like adds nothing");
}

#[test]
fn deleted_post_cannot_be_liked() {
	let (db, world) = loaded_sample();
	assert_eq!(
		like(&db, ADA_SESSION, DELETED).expect("like"),
		EngineResult::Denied
	);
	assert_eq!(
		unlike(&db, ADA_SESSION, DELETED).expect("unlike"),
		EngineResult::Denied
	);
	assert_eq!(from_db(&db), world);
}

#[test]
fn social_commands_expire_on_an_inactive_session() {
	let (db, world) = loaded_sample();
	for sid in [REVOKED_SESSION, SessionId(999)] {
		let results = [
			("follow", follow(&db, sid, "bob").expect("follow")),
			("unfollow", unfollow(&db, sid, "bob").expect("unfollow")),
			("like", like(&db, sid, PUBLIC).expect("like")),
			("unlike", unlike(&db, sid, PUBLIC).expect("unlike")),
		];
		for (name, result) in results {
			assert_eq!(result, EngineResult::Expired, "{name} on {sid:?}");
			assert_eq!(from_db(&db), world, "{name} on {sid:?} changes nothing");
		}
	}
}
