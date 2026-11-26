//! Property and unit tests for the post lifecycle engine (task T2b, migrated to
//! the Q1 world-state harness by task Q1b).
//!
//! Every property below is a direct rendering of a `Step` rule of
//! `spec/Twitter.agda` over a generated `WorldState`, and the expected world is
//! a *pure* function of that world (clone, mutate, `validate`) -- never a
//! database query. The matching Agda lemma lives in `ImplProofs.agda` and is
//! cited at each property:
//!
//! | property | rule (Twitter.agda) | Agda lemma |
//! |---|---|---|
//! | `publish_without_a_parent_creates_the_post` | `successful-post` | `post-success` |
//! | `reply_to_a_readable_parent_creates_a_reply` | `successful-reply` | `reply-success-everyone`, `reply-success-followers-only` |
//! | `reply_to_an_absent_parent_is_denied` | `failed-reply` | `reply-denied-absent` |
//! | `reply_to_a_deleted_parent_is_denied` | `failed-reply` | `reply-denied-deleted` |
//! | `reply_to_an_unfollowed_private_parent_is_denied` | `failed-reply` | `reply-denied-private` |
//! | `delete_of_an_own_live_post_marks_it_deleted` | `delete-post` | `delete-success` |
//! | `delete_of_an_already_deleted_own_post_succeeds` | `delete-post` | `delete-idempotent` |
//! | `delete_of_an_absent_post_is_denied` | `failed-delete-non-existant-post` | `delete-denied-absent` |
//! | `delete_of_a_foreign_post_is_denied` | `failed-delete-not-author` | `delete-denied-not-author` |
//! | `read_logged_in_returns_a_readable_post` | `read-post-logged-in` | `read-logged-in` |
//! | `read_logged_in_is_denied_for_unreadable_posts` | `cant-read-post-*` | `read-denied-absent`, `read-denied-deleted`, `read-denied-private` |
//! | `read_anonymous_returns_a_public_live_post` | `read-post-anonymously` | `read-anonymous` |
//! | `read_anonymous_expires_for_unreadable_posts` | `failed-access` | `read-anonymous-expired` |
//! | `post_commands_expire_with_an_inactive_session` | `failed-access` | `publish-expired`, `delete-expired`, `read-expired` |
//!
//! Harness shape (see `support`):
//!
//! * **one** in-memory sqlite database per `#[test]`, created outside the
//!   quickcheck cases by `support::check`; each case resets it, materialises the
//!   generated world and asserts the round-trip `from_db == world` before the
//!   property body runs. No database is built inside a property.
//! * A property that needs a row the generator may not have produced (an active
//!   session, a readable parent, a deleted or foreign post, a revoked session)
//!   *extends* the world with a pure helper and re-materialises through
//!   `reseed`, which re-asserts the round-trip. No case is discarded.
//! * A `WorldState` records every column, so `assert_eq!(from_db(db), expected)`
//!   discharges both halves of a `Step` at once: the `Result` is asserted
//!   separately and the expected world carries the "everything else unchanged"
//!   premises (Twitter.agda:391-395, 417-421, 449-455).
//! * Fresh ids: `publish` draws from the whole safe-`i64` range, so the returned
//!   `pid` is asserted absent from the generated world before it is substituted
//!   into the expected world.
//! * `read-post nothing` extracts no session (`extract-sid`, Twitter.agda:196),
//!   so `failed-access` (Twitter.agda:464-468) applies to it vacuously and an
//!   unreadable anonymous read is `Expired`, never `Denied`
//!   (`read-anonymous-expired`).
//!
//! Assumption (shared with `support`): `Post.replies` is in `seq` order -- the
//! children sorted by ascending rank in `newest_first` -- because the engine
//! serves replies through `store::replies_of` (`ORDER BY seq DESC`); a new
//! reply therefore *prepends* to both `newest_first` and the parent's list.

mod support;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use formal_twitter::db::Db;
use formal_twitter::engine::EngineResult;
use formal_twitter::engine::posts::{delete, publish, read_post};
use formal_twitter::model::{PostId, PostStatus, SessionId, SessionStatus, Visibility};
use quickcheck::{Arbitrary, Gen, TestResult};

use support::{AccountState, PostState, WorldState, check, from_db, materialise, reset};

// ---------------------------------------------------------------------------
// Generated arguments.
// ---------------------------------------------------------------------------

/// A post body over a line-safe, `'\0'`-free alphabet, so a failing case prints
/// legibly and the text binds into sqlite as plain text.
const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.!#$%&* ";

#[derive(Clone, Debug)]
struct Body(String);

impl Arbitrary for Body {
	fn arbitrary(g: &mut Gen) -> Self {
		let len = usize::arbitrary(g) % 9;
		let mut out = String::with_capacity(len);
		for _ in 0..len {
			out.push(ALPHABET[usize::arbitrary(g) % ALPHABET.len()] as char);
		}
		Body(out)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
		let chars: Vec<char> = self.0.chars().collect();
		Box::new(
			(0..chars.len())
				.rev()
				.map(move |n| Body(chars[..n].iter().collect())),
		)
	}
}

// ---------------------------------------------------------------------------
// Worlds: fixtures, lookups and pure extensions.
// ---------------------------------------------------------------------------

fn account(password: &str, visibility: Visibility) -> AccountState {
	AccountState {
		password: password.to_string(),
		visibility,
	}
}

fn post(author: &str, text: &str, visibility: Visibility) -> PostState {
	PostState {
		author: author.to_string(),
		text: text.to_string(),
		visibility,
		status: PostStatus::Live,
		likes: Vec::new(),
		replies: Vec::new(),
		parent: None,
	}
}

fn deleted(mut post: PostState) -> PostState {
	post.status = PostStatus::Deleted;
	post
}

fn empty_world() -> WorldState {
	WorldState {
		accounts: BTreeMap::new(),
		sessions: HashMap::new(),
		posts: HashMap::new(),
		follows: BTreeSet::new(),
		newest_first: Vec::new(),
	}
}

fn follows(world: &WorldState, follower: &str, followee: &str) -> bool {
	world
		.follows
		.contains(&(follower.to_string(), followee.to_string()))
}

/// `can-read-post` for a session's user: `live` and (`everyone` or followed)
/// (Twitter.agda:158-179; `CanReadPost` in `ImplProofs.agda`).
fn can_read(world: &WorldState, user: &str, post: &PostState) -> bool {
	post.status == PostStatus::Live
		&& (post.visibility == Visibility::Everyone || follows(world, user, &post.author))
}

/// `is-post-public` (Twitter.agda:342-357).
fn is_public(post: &PostState) -> bool {
	post.status == PostStatus::Live && post.visibility == Visibility::Everyone
}

/// A post id no world uses; generated ids are small, so start far above them.
fn absent_post(world: &WorldState) -> PostId {
	let mut id = 1_000_000;
	while world.posts.contains_key(&PostId(id)) {
		id += 1;
	}
	PostId(id)
}

/// A session id no world uses.
fn absent_session(world: &WorldState) -> SessionId {
	let mut id = 1_000_000;
	while world.sessions.contains_key(&SessionId(id)) {
		id += 1;
	}
	SessionId(id)
}

/// `world` plus a fresh post appended to the *oldest* end of `newest_first`.
fn with_post(world: &WorldState, post: PostState) -> (WorldState, PostId) {
	let pid = absent_post(world);
	let mut next = world.clone();
	next.posts.insert(pid, post);
	next.newest_first.push(pid);
	next.validate().expect("the extended world is valid");
	(next, pid)
}

/// The first post (in id order) satisfying `pred`, or `world` extended with
/// `make()` when there is none. Deterministic, so a failure reproduces.
fn existing_or_added(
	world: &WorldState,
	pred: impl Fn(&PostState) -> bool,
	make: impl FnOnce() -> PostState,
) -> (WorldState, PostId) {
	let mut ids: Vec<PostId> = world.posts.keys().copied().collect();
	ids.sort_unstable_by_key(|pid| pid.0);
	for pid in ids {
		if pred(&world.posts[&pid]) {
			return (world.clone(), pid);
		}
	}
	with_post(world, make())
}

/// An author name the user does not follow, synthesised when every account is
/// followed (a post's author need not be an account).
fn unfollowed_author(world: &WorldState, user: &str) -> String {
	let mut candidate = "stranger".to_string();
	let mut n = 0;
	while follows(world, user, &candidate) {
		n += 1;
		candidate = format!("stranger{n}");
	}
	candidate
}

/// The smallest session id whose status is `active`, with its user.
fn first_active(world: &WorldState) -> Option<(SessionId, String)> {
	let mut ids = world.active_sessions();
	ids.sort_unstable_by_key(|sid| sid.0);
	let sid = *ids.first()?;
	match world.session_status(sid) {
		SessionStatus::Active(user) => Some((sid, user)),
		_ => unreachable!("listed as active"),
	}
}

/// `world` with at least one `active` session, that session's id and its user.
///
/// Adds a session for an existing account (or a fresh `actor` account) when the
/// generator produced no active session, which is the case for roughly half of
/// the generated worlds.
fn with_actor(world: &WorldState) -> (WorldState, SessionId, String) {
	if let Some((sid, user)) = first_active(world) {
		return (world.clone(), sid, user);
	}
	let mut next = world.clone();
	let user = match next.accounts.keys().next().cloned() {
		Some(user) => user,
		None => {
			next.accounts.insert(
				"actor".to_string(),
				account("pw-actor", Visibility::Everyone),
			);
			"actor".to_string()
		}
	};
	let sid = absent_session(&next);
	next.sessions
		.insert(sid, SessionStatus::Active(user.clone()));
	next.validate().expect("the world with an actor is valid");
	(next, sid, user)
}

/// `world` with at least one `revoked` session, and such a session's id.
fn with_revoked_session(world: &WorldState) -> (WorldState, SessionId) {
	let mut ids: Vec<SessionId> = world
		.sessions
		.iter()
		.filter(|(_, status)| matches!(status, SessionStatus::Revoked))
		.map(|(sid, _)| *sid)
		.collect();
	ids.sort_unstable_by_key(|sid| sid.0);
	if let Some(sid) = ids.first() {
		return (world.clone(), *sid);
	}
	let sid = absent_session(world);
	let mut next = world.clone();
	next.sessions.insert(sid, SessionStatus::Revoked);
	next.validate()
		.expect("the world with a revoked session is valid");
	(next, sid)
}

/// Materialise `seeded` when it differs from the world the harness already
/// wrote (the harness knows only the generated `world`), re-asserting the
/// round-trip. Never builds a database.
fn reseed(db: &Db, world: &WorldState, seeded: &WorldState) {
	if seeded == world {
		return;
	}
	reset(db);
	materialise(db, seeded);
	assert_eq!(
		from_db(db),
		*seeded,
		"the materialiser must round-trip the extended world"
	);
}

// ---------------------------------------------------------------------------
// Results and expected worlds.
// ---------------------------------------------------------------------------

fn created(result: EngineResult) -> PostId {
	match result {
		EngineResult::CreatedPost(pid) => pid,
		other => panic!("expected CreatedPost, got {other:?}"),
	}
}

fn returned(result: EngineResult) -> (String, String, u64, Vec<PostId>) {
	match result {
		EngineResult::ReturnedPost {
			author,
			text,
			likes,
			replies,
		} => (author, text, likes, replies),
		other => panic!("expected ReturnedPost, got {other:?}"),
	}
}

/// `world` with `new_post` at `pid`, `pid` prepended to `newest_first` and --
/// when the new post is a reply -- `pid` prepended to its parent's reply list.
///
/// That is exactly the expected after-world of `successful-post` and
/// `successful-reply`: `PostIsNew`, `pid ∷ newest-first`, and `ppost'` with
/// `pid ∷ preplies`.
fn posted_world(world: &WorldState, pid: PostId, new_post: PostState) -> WorldState {
	assert!(
		!world.posts.contains_key(&pid),
		"a freshly allocated id must be unused"
	);
	let parent = new_post.parent;
	let mut next = world.clone();
	next.posts.insert(pid, new_post);
	next.newest_first.insert(0, pid);
	if let Some(parent) = parent {
		next.posts
			.get_mut(&parent)
			.expect("the parent exists")
			.replies
			.insert(0, pid);
	}
	next.validate().expect("the expected posted world is valid");
	next
}

// ---------------------------------------------------------------------------
// P1: publish without a parent -- `successful-post` (Twitter.agda:387-398).
// Agda: `post-success`.
// ---------------------------------------------------------------------------

/// `successful-post`: a fresh id holds `new-post user txt acc` -- the text, the
/// account's `default-visibility`, `live`, no parent, no likes, no replies --
/// the id heads `newest-first`, and every account, session, post, follow and
/// like is otherwise untouched.
#[test]
fn publish_without_a_parent_creates_the_post() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		reseed(db, world, &seeded);

		let default = seeded.accounts[&user].visibility;
		let before = seeded.clone();
		let pid = created(publish(db, sid, &body.0, None).expect("publish"));

		let expected = posted_world(
			&before,
			pid,
			PostState {
				author: user.clone(),
				text: body.0.clone(),
				visibility: default,
				status: PostStatus::Live,
				likes: Vec::new(),
				replies: Vec::new(),
				parent: None,
			},
		);
		assert_eq!(
			expected.newest_first.first(),
			Some(&pid),
			"the new post heads newest-first"
		);
		assert_eq!(
			from_db(db),
			expected,
			"publish must insert exactly new-post and change nothing else"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P2: publish with a parent -- `successful-reply` (Twitter.agda:400-422),
// including `new-reply`'s visibility rule (Twitter.agda:213-217).
// Agda: `reply-success-everyone` / `reply-success-followers-only`.
// ---------------------------------------------------------------------------

/// `successful-reply` on a parent the session can read: the reply takes
/// `new-reply`'s visibility (the account default for an `everyone` parent,
/// `followers-only` for a `followers-only` one), points at the parent, is
/// prepended to the parent's reply list and heads `newest-first`; every other
/// column of every other row is untouched.
#[test]
fn reply_to_a_readable_parent_creates_a_reply() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, parent) = existing_or_added(
			&seeded,
			|post| can_read(&seeded, &user, post),
			|| post(&user, "parent", Visibility::Everyone),
		);
		reseed(db, world, &seeded);

		let parent_before = seeded.posts[&parent].clone();
		let default = seeded.accounts[&user].visibility;
		let visibility = match parent_before.visibility {
			Visibility::Everyone => default,
			Visibility::FollowersOnly => Visibility::FollowersOnly,
		};

		let before = seeded.clone();
		let pid = created(publish(db, sid, &body.0, Some(parent)).expect("publish"));
		assert_ne!(pid, parent, "a reply never reuses its parent's id");

		let expected = posted_world(
			&before,
			pid,
			PostState {
				author: user.clone(),
				text: body.0.clone(),
				visibility,
				status: PostStatus::Live,
				likes: Vec::new(),
				replies: Vec::new(),
				parent: Some(parent),
			},
		);
		// `preplies` becomes `pid ∷ preplies`: the new reply is the newest child.
		let mut preplies = vec![pid];
		preplies.extend(parent_before.replies.iter().copied());
		assert_eq!(
			expected.posts[&parent].replies, preplies,
			"the parent's reply list gains pid at the front"
		);

		// The parent keeps every other field (`ppost` -> `ppost'`).
		assert_eq!(
			PostState {
				replies: Vec::new(),
				..expected.posts[&parent].clone()
			},
			PostState {
				replies: Vec::new(),
				..parent_before
			},
			"a reply changes only the parent's reply list"
		);
		assert_eq!(
			from_db(db),
			expected,
			"publish with a parent must insert exactly new-reply"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P3: failed replies -- `failed-reply` (Twitter.agda:424-430).
// Agda: `reply-denied-absent` / `reply-denied-deleted` / `reply-denied-private`.
// ---------------------------------------------------------------------------

/// `failed-reply` when the parent is absent: `denied`, world untouched.
#[test]
fn reply_to_an_absent_parent_is_denied() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, sid, _) = with_actor(world);
		reseed(db, world, &seeded);
		let absent = absent_post(&seeded);
		assert!(!seeded.posts.contains_key(&absent));

		assert_eq!(
			publish(db, sid, &body.0, Some(absent)).expect("publish"),
			EngineResult::Denied
		);
		assert_eq!(
			from_db(db),
			seeded,
			"a failed reply must not change the world"
		);
		TestResult::passed()
	});
}

/// `failed-reply` when the parent is deleted (`can-read-deleted`): `denied`,
/// world untouched.
#[test]
fn reply_to_a_deleted_parent_is_denied() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, parent) = existing_or_added(
			&seeded,
			|post| post.status == PostStatus::Deleted,
			|| {
				deleted(post(
					&unfollowed_author(&seeded, &user),
					"gone",
					Visibility::Everyone,
				))
			},
		);
		reseed(db, world, &seeded);

		assert_eq!(
			publish(db, sid, &body.0, Some(parent)).expect("publish"),
			EngineResult::Denied
		);
		assert_eq!(
			from_db(db),
			seeded,
			"a failed reply must not change the world"
		);
		TestResult::passed()
	});
}

/// `failed-reply` when the parent is `followers-only` and the session's user
/// does not follow its author (`can-read-private`): `denied`, world untouched.
#[test]
fn reply_to_an_unfollowed_private_parent_is_denied() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, parent) = existing_or_added(
			&seeded,
			|post| {
				post.status == PostStatus::Live
					&& post.visibility == Visibility::FollowersOnly
					&& !follows(&seeded, &user, &post.author)
			},
			|| {
				post(
					&unfollowed_author(&seeded, &user),
					"secret",
					Visibility::FollowersOnly,
				)
			},
		);
		reseed(db, world, &seeded);
		assert!(
			!can_read(&seeded, &user, &seeded.posts[&parent]),
			"precondition: the parent is unreadable"
		);

		assert_eq!(
			publish(db, sid, &body.0, Some(parent)).expect("publish"),
			EngineResult::Denied
		);
		assert_eq!(
			from_db(db),
			seeded,
			"a failed reply must not change the world"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P4: delete -- `delete-post` (Twitter.agda:432-449), with no `live` premise.
// Agda: `delete-success` / `delete-idempotent`.
// ---------------------------------------------------------------------------

/// `delete-post`: the author's live post becomes `deleted`; author, text,
/// visibility, parent, likes, replies, the whole of `newest-first` and every
/// other row are unchanged.
#[test]
fn delete_of_an_own_live_post_marks_it_deleted() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, own) = existing_or_added(
			&seeded,
			|post| post.status == PostStatus::Live && post.author == user,
			|| post(&user, "mine", Visibility::FollowersOnly),
		);
		reseed(db, world, &seeded);
		let before = seeded.clone();

		assert_eq!(delete(db, sid, own).expect("delete"), EngineResult::Success);

		let mut expected = before.clone();
		expected
			.posts
			.get_mut(&own)
			.expect("the post exists")
			.status = PostStatus::Deleted;
		expected
			.validate()
			.expect("the expected tombstone world is valid");

		// Only `status` moved on the post itself (`deleted-post pst`): every
		// other field of the row is the one `before` held.
		assert_eq!(
			expected.posts[&own],
			PostState {
				status: PostStatus::Deleted,
				..before.posts[&own].clone()
			},
			"only the status changes on the post itself"
		);
		// ... and the tombstone keeps its place in `newest-first`.
		assert_eq!(
			expected.newest_first, before.newest_first,
			"a tombstone keeps its place in newest-first"
		);
		assert_eq!(
			from_db(db),
			expected,
			"delete must change nothing but the status"
		);
		TestResult::passed()
	});
}

/// `delete-post` has no `live` premise: deleting an already `deleted` own post
/// succeeds and changes nothing at all (`delete-idempotent`).
#[test]
fn delete_of_an_already_deleted_own_post_succeeds() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, own) = existing_or_added(
			&seeded,
			|post| post.status == PostStatus::Deleted && post.author == user,
			|| deleted(post(&user, "mine", Visibility::Everyone)),
		);
		reseed(db, world, &seeded);

		assert_eq!(delete(db, sid, own).expect("delete"), EngineResult::Success);
		assert_eq!(from_db(db), seeded, "an idempotent delete changes nothing");
		TestResult::passed()
	});
}

/// `failed-delete-non-existant-post`: an absent post is `denied` (not an error)
/// and the world is untouched (`delete-denied-absent`).
#[test]
fn delete_of_an_absent_post_is_denied() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, sid, _) = with_actor(world);
		reseed(db, world, &seeded);
		let absent = absent_post(&seeded);

		assert_eq!(
			delete(db, sid, absent).expect("delete"),
			EngineResult::Denied
		);
		assert_eq!(
			from_db(db),
			seeded,
			"a failed delete must not change the world"
		);
		TestResult::passed()
	});
}

/// `failed-delete-not-author`: someone else's post is `denied` and untouched,
/// even when its author follows the deleter (`delete-denied-not-author`).
#[test]
fn delete_of_a_foreign_post_is_denied() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (mut seeded, sid, user) = with_actor(world);
		let (extended, foreign) = existing_or_added(
			&seeded,
			|post| post.author != user,
			|| {
				post(
					&unfollowed_author(&seeded, &user),
					"stranger",
					Visibility::Everyone,
				)
			},
		);
		seeded = extended;
		// A follow in the other direction must not help.
		let author = seeded.posts[&foreign].author.clone();
		if !follows(&seeded, &author, &user) {
			seeded.follows.insert((author, user.clone()));
			seeded
				.validate()
				.expect("the world with an extra follow is valid");
		}
		reseed(db, world, &seeded);

		assert_eq!(
			delete(db, sid, foreign).expect("delete"),
			EngineResult::Denied
		);
		assert_eq!(
			from_db(db),
			seeded,
			"a failed delete must not change the world"
		);
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P5: read-post with a session -- `read-post-logged-in` (Twitter.agda:540-548)
// and the `cant-read-post-*` rules (Twitter.agda:518-538).
// Agda: `read-logged-in`, `read-denied-absent` / `-deleted` / `-private`.
// ---------------------------------------------------------------------------

/// `read-post-logged-in`: `returned-post author txt (length likes) replies` for
/// a readable live post; `likes` is the length of the like list and `replies`
/// is the world's reply list for the post (already `seq`-descending). A read
/// changes nothing.
#[test]
fn read_logged_in_returns_a_readable_post() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, pid) = existing_or_added(
			&seeded,
			|post| can_read(&seeded, &user, post),
			|| post(&user, "hello", Visibility::Everyone),
		);
		reseed(db, world, &seeded);
		let post = seeded.posts[&pid].clone();

		let (author, text, likes, replies) =
			returned(read_post(db, Some(sid), pid).expect("read-post"));
		assert_eq!(author, post.author);
		assert_eq!(text, post.text);
		assert_eq!(likes, post.likes.len() as u64);
		assert_eq!(replies, post.replies, "the reply list is the world's");
		assert_eq!(from_db(db), seeded, "a read must not change the world");
		TestResult::passed()
	});
}

/// `cant-read-post-public` / `-private-deleted` / `-private`: a logged-in read
/// of an absent, deleted or unfollowed `followers-only` post is `denied`, and
/// the world is untouched.
#[test]
fn read_logged_in_is_denied_for_unreadable_posts() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, sid, user) = with_actor(world);
		let (seeded, gone) = existing_or_added(
			&seeded,
			|post| post.status == PostStatus::Deleted,
			|| {
				deleted(post(
					&unfollowed_author(&seeded, &user),
					"gone",
					Visibility::Everyone,
				))
			},
		);
		let (seeded, secret) = existing_or_added(
			&seeded,
			|post| {
				post.status == PostStatus::Live
					&& post.visibility == Visibility::FollowersOnly
					&& !follows(&seeded, &user, &post.author)
			},
			|| {
				post(
					&unfollowed_author(&seeded, &user),
					"secret",
					Visibility::FollowersOnly,
				)
			},
		);
		// Take the absent id only now: `with_post` allocates with the same
		// `absent_post`, so an id computed before the extensions above could
		// name a post this test just added.
		let absent = absent_post(&seeded);
		assert!(
			!seeded.posts.contains_key(&absent),
			"the absent id is genuinely unused"
		);
		reseed(db, world, &seeded);
		// Preconditions: the two existing targets really are unreadable.
		assert!(!can_read(
			&seeded,
			&user,
			seeded.posts.get(&gone).expect("the deleted post exists")
		));
		assert!(!can_read(
			&seeded,
			&user,
			seeded.posts.get(&secret).expect("the private post exists")
		));

		for pid in [absent, gone, secret] {
			assert_eq!(
				read_post(db, Some(sid), pid).expect("read-post"),
				EngineResult::Denied,
				"reading {pid:?}"
			);
			assert_eq!(
				from_db(db),
				seeded,
				"a denied read must not change the world"
			);
		}
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P6: read-post anonymously -- `read-post-anonymously` (Twitter.agda:550-554)
// and the `failed-access` expiry of the unreadable cases.
// Agda: `read-anonymous` / `read-anonymous-expired`.
// ---------------------------------------------------------------------------

/// `read-post-anonymously`: a public live post is returned with its author,
/// text, like count and reply list, without a session and without a change.
#[test]
fn read_anonymous_returns_a_public_live_post() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, _, user) = with_actor(world);
		let (seeded, pid) = existing_or_added(&seeded, is_public, || {
			post(
				&unfollowed_author(&seeded, &user),
				"public",
				Visibility::Everyone,
			)
		});
		reseed(db, world, &seeded);
		let post = seeded.posts[&pid].clone();

		let (author, text, likes, replies) = returned(read_post(db, None, pid).expect("read-post"));
		assert_eq!(author, post.author);
		assert_eq!(text, post.text);
		assert_eq!(likes, post.likes.len() as u64);
		assert_eq!(replies, post.replies);
		assert_eq!(from_db(db), seeded, "a read must not change the world");
		TestResult::passed()
	});
}

/// An anonymous read of an absent, `followers-only` or deleted post is
/// `Expired` -- not `Denied`: `extract-sid (read-post nothing pid) = nothing`
/// (Twitter.agda:196), so `failed-access` (Twitter.agda:464-468) is vacuous
/// (`read-anonymous-expired`) -- and nothing changes.
#[test]
fn read_anonymous_expires_for_unreadable_posts() {
	check(|db: &Db, world: &WorldState, _: ()| -> TestResult {
		let (seeded, _, user) = with_actor(world);
		let (seeded, secret) = existing_or_added(
			&seeded,
			// `live`, so this cannot coincide with the deleted `gone` below.
			|post| post.status == PostStatus::Live && post.visibility == Visibility::FollowersOnly,
			|| {
				post(
					&unfollowed_author(&seeded, &user),
					"secret",
					Visibility::FollowersOnly,
				)
			},
		);
		let (seeded, gone) = existing_or_added(
			&seeded,
			|post| post.status == PostStatus::Deleted,
			|| {
				deleted(post(
					&unfollowed_author(&seeded, &user),
					"gone",
					Visibility::Everyone,
				))
			},
		);
		// Take the absent id only now: `with_post` allocates with the same
		// `absent_post`, so an id computed before the extensions above could
		// name a post this test just added.
		let absent = absent_post(&seeded);
		assert!(
			!seeded.posts.contains_key(&absent),
			"the absent id is genuinely unused"
		);
		reseed(db, world, &seeded);

		for pid in [absent, secret, gone] {
			assert_eq!(
				read_post(db, None, pid).expect("read-post"),
				EngineResult::Expired,
				"anonymous read of {pid:?}"
			);
			assert_eq!(
				from_db(db),
				seeded,
				"an expired read must not change the world"
			);
		}
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// P7: failed-access on every session-carrying post command (Twitter.agda:464-468).
// Agda: `publish-expired`, `delete-expired`, `read-expired`.
// ---------------------------------------------------------------------------

/// Every post command that carries a session answers `expired` and leaves the
/// world untouched when its session is revoked or was never issued.
#[test]
fn post_commands_expire_with_an_inactive_session() {
	check(|db: &Db, world: &WorldState, body: Body| -> TestResult {
		let (seeded, _, _) = with_actor(world);
		let (seeded, revoked) = with_revoked_session(&seeded);
		reseed(db, world, &seeded);
		let unused = absent_session(&seeded);
		assert_eq!(seeded.session_status(unused), SessionStatus::Unused);
		let target = seeded
			.newest_first
			.first()
			.copied()
			.unwrap_or_else(|| absent_post(&seeded));

		for sid in [revoked, unused] {
			assert_eq!(
				publish(db, sid, &body.0, None).expect("publish"),
				EngineResult::Expired,
				"publish with {sid:?}"
			);
			assert_eq!(from_db(db), seeded, "an expired publish changes nothing");

			assert_eq!(
				publish(db, sid, &body.0, Some(target)).expect("publish"),
				EngineResult::Expired,
				"reply with {sid:?}"
			);
			assert_eq!(from_db(db), seeded, "an expired reply changes nothing");

			assert_eq!(
				delete(db, sid, target).expect("delete"),
				EngineResult::Expired,
				"delete with {sid:?}"
			);
			assert_eq!(from_db(db), seeded, "an expired delete changes nothing");

			assert_eq!(
				read_post(db, Some(sid), target).expect("read-post"),
				EngineResult::Expired,
				"read-post with {sid:?}"
			);
			assert_eq!(from_db(db), seeded, "an expired read changes nothing");
		}
		TestResult::passed()
	});
}

// ---------------------------------------------------------------------------
// Deterministic unit tests: one database each, worlds built as data.
// ---------------------------------------------------------------------------

/// Two accounts (`ada`, `bob`), an active session for `bob`, and a public live
/// post `200` by `ada` with two replies ordered `seq`-descending and three
/// likes. `bob` follows `ada`.
fn fixture() -> WorldState {
	let mut root = post("ada", "hello", Visibility::Everyone);
	root.replies = vec![PostId(202), PostId(201)];
	root.likes = vec!["bob".to_string(), "carol".to_string(), "dave".to_string()];
	let mut one = post("ada", "one", Visibility::Everyone);
	one.parent = Some(PostId(200));
	let mut two = post("bob", "two", Visibility::Everyone);
	two.parent = Some(PostId(200));
	let world = WorldState {
		accounts: BTreeMap::from([
			("ada".to_string(), account("pw-ada", Visibility::Everyone)),
			(
				"bob".to_string(),
				account("pw-bob", Visibility::FollowersOnly),
			),
		]),
		sessions: HashMap::from([(SessionId(100), SessionStatus::Active("bob".to_string()))]),
		posts: HashMap::from([(PostId(200), root), (PostId(201), one), (PostId(202), two)]),
		follows: BTreeSet::from([("bob".to_string(), "ada".to_string())]),
		// 202 ranks before 201, so the parent's reply list is [202, 201].
		newest_first: vec![PostId(202), PostId(201), PostId(200)],
	};
	world.validate().expect("the fixture is valid");
	world
}

/// A fresh database holding `world`.
fn seeded(world: &WorldState) -> Db {
	let db = Db::in_memory().expect("create in-memory database");
	reset(&db);
	materialise(&db, world);
	assert_eq!(from_db(&db), *world, "the fixture round-trips");
	db
}

/// `read-post-logged-in` reports the like *count* and the parent's reply list in
/// `seq` order (`store::replies_of`), and changes nothing.
#[test]
fn read_post_reports_the_like_count_and_the_seq_ordered_replies() {
	let world = fixture();
	let db = seeded(&world);

	assert_eq!(
		read_post(&db, Some(SessionId(100)), PostId(200)).expect("read-post"),
		EngineResult::ReturnedPost {
			author: "ada".to_string(),
			text: "hello".to_string(),
			likes: 3,
			replies: vec![PostId(202), PostId(201)],
		}
	);
	assert_eq!(from_db(&db), world, "a read must not change the world");
}

/// `new-reply` (Twitter.agda:213-217), both halves: an `everyone` parent keeps
/// the author's default visibility, a `followers-only` parent forces
/// `followers-only`.
#[test]
fn reply_visibility_comes_from_the_parent_when_it_is_followers_only() {
	let mut world = fixture();
	// `eve`'s default is the permissive visibility, unlike `bob`'s
	// `followers-only`; both follow `ada`, so both parents below are readable.
	world
		.accounts
		.insert("eve".to_string(), account("pw-eve", Visibility::Everyone));
	world
		.sessions
		.insert(SessionId(7), SessionStatus::Active("eve".to_string()));
	world.follows.insert(("eve".to_string(), "ada".to_string()));
	world.validate().expect("the extended world is valid");
	let (world, parent) = with_post(&world, post("ada", "secret", Visibility::FollowersOnly));
	let db = seeded(&world);

	// `bob`'s default is `followers-only`, so the `everyone` parent keeps it.
	let pid = created(publish(&db, SessionId(100), "reply", Some(PostId(200))).expect("publish"));
	let expected = posted_world(
		&world,
		pid,
		PostState {
			parent: Some(PostId(200)),
			..post("bob", "reply", Visibility::FollowersOnly)
		},
	);
	assert_eq!(from_db(&db), expected);

	// A `followers-only` parent forces `followers-only` for an account whose
	// default is the permissive one.
	let pid = created(publish(&db, SessionId(7), "reply", Some(parent)).expect("publish"));
	let expected = posted_world(
		&expected,
		pid,
		PostState {
			parent: Some(parent),
			..post("eve", "reply", Visibility::FollowersOnly)
		},
	);
	assert_eq!(from_db(&db), expected);
}

/// A reply is prepended to the parent's reply list in arrival order and heads
/// `newest-first`; nothing else moves.
#[test]
fn replies_are_prepended_in_arrival_order() {
	let mut expected = fixture();
	let db = seeded(&expected);

	for text in ["first", "second"] {
		let before = expected.clone();
		let pid = created(publish(&db, SessionId(100), text, Some(PostId(200))).expect("publish"));
		expected = posted_world(
			&before,
			pid,
			PostState {
				parent: Some(PostId(200)),
				..post("bob", text, Visibility::FollowersOnly)
			},
		);
	}

	assert_eq!(
		expected.posts[&PostId(200)].replies,
		expected.newest_first[..4].to_vec(),
		"both replies are the two newest posts, newest first"
	);
	assert_eq!(from_db(&db), expected);
}

/// A foreign post is `denied`; an own post becomes a tombstone that keeps its
/// id and likes, so a later publish gets another id.
#[test]
fn delete_keeps_the_tombstone() {
	let world = fixture();
	let db = seeded(&world);

	// `201` is `ada`'s, `202` is `bob`'s.
	assert_eq!(
		delete(&db, SessionId(100), PostId(201)).expect("delete"),
		EngineResult::Denied
	);
	assert_eq!(from_db(&db), world, "a denied delete changes nothing");

	let mut expected = world.clone();
	expected
		.posts
		.get_mut(&PostId(202))
		.expect("the post exists")
		.status = PostStatus::Deleted;
	expected.validate().expect("the expected world is valid");
	assert_eq!(
		delete(&db, SessionId(100), PostId(202)).expect("delete"),
		EngineResult::Success
	);
	assert_eq!(from_db(&db), expected);

	// A tombstone still occupies its id.
	let pid = created(publish(&db, SessionId(100), "new", None).expect("publish"));
	let after = posted_world(
		&expected,
		pid,
		PostState {
			author: "bob".to_string(),
			..post("bob", "new", Visibility::FollowersOnly)
		},
	);
	after.validate().expect("the expected world is valid");
	assert_eq!(from_db(&db), after);
	assert_eq!(
		after.posts[&PostId(202)].status,
		PostStatus::Deleted,
		"the tombstone is kept"
	);
}

/// Anonymous reads of an absent, `followers-only` or deleted post are `Expired`
/// (`read-anonymous-expired`) and change nothing.
#[test]
fn anonymous_reads_of_unreadable_posts_expire() {
	let (world, secret) = with_post(&fixture(), post("ada", "secret", Visibility::FollowersOnly));
	let (world, gone) = with_post(&world, deleted(post("ada", "gone", Visibility::Everyone)));
	let db = seeded(&world);

	for pid in [absent_post(&world), secret, gone] {
		assert_eq!(
			read_post(&db, None, pid).expect("read-post"),
			EngineResult::Expired,
			"anonymous read of {pid:?}"
		);
	}
	assert_eq!(from_db(&db), world, "an expired read changes nothing");
}

/// `delete-post` leaves the reply list alone (`Post.replies post ≡
/// Post.replies post'`): a tombstoned parent keeps its children, in `seq` order,
/// and the children keep pointing at it.
#[test]
fn delete_of_a_parent_keeps_its_replies() {
	let mut root = post("bob", "root", Visibility::Everyone);
	root.replies = vec![PostId(302), PostId(301)];
	let mut first = post("ada", "first", Visibility::Everyone);
	first.parent = Some(PostId(300));
	let mut second = post("carol", "second", Visibility::Everyone);
	second.parent = Some(PostId(300));
	let world = WorldState {
		accounts: BTreeMap::from([("bob".to_string(), account("pw-bob", Visibility::Everyone))]),
		sessions: HashMap::from([(SessionId(100), SessionStatus::Active("bob".to_string()))]),
		posts: HashMap::from([
			(PostId(300), root),
			(PostId(301), first),
			(PostId(302), second),
		]),
		follows: BTreeSet::new(),
		newest_first: vec![PostId(302), PostId(301), PostId(300)],
	};
	world.validate().expect("the fixture is valid");
	let db = seeded(&world);

	assert_eq!(
		delete(&db, SessionId(100), PostId(300)).expect("delete"),
		EngineResult::Success
	);
	let after = from_db(&db);
	assert_eq!(after.posts[&PostId(300)].status, PostStatus::Deleted);
	assert_eq!(
		after.posts[&PostId(300)].replies,
		vec![PostId(302), PostId(301)],
		"the tombstone keeps its reply list"
	);
	assert_eq!(
		after.posts[&PostId(301)].parent,
		Some(PostId(300)),
		"the children still point at the tombstone"
	);
	assert_eq!(after.posts[&PostId(301)].status, PostStatus::Live);
}

/// A `followers-only` post by the session's user is not special: without a
/// self-follow it is unreadable, so replying to it is `denied`
/// (`can-read-private`); a self-follow makes the same reply succeed.
#[test]
fn reply_to_an_own_private_post_needs_a_self_follow() {
	let (world, own) = with_post(
		&{
			let mut world = empty_world();
			world
				.accounts
				.insert("bob".to_string(), account("pw-bob", Visibility::Everyone));
			world
				.sessions
				.insert(SessionId(100), SessionStatus::Active("bob".to_string()));
			world
		},
		post("bob", "mine", Visibility::FollowersOnly),
	);
	let db = seeded(&world);

	assert_eq!(
		publish(&db, SessionId(100), "reply", Some(own)).expect("publish"),
		EngineResult::Denied,
		"the author does not follow themself"
	);
	assert_eq!(from_db(&db), world, "a failed reply changes nothing");

	let mut followed = world.clone();
	followed
		.follows
		.insert(("bob".to_string(), "bob".to_string()));
	followed
		.validate()
		.expect("the world with a self-follow is valid");
	reset(&db);
	materialise(&db, &followed);

	let pid = created(publish(&db, SessionId(100), "reply", Some(own)).expect("publish"));
	let expected = posted_world(
		&followed,
		pid,
		PostState {
			parent: Some(own),
			..post("bob", "reply", Visibility::FollowersOnly)
		},
	);
	assert_eq!(from_db(&db), expected);
}
