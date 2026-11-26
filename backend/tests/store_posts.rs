//! Unit tests for the post-lifecycle store helpers added in T2b.
//!
//! These helpers are internal plumbing without a spec `Step` of their own, so
//! -- as for T1 -- they get deterministic unit tests rather than properties
//! and Agda proofs. The spec-level behaviour they support is property tested
//! in `tests/engine_posts.rs`.

use diesel::RunQueryDsl;
use diesel::sql_types::Text;

use formal_twitter::db::Db;
use formal_twitter::model::{DbError, Post, PostId, PostStatus, SessionId, Visibility};
use formal_twitter::store;

const PASSWORD: &str = "secret";

fn database() -> Db {
	Db::in_memory().expect("create in-memory database")
}

fn seed_account(db: &Db, name: &str) {
	assert!(
		db.write(|c| store::create_account(c, name, PASSWORD))
			.expect("seed account"),
		"precondition: {name} is a free username"
	);
}

fn seed_session(db: &Db, sid: SessionId, name: &str) {
	db.write(|c| store::activate_session(c, sid, name))
		.expect("seed session");
}

fn seed_post(db: &Db, id: PostId, author: &str, text: &str, vis: Visibility) {
	db.write(|c| store::insert_post(c, id, author, text, vis))
		.expect("seed post");
}

fn seed_reply(db: &Db, id: PostId, author: &str, text: &str, vis: Visibility, parent: PostId) {
	db.write(|c| store::insert_reply(c, id, author, text, vis, parent))
		.expect("seed reply");
}

fn active_user(db: &Db, sid: SessionId) -> Option<String> {
	db.read(|c| store::active_user(c, sid))
		.expect("active user")
}

fn can_read_post(db: &Db, user: &str, id: PostId) -> bool {
	db.read(|c| store::can_read_post(c, user, id))
		.expect("can read post")
}

fn can_read_anonymous(db: &Db, id: PostId) -> bool {
	db.read(|c| store::can_read_anonymous(c, id))
		.expect("can read anonymously")
}

fn post_view(db: &Db, id: PostId) -> Option<store::PostView> {
	db.read(|c| store::post_view(c, id)).expect("post view")
}

fn delete_own(db: &Db, id: PostId, author: &str) -> Option<Post> {
	db.write(|c| store::delete_own(c, id, author))
		.expect("delete own")
}

fn status_of(db: &Db, id: PostId) -> PostStatus {
	db.read(|c| store::get_post(c, id))
		.expect("read post")
		.expect("post row exists")
		.status
}

const SID: SessionId = SessionId(100);
const REVOKED: SessionId = SessionId(101);
const UNUSED: SessionId = SessionId(102);
const POST: PostId = PostId(200);
const REPLY: PostId = PostId(201);
const OTHER: PostId = PostId(202);
const ABSENT: PostId = PostId(9_000_000);

// ---------------------------------------------------------------------------
// active_user
// ---------------------------------------------------------------------------

#[test]
fn active_user_reports_the_active_sessions_user() {
	let db = database();
	seed_account(&db, "ada");
	seed_session(&db, SID, "ada");
	assert_eq!(active_user(&db, SID), Some("ada".to_string()));
}

#[test]
fn active_user_is_none_for_revoked_unknown_and_accountless_sessions() {
	let db = database();
	seed_account(&db, "ada");
	seed_session(&db, SID, "ada");
	seed_session(&db, REVOKED, "ada");
	db.write(|c| store::revoke_session(c, REVOKED)).unwrap();
	// A session whose account vanished: `only-valid-sessions` forbids this,
	// but the helper must stay total.
	seed_session(&db, SessionId(103), "ghost");

	assert_eq!(active_user(&db, SID), Some("ada".to_string()));
	assert_eq!(active_user(&db, REVOKED), None);
	assert_eq!(active_user(&db, UNUSED), None);
	assert_eq!(active_user(&db, SessionId(103)), None);
}

// ---------------------------------------------------------------------------
// active_account
// ---------------------------------------------------------------------------

fn active_account(db: &Db, sid: SessionId) -> Option<(String, Visibility)> {
	db.read(|c| store::active_account(c, sid))
		.expect("active account")
}

/// `create_account` only ever makes `everyone` accounts, so a
/// `followers-only` one is set directly.
fn set_default_visibility(db: &Db, name: &str, vis: Visibility) {
	let text = match vis {
		Visibility::Everyone => "everyone",
		Visibility::FollowersOnly => "followers-only",
	};
	db.write(|c| {
		diesel::sql_query("UPDATE accounts SET default_visibility = ? WHERE username = ?")
			.bind::<Text, _>(text)
			.bind::<Text, _>(name)
			.execute(c)
			.map(|_| ())
			.map_err(DbError)
	})
	.expect("set default visibility");
}

#[test]
fn active_account_reports_the_active_sessions_username_and_visibility() {
	let db = database();
	seed_account(&db, "ada");
	seed_session(&db, SID, "ada");
	assert_eq!(
		active_account(&db, SID),
		Some(("ada".to_string(), Visibility::Everyone))
	);

	set_default_visibility(&db, "ada", Visibility::FollowersOnly);
	assert_eq!(
		active_account(&db, SID),
		Some(("ada".to_string(), Visibility::FollowersOnly)),
		"the account's current default-visibility, not a copy taken at login"
	);
}

#[test]
fn active_account_is_none_for_revoked_unknown_and_accountless_sessions() {
	let db = database();
	seed_account(&db, "ada");
	seed_session(&db, SID, "ada");
	seed_session(&db, REVOKED, "ada");
	db.write(|c| store::revoke_session(c, REVOKED)).unwrap();
	seed_session(&db, SessionId(103), "ghost");

	assert_eq!(
		active_account(&db, SID),
		Some(("ada".to_string(), Visibility::Everyone))
	);
	assert_eq!(active_account(&db, REVOKED), None);
	assert_eq!(active_account(&db, UNUSED), None);
	assert_eq!(active_account(&db, SessionId(103)), None);
}

#[test]
fn active_account_agrees_with_active_user() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_session(&db, SID, "ada");
	seed_session(&db, REVOKED, "bob");
	db.write(|c| store::revoke_session(c, REVOKED)).unwrap();
	seed_session(&db, SessionId(103), "ghost");
	for sid in [SID, REVOKED, UNUSED, SessionId(103)] {
		assert_eq!(
			active_account(&db, sid).map(|(name, _)| name),
			active_user(&db, sid),
			"the two helpers must agree on the user"
		);
	}
}

// ---------------------------------------------------------------------------
// can_read_post
// ---------------------------------------------------------------------------

#[test]
fn can_read_post_accepts_public_live_posts() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_post(&db, POST, "ada", "hello", Visibility::Everyone);
	assert!(can_read_post(&db, "bob", POST));
	assert!(can_read_post(&db, "ada", POST), "the author can read it");
}

#[test]
fn can_read_post_accepts_followed_private_posts_only() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_post(&db, POST, "ada", "secret", Visibility::FollowersOnly);
	assert!(!can_read_post(&db, "bob", POST));
	db.write(|c| store::add_follow(c, "bob", "ada")).unwrap();
	assert!(can_read_post(&db, "bob", POST));
	// A follow in the other direction does not help another reader.
	seed_account(&db, "carol");
	db.write(|c| store::add_follow(c, "ada", "carol")).unwrap();
	assert!(!can_read_post(&db, "carol", POST));
}

#[test]
fn can_read_post_rejects_deleted_absent_and_private_unfollowed() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_post(&db, POST, "ada", "gone", Visibility::Everyone);
	seed_post(&db, OTHER, "ada", "secret", Visibility::FollowersOnly);
	db.write(|c| store::soft_delete_post(c, POST)).unwrap();

	assert!(
		!can_read_post(&db, "ada", POST),
		"deleted, even for the author"
	);
	assert!(!can_read_post(&db, "bob", POST), "deleted");
	assert!(!can_read_post(&db, "bob", OTHER), "private, unfollowed");
	assert!(!can_read_post(&db, "bob", ABSENT), "absent");
}

// ---------------------------------------------------------------------------
// can_read_anonymous
// ---------------------------------------------------------------------------

#[test]
fn can_read_anonymous_is_public_only() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, POST, "ada", "public", Visibility::Everyone);
	seed_post(&db, OTHER, "ada", "secret", Visibility::FollowersOnly);
	db.write(|c| store::add_follow(c, "bob", "ada")).unwrap();

	assert!(can_read_anonymous(&db, POST));
	assert!(!can_read_anonymous(&db, OTHER), "private is never public");
	assert!(!can_read_anonymous(&db, ABSENT), "absent");

	db.write(|c| store::soft_delete_post(c, POST)).unwrap();
	assert!(!can_read_anonymous(&db, POST), "deleted");
}

// ---------------------------------------------------------------------------
// post_view
// ---------------------------------------------------------------------------

#[test]
fn post_view_returns_the_post_with_its_like_count() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, POST, "ada", "hello", Visibility::Everyone);
	for liker in ["bob", "carol", "dave"] {
		db.write(|c| store::add_like(c, POST, liker)).unwrap();
	}
	// A like on another post must not leak into the count.
	seed_post(&db, OTHER, "ada", "other", Visibility::Everyone);
	db.write(|c| store::add_like(c, OTHER, "bob")).unwrap();

	let view = post_view(&db, POST).expect("the post exists");
	assert_eq!(view.post.id, POST);
	assert_eq!(view.post.author, "ada");
	assert_eq!(view.post.text, "hello");
	assert_eq!(view.post.visibility, Visibility::Everyone);
	assert_eq!(view.post.status, PostStatus::Live);
	assert_eq!(view.post.parent, None);
	assert_eq!(view.likes, 3);
}

#[test]
fn post_view_without_likes_is_zero_and_absent_view_is_none() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, POST, "ada", "quiet", Visibility::Everyone);

	assert_eq!(post_view(&db, POST).expect("the post exists").likes, 0);
	assert_eq!(post_view(&db, ABSENT), None);
}

#[test]
fn post_view_reports_parent_and_likes_of_replies() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_post(&db, POST, "ada", "hello", Visibility::Everyone);
	seed_reply(&db, REPLY, "bob", "reply", Visibility::FollowersOnly, POST);
	for liker in ["ada", "bob"] {
		db.write(|c| store::add_like(c, REPLY, liker)).unwrap();
	}

	let view = post_view(&db, REPLY).expect("the reply exists");
	assert_eq!(view.post.parent, Some(POST));
	assert_eq!(view.post.visibility, Visibility::FollowersOnly);
	assert_eq!(view.likes, 2);
	// `post_view` counts likes only; the reply list still comes from `replies_of`.
	let replies = db
		.read(|c| store::replies_of(c, POST))
		.expect("read replies");
	assert_eq!(replies, vec![REPLY]);
}

// ---------------------------------------------------------------------------
// delete_own
// ---------------------------------------------------------------------------

#[test]
fn delete_own_returns_the_pre_image_and_marks_the_post_deleted() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, POST, "ada", "mine", Visibility::FollowersOnly);

	let pre = delete_own(&db, POST, "ada").expect("the author owns the post");
	assert_eq!(pre.id, POST);
	assert_eq!(pre.author, "ada");
	assert_eq!(pre.text, "mine");
	assert_eq!(pre.visibility, Visibility::FollowersOnly);
	assert_eq!(
		pre.status,
		PostStatus::Live,
		"the returned pre-image is live"
	);
	assert_eq!(status_of(&db, POST), PostStatus::Deleted);
}

#[test]
fn delete_own_on_a_deleted_post_succeeds_and_returns_the_tombstone() {
	let db = database();
	seed_account(&db, "ada");
	seed_post(&db, POST, "ada", "mine", Visibility::Everyone);
	db.write(|c| store::soft_delete_post(c, POST)).unwrap();

	let pre = delete_own(&db, POST, "ada").expect("still owned");
	assert_eq!(pre.status, PostStatus::Deleted);
	assert_eq!(status_of(&db, POST), PostStatus::Deleted);
}

#[test]
fn delete_own_is_none_for_foreign_and_absent_posts() {
	let db = database();
	seed_account(&db, "ada");
	seed_account(&db, "bob");
	seed_post(&db, POST, "ada", "mine", Visibility::Everyone);

	assert_eq!(delete_own(&db, POST, "bob"), None, "not the author");
	assert_eq!(status_of(&db, POST), PostStatus::Live, "left live");
	assert_eq!(delete_own(&db, ABSENT, "ada"), None, "absent");
	assert_eq!(status_of(&db, POST), PostStatus::Live);
}
