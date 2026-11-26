use diesel::{RunQueryDsl, SqliteConnection};

use formal_twitter::db::{Db, configure, establish, run_migrations};
use formal_twitter::ids::{allocate_post_id, allocate_session_id};
use formal_twitter::model::{DbError, PostId, PostStatus, SessionStatus, Visibility};
use formal_twitter::store::*;

fn conn() -> SqliteConnection {
	let mut c = establish(":memory:").expect("establish in-memory database");
	configure(&mut c).expect("configure connection");
	run_migrations(&mut c).expect("run migrations");
	c
}

#[derive(diesel::QueryableByName)]
struct NameRow {
	#[diesel(sql_type = diesel::sql_types::Text)]
	name: String,
}

fn table_names(c: &mut SqliteConnection) -> Vec<String> {
	let rows: Vec<NameRow> =
		diesel::sql_query("SELECT name FROM sqlite_master WHERE type = 'table'")
			.load(c)
			.expect("query sqlite_master");
	rows.into_iter().map(|row| row.name).collect()
}

#[derive(diesel::QueryableByName)]
struct SeqRow {
	#[diesel(sql_type = diesel::sql_types::BigInt)]
	seq: i64,
}

fn seq_of(c: &mut SqliteConnection, id: PostId) -> i64 {
	let rows: Vec<SeqRow> = diesel::sql_query("SELECT seq FROM posts WHERE id = ?")
		.bind::<diesel::sql_types::BigInt, _>(id.0)
		.load(c)
		.expect("read post seq");
	rows.first().expect("post should have a seq").seq
}

// ---------------------------------------------------------------------------
// Migrations
// ---------------------------------------------------------------------------

#[test]
fn migrations_apply_and_tables_exist() {
	let mut c = conn();
	let names = table_names(&mut c);
	for table in ["accounts", "sessions", "posts", "follows", "post_likes"] {
		assert!(
			names.iter().any(|name| name == table),
			"missing table {table}; found {names:?}"
		);
	}
}

// ---------------------------------------------------------------------------
// Accounts
// ---------------------------------------------------------------------------

#[test]
fn account_create_duplicate_and_get() {
	let mut c = conn();
	assert!(create_account(&mut c, "alice", "secret").unwrap());
	assert!(!create_account(&mut c, "alice", "other").unwrap());

	let account = get_account(&mut c, "alice")
		.unwrap()
		.expect("account exists");
	assert_eq!(account.username, "alice");
	assert_eq!(account.password, "secret");
	assert_eq!(account.default_visibility, Visibility::Everyone);

	assert!(get_account(&mut c, "nobody").unwrap().is_none());
}

// ---------------------------------------------------------------------------
// Sessions
// ---------------------------------------------------------------------------

#[test]
fn session_lifecycle() {
	let mut c = conn();
	create_account(&mut c, "u", "pw").unwrap();
	let sid = allocate_session_id(&mut c).unwrap();

	assert_eq!(get_session(&mut c, sid).unwrap(), SessionStatus::Unused);
	assert_ne!(SessionStatus::Revoked, SessionStatus::Unused);

	activate_session(&mut c, sid, "u").unwrap();
	assert_eq!(
		get_session(&mut c, sid).unwrap(),
		SessionStatus::Active("u".to_string())
	);
	assert_ne!(
		SessionStatus::Revoked,
		SessionStatus::Active("u".to_string())
	);

	revoke_session(&mut c, sid).unwrap();
	assert_eq!(get_session(&mut c, sid).unwrap(), SessionStatus::Revoked);
}

#[test]
fn session_second_activate_fails() {
	let mut c = conn();
	create_account(&mut c, "u", "pw").unwrap();
	let sid = allocate_session_id(&mut c).unwrap();
	activate_session(&mut c, sid, "u").unwrap();
	assert!(activate_session(&mut c, sid, "u").is_err());
}

#[test]
fn revoke_all_sessions_revokes_active() {
	let mut c = conn();
	create_account(&mut c, "u", "pw").unwrap();
	let s1 = allocate_session_id(&mut c).unwrap();
	let s2 = allocate_session_id(&mut c).unwrap();
	activate_session(&mut c, s1, "u").unwrap();
	activate_session(&mut c, s2, "u").unwrap();

	revoke_all_sessions(&mut c).unwrap();
	assert_eq!(get_session(&mut c, s1).unwrap(), SessionStatus::Revoked);
	assert_eq!(get_session(&mut c, s2).unwrap(), SessionStatus::Revoked);
}

// ---------------------------------------------------------------------------
// Posts
// ---------------------------------------------------------------------------

#[test]
fn insert_post_assigns_increasing_seq_and_roundtrips() {
	let mut c = conn();
	let p1 = allocate_post_id(&mut c).unwrap();
	let p2 = allocate_post_id(&mut c).unwrap();
	let p3 = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, p1, "a", "one", Visibility::Everyone).unwrap();
	insert_post(&mut c, p2, "a", "two", Visibility::FollowersOnly).unwrap();
	insert_post(&mut c, p3, "b", "three", Visibility::Everyone).unwrap();

	let s1 = seq_of(&mut c, p1);
	let s2 = seq_of(&mut c, p2);
	let s3 = seq_of(&mut c, p3);
	assert!(s1 < s2 && s2 < s3, "seq must increase: {s1} {s2} {s3}");

	assert_eq!(newest_first(&mut c, 10).unwrap(), vec![p3, p2, p1]);

	let post = get_post(&mut c, p2).unwrap().expect("post exists");
	assert_eq!(post.id, p2);
	assert_eq!(post.author, "a");
	assert_eq!(post.text, "two");
	assert_eq!(post.visibility, Visibility::FollowersOnly);
	assert_eq!(post.status, PostStatus::Live);
	assert_eq!(post.parent, None);
	assert!(get_post(&mut c, PostId(9_999_999)).unwrap().is_none());
}

#[test]
fn insert_reply_links_parent_and_lists_newest_first() {
	let mut c = conn();
	let parent = allocate_post_id(&mut c).unwrap();
	let r1 = allocate_post_id(&mut c).unwrap();
	let r2 = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, parent, "a", "root", Visibility::Everyone).unwrap();
	insert_reply(&mut c, r1, "b", "first reply", Visibility::Everyone, parent).unwrap();
	insert_reply(
		&mut c,
		r2,
		"c",
		"second reply",
		Visibility::Everyone,
		parent,
	)
	.unwrap();

	let reply = get_post(&mut c, r1).unwrap().expect("reply exists");
	assert_eq!(reply.parent, Some(parent));

	assert_eq!(replies_of(&mut c, parent).unwrap(), vec![r2, r1]);
	assert!(replies_of(&mut c, r1).unwrap().is_empty());
}

#[test]
fn soft_delete_keeps_row_and_lists_it() {
	let mut c = conn();
	let p = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, p, "a", "doomed", Visibility::Everyone).unwrap();
	soft_delete_post(&mut c, p).unwrap();

	let post = get_post(&mut c, p)
		.unwrap()
		.expect("deleted post is retained");
	assert_eq!(post.status, PostStatus::Deleted);
	assert!(newest_first(&mut c, 10).unwrap().contains(&p));
}

// ---------------------------------------------------------------------------
// Likes
// ---------------------------------------------------------------------------

#[test]
fn likes_are_idempotent_and_removable() {
	let mut c = conn();
	let p = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, p, "a", "likeable", Visibility::Everyone).unwrap();

	assert!(!is_liked(&mut c, p, "u").unwrap());
	assert_eq!(like_count(&mut c, p).unwrap(), 0);

	add_like(&mut c, p, "u").unwrap();
	add_like(&mut c, p, "u").unwrap();
	assert!(is_liked(&mut c, p, "u").unwrap());
	assert_eq!(like_count(&mut c, p).unwrap(), 1);

	add_like(&mut c, p, "v").unwrap();
	assert_eq!(like_count(&mut c, p).unwrap(), 2);

	remove_like(&mut c, p, "u").unwrap();
	remove_like(&mut c, p, "u").unwrap();
	assert!(!is_liked(&mut c, p, "u").unwrap());
	assert_eq!(like_count(&mut c, p).unwrap(), 1);
}

#[test]
fn like_primary_key_prevents_duplicates() {
	let mut c = conn();
	let p = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, p, "a", "likeable", Visibility::Everyone).unwrap();
	add_like(&mut c, p, "u").unwrap();

	let duplicate = diesel::sql_query("INSERT INTO post_likes (pid, user) VALUES (?, ?)")
		.bind::<diesel::sql_types::BigInt, _>(p.0)
		.bind::<diesel::sql_types::Text, _>("u")
		.execute(&mut c);
	assert!(
		duplicate.is_err(),
		"post_likes primary key must reject duplicates"
	);
}

// ---------------------------------------------------------------------------
// Follows
// ---------------------------------------------------------------------------

#[test]
fn follows_are_idempotent_and_removable() {
	let mut c = conn();
	assert!(!is_following(&mut c, "a", "ghost").unwrap());

	// Following a user that does not exist is allowed by the model.
	add_follow(&mut c, "a", "ghost").unwrap();
	add_follow(&mut c, "a", "ghost").unwrap();
	assert!(is_following(&mut c, "a", "ghost").unwrap());
	assert!(!is_following(&mut c, "ghost", "a").unwrap());

	remove_follow(&mut c, "a", "ghost").unwrap();
	remove_follow(&mut c, "a", "ghost").unwrap();
	assert!(!is_following(&mut c, "a", "ghost").unwrap());
}

#[test]
fn follow_primary_key_prevents_duplicates() {
	let mut c = conn();
	add_follow(&mut c, "a", "b").unwrap();
	let duplicate = diesel::sql_query("INSERT INTO follows (follower, followee) VALUES (?, ?)")
		.bind::<diesel::sql_types::Text, _>("a")
		.bind::<diesel::sql_types::Text, _>("b")
		.execute(&mut c);
	assert!(
		duplicate.is_err(),
		"follows primary key must reject duplicates"
	);
}

// ---------------------------------------------------------------------------
// Timelines
// ---------------------------------------------------------------------------

#[test]
fn newest_first_orders_desc_and_applies_limit() {
	let mut c = conn();
	let a = allocate_post_id(&mut c).unwrap();
	let b = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, a, "x", "a", Visibility::Everyone).unwrap();
	insert_post(&mut c, b, "y", "b", Visibility::Everyone).unwrap();

	assert_eq!(newest_first(&mut c, 10).unwrap(), vec![b, a]);
	assert_eq!(newest_first(&mut c, 1).unwrap(), vec![b]);
	assert!(newest_first(&mut c, 0).unwrap().is_empty());
}

#[test]
fn public_timeline_only_live_everyone() {
	let mut c = conn();
	let public = allocate_post_id(&mut c).unwrap();
	let private = allocate_post_id(&mut c).unwrap();
	let deleted = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, public, "a", "public", Visibility::Everyone).unwrap();
	insert_post(&mut c, private, "a", "private", Visibility::FollowersOnly).unwrap();
	insert_post(&mut c, deleted, "a", "deleted", Visibility::Everyone).unwrap();
	soft_delete_post(&mut c, deleted).unwrap();

	assert_eq!(public_timeline(&mut c, 10).unwrap(), vec![public]);
}

#[test]
fn public_timeline_applies_limit_after_filtering() {
	let mut c = conn();
	let mut ids = Vec::new();
	for i in 0..5 {
		let id = allocate_post_id(&mut c).unwrap();
		ids.push(id);
		let vis = if i % 2 == 0 {
			Visibility::Everyone
		} else {
			Visibility::FollowersOnly
		};
		insert_post(&mut c, id, "a", "t", vis).unwrap();
	}
	// Everyone-visibility ids are indexes 0, 2, 4; newest first is 4 then 2.
	assert_eq!(public_timeline(&mut c, 2).unwrap(), vec![ids[4], ids[2]]);
}

#[test]
fn global_timeline_for_combines_public_and_followed() {
	let mut c = conn();
	let own = allocate_post_id(&mut c).unwrap();
	let followed = allocate_post_id(&mut c).unwrap();
	let stranger = allocate_post_id(&mut c).unwrap();
	let deleted = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, own, "u", "own", Visibility::Everyone).unwrap();
	insert_post(&mut c, followed, "friend", "f", Visibility::FollowersOnly).unwrap();
	insert_post(&mut c, stranger, "stranger", "s", Visibility::FollowersOnly).unwrap();
	insert_post(&mut c, deleted, "friend", "d", Visibility::Everyone).unwrap();
	soft_delete_post(&mut c, deleted).unwrap();
	add_follow(&mut c, "u", "friend").unwrap();

	let timeline = global_timeline_for(&mut c, "u", 10).unwrap();
	assert!(timeline.contains(&own), "everyone post is visible");
	assert!(
		timeline.contains(&followed),
		"followed private post is visible"
	);
	assert!(
		!timeline.contains(&stranger),
		"unfollowed private post is hidden"
	);
	assert!(!timeline.contains(&deleted), "deleted posts are hidden");
}

#[test]
fn personal_timeline_excludes_own_without_self_follow() {
	let mut c = conn();
	let own = allocate_post_id(&mut c).unwrap();
	let friend = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, own, "u", "own", Visibility::Everyone).unwrap();
	insert_post(&mut c, friend, "friend", "f", Visibility::Everyone).unwrap();
	add_follow(&mut c, "u", "friend").unwrap();

	assert_eq!(
		personal_timeline_for(&mut c, "u", 10).unwrap(),
		vec![friend]
	);

	add_follow(&mut c, "u", "u").unwrap();
	let timeline = personal_timeline_for(&mut c, "u", 10).unwrap();
	assert!(timeline.contains(&own), "self-follow includes own posts");
	assert!(timeline.contains(&friend));
}

// ---------------------------------------------------------------------------
// Id allocation
// ---------------------------------------------------------------------------

#[test]
fn allocate_ids_are_distinct_across_calls() {
	let mut c = conn();
	let p1 = allocate_post_id(&mut c).unwrap();
	let p2 = allocate_post_id(&mut c).unwrap();
	assert_ne!(p1, p2);

	create_account(&mut c, "u", "pw").unwrap();
	let s1 = allocate_session_id(&mut c).unwrap();
	let s2 = allocate_session_id(&mut c).unwrap();
	assert_ne!(s1, s2);
}

#[test]
fn allocate_ids_avoid_existing_rows() {
	let mut c = conn();
	let used_post = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, used_post, "a", "seed", Visibility::Everyone).unwrap();
	for _ in 0..20 {
		let candidate = allocate_post_id(&mut c).unwrap();
		assert_ne!(candidate, used_post, "allocated id must not collide");
	}

	create_account(&mut c, "u", "pw").unwrap();
	let used_session = allocate_session_id(&mut c).unwrap();
	activate_session(&mut c, used_session, "u").unwrap();
	for _ in 0..20 {
		let candidate = allocate_session_id(&mut c).unwrap();
		assert_ne!(
			candidate, used_session,
			"allocated session id must not collide"
		);
	}
}

// ---------------------------------------------------------------------------
// Db transactions
// ---------------------------------------------------------------------------

#[test]
fn db_write_rolls_back_on_error() {
	let db = Db::new(":memory:").expect("create Db");
	let pid = PostId(424_242);
	let result: Result<(), DbError> = db.write(|c| {
		insert_post(c, pid, "alice", "rolled back", Visibility::Everyone)?;
		Err(DbError(diesel::result::Error::RollbackTransaction))
	});
	assert!(result.is_err(), "write with an error must fail");

	let found = db.read(|c| get_post(c, pid)).expect("read post");
	assert!(found.is_none(), "the insert must have been rolled back");
}

#[test]
fn db_read_see_committed_write() {
	let db = Db::new(":memory:").expect("create Db");
	let pid = PostId(7);
	db.write(|c| insert_post(c, pid, "alice", "kept", Visibility::Everyone))
		.expect("write commits");
	let found = db.read(|c| get_post(c, pid)).expect("read post");
	assert!(found.is_some(), "committed write is visible to reads");
}

// ---------------------------------------------------------------------------
// Replies survive deletion
// ---------------------------------------------------------------------------

#[test]
fn soft_delete_keeps_reply_listed() {
	let mut c = conn();
	let parent = allocate_post_id(&mut c).unwrap();
	let reply = allocate_post_id(&mut c).unwrap();
	insert_post(&mut c, parent, "a", "root", Visibility::Everyone).unwrap();
	insert_reply(
		&mut c,
		reply,
		"b",
		"doomed reply",
		Visibility::Everyone,
		parent,
	)
	.unwrap();

	soft_delete_post(&mut c, reply).unwrap();

	assert_eq!(
		replies_of(&mut c, parent).unwrap(),
		vec![reply],
		"deleting a reply preserves it in the parent's replies list"
	);
	let deleted = get_post(&mut c, reply)
		.unwrap()
		.expect("deleted reply retained");
	assert_eq!(deleted.status, PostStatus::Deleted);
}
