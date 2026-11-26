use diesel::SqliteConnection;

use crate::model::{Account, DbError, Post, PostId, SessionId, SessionStatus, Visibility};

pub fn create_account(
	_c: &mut SqliteConnection,
	_username: &str,
	_password: &str,
) -> Result<bool, DbError> {
	unimplemented!()
}

pub fn get_account(_c: &mut SqliteConnection, _username: &str) -> Result<Option<Account>, DbError> {
	unimplemented!()
}

pub fn activate_session(
	_c: &mut SqliteConnection,
	_sid: SessionId,
	_username: &str,
) -> Result<(), DbError> {
	unimplemented!()
}

pub fn get_session(_c: &mut SqliteConnection, _sid: SessionId) -> Result<SessionStatus, DbError> {
	unimplemented!()
}

pub fn revoke_session(_c: &mut SqliteConnection, _sid: SessionId) -> Result<(), DbError> {
	unimplemented!()
}

pub fn revoke_all_sessions(_c: &mut SqliteConnection) -> Result<(), DbError> {
	unimplemented!()
}

pub fn insert_post(
	_c: &mut SqliteConnection,
	_id: PostId,
	_author: &str,
	_text: &str,
	_vis: Visibility,
) -> Result<(), DbError> {
	unimplemented!()
}

pub fn insert_reply(
	_c: &mut SqliteConnection,
	_id: PostId,
	_author: &str,
	_text: &str,
	_vis: Visibility,
	_parent: PostId,
) -> Result<(), DbError> {
	unimplemented!()
}

pub fn get_post(_c: &mut SqliteConnection, _id: PostId) -> Result<Option<Post>, DbError> {
	unimplemented!()
}

pub fn soft_delete_post(_c: &mut SqliteConnection, _id: PostId) -> Result<(), DbError> {
	unimplemented!()
}

pub fn replies_of(_c: &mut SqliteConnection, _id: PostId) -> Result<Vec<PostId>, DbError> {
	unimplemented!()
}

pub fn add_follow(
	_c: &mut SqliteConnection,
	_follower: &str,
	_followee: &str,
) -> Result<(), DbError> {
	unimplemented!()
}

pub fn remove_follow(
	_c: &mut SqliteConnection,
	_follower: &str,
	_followee: &str,
) -> Result<(), DbError> {
	unimplemented!()
}

pub fn is_following(
	_c: &mut SqliteConnection,
	_follower: &str,
	_followee: &str,
) -> Result<bool, DbError> {
	unimplemented!()
}

pub fn add_like(_c: &mut SqliteConnection, _id: PostId, _user: &str) -> Result<(), DbError> {
	unimplemented!()
}

pub fn remove_like(_c: &mut SqliteConnection, _id: PostId, _user: &str) -> Result<(), DbError> {
	unimplemented!()
}

pub fn is_liked(_c: &mut SqliteConnection, _id: PostId, _user: &str) -> Result<bool, DbError> {
	unimplemented!()
}

pub fn like_count(_c: &mut SqliteConnection, _id: PostId) -> Result<i64, DbError> {
	unimplemented!()
}

pub fn newest_first(_c: &mut SqliteConnection, _n: u32) -> Result<Vec<PostId>, DbError> {
	unimplemented!()
}

pub fn public_timeline(_c: &mut SqliteConnection, _n: u32) -> Result<Vec<PostId>, DbError> {
	unimplemented!()
}

pub fn global_timeline_for(
	_c: &mut SqliteConnection,
	_user: &str,
	_n: u32,
) -> Result<Vec<PostId>, DbError> {
	unimplemented!()
}

pub fn personal_timeline_for(
	_c: &mut SqliteConnection,
	_user: &str,
	_n: u32,
) -> Result<Vec<PostId>, DbError> {
	unimplemented!()
}
