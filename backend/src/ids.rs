use diesel::SqliteConnection;

use crate::model::{DbError, PostId, SessionId};

pub fn allocate_post_id(_c: &mut SqliteConnection) -> Result<PostId, DbError> {
	unimplemented!()
}

pub fn allocate_session_id(_c: &mut SqliteConnection) -> Result<SessionId, DbError> {
	unimplemented!()
}
