diesel::table! {
	accounts (username) {
		username -> Text,
		password -> Text,
		default_visibility -> Text,
	}
}

diesel::table! {
	sessions (id) {
		id -> BigInt,
		status -> Text,
		username -> Text,
	}
}

diesel::table! {
	posts (id) {
		id -> BigInt,
		seq -> BigInt,
		author -> Text,
		text -> Text,
		visibility -> Text,
		status -> Text,
		parent -> Nullable<BigInt>,
	}
}

diesel::table! {
	follows (follower, followee) {
		follower -> Text,
		followee -> Text,
	}
}

diesel::table! {
	post_likes (pid, user) {
		pid -> BigInt,
		user -> Text,
	}
}

diesel::allow_tables_to_appear_in_same_query!(accounts, sessions, posts, follows, post_likes,);
