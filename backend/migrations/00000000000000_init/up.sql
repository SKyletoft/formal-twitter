CREATE TABLE accounts (
	username TEXT PRIMARY KEY NOT NULL,
	password TEXT NOT NULL,
	default_visibility TEXT NOT NULL
);

CREATE TABLE sessions (
	id INTEGER PRIMARY KEY NOT NULL,
	status TEXT NOT NULL,
	username TEXT NOT NULL
);

CREATE TABLE posts (
	id INTEGER PRIMARY KEY NOT NULL,
	seq INTEGER NOT NULL UNIQUE,
	author TEXT NOT NULL,
	text TEXT NOT NULL,
	visibility TEXT NOT NULL,
	status TEXT NOT NULL,
	parent INTEGER
);

CREATE TABLE follows (
	follower TEXT NOT NULL,
	followee TEXT NOT NULL,
	PRIMARY KEY (follower, followee)
);

CREATE TABLE post_likes (
	pid INTEGER NOT NULL,
	user TEXT NOT NULL,
	PRIMARY KEY (pid, user)
);
