CREATE TABLE accounts (
    username TEXT PRIMARY KEY NOT NULL,
    password TEXT NOT NULL,
    default_visibility TEXT NOT NULL
        CHECK (default_visibility IN ('everyone', 'followers-only'))
);

CREATE TABLE sessions (
    id INTEGER PRIMARY KEY NOT NULL,
    status TEXT NOT NULL CHECK (status IN ('active', 'revoked')),
    username TEXT NOT NULL
);

CREATE TABLE posts (
    id INTEGER PRIMARY KEY NOT NULL,
    seq INTEGER NOT NULL UNIQUE,
    author TEXT NOT NULL,
    text TEXT NOT NULL,
    visibility TEXT NOT NULL CHECK (visibility IN ('everyone', 'followers-only')),
    status TEXT NOT NULL CHECK (status IN ('live', 'deleted')),
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

CREATE INDEX idx_posts_seq ON posts (seq DESC);
CREATE INDEX idx_posts_parent_seq ON posts (parent, seq DESC);
CREATE INDEX idx_posts_author_seq ON posts (author, seq DESC);
CREATE INDEX idx_follows_followee ON follows (followee);
