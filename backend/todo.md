# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Done

## Next
- [x] Study spec: Twitter.agda (state model + Step relation), Interface.agda (wire protocol:
      paths /api/{post-tweet,post-reply,delete-tweet,like-tweet,unlike-tweet,follow-user,
      unfollow-user,get-tweet,global-timeline,private-timeline,login,logout,signup};
      bodies = line-separated token/text/id; responses per to-output: ok/403 access_denied/
      401 session_expired/401 login_failed/400 signup_failed/200 {'tweet_id'}/200 {'timeline'}/
      200 {'session_token'}/200 tweet json)
- [ ] Task R1 (subagent research): frontend wire protocol from frontend/app.js
- [ ] Task R2 (subagent research): Rocket 0.5.2 API — GET data routes, custom responses, state, port config
- [ ] Task R3 (subagent research): Diesel 2.4.0 sqlite API — schema macros vs allow_sql, queries
- [ ] Task T1 (subagent impl): server — pure model module (mirrors Agda), diesel/sqlite storage
      (accounts, sessions, posts(seq order + parent, likes, replies), follows), rocket routes
      implementing Step semantics, reentrant startup on existing DB, crypto-random Nat ids
      checked fresh. Must pass cargo build, clippy -D warnings, cargo fmt.
- [ ] Task T2 (subagent impl): network integration tests — launch server, raw-TCP HTTP/1.1
      client in Rust (stdlib only), exercise all endpoints incl. error paths per spec semantics.
- [ ] Task T3 (subagent impl): pure-model QuickCheck tests (quickcheck 1.1 + quickcheck_macros 1.2,
      one property per forall) + matching theorems in ImplProofs.agda; `agda --compile`/typecheck must pass.
- [ ] Task T4 (subagent impl): flake.nix — vendor deps so `nix run` works offline (cargo vendor
      committed; rustPlatform buildRustPackage with sqlite lib), verify `nix run`.
- [ ] Final verify: cargo build/test, clippy clean, cargo fmt, agda typecheck, nix run; commit each accepted task.

## Design decisions
- DB schema: accounts(username PK,password,vis), sessions(sid PK,status active:user|revoked),
  posts(pid PK,author,text,vis,status,parent NULL,seq — newest-first = order by seq desc),
  likes(pid,user), replies(pid,reply_pid), follows(follower,followee); absence = false/unused/nothing.
- ids: Nat (u64) from CSPRNG, rejected if already used (matches CreateNew postulate).
- time-passes / collect-dead-posts have no Action constructor in Interface.agda → not endpoints;
  only implemented in model tests if proofs require.
- Anonymous read of private/deleted/nonexistent post has no Step rule; implementation returns
  permission-error (403), consistent with denied family.
- Wire requests: HTTP/1.1 with CRLF, `Host: localhost`, POST bodies carry `Content-Length`.
  POST keeps session token in the line-oriented body; GET carries it in
  `Authorization: Bearer <tk>`. GET targets are `/api/get-tweet?id=<twt>` and
  `/api/{global,private}-timeline?len=<n>`; there are no GET bodies.
