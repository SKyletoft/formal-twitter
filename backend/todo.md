# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Done

## Next
- [x] Study spec: Twitter.agda (World state, Step relation semantics for all commands),
      Interface.agda (Actions/Responses/to-output result mapping), frontend/app.js
- [x] Task R1 (research subagent): frontend/app.js protocol — POST bodies newline-joined,
      GETs via query params incl. token in query (non-conformant; fixed in T5), no logout call,
      response parser handles single-quoted records (app.js:62-69), status handling 401/403.
- [x] Task R2 (research subagent): Rocket 0.5.2 — GET+data compiles (warning, suppress
      dubious_payload) but unused per I1; String data guard = Capped<String> (raise `string`
      limit); custom replies: (Status, (ContentType, String)) responders or Response::build()
      .status/.header/.sized_body.finalize; state via manage + &State<T>; config keys address/
      port (default 127.0.0.1:8000, ROCKET_PORT env works); #[launch] gives blocking main.
- [x] Task R3 (research subagent): Diesel 2.4.0 sqlite — hand-written table! macros (no CLI);
      sql_query only for constant CREATE TABLEs + QueryableByName; user data via static typed
      queries (filter/find/order_by/limit/nullable Option); sqlite transactions = pragmas;
      needs libsqlite3 at link time — use libsqlite3-sys 0.29 bundled feature for hermetic nix.
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
- [ ] Task T4 (subagent impl): flake.nix — cargo vendor committed; add libsqlite3-sys bundled
      dep; rustPlatform buildRustPackage hermetic; verify `nix run` starts server.
- [ ] Task T5 (subagent impl): frontend-conformant GET parsing (query params + Authorization Bearer)
      alongside spec-conformant line bodies; both must route to the same Action.
- [ ] Final verify: cargo build/test, clippy clean, cargo fmt, agda typecheck, nix run; commit each accepted task.

## Progress log (as of restart)
- src/ is back to the hello-world stub: T1-T4 are fresh work, R1-R3 research results above are reusable.
- Coordinator launches subagents in dependency order; each accepted task gets its own commit.
- R4 (research subagent, background): Twitter.agda — World state + Step rules per command + Result set.
- R5 (research subagent, background): nix buildRustPackage vendoring (vendorDir/cargoLock) + `nix run` entrypoint.
- R6 (research subagent, background): Rocket 0.5.2 — GET query-param routes, custom responses, State/Diesel
  connection sharing, data limits, config/env port.
- Design note: commit every todo.md change together with the task it tracks; co-author maki@qwen3.8-flash-next-coder.

## Design decisions
- DB schema: accounts(username PK,password,vis), sessions(sid PK,status active:user|revoked),
  posts(pid PK,author,text,vis,status,parent NULL,seq — newest-first = order by seq desc),
  likes(pid,user), replies(pid,reply_pid), follows(follower,followee); absence = false/unused/nothing.
- ids: Nat (u64) from CSPRNG, rejected if already used (matches CreateNew postulate).
- time-passes / collect-dead-posts have no Action constructor in Interface.agda → not endpoints;
  only implemented in model tests if proofs require.
- Anonymous read of private/deleted/nonexistent post has no Step rule; implementation returns
  permission-error (403), consistent with denied family.
- Frontend (frontend/app.js:106-135) speaks POST with newline-joined bodies (`token\ntext\n`) for
  login/signup/post-tweet and GET with `?token=&id=` (get-tweet) / `?token=&len=` (timeline); the
  timeline path is picked by token presence: `private-timeline` if a token is set else `global-timeline`.
  Frontend only uses login/signup/post-tweet/get-tweet/timeline; response parser accepts the single-quoted
  JSON of to-response (app.js:62-94).
- Wire requests: HTTP/1.1 with CRLF, `Host: localhost`, POST bodies carry `Content-Length`.
  POST keeps session token in the line-oriented body; GET carries it in
  `Authorization: Bearer <tk>`. GET targets are `/api/get-tweet?id=<twt>` and
  `/api/{global,private}-timeline?len=<n>`; there are no GET bodies.
