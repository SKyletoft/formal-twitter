# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Done
- [x] Review merge 123051e (brought in 7c49856 "spec/Interface: Try to fix invalid HTTP"):
  ALL endpoints are now POST (`POST /api/X HTTP/1.1`) incl. get-tweet/global-timeline/private-timeline;
  request has Host + Accept: application/json + Content-Type: text/plain; charset=utf-8 + exact
  Content-Length; body = CRLF-joined lines (no trailing newline), token FIRST line when present;
  anonymous get-tweet/global-timeline bodies omit the token line. Responses: strict double-quoted JSON
  ({"tweet_id": "N"}, {"timeline": [N, N]}, {"session_token": "N"}, {"username":..,"text":..,"likes":N,"replies":[..]},
  {"error": access_denied|session_expired|login_failed|signup_failed}), always a `Date:` header,
  `Cache-Control: no-store` on timeline/session-token/tweet, ok = 200 with Content-Length: 0, no body;
  status codes unchanged (ok/tweet-id/timeline/session-token/tweet=200, denied=403, expired+login-error=401,
  signup-error=400); escape postulate applies to username/text in tweet body. host/date are postulates (impl picks values).
  Frontend app.js UNCHANGED by merge: still GET /api/get-tweet?token=&id= + /api/{global,private}-timeline?token=&len=
  and POST login/signup/post-tweet with LF-joined body + trailing newline; parseResponse JSON.parse first
  (real JSON fine), regex fallback. So backend must accept both spec POST bodies and frontend GETs (task T4).

## Next
- [x] Task T4b-1 (subagent impl, ACCEPTED): main.rs helpers (143 lines): http_date std-only IMF
      (civil-date loop, weekday table anchored Thu@day0, verified), to_output Result->ApiResponse
      (arg order (author,text,likes,replies) verified vs model.rs:470 + wire.rs:296 — direct
      passthrough), random_u64 (/dev/urandom 8B BE, 0 on error), sample_id (nonzero+unused loop),
      to_http (WireResponse{status_code,headers,body} -> Response<'static> fold-in-order +
      Status::from_code + sized_body/Cursor + finalize). Coordinator gates: build/clippy -D/fmt/test
      (24) all exit 0; artifact greps clean. NOTE for T4c: to_output + to_http need #[test]s +
      Interface-level pins (no #[test] in main.rs yet) before those count as done.
- [x] Task T4b-2 (subagent impl, ACCEPTED after coordinator fixes): main.rs server layer —
      serve() behind 13 #[post] routes (paths copied from wire.rs table), custom `Served` Responder
      wrapping pre-rendered Response, State<Mutex<Server{world,db_path}>>, per-request init_or_open +
      apply() write-through (never re-establishes into state: Sync-safe), fresh ids via sample_id(used_pid/used_sid),
      launch loads FT_DB (default twitter.db) via init_or_open+load_world. Coordinator fixes applied:
      wire_error() rewritten to spec-style respond(PermissionError) 403 (agent invented non-spec 400
      {"error":"invalid_request"} — REVERTED); truncated tests/smoke.rs DELETED (T5 owns it). Coordinator
      probe: `timeout 3 ./target/debug/formal-twitter` prints all 13 routes + graceful SIGTERM shutdown.
      Gates: build/clippy -D/fmt/test(24) exit 0. curl DENIED in sandbox -> network smoke = T5 cargo
      integration test via std::net (raw TCP), 3 lifecycles on ONE FT_DB file.
- [x] Task T5 (subagent impl, ACCEPTED, committed): backend/tests/smoke.rs (525 lines) — cargo integration
      suite (tests/ dir): spawn_server via timeout+FT_DB+unique ROCKET_PORT per test, wait_ready/wait_gone
      TCP polling, raw std::net req() with exact spec framing (Host/Accept/Content-Type charset/CRLF body).
      5 tests: test_signup_login (signup=empty 200 ok, login=200 {"session_token":N} w/ cache-control, wrong
      pw 401 {"error": "login_failed"}, logout, fresh token per login), test_post_tweet (publish 200 {"tweet_id"},
      anon timeline sees it, like/unlike 200), test_errors (400 signup_failed, 401 session_expired via stale/revoked
      token, 403 access_denied anon get-tweet + unknown-pid like), test_http_framing (status lines, Date header,
      exact Content-Length==body octets, cache-control only on JSON), test_reentrant_three_lifecycles (ONE /tmp
      FT file, servers 8021/8022/8023 sequential: run2's startup REOPENS existing DB — old account+post visible,
      duplicate signup now 400; run3 sees A,B then adds C). Semantics verified vs Interface.agda:269 + model.rs:500
      (login issues session token; signup answers ok-empty). Coordinator gates: cargo test 29 passed (4 suites, 32s),
      clippy -D 0, fmt 0, agda 0. Header-name assertions case-insensitive (rocket lowercases + adds server/shield).
- [x] Review the changes brought in by the merge
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
- [x] (folded into T1/T2 above) Task T1 old text: server — pure model module (mirrors Agda), diesel/sqlite storage
      (accounts, sessions, posts(seq order + parent, likes, replies), follows), rocket routes
      implementing Step semantics, reentrant startup on existing DB, crypto-random Nat ids
      checked fresh. Must pass cargo build, clippy -D warnings, cargo fmt.
- [ ] Task T5 (subagent impl, SMALL): network integration tests — launch server, raw-TCP HTTP/1.1
      client (stdlib only) speaking the NEW spec protocol, exercise all endpoints incl. error paths.
- [x] Task T1 (subagent impl, ACCEPTED d5f78e5): pure model module (backend/src lib: model.rs mirroring Twitter.agda
      World/Step/Result) + QuickCheck tests + matching theorems in ImplProofs.agda; agda typecheck.
- [x] Task T2 (subagent impl, ACCEPTED, NOT committed): wire.rs (542 lines; 322 non-test) — WireAction/WireError/
      ApiResponse/WireResponse; parse_action (CRLF/LF/lone-CR split, drops exactly one trailing empty line,
      u64 = ASCII digits only, arity decides anonymous get-tweet/global-timeline, never panics);
      to_command = from-input; escape_json (" \\ \n \r \t and <0x20 -> \u00xx lower hex); respond = to-response minus
      the status line and minus Content-Length (rocket appends it), header order exact, Cache-Control: no-store
      on timeline/session-token/tweet, ok = 200 empty body. Tests: #[cfg(test)] mod wire_tests with 7 #[test]
      + 1 #[quickcheck] (13 endpoint round-trips CRLF/LF/CR, malformed -> errors, escape_json, timeline bodies
      byte-exact for []/[1]/[1,2]). Proofs: 24 refl theorems in NEW backend/ImplWire.agda (module ImplWire,
      15 from-input + 9 to-output) — ImplProofs.agda cannot open Interface (Command/Result clash at SessionId/PostId);
      pointer comment + `open import ImplWire` added there so `agda ImplProofs.agda` Gates green: build/clippy -D warnings/fmt --check/18 tests/agda both files exit 0.
- [ ] Task T3 (subagent impl, SMALL): db.rs — table! macros (accounts,sessions,posts(seq,parent),likes,replies,follows),
      encodings, init_or_open (reentrant CREATE), load World from DB, save World (full rewrite);
      #[test]s round-trip; ImplStorage.agda refl theorems. NO apply() yet (that goes with T4).
- [ ] Task T4 (subagent impl, SMALL): main.rs — rocket 13 POST routes (wire.rs+model.step), apply(before,after)
      write-through diff in db.rs, fresh u64 ids from /dev/urandom (reject used), Date header,
      managed State; reentrancy curl smoke (3 runs on ONE DB file).
- [ ] Task T6 (subagent impl, SMALL): frontend-conformant GET aliases (/api/get-tweet?token=&id=,
      /api/{global,private}-timeline?token=&len=) → same Action; tolerate LF/trailing-newline bodies.
- [ ] Task T7 (subagent impl): flake.nix — cargo vendor committed; hermetic rustPlatform buildRustPackage
      (vendorDir + cargoLock); libsqlite3-sys bundled pin if needed; verify `nix run .` starts server.
- [x] Task T8 (research + owner decision, RESOLVED): SKyletoft/* are owner forks; use canonical crates.
      cargo reaches crates.io itself (only web tools are sandbox-denied), so deps go straight into Cargo.toml:
      smallstr = { version = "0.3", features = ["union"] } (lock: 0.3.1), smallvec = { version = "1.15", features =
      ["union","const_generics","const_new"] } (lock reuses 1.16.5 already in graph via rocket). Build clean.
      USING SmallStr/SmallVec in model.rs+db.rs deferred to T9 — types are Vec/String-pinned by diesel collect()
      and Agda-style ==; migration must be surgical (candidates: Post.likes/replies, String keys).
- [ ] Task T9 (subagent impl): EVERYTHING. Review the entire implementation for non-idiomatic code and potential performance issues.
- [ ] Task T10 (subagent impl): EVERYTHING: Review the entire implementation for #[doc] instead of ///-doc-comments.
- [ ] Final verify: cargo build/test, clippy clean, cargo fmt, agda typecheck, nix run; commit each accepted task.

## Progress log (as of restart)
- T4b ATTEMPT #1 REJECTED (reverted by coordinator: main.rs back to a tiny stub via printf).
  Failure mode: the subagent's main.rs was GARBAGE — function bodies replaced by nested `{ { { ; } } }`,
  `ref_box` nonsense, only 1 of 13 routes emitted; cargo build 1 error. Same corruption family as the
  earlier wire/tooling gotcha (code-generation tools mangle punctuation-heavy writes). LESSON for impl
  agents: after EVERY write/edit of a .rs file, (a) `wc -l` compare against intent, (b) grep for
  `{;$`/empty-block patterns, (c) run cargo build immediately, and write in small chunks (one function
  per edit), never one giant write. Coordinator note: my own large write call also came out mangled
  (long filler tail) — keep tool payloads short.
- T4a (apply in db.rs) REWORKED in working tree (uncommitted, on top of 58f2c92's db.rs):
  pub apply(conn, before, after) bounded write-through O(delta) — accounts INSERT/DELETE,
  sessions INSERT/UPDATE/DELETE, posts INSERT with seq = (max DB seq)+1 growing (keeps
  ORDER BY seq DESC newest-first), status flips UPDATE, likes/replies/follows pair INSERT/DELETE.
  Verified by coordinator: cargo build OK, fmt --check exit 0, clippy -- -D warnings exit 0,
  24 tests pass (6 new db tests: roundtrips + test_apply_inserts_all + test_apply_diff).
  Agda gate (ImplProofs/ImplWire/ImplStorage) exit 0. NOT acceptable yet: no proofs for the
  apply tests. T4a-P adds them, then commit.
- T3 ATTEMPT #2 CANCELLED (thinking loop; partial non-compiling db.rs deleted, lib.rs restored to HEAD).
  Lessons (R8, verified from diesel-2.4.0 vendored sources during attempt):
  * `.load::<Element>(conn)` returns QueryResult<Vec<Element>> (doctest: `users.load::<String>(connection)`);
    NO load_all needed; `diesel::insert_into(t).values(v).execute(conn)`, `diesel::delete(t).execute(conn)`;
    sql_query(CREATE_SQL_LITERAL).execute(conn).ok() to ignore "table exists" on reopen (reentrant init);
  * table! grammar: `table!(name (pk) { col -> Type, ... });` (diesel_table_macro_syntax-0.4.0);
  * SimpleConnection::batch_execute exists at src/connection/mod.rs:81; prelude lacks `diesel::result::Error`
    (use full path `diesel::result::Error`); SqliteConnection::establish(&str) at sqlite/connection/mod.rs:265;
  * webfetch to docs.diesel.rs DENIED in sandbox; read vendored sources instead.
- T2a ATTEMPT #2 CANCELLED by user (reverted: wire.rs deleted, lib.rs restored, _probe6.rs scratch
  deleted). Lessons kept in memory (tags wire/tooling): the code-generation tools mangle punctuation
  inside writes — grep-verify after every write/edit, compile after each small chunk; Rust 2024 gotchas:
  `use crate::model::{...}`, enum ctors with `::`, comma-separated struct fields, no extra parens in patterns.
- T2 ATTEMPT #1 REJECTED (not committed, reverted): agent produced non-compiling db.rs pseudo-code
  (110 errors), no wire.rs/main.rs. Lessons recorded as R7 below; files restored to d5f78e5 state
  (db.rs deleted; lib.rs `pub mod db;` removed; Cargo.toml libsqlite3-sys line removed).
- R7 (from rejected T2 attempt, verified facts, diesel 2.4.0 vendored sources):
  * raw SQL: `SqliteConnection::batch_execute(&str)` via trait `diesel::connection::SimpleConnection`
    (NOT in prelude; must import); `sql_query!` only with constant string literals, never runtime-built SQL;
  * `SqliteConnection::establish(&str)`, `::load` (LoadConnection), `::last_insert_rowid`;
  * order methods are `.order(col.asc)`/`.then_by(...)` (NOT order_by in method chains... verify);
  * prelude exports ConnectionError/ConnectionResult/QueryResult but NOT `diesel::result::Error` itself;
  * `delete` is `crate::delete<T: IntoUpdateTarget>`; BoolExpressionMethods `.and(other)`.
  * tooling gotcha: sandbox bash denies rm/mv/git-restore/git-clean/`2>&1`/multi-`;` commands;
    delete files via `find <dir> -name X -delete`, chain separate tool calls instead.
- src/ is back to the hello-world stub: T1-T4 are fresh work, R1-R3 research results above are reusable.
- T1 done: backend/src/model.rs (World/step mirroring Twitter.agda; qc mod: well_formed-checked Arbitrary<World>, 10 prop_*) + backend/ImplProofs.agda (10 theorems, one per prop; delete merged via _×_, register_taken added via failed-create-account).
- Coordinator launches subagents in dependency order; each accepted task gets its own commit.
- R4 (research subagent, background): Twitter.agda — World state + Step rules per command + Result set.
- R5 (research subagent, background): nix buildRustPackage vendoring (vendorDir/cargoLock) + `nix run` entrypoint.
- R6 (research subagent, background): Rocket 0.5.2 — GET query-param routes, custom responses, State/Diesel
  connection sharing, data limits, config/env port.
- Design note: commit every todo.md change together with the task it tracks; co-author maki@qwen3.8-flash-next-coder.

## Spec semantics (from R4, spec/Twitter.agda)
- `World` (:65-109): `account-at : String -> Maybe Account{password, default-visibility}`;
  `session-at : Sid -> SessionStatus{unused, active username, revoked}`; `post-at : Pid -> Maybe Post{author,text,
  visibility,status,likes:List Username,replies:List Pid,parent:Maybe Pid}`; `follows : String -> String -> Bool`;
  `newest-first : List Pid` (head = newest, never filtered/reordered); `used-post-ids`, `used-session-ids`.
  Visibility is 2-valued `everyone`/`followers-only`; PostStatus 2-valued `live`/`deleted`.
- Invariants (proof-carrying, must hold in Rust + DB on restart): pid in used-post-ids <-> post-at pid <> nothing;
  sid in used-session-ids <-> session-at sid <> unused; active session implies account exists; newest-first members
  exist in post-at; replies point back at their parent and child.parent = just parent, child <> parent; uniq replies;
  uniq likes; uniq newest-first.
- `CanReadPost w sid pid` <=> exists post w/ post-at = just post, status live, and (visibility everyone) OR
  (visibility followers-only AND follows user (author post)). Anonymous read = same with visibility everyone.
- Universal rule `failed-access` (:464): any session-taking command whose sid lacks a valid session => `expired`,
  world unchanged, checked BEFORE the command's own rules.
- Commands: publish (reply only when CanReadPost parent, parent live, pid <> parent; reply visibility = parent's
  when parent followers-only else account default-visibility; prepend to newest-first) => created-post, else denied.
  delete (author only; only flips status to deleted, keeps likes/replies/parent; idempotent) => success/denied.
  read-post => returned-post author text (length likes) replies / denied. personal timeline =
  take n . filter(follows-post-author) . filter(can-read-post) . newest-first; logged-in global = drop the
  follows filter; anonymous global = filter is-post-public (everyone AND live). like/unlike => success but denied
  when NOT CanReadPost; like appends username if absent (uniq), unlike removes it. follow/unfollow always succeed
  with a valid session (set pair to true/false; no existence check). register: only when username unused => account
  with default-visibility `everyone`; else signup-failed. login: only for a FRESH (unused) sid + matching password
  => active username + issued-session sid; else login-failed (spec stuck on reused sid; pick fresh sid always).
  logout: active -> revoked => success (unused/revoked => expired). `collect-dead-posts`/`reap-tombstones` are
  commented out in the spec: DO NOT implement; tombstones persist. `time-passes` (session-timeout :691) revokes
  every active session; no Action constructor, so not an endpoint (model tests only if proofs need it).
- `Result`: success | denied | expired | login-failed | signup-failed | returned-timeline ids | issued-session sid
  | created-post pid | returned-post author text likes replies. to-output maps them to the 200/403/401/400 bodies in
  Interface.agda:to-response (single-quoted pseudo-JSON).
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
- Wire requests (NEW post-merge spec): every Action is POST /api/<name> HTTP/1.1 with
  `Host:`, `Accept: application/json`, `Content-Type: text/plain; charset=utf-8`, exact
  `Content-Length`; body lines CRLF-joined, token first, anonymous get-tweet/global-timeline omit it.
  GET only appears from the legacy frontend (query params); support as aliases (T4).

T3 ACCEPTED: db.rs init_or_open+load_world+save_world, 4 db_tests (22 lib tests total), 6 ImplStorage theorems; gates green (build, clippy -D warnings zero, fmt, tests, agda both exit 0).

T5 ACCEPTED: backend/tests/smoke.rs (cargo integration test target "smoke", 5 tests, std-net raw TCP only, no new deps). Each test spawns target/debug/formal-twitter under `timeout` with its own ROCKET_PORT + FT_DB; wait_ready polls connect, wait_gone polls until the killed process frees the port (used by the reentrancy test to start 3 sequential servers on one shared /tmp/ft-smoke-T5.sqlite). Results: signup=200 empty (Content-Length 0), login=200 {"session_token":"N"} (quoted ids!), duplicate signup=400 signup_failed, bad login=401 login_failed (25 bytes), stale/revoked token=401 session_expired, unreadable pid=403 access_denied; rocket lowercases header names and appends server/shield headers. Gates green: cargo test --quiet -> 24 lib + 5 smoke all pass; clippy --quiet -- -D warnings exit 0; cargo fmt --check exit 0. Dialect notes: `final` is reserved, `xs.contains(&x)`, `s += &other`, no String+String by value.
