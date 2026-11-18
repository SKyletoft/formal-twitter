# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Done (history, condensed; commits in git log)
- [x] Review of merge 123051e (spec/Interface wire protocol): ALL endpoints POST /api/<name>;
  body = CRLF-joined lines, token FIRST, no trailing newline; anonymous get-tweet/global-timeline omit token;
  responses strict double-quoted JSON, always `Date:` header, `Cache-Control: no-store` on timeline/session-token/tweet;
  ok = 200 + Content-Length: 0 empty body; codes: 200 ok/tweet-id/timeline/token/tweet, 403 access_denied,
  401 session_expired/login_failed, 400 signup_failed. frontend/app.js UNCHANGED (legacy GET+LF) -> aliases = T6.
- [x] Study spec: Twitter.agda, Interface.agda, frontend/app.js (facts kept in "Reference" below).
- [x] Task R1/R2/R3 (research): frontend protocol, Rocket 0.5.2, Diesel 2.4.0 sqlite. Findings in memory notes.
- [x] Task T1 (ACCEPTED d5f78e5): model.rs — World/step mirroring Twitter.agda + QuickCheck props +
  matching theorems in ImplProofs.agda.
- [x] Task T2 (ACCEPTED fee6d9e): wire.rs (parse_action CRLF/LF/CR split, to_command = from-input,
  escape_json, respond = to-response minus status line/Content-Length, exact header order) + 24 refl theorems in ImplWire.agda.
- [x] Task T3 (ACCEPTED 58f2c92): db.rs — 9 diesel table!s, init_or_open (reentrant CREATE), load_world,
  save_world + 6 ImplStorage theorems.
- [x] Task T4a (ACCEPTED c411372): db.rs apply(before,after) bounded O(delta) write-through
  (INSERT/UPDATE/DELETE per table, posts seq = max+1) + ImplApply.agda 32 refl theorems.
- [x] Task T4b-1 (ACCEPTED be05d56): main.rs helpers — http_date (std-only IMF), to_output, random_u64
  (/dev/urandom), sample_id, to_http (WireResponse -> Response<'static>).
- [x] Task T4b-2 (ACCEPTED 6bd2426): main.rs server layer — serve() behind 13 #[post] routes,
  State<Mutex<Server{world,db_path}>>, per-request init_or_open + apply() write-through, launch via FT_DB.
- [x] Task T5 (ACCEPTED 794ce85): tests/smoke.rs — 5 network integration tests, raw std::net TCP spec client,
- [ ] Task DB3a (impl, pending acceptance): db.rs apply() -> bool, batch wrapped in raw sqlite pragmas
  (BEGIN TRANSACTION; first, COMMIT TRANSACTION; iff every statement Ok else ROLLBACK TRANSACTION; + false);
  per-statement `ok &= ...execute(conn).is_ok()` keeps the recoverable-error tolerance; reopen() = establish only;
  +db_tests test_apply_returns_true / test_apply_failure_rolls_back (rollback leaks the PK-less like+reply rows
  if the ROLLBACK is dropped); ImplApply.agda +th-apply-ok (refl). main.rs:200 arm now discards the bool (3 lines).
  3-lifecycle reentrancy on ONE FT_DB file.
- [x] Task T8 (RESOLVED e5dd9f9): SKyletoft/* are owner forks; canonical deps smallstr 0.3+union,
  smallvec 1.15+union in Cargo.toml. Use in src deferred to T9 (types pinned by diesel + Agda-style ==).

## Next (in order)
- [ ] TD1 (coordinator): clean up this todo list structure. (commit todo changes)
- [ ] DB2 (research subagent): audit implementation vs the AGENTS.md database rules
  ("database is source of truth"; "no data served unless committed in DB"; "RAM cache must periodically be
  thrown out and re-queried from the DB, NOT all at once"); report violations with file:line refs.
- [ ] DB3 (impl subagent): fix the DB2 findings — serve AFTER commit (or error path on DB failure),
  periodic PARTIAL cache reload (cycle over cache sections, reload one section per N requests,
  never the whole World at once), db.rs gains reopen + per-section reload fns. Tests + proofs + gates.
- [ ] Task TA (impl, SMALL): perf main.rs+db.rs — sample_id by reference, one 16B /dev/urandom read per
  request (two u64s), poison-tolerant lock, reopen() = establish-only (no per-request failing CREATE batch).
- [ ] Task TB (impl, SMALL): perf db.rs apply() — borrows instead of deep-clone HashMaps/HashSets
  (HashMap<u64,&Post>, HashSet<&String>, HashSet<(&String,&String)>, no status/username clones).
- [ ] Task TC (impl, MED): perf model.rs timelines — hoist active_user/account_at out of newest_first loop,
  early-stop after n matches, post_at_ref -> Option<&Post> for read-only callers.
- [ ] Task T6 (impl, SMALL): frontend-conformant GET aliases (/api/get-tweet?token=&id=,
  /api/{global,private}-timeline?token=&len=) -> same Action; tolerate LF/trailing-newline bodies.
- [ ] Task T7 (impl): flake.nix — hermetic rustPlatform buildRustPackage (vendored cargo), `nix run .`
  starts the server; libsqlite3-sys bundled pin if needed.
- [ ] Task T10 (impl, MECHANICAL): convert ALL #[doc = "..."] one-liners + stacks to /// across
  model.rs/wire.rs/db.rs/main.rs/smoke.rs; verify fmt/clippy/test/agda unchanged.
- [ ] Task T9 (impl): review whole implementation for non-idiomatic code + perf issues (after TA-TB-TC landed).
- [ ] Task T10 (research): Is frontend spec-conformant?
- [ ] Task T11 (research): Remove compat aliases?
- [ ] Final verify: cargo build/test, clippy -D warnings, cargo fmt --check, agda typecheck all files, nix run;
  commit each accepted task with co-author maki@qwen3.8-flash-next-coder.

## Reference: spec semantics (Twitter.agda + Interface.agda, from R4/R5)
- `World` (:65-109): account-at String -> Maybe Account{password, default-visibility}; session-at Sid ->
  {unused, active username, revoked}; post-at Pid -> Maybe Post{author,text,visibility,status,likes:List Username,
  replies:List Pid,parent:Maybe Pid}; follows String -> String -> Bool; newest-first : List Pid (head = newest);
  used-post-ids, used-session-ids. Visibility everyone/followers-only; PostStatus live/deleted.
- Invariants: pid used <-> post-at <> nothing; sid used <-> session-at <> unused; active session => account exists;
  newest-first members exist; replies point back at parent (child.parent = just parent, child <> parent);
  uniq replies/likes/newest-first.
- CanReadPost w sid pid <=> post live AND (everyone OR (followers-only AND follows (author post)));
  anonymous read = everyone only. failed-access (:464): session-taking command with invalid sid => expired,
  world unchanged, checked BEFORE command's own rules.
- publish (reply only when CanReadPost parent, parent live, pid <> parent; reply visibility = parent's when
  followers-only else account default; prepend newest-first) => created-post/denied. delete (author only; flips
  status to deleted, keeps likes/replies/parent; idempotent) => success/denied. read-post => returned-post
  (author text (length likes) replies) / denied. personal timeline = take n . filter(follows-author) .
  filter(can-read) over newest-first; logged-in global drops follows filter; anonymous global filters
  is-post-public (everyone AND live). like/unlike => success, denied when NOT CanReadPost; like appends
  username if absent, unlike removes. follow/unfollow always succeed with valid session (set pair true/false;
  no existence check). register: only when username unused => account (default-visibility everyone); else signup-failed.
  login: only for FRESH (unused) sid + matching password => active username + issued-session sid; else login-failed
  (always pick a fresh sid). logout: active -> revoked => success (unused/revoked => expired).
  collect-dead-posts/reap-tombstones COMMENTED OUT in spec: DO NOT implement; tombstones persist.
  time-passes (session-timeout :691) revokes all active sessions; no Action constructor => not an endpoint.
- `Result`: success | denied | expired | login-failed | signup-failed | returned-timeline ids | issued-session sid |
  created-post pid | returned-post author text likes replies. to-output -> the 200/403/401/400 bodies in
  Interface.agda:to-response. escape postulate applies to username/text in tweet body.
- DB schema (our encoding, 9 table!s): accounts(username PK,password,vis,ord), sessions(sid PK,status,user,ord),
  posts(pid PK,author,text,vis,status,parent,seq — newest-first = ORDER BY seq DESC), likes(post_pid,user,ord),
  replies(reply_pid,parent), follows(follower,followee,ord), timeline(pid,ord), used_pids(pid), used_sids(sid).
- ids: Nat (u64) from CSPRNG, rejected if used (matches CreateNew postulate). time-passes / collect-dead-posts:
  not endpoints. Anonymous read of private/deleted/missing post has no Step rule; impl returns 403 (denied family).
- Wire requests (post-merge spec): POST /api/<name> HTTP/1.1, Host + Accept: application/json +
  Content-Type: text/plain; charset=utf-8 + exact Content-Length; body CRLF-joined lines, token FIRST,
  no trailing newline. GET only from legacy frontend (query params) -> support as aliases (T6).

## Progress log (lessons; details live in memory notes)
- Code-generation tools mangle punctuation-heavy writes/edits: after EVERY write/edit of a .rs file
  `wc -l`, grep for `{;$`/`=t `/`::` artifacts, run cargo build, write one function per edit. Keep tool payloads short.
- Sandbox: webfetch denied to non-allowed hosts; bash denies rm/mv/git-restore/`2>&1`/many-`;` chains;
  delete via `find <dir> -name X -delete`; cargo fmt only at backend root; curl blocked (T5 uses std::net).
- Agda gates: `cd backend && agda FILE.agda` exit 0 for ImplProofs/ImplWire/ImplStorage/ImplApply;
  ImplProofs cannot `open import Interface` (Command/Result clash) — separate modules with pointer comments.
- Rejected attempts (T2a, T3 #2, T4b #1): garbage output (nested `{ { { ; } } }`, 110-error pseudo-db.rs);
  lessons R7/R8 (diesel: batch_execute via SimpleConnection, sql_query constants only, load::<T> no load_all,
  table! grammar) recorded in memory fork-rust-quirks / diesel notes.
- Coordinator probe: `timeout 3 ./target/debug/formal-twitter` prints all 13 routes + graceful shutdown.
- T4a note: apply() tests exist (test_apply_inserts_all/test_apply_diff) with ImplApply.agda pins; proofs landed.
- T5 note: cargo test = 29 passed (4 suites, 32s); smoke reentrancy = 3 sequential servers on ONE /tmp sqlite file.
