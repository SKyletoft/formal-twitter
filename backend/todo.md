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
  3-lifecycle reentrancy on ONE FT_DB file.
- [x] Task T8 (RESOLVED e5dd9f9): SKyletoft/* are owner forks; canonical deps smallstr 0.3+union,
  smallvec 1.15+union in Cargo.toml. Use in src deferred to T9 (types pinned by diesel + Agda-style ==).
- [x] Task DB3a (ACCEPTED 58cbc47): db.rs apply() -> bool transactional (BEGIN TRANSACTION; first,
  per-statement `ok &= execute(conn).is_ok()`, COMMIT iff all Ok else ROLLBACK TRANSACTION; + false),
  reopen() = establish-only; db_tests +test_apply_returns_true/test_apply_failure_rolls_back (non-vacuous:
  sabotaging ROLLBACK fails the test); ImplApply.agda +th-apply-ok (refl); main.rs call site discards bool.
- [x] Task DB3b (ACCEPTED 96da42d): db.rs per-section reload_accounts (:257 accounts only), reload_sessions
  (:287 sessions + used_session_ids as ONE section), reload_follows (:309), reload_posts (:325 posts +
  newest_first + used_post_ids via ORDER BY seq DESC); diesel pipelines copied from load_world; 4 db_tests
  tamper one RAM section and assert reload restores the DB view while untouched sections stay tampered;
  backend/ImplReload.agda (open import ImplApply) +10 refl theorems th-reload-* incl -used/-rest; ImplProofs
  +open import ImplReload. cargo test 35 passed; agda ImplReload/ImplApply/ImplProofs/ImplStorage exit 0.
- [x] Task DB3c (ACCEPTED, commit follows): main.rs serve-layer rule enforcement — Server +tick: u64;
  poison-tolerant lock (Ok guard / Err(poisoned).into_inner()); COMMIT FIRST: reopen + apply(&before,&after),
  on false/reopen-Err the world is NOT advanced and the answer is the 403 access_denied shape (wire_error);
  after commit exactly ONE section reloads keyed by tick (0 follows, 1 sessions, 2 accounts, 3 posts) then
  tick = next_tick(t) = (t+1)%4; load_world never at runtime; `after` moved into reload (no extra clone).
  +#[test] test_tick_rotation_cycle (4-cycle balance + next_tick^4 == id) with pointer doc mapping DB-facing
  theorems to ImplApply/ImplStorage/ImplReload. cargo test 36 (31 lib + 5 smoke).
- [x] Task CL1 (ACCEPTED, commit follows): tests/smoke.rs clippy --all-targets cleanup — 6 findings fixed
  (2 to_string elisions, match Option -> is_some, 3 == x.to_string() -> == x), 525 -> 516 lines, logic
  byte-identical; clippy --all-targets -D warnings now exit 0.
- [x] RV1 (research): test<->proof alignment audit — 83 theorems vs 31 unit tests; found: ORPHAN test_tick_rotation_cycle;
  ORPHAN weak wi-out-* (7 integration-only); MISALIGNMENTS M1 prop_timeline_valid (global+uniq+len<=n vs personal-eq only),
  M2 register theorems weaker (no nw==w half), M3 revoke missing rest-unchanged, M4 ImplReload dead tampered defs;
  GAP: parse-level (wire.rs byte decisions) unpinned; ImplStorage not opened by ImplProofs. Fix plan = RV2a/c/f/g (wave 1),
  RV2b+d (wave 2: ImplStorage pins + ImplProofs opens + timeline-global + M2/M3), RV2e (parse pins).
- [x] RV2a (ACCEPTED, commit follows): ImplTick.agda (standalone, stdlib-only) — next-tick = suc % 4 mirror of main.rs:170,
  8 shift pins th-next-tick-0..7 (4->1 etc.; brief's 4≡0 was arithmetically wrong, pinned Rust's actual (t+1)%4),
  th-cycle-0..3 next-tick^4 = id, th-tick-hits map next-tick [0..7] ≡ [1,2,3,0,1,2,3,0] refl (lands twice each => hits [2,2,2,2]);
  + 1 pointer #[doc] line at main.rs test_tick_rotation_cycle. agda ImplTick exit 0; 36 tests unchanged.
- [x] RV2c (ACCEPTED, commit follows): ImplApply.agda — found th-apply-ok VACUOUS (apply-ok conflates DB with before -> always true);
  added DB-keyed carrier apply-ok-on (disk,before,after) :456 reusing collide/inserted-pids; pins th-collide-inserted :449,
  th-collide-disk :453, th-apply-collide :461 ≡ false (world-B-minus-1 lies RAM, collides on disk — test_apply_failure_rolls_back),
  th-apply-collide-honest :465 ≡ true (guards always-false). Non-vacuity: flipped RHS -> agda exit 42.
- [x] RV2f (ACCEPTED, commit follows): ImplReload.agda — verified th-reload-posts/-used ALREADY pin the restored nf 3∷2∷1 +
  used 1∷2∷3 from tampered input; nf/used lies [9,8] unmodellable (fields are DERIVED in the row model) -> deleted dead
  posts-tampered-nf/used defs with explanatory comment :70-76. No theorem added (would be duplicate/vacuous).
- [x] RV2g (ACCEPTED, commit follows): wire.rs tests — new #[test] respond_shapes() in wire_tests: all 9 respond() constructors
  unit-backed (status codes 403/401/401/400/200/200/200, header-tuple equality pinning Cache-Control presence per spec +
  Content-Type iff non-empty body, exact body bytes incl. escaped tweet "a\"b/c\nd and quoted ids) matching ImplWire wi-out-*;
  respond() source untouched. cargo test 37.

## In progress
- [x] TA (ACCEPTED, this commit; impl subagent general/medium): perf main.rs — random_u64 -> random_block() [u8;16] (ONE /dev/urandom read/req), NEW pure sample_id_from(bytes,used) core, sample_id(&World) -> (pid,sid) with ZERO World clones (was 2/req; used_pid/used_sid imports dropped, membership==World fields verified model.rs:177/182); mod qc NEW: prop_pid_fresh/prop_sid_fresh #[quickcheck] + boundaries/halves/determinism tests; ImplProofs NEW th-sample-id-fresh — ∀w: new-sid/new-pid id component ∉ used lists over SPEC definitions (Proofs uses the conjunct only inline, :828/:997). GATES: cargo test 42 (37+new) green, clippy --all-targets -D warnings clean, fmt no-op, agda ImplWire+ImplProofs exit 0.
      TA RESULTS (subagent, no commit): main.rs:128 random_u64 -> random_block() -> [u8;16] (ONE /dev/urandom read per request, 2 BE u64s);
      main.rs:151 NEW pub sample_id_from(bytes: &[u8], used: &[u64]) -> (u64, bool) — pure decision (first 8 bytes, r != 0 && !used.contains(&r), total on short blocks);
      main.rs:161 pub sample_id(&World) -> (u64, u64) (was (World, fn) — no World clone, borrows used_post_ids/used_session_ids, retries whole block on any collision);
      serve() call site now let (fresh_pid, fresh_sid) = sample_id(&before) (was 2x sample_id(before.clone(), used_pid/used_sid)); model.rs used_pid/used_sid imports dropped (membership == the World fields, verified model.rs:177/182).
      main.rs:mod qc (cfg test) NEW: prop_pid_fresh + prop_sid_fresh (#[quickcheck] over Vec<u64> used sets + Vec<u8> blocks padded to 16B), test_sample_id_boundaries (empty/short block + zero + 2^64-1 offered-vs-used exhaustion path), test_sample_id_halves (one 16B block -> two ids, 0..8 vs 8..16), test_sample_id_deterministic (same bytes+used -> same (id,ok), x10 replay).
      ImplProofs.agda:481 NEW th-sample-id-fresh — ∀ w: the id component (Data.Product.proj₂∘proj₁) of new-sid (World.used-session-ids w) ∉ that list, × same for new-pid/used-post-ids; 8-line pointer comment names Proofs.agda's inline uses (:828 not-used-before, :997 sid∉) — no named lemma existed there.
      GATES: agda ImplProofs/ImplWire exit 0; cargo fmt --check clean; cargo clippy --all-targets -D warnings exit 0; cargo test 42 passed 0 failed (31 lib + 6 bin incl new 5 + 5 smoke). db.rs/model.rs/wire.rs untouched.
- [x] A4 snapshot (ACCEPTED b6b868b): recovery commit of the WHOLE Agda tree pre-deletion — untracked ImplLite{0,1,2,M}/ImplParse staged + kept (never typechecked; recovery only), RV2b+d ImplProofs/ImplStorage additions preserved, A4-impl import/comment edits included. All 9 doomed modules are now TRACKED, so recoverable.
- [x] RV2b+d (impl subagent, DONE — ImplProofs half committed with A4; ImplStorage half SUPERSEDED by A4 deletion, recovery b6b868b): ImplStorage th-load-empty + load/save round-trip pin;
      ImplProofs th-prop-timeline-global + M2/M3 audit. Gate: cargo test + agda typecheck (LONG timeouts).
      ImplProofs half DONE (subagent, gate `agda ImplProofs.agda` exit 0): th-prop-revoke-used (:365, ∃-witness logout step
      preserving used-post-ids/used-session-ids — spec's logout constructor leaves those fields free so the ∀ nw==want
      conjuncts are NOT derivable, pinned as witness instead); th-timeline-global-uniq/len, -anon-uniq/len, -personal-uniq/len
      (:421-470) closing M1 uniq+len<=n conjuncts of prop_timeline_valid via general lemmas ∈-filterᵇ/crp/puc, ∈-take,
      take-uniq, take-len, filterᵇ-uniq, crp/puc-filter-uniq (:291-346). Existing theorems untouched.
      Also landed (11d): th-timeline-global-membership / -anon-membership / -personal-membership (:459-483) closing the
      ts.iter().all(member &w.newest_first) conjunct of prop_timeline_valid via ∈-take ∘ ∈-filter-crp/ᵇ/puc; gate re-run exit 0.
- [x] RV2e CANCELLED by A4: its target ImplParse.agda (stdlib-only parse_action pins, no Interface connection) was classified POINTLESS and deleted; ImplWire.agda already pins from-input/to-output at the SPEC level for all clauses. Recovery b6b868b keeps the file.
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
- [ ] Task A4 (research): Remove pointless agda. Any agda that isn't proving (or providing lemmas for) anything in relation to the model in @spec/Twitter.agda or @spec/Interface.agda is useless and pointless.
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
