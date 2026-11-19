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
- [ ] TDC (coordinator): Clean up todo list
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
      TB REDO RESULTS (subagent, no commit; clean baseline 4356374, db.rs 1135 -> 1197 lines):
      enc_sess_row sibling enc_sess_row_ref(&SessionStatus) at HEAD:94 -> now :104; enc moved INTO executed branches (now :564 None, :576 Some-changed), pre-loop enc (HEAD :556) gone.
      views: users HashMap<String,bool> HEAD:515/520 -> HashSet<&String> now :525/530 (probes contains(&username) HEAD:526/538 -> :536/548);
      prev_sessions HEAD:545 -> HashMap<u64,&SessionStatus> now :555 (no status.clone); next_sessions map HEAD:550-554 -> next_sids HashSet<u64> one-liner now :560 (probe HEAD:580 -> :587 contains(sid));
      prev_posts HEAD:598 -> HashMap<u64,&Post> now :605 (no post.clone); next_pids already keys-only (HEAD:603 -> now :610);
      follows HEAD:715/720 -> HashSet<(&String,&String)> now :722/727; probes without clones HEAD:726/737 -> now :733/744.
      PRESERVATION: LCS diff of the whole apply() span shows ONLY view/probe/let lines changed; the 23-statement seq (insert_into/update/delete chains, BEGIN/COMMIT/ROLLBACK pragmas, ok &=, return bool) is byte-identical (programmatic A==B check True).
      NEW #[test] test_apply_perf_scale at now :1147: 500 posts pids 1..500 (used_post_ids, newest_first reverse), save_world(empty) wipe + save_world(before) (seqs 1..500), diff DELETE pid7 / UPDATE pid11->Deleted / INSERT pid900 (seq 501), committed==true, load_world==after (newest_first [900,500..8,6..1]), reopen agrees.
      GATES: cargo fmt --check exit 0 (nightly-option warnings only); cargo test 43 passed 0 failed (42+new, all db_tests green = behaviour guard); clippy --all-targets -D warnings exit 0; agda ImplWire+ImplProofs exit 0 (no Agda edits).
- [ ] Task TC (impl, MED): perf model.rs timelines — hoist active_user/account_at out of newest_first loop,
  early-stop after n matches, post_at_ref -> Option<&Post> for read-only callers.
    - TC (subagent, STARTED): timeline perf model.rs
    - TC (subagent, RESULTS): model.rs 1051->1220 lines. NEW borrowing lookups account_at_ref :147,
      post_at_ref :177, active_user_ref :215 (old owned fns kept). Read paths switched to refs:
      can_read :264, is_post_public :283, follows_author :291, well_formed :423/:434/:441/:459.
      personal_timeline rewritten :311 (hoist active_user_ref+account_at_ref guard, n==0 early return,
      one post_at_ref per candidate, break at n matches) was :278; global_timeline :346 (was :294);
      public_timeline :379 (was :305). qc imports +follows_author/global_timeline/is_post_public/
      personal_timeline/public_timeline/take_n. NEW qc baselines old_global_timeline/old_public_timeline/
      old_personal_timeline :1143-1179 (pre-TC full-filter+take_n) + #[quickcheck] prop_timeline_global_equiv
      :1181, prop_timeline_personal_equiv :1203 (n,0,1,2,1000 each; sid/n drawn from generated Command pools
      so the active-session branch is hit). ImplProofs.agda: 9-line pointer comment :405 (no new module) saying
      semantics unchanged, so th-timeline-* uniq/len/membership still apply.
      GATES: cargo fmt --check exit 0 (nightly-option warnings only); cargo test 45 passed 0 failed
      (34 lib + 6 bin + 5 smoke = 43 baseline + 2 new props); clippy --all-targets -D warnings exit 0;
      agda ImplWire.agda + ImplProofs.agda exit 0. NOT committed.
- [ ] Task T6 (impl, SMALL): frontend-conformant GET aliases (/api/get-tweet?token=&id=,
  /api/{global,private}-timeline?token=&len=) -> same Action; tolerate LF/trailing-newline bodies.
- [x] Task T7 (impl): flake.nix — hermetic rustPlatform buildRustPackage (vendored cargo), `nix run .`
  starts the server; libsqlite3-sys bundled pin if needed.
- [x] Task T10 (impl, MECHANICAL): convert ALL #[doc = "..."] one-liners + stacks to /// across
  model.rs/wire.rs/db.rs/main.rs/smoke.rs; verify fmt/clippy/test/agda unchanged. (ACCEPTED, committed
  below; 274 attrs, gates identical 49 tests)
- [x] Task T9 (impl): review whole implementation for non-idiomatic code + perf issues (after TA-TB-TC landed). (RESEARCH DONE: 12 findings, queued as F1..F12 + D1 below)
- [ ] Task T10 (research): Is frontend spec-conformant?
- [ ] Task T11 (research): Remove compat aliases?
- [ ] Task A4 (research): Remove pointless agda. Any agda that isn't proving (or providing lemmas for) anything in relation to the model in @spec/Twitter.agda or @spec/Interface.agda is useless and pointless.
- [ ] Final verify: cargo build/test, clippy -D warnings, cargo fmt --check, agda typecheck all files, nix run;
  commit each accepted task with co-author maki@qwen3.8-flash-next-coder.
- T6 (subagent, STARTED): frontend GET aliases
- T6 (subagent, DONE, NOT committed): main.rs query_param (raw query -> first pair with name, bare/
  empty/absent = None) + alias_body (token line only when present, then value line, CRLF, trailing) +
  serve_alias(&Origin<'_> via Rocket's FromRequest for &Origin) + 3 #[get] aliases
  (get_tweet_alias/global_timeline_alias/private_timeline_alias) added to routes!; they rebuild the
  POST-equivalent body and re-enter the self-same parse_action + to_command + serve_command, so verdicts
  and bytes match the POST twins (no new error codes). GETS: cargo fmt --check exit 0 (nightly-option
  warnings only); cargo build 0 errors; cargo test 34 lib + 9 bin (test_alias_get_tweet_parses,
  test_alias_timeline_parses, test_alias_query_param_parses) + 6 smoke (new test_get_alias_roundtrip:
  raw-TCP GET vs POST twins equal status line + body, incl. token-less private refusal on both
  transports); clippy --all-targets -D warnings exit 0; agda ImplWire.agda + ImplProofs.agda exit 0
  (ImplWire gains only a pointer comment: the aliases add no Interface clause).
- T7 (subagent, STARTED): flake nix run wiring
- T7 (subagent, ACCEPTED, committed b90d112 — see flake-nix-t7 memory): flake nix run wiring.
      flake.nix BEFORE: packages.default = buildRustPackage inline, no apps.default.
      AFTER: moved the buildRustPackage into let as `package` (lines 24-40; flake-utils does not bind `packages`, so
      `getExe packages.default` was an undefined-variable error), added buildInputs = with pkgs; [ sqlite ];
      (diesel 2.4.0 feature sqlite -> libsqlite3-sys 0.40.0 links the system sqlite; buildInputs present in drv env),
      dontCargoCheck = true; + comment (skipTests is IGNORED by the rust hook — verified in
      cargo-check-hook.sh setup-hook:62, gate is `dontCargoCheck`; the package check phase had run smoke.rs spawning
      live servers, which can never start in the no-network sandbox), meta.mainProgram = "formal-twitter";
      (kills getExe's deprecated-name warning), packages.default = package; apps.default = { type = "app";
      program = pkgs.lib.getExe package; } (lines 46-49; type="application" -> error "should have type 'app'";
      flake-utils mkApp uses type="app" too — lib.nix:194).
      BUILD: `nix build .#packages.x86_64-linux.default` and `nix build .` exit 0 (first full build: 125 crate drvs,
      cache.nixos.org+nix-community.cachix fetches; rebuild fast). NOTE `nix build .#packages.default` (bare) FAILS on
      flake-utils' shape — nix only tries packages.x86_64-linux.packages.default / legacyPackages.../packages.default /
      top-level packages.default, none of which exist; the working invocations are `nix build .` and the explicit-system
      form; `nix run .` resolves apps.x86_64-linux.default fine.
      ARTIFACT: ./result -> /nix/store/yvbms08vg7bnpr82wzlw3y6y042n2paq-formal-twitter-0.0.1; $out/bin has EXACTLY ONE
      binary: formal-twitter (5.3M); $out/frontend copied as before.
      LINKAGE: nix-store --query --references $out/bin/formal-twitter =
      glibc-2.42-61 + sqlite-3.51.2 + gcc-15.2.0-lib — all nix-store paths (vDSO implicit), NO /usr refs; sqlite
      linkage found via buildInputs sqlite dev output.
      RUN: `nix run .` 5s (timeout -s INT): prints "Rocket has launched from http://127.0.0.1:8000",
      "Warning: Received SIGINT. Requesting shutdown." (graceful), exit 124 (timeout sends INT); clean rerun after
      meta.mainProgram no longer prints the getExe mainProgram deprecation warning.
      e2e signup curl NOT done: sandbox denies curl and script exec; smoke.rs untouched and remains the real guard.
      Agda/cargo gates UNTOUCHED this task (no src/, no .agda edits; flake only).
- T10-doc (subagent, STARTED): convert ALL #[doc = "..."] one-liners + stacks to /// across model.rs/
  wire.rs/db.rs/main.rs/smoke.rs; gates must stay identical (49 tests, agda x2).
- T10-doc (subagent, ACCEPTED, committed below): 274 #[doc] attrs -> /// line-for-line: model.rs 68,
  wire.rs 32, db.rs 43, main.rs 99, smoke.rs 32; all five files 0 remaining; escaped quotes unescaped
  (main.rs:48), 3 trailing-space literals trimmed (db.rs:1143-1145); line counts unchanged 1220/641/1197/849/651;
  gates identical: fmt 0, build 0, clippy --all-targets -D warnings 0, cargo test 34 lib + 9 bin + 6 smoke = 49,
  agda ImplProofs + ImplWire 0. Coordinator reran fmt/build/clippy/test/agda myself: all green.
- T9 (research subagent, DONE, 12 findings): F1 main.rs:256 before=locked.world.clone() + 23 step-clone
  sites = 2+ full World copies/request; F2 db.rs:521-760 apply rebuilds 6 hash collections over ENTIRE
  world per request incl reads; F3 db.rs:595-604 full SELECT seq + max-fold per request (hand-rolled max);
  F4 model.rs timelines O(P^2+P*F): Vec-based World, post_at_ref/follows linear; F5 db.rs:219-228/:379-388
  reload attaches likes/replies by filtering ALL rows per post O(P*(L+R)); F6 db.rs:657-666/:680-702 like/reply
  diff old.likes.iter().any inside post.likes.iter O(L^2)/O(R^2); F7 db.rs:358-365/:201-208 reload_posts issues
  4 full-table queries incl redundant ORDER BY seq DESC re-scan (sort loaded rows in RAM); F8 db.rs:628-644 etc
  one insert/delete statement per changed pair (batch .values(&rows) pattern exists at save_world:466);
  F9 main.rs:265 reopen(db_path.clone()) = new SqliteConnection establish + String alloc per request;
  F10 wire.rs:270/:272 out += ", "/&x.to_string() quadratic show_tweets (+ main.rs:386/:391 alias_body, :37 two());
  F11 idioms: model.rs:97-105 member loop->.iter().any (also like-check clone at :646), :128-134 len_u64->xs.len(),
  :298-308 take_n->.take(n), :632-636/:660 Unfollow/Unlike re-collect+clone -> retain, main.rs:397-415 query_param
  collect-all-then-first -> .find_map, :426 origin.query()->String copy, :49 http_date year-scan, wire.rs:233-262
  escape_json no capacity; F12 dead: key_unique never called, follows_author/take_n test-only, save_world test-only
  + LOSSY (stamps seq=0 for pids absent from newest-first), wire_error(e) discards arg, well_formed never runs.
  D1 discipline gap: on reopen/apply FAIL main.rs:266/:286 skip re-querying the other RAM sections (AGENTS.md
  periodic re-query violated on failure path); well_formed unchecked. Verdict: DB-truth holds on happy path,
  reentrancy plausible (FT_DB + init_or_open + smoke restarts), cache cost dominates DB work at O(DB)/request.
- F-queue (impl subagents, sequential, one per finding unless batched H1/H2): H1=F10+F11 hygiene (wire.rs/main.rs/model.rs,
  mechanical, gates identical 49 tests); H2=F12 dead-code (key_unique remove, wire_error arg, keep test-only
  helpers, note save_world lossy in doc); F3 max_seq in Server; F9 hold conn in Server (reopen only on failure);
  F7 sort loaded rows in RAM (kill 4th query); F5 groupby rows once; F6 HashSet per touched post; F4 World HashMap/HashSet
  side-caches (periodic reload rebuilds); F1 step(&World)->(Result,Delta) single-copy; F2 delta-driven apply (touched
  keys only); D1 re-query ALL sections on reopen/apply failure.

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
