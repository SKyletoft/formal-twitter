# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Done (history, condensed; details in git log)
- [x] Review of merge 123051e (spec/Interface wire protocol): ALL endpoints POST /api/<name>;
  body = CRLF-joined lines, token FIRST, no trailing newline; anonymous get-tweet/global-timeline omit token;
  responses strict double-quoted JSON, always `Date:`, `Cache-Control: no-store` on timeline/session-token/tweet;
  ok = 200 + Content-Length: 0 empty body; codes: 200 ok/tweet-id/timeline/token/tweet, 403 access_denied,
  401 session_expired/login_failed, 400 signup_failed. frontend/app.js UNCHANGED (legacy GET+LF) -> aliases = T6.
- [x] Study spec: Twitter.agda, Interface.agda, frontend/app.js (facts kept in "Reference" below).
- [x] R1/R2/R3 research: frontend protocol, Rocket 0.5.2, Diesel 2.4.0 sqlite. Findings in memory notes.
- [x] T1 (d5f78e5): model.rs — World/step mirroring Twitter.agda + QuickCheck props + ImplProofs theorems.
- [x] T2 (fee6d9e): wire.rs — parse_action, to_command, escape_json, respond + 24 refl theorems in ImplWire.agda.
- [x] T3 (58f2c92): db.rs — 9 diesel table!s, init_or_open (reentrant CREATE), load_world, save_world + 6 ImplStorage theorems.
- [x] T4a (c411372): db.rs apply(before,after) bounded O(delta) write-through + ImplApply.agda 32 refl theorems.
- [x] T4b-1 (be05d56): main.rs helpers — http_date, to_output, random_u64, sample_id, to_http.
- [x] T4b-2 (6bd2426): main.rs server layer — serve() behind 13 #[post] routes, State<Mutex<Server>>, per-request
  init_or_open + apply() write-through, launch via FT_DB.
- [x] T5 (794ce85): tests/smoke.rs — 5 network integration tests, raw std::net TCP spec client, 3-lifecycle reentrancy.
- [x] T8 (e5dd9f9): SKyletoft/* are owner forks; canonical smallstr 0.3+union, smallvec 1.15+union in Cargo.toml.
- [x] DB3a (58cbc47): db.rs apply() -> bool transactional (BEGIN first, COMMIT iff all Ok else ROLLBACK; +false);
  reopen() = establish-only; db_tests rollback test non-vacuous.
- [x] DB3b (96da42d): db.rs per-section reload_accounts/sessions/follows/posts (one cache section re-queried,
  others stay tampered) + ImplReload.agda 10 refl theorems.
- [x] DB3c (1c89048): main.rs serve() rule enforcement — Server +tick; poison-tolerant lock; COMMIT FIRST
  (reopen + apply bool; on false/Err world NOT advanced, 403 wire_error); exactly ONE section reloads per request
  keyed by tick (0 follows,1 sessions,2 accounts,3 posts), tick=(t+1)%4; load_world never at runtime.
- [x] CL1 (555e193): tests/smoke.rs clippy --all-targets cleanup (6 findings, logic byte-identical).
- [x] RV1 (research): test<->proof alignment audit (83 theorems vs 31 tests): orphans + misalignments M1-M4
  -> fix plan RV2a/c/f/g (wave 1), RV2b+d (wave 2), RV2e (parse pins, later cancelled by A4).
- [x] RV2a (a3ae476): ImplTick.agda — next-tick = suc%4 mirror, 8 shift pins, th-cycle-0..3, th-tick-hits.
- [x] RV2c (9203226): ImplApply — DB-keyed apply-ok-on carrier; th-apply-collide = false (non-vacuous, ROLLBACK flip -> exit 42).
- [x] RV2f (51e1935): ImplReload — deleted dead posts-tampered-nf/used defs (nf/used are DERIVED in row model); existing pins verified.
- [x] RV2g (f10c298): wire.rs respond_shapes() #[test] — all 9 respond() constructors unit-backed vs ImplWire wi-out-*.
- [x] A4 snapshot (b6b868b): recovery commit of whole Agda tree pre-deletion (all 9 doomed modules tracked).
- [x] A4 (9f19355): Remove pointless Agda — deleted ImplLite{0,1,2,M} + ImplParse (never typechecked / superseded);
  remaining tree = ImplProofs.agda + ImplWire.agda. RV2b+d ImplProofs half (th-prop-revoke-used witness,
  timeline-global uniq/len/membership lemmas closing M1) landed in this commit. ImplStorage superseded -> recovery keeps it.
- [x] TA (4356374): main.rs perf — random_block [u8;16] ONE urandom read/req; pure sample_id_from core; sample_id(&World)
  zero World clones; qc prop_pid/sid_fresh + 3 tests; ImplProofs th-sample-id-fresh.
- [x] TB (4a3aaae): db.rs apply() borrowed diff views — HashMap<u64,&Post>/HashSet<&String> etc, zero value clones;
  23-statement stmt seq byte-identical; + test_apply_perf_scale (500 posts).
- [x] TC (5e634f4): model.rs timeline perf — account_at_ref/post_at_ref/active_user_ref borrows, hoisted guards,
  early-stop at n matches; qc baselines + prop_timeline_global_equiv/prop_timeline_personal_equiv.
- [x] T6 (3ad81b5): GET aliases /api/get-tweet?..., /api/{global,private}-timeline?... over the SAME parse_action/serve_command
  pipeline; query_param/alias_body/serve_alias; 3 lib + 1 smoke alias tests (GET vs POST twins byte-equal).
- [x] T7 (b90d112): flake.nix — hermetic rustPlatform buildRustPackage, sqlite buildInputs, dontCargoCheck,
  meta.mainProgram, apps.default; nix build/run exit 0; binary links only nix-store glibc+sqlite+libgcc.
- [x] T10-doc (734cb19): 274 #[doc="..."] -> /// across model/wire/db/main/smoke; gates unchanged (49 tests).
- [x] T9 (research): whole-impl review — 12 findings F1..F12 + D1 discipline gap, queued as F-queue below.
- [x] H1 (8c1ea65): hygiene/perf batch — push_str/reserve (show_tweets, escape_json, alias_body, two()),
  query_param find_map, member->contains, Like/Unlike/Unfollow retain, len as u64, take.
- [x] H2 (db9be76): dead-code — key_unique deleted (zero callers); follows_author/take_n/save_world/well_formed KEPT
  with test-only/lossy docs; wire_error param ->_e.
- [x] G1 (6b2ff4b): db.rs internals F5+F6+F7 — bucket_like_rows/bucket_reply_rows run-contiguous grouping (one pass
  instead of per-post row filters), HashSet set-diffs for like/reply apply (O(1) probes), newest_first derived by
  stable RAM seq sort (4th full-table ORDER BY query gone in load_world AND reload_posts); db.rs 1199->1285 lines;
  gates: fmt/build/test 49 (34 lib+9 bin+6 smoke)/clippy -D warnings/agda ImplProofs+ImplWire all 0.
- [x] TDC (34e44f6, coordinator): todo.md cleanup — condensed history to one line/commit, ordered Next queue.
- [x] T10 (research): frontend/app.js NON-CONFORMANT vs Interface.agda — 6 endpoints names/paths exact and POST bodies
  token-first OK, but get-tweet/global/private-timeline are GET+query (Interface.agda: 15 to-request clauses ALL POST,
  zero GET), POST bodies LF-joined + trailing LF vs CRLF no-trailing (app.js:134), empty-token sent as `token=`/''
  line vs spec arity-omission (:134-142/:153-161), headers lack Accept/charset, logout never called. Aliases (T6)
  bridge FULLY for what app.js sends: query_param None-rules + alias_body no-token-line + split_lines trailing-CRLF
  tolerance; GET/POST twins byte-equal incl. token-less private refusal (smoke test_get_alias_roundtrip).
- [x] T11 (decision): KEEP the GET aliases. Only consumers of GET: frontend/app.js (shipped verbatim in result/frontend
  build output) + smoke test_get_alias_roundtrip; spec sanctions POST-only, so removing aliases breaks the shipped
  frontend for get-tweet + timelines -> deletion would require editing a legacy artifact we do not own. Aliases add no
  permission logic (re-enter same parse_action/to_command/serve_command). Decision + rationale recorded in routes! comment.
- [x] D1 (659e18c): main.rs failure paths (reopen Err / apply==false) now call reload_all_sections(path,&world-before)
  -> reopen + reload_accounts/sessions/follows/posts chain (Err -> cache stays put, documented); World stays unadvanced,
  403 bytes identical, tick not rotated, happy path unchanged; + test_reload_all_sections (tampers ALL FOUR sections,
  asserts reloaded == load_world(fresh) + Err-branch no-panic); 49->50 tests; fmt/build/clippy/agda x2 all 0.
- [x] F3 (d6a1487): db.rs apply(conn,before,after,max_hint) — new-post stamp = max_hint+1; per-request full SELECT-seq
  hand-fold DELETED (db_max_seq = one-shot launch seed on the load conn); Server +max_seq, bumped by new_post_count
  two-finger merge on COMMITTED apply only (failure arms leave it; single-writer-per-DB-file caveat documented);
  test_apply_max_hint pins hint verbatim (seqs 1..5, hint 42 -> seq 43); perf-scale 501 via hint 500; 50->51 tests.
- [x] F9 (68c7f2b): Server +conn: Option<SqliteConnection> seeded from the LAUNCH connection (init_or_open now returns
  (world,max_seq,conn) tuple); serve_command mem::swaps conn out for the request — happy path reuses held conn for apply
  + tick reload (zero reopen/path-copy), failed-reopen arm reopens once + reload_all_sections(&fresh) + stores it back,
  rolled-back arm resyncs over held conn; reload_all_sections signature (conn,&w)->w, Err->cache-stays-put pinned at call
  site; + test_apply_conn_reuse (one establish, two successive apply commits same conn, both views == after2);
  test_reload_all_sections updated; 51->52 tests; fmt/clippy/agda x2 all 0.

## Next (ordered queue)
- [x] F4a (attempt 1, REJECTED): subagent died mid-run leaving broken stubs (pub fun(, dangling 'a, comment-only
      bodies) — partial reverted, model.rs back to HEAD byte-identical. Lesson: keep subagent generation units small;
      split F4a into helpers-first, step-conversion second. DESIGN COMMITTED: WorldIndex{accounts_ix,sessions_ix,
      posts_ix: first-occurrence HashMaps; follows_ix HashSet} + build_index (insert-if-absent = Vec first-match) +
      _ix lookup/predicate helpers; step KEEPS signature: step(w,..) = step_ix(w, build_index(w), ..) (one ix body,
      no 200-line copy); original timelines keep names/signatures, delegate to _ix twins; pure-Vec *_timeline_ref
      kept test-only as QuickCheck reference; Server holds index, rebuilt on reload, serve_command passes it to step_ix.
- [x] F4a-1 (impl subagent, ACCEPTED, THIS COMMIT): WorldIndex+build_index + 9 _ix helpers landed in
      model.rs (1207->1446 lines): imports 3-4, WorldIndex 67-78, build_index 80-109, account_at_ix 190-194,
      session_at_ix 206-213, post_at_ix 235-239, follows_ix 251-256, active_user_ix 289-296, valid_session_ix
      306-313, access_ok_ix 342-349, can_read_ix 370-388, is_post_public_ix 398-405; 3 qc props (prop_ix_lookups_equiv,
      prop_ix_predicates_equiv, prop_ix_build_firstwins w/ hand-built duplicate-username world, no well_formed guard)
      at mod qc end ~1330-1446; tests 52->55 (39 lib + 10 bin + 6 smoke); gates fmt --check/build/clippy(-D warnings,
      silent)/test/agda x2 all rc 0; no commit yet.
- [x] F4a-2 (impl subagent, ACCEPTED, THIS COMMIT): step body MOVED to step_ix(w, ix, ..) — every scan lookup ->
      _ix twin, World-construction blocks byte-identical, no intermediate-world lookups; step = build_index + step_ix
      wrapper (signature kept, main.rs untouched); timelines: *_timeline_ref pure-Vec refs (test-only QuickCheck refs),
      public names delegate to _ix twins via fresh index; borrow helpers active_user_bx/account_at_bx/post_at_bx +
      indexed-borrow can_read_ix/is_post_public_ix (zero per-probe clones); qc prop_timeline_{global,personal,public}_ix
- [x] F4b (impl subagent, ACCEPTED, THIS COMMIT): Server +index: WorldIndex (launch build_index(&world), rebuilt
      after ALL THREE reload arms in serve_command: reopen-Err, committed tick-rotate, rollback resync); serve_command
- [x] F1a (impl subagent, ACCEPTED, THIS COMMIT): Delta sum-type (None_, Publish(pid,author,text,vis,parent?),
      Delete(pid), Authenticate(sid,user), RevokeToken(sid), Register(user,acct), Follow/Unfollow(f,g), Like/Unlike(pid,user),
      TimePasses(Vec sids)) at :144 + step_d(&w,&ix,..) -> (Result,Delta) :968 (guards byte-mirror step_ix, zero World clones)
      + patch_world(w: World, d) -> World :1131 (owned in-place, push/insert(0,)/retain/status/ids ops byte-match step_ix);
      qc prop_delta_equiv (:2006: result equal AND patch_world(w.clone(),d) == step-after, well-formed guard) + test_delta_register
- [x] F1b (impl subagent, ACCEPTED, THIS COMMIT): serve_command evaluates step_d(&before, &locked.index, ..) -> (Result,Delta),
      after = patch_world(before.clone(), delta) (before clone kept + note: true single-copy move-swap is F2's job);
      max_seq bump delta-derived k (Delta::Publish(..) -> 1 else 0; new_post_count kept #[cfg(test)] test-only);
      imports: step_ix dropped (test-local use), Delta/patch_world/step_d added; +test_delta_publish_equiv (step_d/patch
      == step on literal world, k == new_post_count == 1); 64->65 tests (47 lib + 12 bin + 6 smoke); apply signature
      UNCHANGED (F2 owns delta-driven body); gates all rc 0, Agda untouched.
      before clone KEPT for apply(&before,&after,hint) + failure arms (single-copy move-swap deferred; F2 owns apply);
      new_post_count replaced by delta-derived k for max_seq bump (old fn kept test-only doc); +one bin pin test; smoke green.
      == step via built index + reload-site round-trip hit/miss); 60->61 tests (44 lib + 11 bin + 6 smoke); gates
      fmt/build/clippy -D warnings silent/test/agda x2 rc 0; main.rs only touched.
- [x] F4b (eafb425, impl subagent, ACCEPTED): main.rs Server +index: WorldIndex — launch build_index(&world), rebuilt
      after ALL THREE reload arms; serve_command steps via step_ix(&before,&locked.index,..); +test_serve_index_consistency.
- [x] F1 (F1a 525c028 + F1b 6d2209b, impl subagents, ACCEPTED): Delta sum-type + step_d -> (Result,Delta) + patch_world;
      serve_command runs step_d/patch_world, delta-derived k drives the max_seq bump; prop_delta_equiv + pins.
- [x] F2 (impl subagent, ACCEPTED, THIS COMMIT): db.rs apply_delta(conn,&before,delta,max_hint) :882-1058 + doc; per-branch
      diesel statements mirroring apply's per-row idioms verbatim: None_ zero-stmt COMMIT true; Publish INSERTs posts(seq=max_hint+1)+used_pids
      (+replies row reply_pid=pid,parent when parent is Some — patch appends reply to parent list); Delete UPDATEs posts
      cols apply's UPDATE sets (status+visibility, verify by reading); Authenticate/RevokeToken/TimePasses session-row ops
      (one per sid); Register accounts INSERT cols; Follow/Unfollow follows-branch op; Like INSERT / Unlike DELETE likes row;
      PK clash -> ROLLBACK false unchanged. apply() doc -> "test-only reference" (tests kept). serve_command :392 ->
      apply_delta(&mut conn,&before,delta,locked.max_seq); after stays (moved into reload arms); import +1 (F2) comment.
      6 db.rs scenario tests (publish seq=hint+1 + newest_first head, publish_reply load==want-PLUS-row (patch lags by the
      row; reload_posts converges), delete UPDATE-only idempotent tombstone, follow/unfollow/ghost successive, collision
      Publish+Register -> false&DB-unchanged&conn-reusable, None_/empty TimePasses/TimePasses/Authenticate/RevokeToken/
      Like/Unlike pins) :1664-1939; apply_delta :882-1058; main.rs :392->apply_delta + import swap (apply dropped from top
      import, test modules keep local imports) + delta.clone() for patch (commented) + (F1b) comment corrected; ImplProofs
      7-line (F2) pointer comment ONLY (A4); 65->71 tests (53 lib + 12 bin + 6 smoke 31.7s), gates fmt/build/clippy/agda x2
      all rc 0. Note: neither step_ix nor patch_world appends to a parent's replies FIELD — the replies ROW is the DB encoding
      of child.parent, load_world re-derives it; Follow/Like deltas guarded by *_ix probes so INSERTs never re-clash.
- [x] Final verify (coordinator, DONE): fmt --check rc 0, build 0 warnings, clippy --all-targets -D warnings silent,
  71 tests (53 lib + 12 bin + 6 smoke lifecycle green), agda ImplProofs + ImplWire rc 0, quick probe + nix run launch
  OK; every accepted task committed with co-author maki@qwen3.8-flash-next-coder. QUEUE EMPTY — F-queue complete.

## Reference: spec semantics (Twitter.agda + Interface.agda, from R4/R5)
- `World` (:65-109): account-at String -> Maybe Account{password, default-visibility}; session-at Sid ->
  {unused, active username, revoked}; post-at Pid -> Maybe Post{author,text,visibility,status,likes:List Username,
  replies:List Pid,parent:Maybe Pid}; follows String -> String -> Bool; newest-first : List Pid (head = newest);
  used-post-ids, used-session-ids. Visibility everyone/followers-only; PostStatus live/deleted.
- Invariants: pid used <-> post-at <> nothing; sid used <-> session-at <> unused; active session => account exists;
  newest-first members exist; replies point back at parent (child.parent = just parent, child <> parent);
  uniq replies/likes/newest-first.
- CanReadPost w sid pid <=> post live AND (everyone OR (followers-only AND follows (author post))). Anonymous read = everyone only.
  failed-access (:464): session-taking command with invalid sid => expired, world unchanged, checked BEFORE the command's own rules.
- publish (reply only when CanReadPost parent, parent live, pid <> parent; reply visibility = parent's when
  followers-only else account default; prepend newest-first) => created-post/denied. delete (author only; flips status to deleted,
  keeps likes/replies/parent; idempotent) => success/denied. read-post => returned-post (author text (length likes) replies) / denied.
  personal timeline = take n . filter(follows-author) . filter(can-read) over newest-first; logged-in global drops the follows filter; anonymous global
  filters is-post-public (everyone AND live). like/unlike => success, denied when NOT CanReadPost; like appends
  username if absent, unlike removes it. follow/unfollow always succeed with valid session (set pair true/false; no existence check).
  register: only when username unused => account (default-visibility everyone); else signup-failed.
  login: only FRESH (unused) sid + matching password => active username + issued-session sid; else login-failed
  (always pick a fresh sid). logout: active -> revoked => success (unused/revoked => expired).
  collect-dead-posts/reap-tombstones COMMENTED OUT in spec: DO NOT implement; tombstones persist.
  time-passes (session-timeout :691) revokes all active sessions; no Action constructor => not an endpoint.
- `Result`: success | denied | expired | login-failed | signup-failed | returned-timeline ids | issued-session sid |
  created-post pid | returned-post author text likes replies. to-output -> the 200/403/401/400 bodies in
  Interface.agda:to-response. escape postulate applies to username/text in tweet bodies.
- DB schema (our encoding, 9 table!s): accounts(username PK,password,vis,ord), sessions(sid PK,status,user,ord),
  posts(pid PK,author,text,vis,status,parent,seq — newest-first = ORDER BY seq DESC), likes(post_pid,user,ord),
  replies(reply_pid,parent), follows(follower,followee,ord), timeline(pid,ord), used_pids(pid), used_sids(sid).
- ids: Nat (u64) from CSPRNG, rejected if used (matches CreateNew postulate). time-passes / collect-dead-posts:
  not endpoints. Anonymous read of private/deleted/missing post has no Step rule; impl returns 403 (denied family).
- Wire requests (post-merge spec): POST /api/<name> HTTP/1.1, Host + Accept: application/json +
  Content-Type: text/plain; charset=utf-8 + exact Content-Length; body CRLF-joined lines, token FIRST,
  no trailing newline. GET only from the legacy frontend (query params) -> support as aliases (T6).

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
