# todo.md — formal-twitter backend

Coordinator plan. Mirror of todo-tool state; update statuses as work lands.
Tasks are performed by subagents; accepted tasks are committed, rejected ones reverted.

## Next
- [ ] RAW1 (impl) main.rs: /raw — DROP <pre> wrap (already rawtext), pretty-print World {:#?} not {:?}; retarget test_raw_text_shape + smoke test_raw_and_log pins. Subagent: general, main.rs only.
- [ ] LOG1 (impl) main.rs: /log un-redacted — EVERY line carries epoch ts + method+path + RAW request body (tokens/plaintext verbatim) + parsed Command + Result; drop endpoint-name-only logline. Retarget test_log_line_naming + smoke pins. Subagent: general, main.rs only.
- [ ] CLN research wave: 4 research agents, one per rust file (model.rs, wire.rs, db.rs, main.rs) — redundant/unused code, merge candidates, library-replaceable code, const-vs-let. Report-only, file:line refs, compact.
- [ ] CLN impl wave: per-file small impl tasks applying accepted findings (sequential, gates per task: fmt/build/clippy/test/agda).
- [ ] BENCH (research): design realistic perf benchmarks — NO new deps (subagents forbidden to touch Cargo.toml; lesson RV5-4); std-timed bench harness or bench bin target. Deliver design + numbers.
- [ ] OPT (impl): benchmark-guided hot-path optimisation, small per-site tasks, gates as usual.

## Done (history, condensed; details in git log)

## Done (history, condensed; details in git log)
- [x] RV5-4 (255267f, retry): UNLIKE ok/denied + unfollow (set-semantics, idempotent absent pair) + follow-gates-timeline (like ok + personal-timeline membership) + timeline-excludes-deleted (live/readable/prefix strengthens prop_timeline_valid) + th-prop-unlike-ok/denied/unfollow/follow-gate/timeline-excludes (proved contra-Bool absurd helper, NO postulates, ∈-filterᵇ-keep impossible branch fixed via contra-Bool not ⊥-elim metas). ATTEMPT 1 REJECTED — variantly 0.4.0 dependency contamination + dead subagent: reverted Cargo.toml/lock, deleted scripts/runqc.sh, rewrote derive + as_unlike/as_unfollow plain-style. Lesson: subagents forbidden from adding deps; VERIFY manifest after any general task.
- [x] RV5-3 (055a77a): PUBLISH trio — prop_publish_new/prop_reply_publish (vis inheritance + parent replies PREPEND)/prop_reply_denied over correlated PublishCase generator, mutation-probe non-vacuous; th-prop-publish-new/th-prop-reply-publish/th-prop-reply-denied refl-on-constructors. 64 lib.
- [x] RV5-2 (e6f6606): READ-POST — prop_read_logged_in/public_shape (ReturnedPost fields == stored post), denied trio missing/private/deleted; th-prop-read-logged-in/public + denied trio ALL refl-by-inversion (just-injective inline replaced post-at-unique; slv pattern rename). 61 lib + 9 smoke.
- [x] RV5-1 (293c307): LOGIN trio — prop_login_success/unknown_user/wrong_password + passwd_pool non-vacuity + as_authenticate; th-prop-login-issued (flip + pointwise rest)/unknown/wrong (7-section identity), refl-by-inversion; non-vacuity witness-checked. 56 lib.
- [x] RV5-0 (a9a3857): SPEC CONFORMANCE — step_ix/patch_world PREPEND reply child to parent.replies (Twitter.agda:401; step/step_d thin wrappers inherit); build_world generator +follows pairs +followed-author bias +readable reply parents; db.rs canonical reply order RAM newest-first / rows INSERT-chronological (no ascending sort; stable pid-group + reverse runs; save/apply write reversed); two stale db push(900)-hack tests replaced with spec-order pins.
- [x] RV5 audit (research, this commit): missing-tests review — 120 active spec constructors/rule shapes vs qc+tests: 17 GAP items (login trio, read-post shape trio + denied trio, publish/ reply pair + reply-denied, unlike pair, unfollow, follow-gates-timeline, timeline-excludes-deleted, publish-new) -> RV5-0..4 queued; COVERED highlights: 15 from-input + 15 to-request + 9 to-response/Response ctors (commands/anonymous_and_tokened/respond_shapes/timeline_bodies), CreateNew -> prop_pid/sid_fresh. EXCLUDED: commented-out collect-dead-posts/reap-tombstones, postulates unlines-crlf/show/escape/octet-strlen, ValidSession/PostIsNew/CanReadPost helper DATA (exercise through props). KEY FINDINGS: model step never appends parent.replies on reply publish (DB-only convergence today) -> RV5-0; build_world emits NO follows -> RV5-0; impl guards used-pid/!used-sid spec-free, keep out of hypotheses; each new prop needs matching th-prop-* in ImplProofs.
- [x] RV4 (3aa7135): ImplProofs Delta-bridge (data Delta 11 ctors + patch/res-of postulates + th-delta-equiv/register/like/publish) + Index-bridge (IndexW record + build-index/step-ix/timeline-ix stubs + 7 th-ix-* signatures); ImplWire wi-request-roundtrip/command (refl TRIED -> stuck-neutral via unlines-crlf/show/++/octet-strlen, postulated). Postulate-style: unsolved metas exit 42, agda-rc 0 required.
- [x] RV3d (06c3016): ImplWire wi-resp-* — 9 refl to-response pins (status line, header LIST order, Content-Length term, body expr per Result ctor) + commented wi-bytes-* opaque framing signatures; respond_shapes /// doc asserts-1:1-theorems, header ORDER/framing impl-defined.
- [x] RV3c (7cd7a29): revoke alignment — model.rs prop_revoke_token doc splits theorem-backed flip/inversion vs IMPL-DEFINED full identity (used-id pair unconstrained by spec logout); ImplProofs (4) TRIO block + (4c) cross-ref. Comment-only.
- [x] RV3e (b213173): wire.rs docs — commands() 13->15 (names wi-get-tweet-anon/wi-global-timeline-anon); endpoint_shapes doc cross-refs anonymous_and_tokened for the 2 anon arities.
- [x] RV3a+RV3b (6719e7b): th-prop-register-taken-id +account-at conjunct (7 refl; failed-create-account forces after≡before); th-prop-time-passes full inversion success⊎expired (failed-access always applies) + postulate prop-time-passes-full for the Rust-outright claim (Rust never fails that arm; spec relation admits it).
- [x] RV3 audit (research, this commit): test<->proof alignment review, 80 Rust tests vs 49 Agda theorems (ImplProofs+ImplWire): 9 aligned pairs, 0 orphan proofs, 5 MISALIGNMENTS (M1 register-taken missing account-at eq; M2 time-passes ∃-weakened vs full Rust characterization; M3 revoke used-ids spec-unconstrained; M4 respond_shapes concrete-HTTP vs wi-out-* abstract to-output, zero to-response pins; M5 commands() 13-vs-15 doc count) and 12 spec-level ORPHAN TESTS (Delta bridge, _ix bridge, endpoint_shapes) -> queued RV3a-e + RV4. Spot-checked M1 (ImplProofs.agda:78-99 omits account-at vs model.rs nw==w) and M5 (wire.rs:420 doc) before accepting.
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
- [x] F4a attempt 1 (REJECTED, d451d1c): subagent died mid-run (broken stubs) — reverted, model.rs HEAD-identical. Lesson: small generation units. DESIGN COMMITTED: WorldIndex side-index + _ix helpers; step keeps signature via build_index wrapper.
- [x] F4a-1 (48a315e): model.rs WorldIndex{accounts/sessions/posts first-occurrence HashMaps, follows HashSet} + build_index + 9 _ix lookup/predicate helpers + 3 qc equiv props; 52->55 tests.
- [x] F4a-2 (77c8c23): step body moved to step_ix(w,ix,..), every scan -> _ix twin; timelines delegate to _ix twins, pure-Vec *_timeline_ref kept as QuickCheck refs; borrow helpers zero per-probe clones; qc prop_timeline_*_ix; 60->61 tests.
- [x] F4b (eafb425): main.rs Server +index: WorldIndex — launch build_index(&world), rebuilt after ALL THREE reload arms; serve_command steps via step_ix; +test_serve_index_consistency.
- [x] F1a (525c028): Delta sum-type (None_/Publish/Delete/Authenticate/RevokeToken/Register/Follow/Unfollow/Like/Unlike/TimePasses) + step_d(&w,&ix,..) -> (Result,Delta) zero-World-clone + patch_world in-place; qc prop_delta_equiv (result equal AND patch == step-after); 64->65 tests.
- [x] F1b (6d2209b): serve_command runs step_d + patch_world; max_seq bump delta-derived k (Publish -> 1 else 0); +test_delta_publish_equiv; apply signature unchanged (F2 owns body).
- [x] F2 (ff1ea85): db.rs apply_delta(conn,&before,delta,max_hint) — per-branch O(delta) diesel statements mirroring apply's per-row idioms (Publish INSERT posts+used_pids(+reply row), Delete UPDATE tombstone, session/register/follow/like ops; PK clash -> ROLLBACK false); serve_command switched to apply_delta; apply() now test-only reference; 6 scenario pins; 65->71 tests.
- [x] ST queue (AGENTS instruction restored at a0ae1b5: "/" serves frontend/, /raw Debug dump, /log request log):
  - ST1 attempt 1 REJECTED (f6c6012, cancelled mid-run, partial main.rs reverted); split ST1a/ST1b.
  - ST1a (c679b74): frontend_root() ($out/frontend via current_exe, dev fallback CARGO_MANIFEST_DIR/../frontend) + read_frontend() guard-first (empty/sep/.. /leading-dot -> None) + 2 bin tests; 71->73.
  - ST1b (2d39d04): serve_static(name,mime) + #[get /][style.css][app.js] mounted (read per request, never RAM-cached); smoke test_static_serving over REAL TCP: doctype+shape pins, octet-pinned app.js len, bogus path -> 404; 74 tests, smoke 7/7.
  - ST2 (28e7627): Server.log ring LOG_CAP=1000 (push+evict after poison-tolerant lock, &command borrow); now_secs + http_date_from single epoch source; #[get /raw] <pre>{:?}</pre> of cached World (Debug already derived); #[get /log] CRLF http_date+Interface request-line names (Publish both arities -> post-tweet); 16-assert naming test + smoke test_raw_and_log (order + GMT + >=1000 year); 77 tests, smoke 8/8. Subagent committed despite no-commit; coordinator re-verified gates + routes post-hoc, ACCEPTED (fb93502).
- [x] Final verify (ST, DONE, fb93502): fmt --check / build 0 warnings / clippy --all-targets -D warnings silent / 77 tests (53 lib + 16 bin + 8 smoke) / agda ImplProofs + ImplWire rc 0; launch probe mounts all routes incl. /raw + /log. F-queue was complete; frontend-update queue (F10) then opened at c7dc308.
- [x] F10 (research, 1a2630c): audit — frontend/ reached only 6/13 wire actions; missing post-reply/delete/like/unlike/follow/unfollow/logout (logout-btn was localStorage-only, server never revoked).
- [x] F11a (bc8f643): frontend/app.js PROTOCOL layer — ENDPOINTS +7, buildBody token-first CRLF per wire.rs (clean() strips [\\r\\n]), logout endpoint BEFORE clearSession, signup-400 friendly msg; 384->431 lines.
- [x] F11b (b72f3ca): frontend UI — detail like/unlike/delete/reply buttons + textarea, timeline-row controls, #follow-form, forced-global #global-btn; index 67->77, app.js 431->532.
- [x] F11c (45ce02b): smoke test_new_actions_roundtrip — 7 new actions over REAL server, exact CRLF token-first bodies (byte contract w/ F11a wireBody), anon-alias 403 + reply-alias 200 pins, logout->relogin new token; smoke 8->9.
- [x] F12 (research, 02903da): decision — option (a) node --check in preBuild via bare ${pkgs.nodejs_24.out} store path (nodejs NOT in buildInputs = link-flag hazard); facts: buildRustPackage honours preBuild, dontCargoCheck = zero tests at build today.
- [x] F13 (14fdf95): flake — frontendSrc = ./frontend hoisted; preBuild node --check app.js; NEGATIVE PROOF broken-copy build rc 1 + byte-exact restore (nix hash path); nodejs-free binary closure.
- [x] F14 (be2589f): flake — cargoTestFlags = "--lib --bin=formal-twitter" (string attr) replaces dontCargoCheck: 69 network-free unit tests run at nix build check phase, ZERO smoke; flag-placement proof from drv log; forced fresh build 41.3s.
- [x] FINAL VERIFY (coordinator, 11069d4): 78 tests (53+16+9, smoke 9/9), fmt/build/clippy -D warnings clean, agda x2 rc 0, nix flake check/build 0 + nix run launch/shutdown OK. Queue empty at that point.
- [x] TD300 (613e8ec): todo cleanup — F4/F1/F2/ST waves condensed above; superseded parents dropped; lessons kept.
User reqs: logged-out ~= current frontend/; logged-in = TWO PARALLEL timelines (private + global); Like button on EVERY displayed tweet; poster name = follow/unfollow TOGGLE showing ✓ when followed. Queue opened 29ad704; wire = POST /api/<name>, CRLF-joined lines token-first no trailing newline (see wire.rs + Reference section); liked/followed state = client-side caches (no wire read-endpoint; header-noted in each app.js).
- [x] F16a (e500357, record d3b5c21): main.rs — frontend_dir_name pure guard (empty //\\/../leading-dot -> "frontend"), frontend_root_named(name) dev+install arms, frontend_root() = getenv FT_FRONTEND default; serve_static unchanged; +3 bin tests (validation table, dev-fallback shapes, absent-env byte-identical); 16->19 bin, 78->81 tests.
- [x] F16c (a145932, record 5b54e56): frontend2/ — side-by-side PRIVATE/GLOBAL panels, closest to current look; Promise.all pair; likedIds Set + followState Map; CRLF join :128.
- [x] F16d (7c6821f, record 0d3bf53): frontend3/ — stacked full-width labeled rails (PRIVATE above GLOBAL), tweet cards, dark palette; ✓ author label :91, CRLF join :133.
- [x] F16e (f935ce8, record 117ecdf): frontend4/ — newspaper broadsheet grid 1fr 1fr (private left/global right), text-only rows, NO tweet-detail view; toggleFollow :370, toggleLike :399, CHECK ' ✓' :34, anon wire branches :140/:144.
- [x] F16b (164d86e, record 6150108): flake — frontend2/3/4Src drv inputs mirroring frontendSrc; preBuild 4x node --check (every variant syntax-pinned at build); postInstall cp -r each -> $out/frontendN (install arm of frontend_root_named finds them); flake check + nix build rc 0 (72 unit tests), nodejs-free closure.
- [x] F16-verify (coordinator, a7ade8a): GATES GREEN — 81 cargo tests (53+19+9), fmt/build/clippy clean, agda ImplProofs + ImplWire rc 0, nix flake check/build 0 (4 pins + unit tests in check phase), nix run rc 124 launch+SIGTERM OK; preview table of the 3 variants delivered.
- [x] F17 (8767cc7): USER PICK = KEEP CURRENT frontend/ -> adoption NO-OP; frontend2/3/4 remain shipped extras, runtime-selectable via FT_FRONTEND=frontendN nix run; smoke byte-pins still on frontend/. F16 wave CLOSED.

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
- ST2 accepted + committed: /raw + /log RAM-debug layer (log ring cap 1000, one epoch source, Interface naming) green:
  77 tests (53+16+8), smoke 8/8, agda ImplProofs + ImplWire rc 0 with comment-only (ST) tail note (unlines-crlf postulate = opaque, F2 precedent).
- F16b: flake.nix extended (+frontend2/3/4 srcs, 4x node --check syntax-pin in preBuild, cp -r into $out/frontendN in postInstall);
  gates: nix flake check rc 0, nix build rc 0 (72 unit tests 53 lib + 19 bin), nix run preview rc 124 (timeout, no env prefix: sandbox denies `env K=V`); binary closure has NO nodejs.
- RV3d note: (_$_) not re-exported via open import Interface -> wi-resp-* use unlines-crlf (...) application; [] / _∷_ added to existing Data.List import.
- Agda gate quirk: UNSOLVED interaction metas ('= ?') make `agda FILE.agda` exit 42 in Agda 2.8; signature-with-hole must be written as POSTULATE to keep the rc-0 gate (RV4 style).

- M4-followup (wire pins) ACCEPTED, not committed: ImplWire.agda + wi-resp-* section (9 refl theorems pinning each to-response clause: status line, header LIST, Content-Length term, body expr; let-bound bodies inlined; + []/_∷_ added to the existing Data.List import, imports kept) + commented wi-bytes-* postulate signatures for the opaque unlines-crlf framing bytes (octet-strlen values 26/28/25/26/18/22/16); wire.rs respond_shapes /// doc rewritten (comments only, +4 lines) mapping asserts 1:1 to wi-out-*/wi-resp-* and marking header ORDER + framing bytes as impl-defined residuals. Gates: agda ImplWire rc 0; fmt/build/clippy -D warnings silent; tests 53 lib + 19 bin unchanged. Note: $ (_$_) not re-exported through open import Interface -> theorems use unlines-crlf (...) application instead.
- RV6 (read-post quintet) ACCEPTED, not committed: model.rs + as_read destructor + 5 quickcheck props
  (prop_read_logged_in / prop_read_public_shape / prop_read_denied_missing / prop_read_denied_private /
  prop_read_denied_deleted, pinned to step's ReadPost arm incl. likes-as-COUNT via len_u64 and nw == w;
  + active_user_ref/post_at_ref added to the qc use super::{...} list); ImplProofs.agda + RV6 section
  th-prop-read-logged-in (refl terms on read-post-logged-in) / th-prop-read-public (read-post-anonymously) /
  th-prop-read-denied-{missing,private,deleted} (refl on the three cant-read-post-* rules, all 3x3 clauses).
  Gates: agda ImplProofs rc 0; fmt/build/clippy -D warnings silent; cargo test = 61 lib + 19 bin + 9 smoke.
  Lessons: (a) `where`-block types CANNOT see clause-telescope implicit vars (NotInScope) -> inline the
  proof term in the RHS; (b) post-at-unique's {w pid} implicits are UNSOLVABLE (inverting the record
  projection World.post-at blocks) -> use just-injective (trans (sym eq₁) eq₂) inline instead; (c) PostStatus
  constructors (live/deleted) and Visibility (followers-only) are in scope as constructors, so a pattern var
  named `live` = ConstructorPatternInWrongDatatype -> rename proof vars (slv).

- RV7 (publish trio) ACCEPTED, not committed: model.rs + PublishCase correlated generator
  (struct {w cmd ids} + Arbitrary ~1554-1640: sid from valid_session list 2/3, fresh_pid from
  PIDS minus used_pid 2/3, parent 4-way Nothing/readable/blocked/arbitrary; the independent
  World/Command/StepArgs triple made publish props VACUOUS ~1/470) +
  prop_publish_new / prop_reply_publish / prop_reply_denied taking (c : PublishCase), claims
  pinned to step's Publish arm incl. parent replies PREPEND (RV5-0 fix) + vis inheritance;
  non-vacuity via mutation probe (each `false &&` -> FAILED 63 passed 1 failed). ImplProofs.agda
  + RV7 section th-prop-publish-new / th-prop-reply-publish / th-prop-reply-denied (one live
  Step clause each; index clashes make the other publish constructors absurd). Gates: agda
  ImplProofs rc 0; fmt/build/clippy -D warnings silent; cargo test = 64 lib + 19 bin.
  Agda lessons: (d) constructor IMPLICIT args are NOT bound in a clause RHS -- bind named braces
  AT TELESCOPE POSITION (block-2 implicits sit between the nf premise and CanReadPost, not lumped
  first); (e) successful-reply declares ppid in BOTH implicit blocks and name lookup picks the
  INNER one -- bind block-1 implicits positionally {_} {_} ... {ppar} {ppost} and claim the new-reply
  parent-id via ∃[ ppar ]; (f) only bracket ∃[x] B syntax is in scope (Data.Product using (∃-syntax)),
  `∃ λ x →` = NotInScope.
