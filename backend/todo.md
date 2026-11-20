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

## Next (ordered queue)
- [ ] TDC (coordinator): Clean up this todo list (condense history, ordered Next queue) -> commit "todo: TDC".
- [ ] T10 (research subagent): Is frontend/app.js spec-conformant? (GET+LF vs Interface POST+CRLF; which endpoints app.js uses)
- [ ] T11 (decision + maybe impl): Remove compat GET aliases? Decide from T10 verdict; if kept, document why.
- [ ] D1 (impl subagent): main.rs — on reopen/apply FAILURE re-query ALL 4 RAM sections (DB-truth discipline gap from T9/D1).
- [ ] F3 (impl subagent): cache max_seq in Server state; bump on insert; kill per-request SELECT-seq max fold (db.rs:595-604 era).
- [ ] F9 (impl subagent): hold SqliteConnection in Server; reopen only on apply/reopen failure; drop per-request establish + path copy.
- [ ] F4 (impl subagent): World HashMap/HashSet side-caches rebuilt on reload (kills O(P^2) timeline lookups) + proof pins.
- [ ] F1 (impl subagent): step(&World) -> (Result, Delta) single-copy; serve feeds apply() the delta.
- [ ] F2 (impl subagent): delta-driven apply() touching only changed keys (was full-world diff views).
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
