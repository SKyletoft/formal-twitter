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
- [ ] Review the changes brought in by the merge
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
- [ ] Task T3 (subagent impl): network integration tests — launch server, raw-TCP HTTP/1.1
      client (stdlib only) speaking the NEW spec protocol, exercise all endpoints incl. error paths.
- [x] Task T1 (subagent impl): pure model module (ACCEPTED: build+clippy -D warnings+fmt+10 QC tests green; ImplProofs.agda = 10 theorems, agda exit 0) (backend/src lib: model.rs mirroring Twitter.agda
      World/Step/Result) + QuickCheck tests + matching theorems in ImplProofs.agda; agda typecheck.
- [ ] Task T2 (subagent impl): diesel/sqlite storage + rocket routes + reentrant startup +
      crypto-random Nat ids + NEW wire protocol (POST, exact Content-Length/Date/Cache-Control,
      JSON responses, escape) — must pass build/clippy -D warnings/fmt.
- [ ] Task T5 (subagent impl): flake.nix — cargo vendor committed; add libsqlite3-sys bundled
      dep; rustPlatform buildRustPackage hermetic (vendorDir + cargoLock); verify `nix run` starts server.
- [ ] Task T4 (subagent impl): frontend-conformant GET aliases (/api/get-tweet?token=&id=,
      /api/global-timeline?token=&len=, /api/private-timeline?...) + tolerate LF/trailing-newline
      POST bodies from the browser; both formats route to the same Action.
- [ ] Final verify: cargo build/test, clippy clean, cargo fmt, agda typecheck, nix run; commit each accepted task.

## Progress log (as of restart)
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
