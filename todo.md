# todo.md — formal-twitter backend

## Conventions
- Main branch: `maki-loop-3` (this worktree).
- Each task gets its own git worktree: `/home/u3836/git/formal-twitter.git/wt-<id>` with branch `task/<id>`.
  (Older worktrees under `~/git/ft-wt-*` were relocated; do not create worktrees outside `formal-twitter.git`.)
- All commit messages must include the trailer:
  `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`
- Commands run inside `nix develop --command ...`.
- Spec files readable: ONLY `spec/Twitter.agda` and `spec/Interface.agda`.

## Done
- [x] Environment/permissions unblocked (worktree + merge).
- [x] Baseline `cargo check` passes (hello world, rocket+diesel resolved).

## In progress
- [ ] T3a: follow/unfollow/like/unlike. Tests+proofs subagent running in
  `/home/u3836/git/formal-twitter.git/wt-t3a` (branch `task/t3a-engine-social`, from merge db56bde).
- [ ] T3 plan: ACCEPTED (split T3a social/`can_read_post`, T3b timelines).
- [ ] T4 plan: ACCEPTED with amendments (see "T4 plan"). Blocked on T2+T3 engine.

## T2b plan (accepted)
- Engine API: `engine::posts::{publish(db,sid,text,Option<PostId>), delete(db,sid,pid), read_post(db,Option<SessionId>,pid)}`.
- Expired first for token commands; publish-no-parent always succeeds after session check;
  reply denied iff `¬ CanReadPost`; reply visibility = account default unless parent is
  `followers-only` then `followers-only`; delete denied if absent or not author, but deleting an
  already-deleted own post succeeds; read logged-in denied if absent/deleted/private-unfollowed;
  anonymous read: public+live -> returned-post; otherwise `expired` (`failed-access` applies
  vacuously because `extract-sid (read-post nothing _) ≡ nothing`; no spec fix needed).
- `newest-first` and reply lists include deleted posts; replies newest-first (`seq DESC`).
- New store helpers: `can_read_post`, `can_read_anonymous`, `post_view` (post+likes+replies),
  `delete_own` (load-check-delete in one transaction).
- Proofs: arbitrary-world builders `posted-world` / `reply-world` via `set-post`; positive
  `post-is-public`/`post-is-private` witnesses and negative `¬CanReadPost` lemmas for
  absent/deleted/private-unfollowed.

## State as of 2026-11-26
- `maki-loop-3` HEAD db56bde: T5 merged (28b5937), T2a merged (3988336), T2b merged (db56bde).
- `wt-t3a` at db56bde, branch `task/t3a-engine-social` (T3a tests+proofs in progress).
- `wt-t2b` removed after merge (branch `task/t2b-engine-posts` retained).


## Done (cont.)
- [x] T1: DB schema + persistence layer. Merged into `maki-loop-3` (merge 099f531, impl 3c12bd0). Review accepted.
- [x] T2 plan: accepted.
- [x] T3 plan: accepted.
- [x] T4 plan: accepted with corrections: signup success = 200 EMPTY body (`ok`), follow/unfollow unknown user = 200 success (no failure step).

## Decisions log
- Do NOT edit `spec/`. Implement defined behavior exactly.
- Token-less commands `register`/`login` return their constructor results (signup/login failure),
  never `expired`. Anonymous `read-post`: `returned-post` when public+live, else `expired` (the only
  derivable `Result`; `failed-access` is vacuous for `extract-sid = nothing`).
- Anonymous unreadable `get-tweet` -> `expired` / 401 `session_expired`, NOT 403; proved by
  `read-anonymous-expired` (`failed-access`).
- T1 has NO quickcheck properties / Agda proofs: it only stores data; no `Step`/spec transition exists at this layer. Unit tests only. (Adding list lemmas would violate "useless proofs" rule.)
- Commit trailer on every commit: `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.
- T4 hint: `flake.nix` `prePatch` copies `frontend/` to the *parent* of the unpacked backend source, so `include_dir!("$CARGO_MANIFEST_DIR/../frontend")` (or rust-embed) is the intended way to embed static assets for `nix run`; serve them from Rocket without depending on cwd.

## Backlog (ordered)
- [x] T2a: engine auth. Merged 3988336 (impl a15d5ac, test fixes 451d52f/704327b, proofs+wiring 9780d3e).
- [x] T2b: post lifecycle. Merged db56bde (tests/proofs 60fa369/6cff937, impl 31578c7).
- [ ] T3a: social (follow/unfollow/like/unlike) + proofs. IN PROGRESS.
- [ ] T3b: `engine/timeline.rs` (personal/private-global/anonymous-global) + P7-P9.
- [ ] T3-impl + review.
- [ ] T4a: parse+respond+routes+server+main (Rocket).
- [ ] T4b: embedded assets (3-file allowlist) + flake.
- [ ] T4c: integration tests.
- [ ] T5: merged 28b5937.
- [ ] T6: Benchmarks + performance hardening.

## Assumptions (recorded)
- T2 was split into T2a (auth, the current uncommitted work) and T2b (post lifecycle); the
  existing `tests/engine_auth.rs` covers only T2a, so T2b is treated as a separate task.
- Worktrees are recreated inside `formal-twitter.git/wt-*`; the stale `ft-wt-*` directories were
  removed (T1 was already merged, T5 was clean).
- Bash/file permissions are restrictive: `rm` is denied for everyone and writes are limited to the
  coordinator's own files. Do not plan tasks that require deleting tracked files; make them
  unreachable instead. Recorded for `frontend/prompt`.
- Proof strategy (from T2a review): state each engine theorem over an arbitrary `World` and
  exhibit the updated world via builders (`registered-world`, `logged-in-world`,
  `logged-out-world`) that re-discharge all `World` invariants. Reuse this for T2b/T3 post,
  follow and like worlds; do not use single-account/single-session toy worlds.
- T3: `store::newest_first(n)` applies `LIMIT` before visibility filtering; never use it to
  build a timeline (spec filters then takes). Use the dedicated timeline queries.
- T2b/T3: `newest-first` and reply lists include deleted posts; reply lists are newest-first.
- Commit trailer on every commit: `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.

## T4 plan (accepted, amendments)
- `server.rs` (manage `Db`, mount), `api/{parse,response,routes}.rs`, `assets.rs`, new `main.rs`.
- DB URL: `FORMAL_TWITTER_DB` else `DATABASE_URL` else `formal-twitter.db`; migrations on start.
- All routes POST `/api/<name>`, body `text/plain`, CRLF lines with exactly one trailing CRLF;
  optional-token forms disambiguated by line count; malformed -> 400 `{"error":"bad_request"}`.
- Exact `to-response` bytes: `ok` = 200 EMPTY body (no content-type/cache-control); timeline /
  session-token / tweet = `Cache-Control: no-store`; JSON field order exactly as Interface.agda;
  `Content-Length` = UTF-8 byte length; `Date` added by a response fairing; JSON-escape
  username/text via `serde_json`; ids equal `show` (plain decimals).
- Deviations chosen: malformed requests = 400 `bad_request` (unspecified); unreadable anonymous
  read = 401 `session_expired` (derivable `expired`, not 403).
- **AMENDED static serving:** because `frontend/prompt` cannot be deleted, do NOT use a generic
  file route. Serve ONLY `index.html` (`/` and `/index.html`), `/app.js`, `/style.css`; everything
  else 404. Embed with `include_dir!("$CARGO_MANIFEST_DIR/../frontend")`.
- `flake.nix`: keep `prePatch` frontend copy; remove `postInstall`; add `meta.mainProgram`.
- Cargo: `include_dir`, `httpdate`, `serde_json`; dev `tempfile`.
- No Agda proofs for T4: every `Interface.agda` helper (`unlines-crlf`, `show`, `escape`,
  `octet-strlen`, `date`, `host`) is a postulate, so only functional/integration tests are meaningful.
- Split: T4a (parse+respond+routes+server+main), T4b (assets+flake), T4c (integration tests).

## Spec gaps / open decisions
- Anonymous `read-post` of absent/private/deleted: `failed-access` applies vacuously
  (`extract-sid (read-post nothing _) ≡ nothing`), so `expired` is derivable and is the chosen
  answer. `read-post-anonymously` covers public+live. No spec fix needed.
- `time-passes` / session timeout is not exposed by Interface (no endpoint); sessions only become invalid via logout.
- Accounts are always created with `default-visibility = everyone`, so `followers-only` is unreachable via API; still implement faithfully.
