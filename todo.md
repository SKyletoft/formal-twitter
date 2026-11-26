# todo.md — formal-twitter backend (final)

## Conventions
- Main branch: `maki-loop-3` (this worktree). Task worktrees live under
  `/home/u3836/git/formal-twitter.git/wt-*` with branch `task/<id>`.
- Commands run inside `nix develop --command ...`.
- Spec files readable: ONLY `spec/Twitter.agda` and `spec/Interface.agda`.
- Every commit carries:
  `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`

## Final state (2026-11-26)
- `maki-loop-3` HEAD `68674ff` (Merge T6c). All planned tasks complete; spec unchanged.
- Tests: **120 passed, 0 failed** (engine_auth 15, engine_posts 21, engine_social 17,
  engine_timeline 18, http_api 10, http_static 2, persistence 22, store_posts 15).
- Agda: `ImplProofs.agda` typechecks with `--safe`; **no postulates, no holes**.
- Lint/format: `cargo clippy --tests -- -D warnings` clean; `cargo fmt --check` clean.
- `nix build .#default` succeeds with `doCheck` enabled (the build runs the full test suite) and
  produces `result/bin/formal-twitter`; `nix run` smoke verified end-to-end.
- Benchmark (release; 2k accounts / 20k posts / 100k likes):
  writes 13–43 µs; get-tweet 32 µs (auth) / 25 µs (anon); personal timeline 77 µs / 243 µs /
  1.49 ms at 1k / 20k / 100k; HTTP signup 6.5 µs, post-tweet 22 µs, get-tweet 37 µs.

## Completed tasks
- [x] T1: DB schema + persistence layer. Merged `099f531` (impl `3c12bd0`).
- [x] T5: static frontend speaking the Interface API. Merged `28b5937`.
- [x] T2a: engine auth (`register`, `authenticate`, `revoke-token`, `failed-access`). Merged `3988336`.
- [x] T2b: post lifecycle (`publish`/reply, `delete`, `read-post`). Merged `db56bde`.
- [x] T3a: social (`follow`/`unfollow`, `like`/`unlike`). Merged `6a28a0d`.
- [x] T3b: timelines (personal, private global, anonymous global). Merged `b00d15e`.
- [x] T4: Rocket HTTP interface, exact `to-response` bytes, embedded assets, `nix run`.
  Merged `f4d17b5` (tests `666b348`/`c8a256b`/`13ccdf6`, impl `2497f7e`, hardening `f451d17`).
- [x] T6: benchmark harness (`4468155`, merged `81ceeba`); T6a/d/g perf (`2faa731`, merged `e4cf748`);
  T6c timeline rewrite (`3fc6aa3`, merged `68674ff`).
- [x] Spec-change audit: CLEAN — neither spec file changed during implementation, and every
  Command/Action/Result/Step is covered.

## Architecture
- `backend/src/{db,model,schema,store,ids}.rs`; `engine/{auth,posts,social,timeline,result,mod}.rs`;
  `api/{parse,response,routes}.rs`; `server.rs`; `assets.rs`; `main.rs`.
- Diesel + sqlite (WAL, `synchronous=NORMAL`, `foreign_keys`, `busy_timeout`); one connection behind
  a `Mutex`; every command is ONE transaction; embedded migrations run on open; production DB from
  `FORMAL_TWITTER_DB`, else `DATABASE_URL`, else `formal-twitter.db`.
- Rocket 0.5: 13 POST routes under `/api`, `text/plain` CRLF bodies, exact `to-response` bytes,
  `Date` fairing, no `Server` header, critical-only logging, 16 MiB string limit. Static serving is
  an explicit allowlist (`index.html`, `app.js`, `style.css`); everything else 404.
- Assets embedded with `include_bytes!`; flake keeps `prePatch` (frontend copy), removes
  `postInstall`, sets `meta.mainProgram`.
- Agda proofs: each engine theorem is stated over an **arbitrary `World`** and exhibits the updated
  world via invariant-preserving builders. Timeline proofs bridge the spec's
  `take`/`filter`/`filterᵇ` composition to the SQL characterization (decision soundness/completeness
  + filter-fusion lemmas), so tests and theorems check the same list.

## Key decisions
- The spec is the source of truth; `spec/` was never edited.
- `Expired` (`failed-access`) takes precedence for every session-carrying command.
- Anonymous `read-post`: `returned-post` for public+live; otherwise `expired` — `failed-access`
  applies vacuously because `extract-sid (read-post nothing _) ≡ nothing`. Not `403`.
- Tokenless `register`/`login` return their constructor results (`signup-failed`/`login-failed`),
  never `expired`.
- Deleting an already-deleted own post succeeds (`delete-post` has no `live` premise).
- Reply visibility: parent `everyone` -> account default; parent `followers-only` -> `followers-only`.
- Personal timeline = live posts by followed authors, newest-first, `take n`; own posts require
  self-follow. Private global = live ∧ (public ∨ followed). Anonymous global = live ∧ public.
- `newest-first` and reply lists include deleted posts; replies are newest-first (`seq DESC`).
- T1 and store helpers have unit tests only (no spec `Step` at that layer); T4 has integration
  tests only (all `Interface.agda` wire helpers are postulates).
- HTTP choices: leading-zero numerals accepted (`"007"` = 7); ids > `i64::MAX` -> 400; timeline
  length parsed as `u64` and clamped to `u32::MAX` (>u64 -> 400); malformed -> 400 `bad_request`;
  non-UTF-8 / over-16-MiB bodies get Rocket's default 400 (unspecified).
- `frontend/prompt` could not be deleted (sandbox denies `rm`); it is never served and no longer
  embedded in the binary.

## Spec notes / limitations
- `time-passes` / `session-timeout` is not exposed by `Interface.agda` (no endpoint); sessions only
  become invalid via logout.
- Accounts are always created with `default-visibility = everyone` (`create-account`), so
  `followers-only` is unreachable via the API; the rule is still implemented faithfully.
- DB errors answer 500 `{"error":"internal"}` (no spec `Response`).
- `collect-dead-posts` is commented out in the spec.
- `store::revoke_all_sessions` is unused (kept as a public helper).

## Deferred performance work
- T6b: read connection pool (r2d2). Risky for `:memory:` tests (would need shared-cache);
  single connection measured sufficient for this workload.
- T6e: coalesce `read_post`'s `can_read_post` + `post_view` into one statement.
- T6f: reduce body-path allocations (`Vec<String>`/join in `show-tweets`, manual `Content-Length`).
- T6h: partial index `posts(seq DESC) WHERE status='live'`.
- Personal timeline at 100k is 1.49 ms (density-dependent, not `n`-dependent); a recursive
  per-followee top-n CTE could reduce it further.

## Assumptions
- Worktrees live under `formal-twitter.git/wt-*`; stale `~/git/ft-wt-*` were removed.
- The sandbox denies `rm` for everyone and restricts writes; tasks must avoid deleting tracked
  files (make them unreachable instead). This is why `frontend/prompt` remains.
- Bash builds/tests run through `nix develop --command ...`; long builds are delegated.
