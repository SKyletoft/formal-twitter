# todo.md — formal-twitter

## Tasks
- [ ] T7: Send a `time-passes` event every couple of minutes.
  - Engine `time_passes` (revoke all active sessions) + Agda `session-timeout` proof + quickcheck.
  - Background timer in `main` only (env-configurable, default ~120 s) so tests and in-process
    `server::build` never revoke sessions mid-test.
- [ ] T8a: Frontend redesign — layout, two timeline tabs (global/followed), tweet cards,
  tweet detail with replies.
- [ ] T8b: Frontend actions — like/unlike, follow/unfollow, reply composer; depends on T8a.

## In progress
- [ ] T7: plan ACCEPTED. Tests+proofs running in `wt-t7` (branch `task/t7-time-passes`).
  Key plan: `engine::time::time_passes` = one write calling `store::revoke_all_sessions`; proof
  `time-passes-success` over `timed-out-world`; timer spawned ONLY in `main` (env
  `FORMAL_TWITTER_TIME_PASSES_SECS`, default 120, 0 disables; `Db` becomes cloneable via
  `Arc<Mutex<_>>`); quickcheck active/revoked/unused + idempotence.
- [ ] T8a: plan ACCEPTED. Implementation+tests running in `wt-t8a` (branch
  `task/t8a-frontend-browse`). Hash-routed single-column SPA; tabs Global/Following; timeline ids +
  bounded `get-tweet` fan-out (20, mapLimit 6); cards; tweet detail with replies; keep 3 frontend
  files; add nodejs to the devShell for `node --check`; extend `http_static` string assertions.
- [ ] T8b: blocked on T8a (like/unlike, follow/unfollow, reply/post/delete, 401/403 UX).

## State
- Branch `maki-loop-3`, HEAD `ee8176c`. All earlier tasks merged: T1 persistence, T2a auth,
  T2b posts, T3a social, T3b timelines, T4 HTTP/static/`nix run`, T5 frontend, T6 benchmarks+perf.

## Working rules (from AGENTS.md)
- Run commands inside `nix develop --command ...`.
- Each task gets a worktree `/home/u3836/git/formal-twitter.git/wt-<id>`, branch `task/<id>`.
- Read ONLY `spec/Twitter.agda` and `spec/Interface.agda` inside `spec/`.
- Commits end with `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.
- Tests: quickcheck properties with a matching theorem in `backend/ImplProofs.agda`; no
  postulates/holes. T1/store-layer (no spec `Step`) and T4 wire layer (Interface helpers are
  postulates) are unit/integration-tested only.
- Sandbox: `rm` is denied; never plan a task requiring deletion of tracked files.

## Gotchas / decisions
- Spec is the source of truth; never edit `spec/`.
- `Expired` (`failed-access`) takes precedence for every session-carrying command.
- Anonymous unreadable `read-post` -> `expired` (vacuous `failed-access`), NOT 403.
- Reply visibility: parent `everyone` -> account default; `followers-only` -> `followers-only`.
- Deleting an already-deleted own post succeeds.
- Personal timeline = live posts by followed authors (self-follow to include own); private global =
  live ∧ (public ∨ followed); anonymous global = live ∧ public.
- `newest-first` and reply lists include deleted posts; replies are newest-first.
- HTTP: malformed -> 400 `bad_request`; leading zeros accepted; ids > `i64::MAX` -> 400; timeline
  length is `u64` clamped to `u32::MAX`; JSON escaping via `serde_json`; static allowlist only
  (`index.html`,`app.js`,`style.css`); `frontend/prompt` must stay unreachable.
- DB: WAL + `synchronous=NORMAL`; one connection behind a Mutex; one transaction per command;
  `FORMAL_TWITTER_DB` / `DATABASE_URL` / `formal-twitter.db`.
- Perf: `store::personal_timeline_for` uses the per-author top-n window query.

## Limitations / deferred
- `time-passes` / session timeout: no Interface endpoint.
- `followers-only` default is unreachable (register always creates `everyone`).
- DB errors -> 500 `{"error":"internal"}`; `collect-dead-posts` is commented out in the spec;
  `store::revoke_all_sessions` is unused.
- Deferred perf: T6b read connection pool, T6e read_post query fusion, T6f body allocations,
  T6h partial index, personal timeline at 100k posts (1.49 ms).
