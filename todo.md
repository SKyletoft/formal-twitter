# todo.md — formal-twitter

## Tasks
- [x] T7: Send a `time-passes` event every couple of minutes. Merged `8d83761`.
- [ ] T8a: Frontend redesign — layout, two timeline tabs (global/followed), tweet cards,
  tweet detail with replies.
- [ ] T8b: Frontend actions — like/unlike, follow/unfollow, reply composer; depends on T8a.
- [ ] C1: Cache commonly read public data (in-memory only; invalidate on every write; the DB stays
  the source of truth before serving).
- [ ] Q1: Redo all quickcheck properties: no new database inside a property; properties take a
  valid AND shrinkable generated world state.
- [ ] B1: Database query batching without destroying worst-case latency.

## In progress
- [x] T7: DONE/merged `8d83761` (tests/proofs `bceac91`, impl `3f818e9`). 132 tests; timer smoke ok.
- [ ] T8a: implementation `fbc3220` reviewed; blocking JSON-id precision defect (ids > 2^53).
  Root-cause fix running: allocate PostId/SessionId in `1..=2^53-1`, frontend safe-integer guards,
  regression tests. Worktree `wt-t8a`.
- [ ] T8b: blocked on T8a.
- [ ] C1/Q1/B1: queued; plan after T8b.

## State
- Branch `maki-loop-3`, HEAD `8d83761`. Merged: T1, T2a, T2b, T3a, T3b, T4, T5, T6, T7.

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
