# todo.md — formal-twitter

## Tasks
- [x] T7: Send a `time-passes` event every couple of minutes. Merged `8d83761`.
- [x] T8a: Frontend redesign — layout, two timeline tabs, tweet cards, detail with replies.
  Merged `0dad6e1`.
- [ ] T8b: Frontend actions — like/unlike, follow/unfollow, post/reply/delete. In progress.
- [ ] C1: Cache commonly read public data (in-memory; total invalidation on every write; DB stays
  the source of truth before serving).
- [ ] Q1: Redo all quickcheck properties: no new database inside a property; properties take a
  valid AND shrinkable generated world state.
- [ ] B1: Database query batching without destroying worst-case latency.

## In progress
- [x] T8a: DONE/merged `0dad6e1` (`fbc3220` + JSON-safe-id fix `c9e0aca`). Post-merge gate: 136
  tests, Agda, lint, `nix build`, HTTP + timer smokes all green.
- [ ] T8b: implementation running in `wt-t8b` (branch `task/t8b-frontend-actions`).
- [ ] C1a: plan ACCEPTED. Public-data cache in `Db` (public tweet views + anonymous global timeline),
  total invalidation at the end of every `Db::write`, cache-vs-DB property tests, no new Agda proof
  (the cache introduces no spec `Step`). NEXT after T8b.
- [ ] B1/T6e: query fusion (`read_post`, reply `publish`, bound `LIMIT`); after C1a.
- [ ] C1b: timeline id caches; after B1.
- [ ] Q1a/Q1b/Q1c: `WorldState` generator/shrinker/materialiser + pilot, then migrate all engine
  suites. One `Db` per `#[test]`, reset per case; no DB construction inside properties. Q1a can run
  in parallel with C1a (src vs tests); Q1b after.

## State
- Branch `maki-loop-3`, HEAD `0dad6e1`. Merged: T1, T2a, T2b, T3a, T3b, T4, T5, T6, T7, T8a.
- 136 tests green; `agda --safe` clean; `nix build` (checks) + `nix run` smoke green; T7 timer verified.

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
