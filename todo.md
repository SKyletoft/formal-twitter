# todo.md — formal-twitter

## Tasks
- [x] T7: Send a `time-passes` event every couple of minutes. Merged `8d83761`.
- [x] T8a: Frontend redesign — layout, two timeline tabs, tweet cards, detail with replies.
  Merged `0dad6e1`.
- [x] T8b: Frontend actions — like/unlike, follow/unfollow, post/reply/delete. Merged `eec038b`.
- [ ] C1: Cache commonly read public data. (C1a public tweet cache merged `c91d9d6`; C1b timeline
  caches pending.)
- [ ] Q1: Redo all quickcheck properties: no new database inside a property; properties take a
  valid AND shrinkable generated world state. (Q1a infra+time `48514db`; Q1b auth/social `4a9f6af`,
  posts/timeline `d938c35`; Q1c cleanup pending.)
- [ ] B1: Database query batching without destroying worst-case latency.

## In progress
- [x] T8a: DONE/merged `0dad6e1` (`fbc3220` + JSON-safe-id fix `c9e0aca`). Post-merge gate: 136
  tests, Agda, lint, `nix build`, HTTP + timer smokes all green.
- [x] T8b: DONE/merged `eec038b` (`4405ef3` + CSS/UX fix `53c2a6d`). 136 tests, DOM stub 73/73,
  live smoke 44/44.
- [x] Q1a: DONE/merged `48514db` (`057c42c` + reply-order fix `e57d2ac`). WorldState/Arbitrary/
  shrink/materialiser + `engine_time` pilot; 137 tests; 0 discards.
- [x] C1a: DONE/merged `c91d9d6` (`4b1b4a9` + strengthened test `e5c2857`). Warm anon get-tweet
  46 ns; render burst 3.4×; dead-cache/invalidation mutations now fail the property.
- [x] Q1b: DONE/merged — auth+social `4a9f6af`, posts+timeline `d938c35`. All engine suites now
  use one `Db` per `#[test]`, reset+materialise a generated valid `WorldState` per case.
- [ ] Q1-harness: `support::WorldProperty::result` panic containment + real shrinking fix running
  in `wt-harness` (review found panics escaped quickcheck, so failures never shrank).
- [ ] B1/T6e: implementation `e8b3caa` (get-tweet 4→3/3→2, reply 5→3, like 3→2, bound LIMIT);
  review running in `wt-b1`.
- [ ] C1b: timeline id caches; after B1.
- [ ] Q1c: cleanup (dead helpers, duplicate tests, docs) after harness+B1 merge.

## State
- Branch `maki-loop-3`, HEAD `d938c35`. Merged: T1, T2a, T2b, T3a, T3b, T4, T5, T6, T7, T8a, T8b, Q1a, Q1b, C1a.
- 155 tests green; `agda --safe` clean; `nix build` (checks) + `nix run` smoke green; T7 timer verified.

## Working rules (from AGENTS.md)
- Run commands inside `nix develop --command ...`.
- Each task gets a worktree `/home/u3836/git/formal-twitter.git/wt-<id>`, branch `task/<id>`.
- Read ONLY `spec/Twitter.agda` and `spec/Interface.agda` inside `spec/`.
- Commits end with `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.
- Tests: quickcheck properties with a matching theorem in `backend/ImplProofs.agda`; no
  postulates/holes. T1/store-layer (no spec `Step`) and T4 wire layer (Interface helpers are
  postulates) are unit/integration-tested only.
- Sandbox: `rm` is denied unless it involves scratch files; never plan a task requiring deletion of tracked files.

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
