# todo.md — formal-twitter

## Tasks
<!-- Add new tasks here as `- [ ] ...`. -->
- [ ] T9: perf-driven optimization run — profile engine hot paths and a loaded server with
  `perf`, then fix the top hotspots.

## In progress
- [ ] T9-profile: symbolized bench scenarios + `perf record`/flamegraphs on personal-tl-100k,
  get-tweet cold/warm, publish, and a `wrk`-loaded server; hotspot report in `wt-t9`.

## Completed (latest cycle)
- [x] T7: `time-passes` engine command (`session-timeout` proof) + background timer in `main`
  (`FORMAL_TWITTER_TIME_PASSES_SECS`, default 120, `0` disables). Merged `8d83761`.
- [x] T8a/T8b: Twitter-like static frontend (hash-routed tabs, timeline cards, tweet detail/replies,
  post/reply/like/unlike/follow/unfollow/delete, safe-integer ids). Merged `0dad6e1`/`eec038b`.
- [x] C1a/C1b: in-memory public read cache (tweet bodies + timeline id lists), total invalidation on
  every committed write, generation-checked. Merged `c91d9d6`/`c5b4447`.
- [x] B1/T6e: query fusion (get-tweet 4→3 / 3→2, reply publish 5→3, like 3→2, bound `LIMIT`).
  Merged `1e69ed4`.
- [x] Q1a/Q1b/Q1-harness/Q1c: world-state-driven quickcheck (one `Db` per `#[test]`, generated valid
  + shrinkable `WorldState`, reset+materialise per case, no DB construction inside properties,
  panic-contained shrinking). Merged `48514db`/`4a9f6af`/`d938c35`/`946d164`/`ebf729b`.
- [x] Earlier: T1 persistence, T2a auth, T2b posts, T3a social, T3b timelines, T4 HTTP/static/`nix run`,
  T5 frontend, T6 benchmark harness + `synchronous=NORMAL`/fused account/lookups/thin LTO/top-n
  timeline.

## Final state (2026-11-27)
- Branch `maki-loop-3`, HEAD `ebf729b` (+ this todo commit).
- **216 tests**, 0 failed (lib 14, main 5, cache 10, engine_auth 19, engine_posts 27,
  engine_social 29, engine_time 13, engine_timeline 22, http_api 11, http_static 2, persistence 26,
  store_posts 28, timeline_cache 10).
- `agda --safe ImplProofs.agda` clean (no postulates/holes); `clippy --tests -D warnings` and
  `fmt --check` clean; `node --check` clean.
- `nix build .#default` runs the full test suite in checkPhase; `nix run` smoke: 95/95 checks
  (all 13 endpoints, static assets, `/prompt` 404, no `Server:` header, JSON-safe ids); timer
  expiry (`=1`) and disabled (`=0`) verified.
- Spec unchanged; audit CLEAN (all Commands/Actions/Results/Steps covered).
- Benchmarks (release): writes 13–47 µs; get-tweet cold 23–31 µs / warm 6.2 µs (anon 52 ns);
  personal timeline cold 237 µs at 20k (1.49 ms at 100k), warm 6.3 µs; anon global warm 24 ns;
  render burst 1+20 449 µs cold → 132 µs warm; HTTP 3–28 µs.

## Working rules (from AGENTS.md)
- Run commands inside `nix develop --command ...`.
- Each task gets a worktree `/home/u3836/git/formal-twitter.git/wt-<id>`, branch `task/<id>`.
- Read ONLY `spec/Twitter.agda` and `spec/Interface.agda` inside `spec/`.
- Commits end with `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.
- Tests: quickcheck properties with matching theorems in `backend/ImplProofs.agda`; no
  postulates/holes. Layer tests with no spec `Step` (T1/store, cache, HTTP wire, frontend) are
  unit/integration-tested only, with cache-vs-DB equivalence properties where relevant.
- Verification policy: one full `cargo test` run, with an elevated `QUICKCHECK_TESTS` (e.g. 1000)
  rather than repeating the whole suite; re-run only a specific target when debugging a flake.
- Sandbox: `rm` is denied; avoid tasks that require deleting tracked files.

## Gotchas / decisions
- Spec is the source of truth; never edit `spec/`.
- `Expired` (`failed-access`) precedes everything for session-carrying commands; anonymous
  unreadable `read-post` is `Expired` (vacuous `failed-access`), NOT 403.
- Reply visibility: parent `everyone` → account default; `followers-only` → `followers-only`.
  Deleting an already-deleted own post succeeds.
- Personal timeline = live ∧ followed(author) (self-follow for own); private global = live ∧
  (public ∨ followed); anonymous global = live ∧ public; `newest-first`/replies include deleted
  posts and are seq-desc (replies newest-first).
- Ids are `i64` but allocated in `1..=2^53−1` so bare JSON ids are safe for JavaScript.
- HTTP: malformed → 400 `bad_request`; leading zeros accepted; timeline length `u64` clamped to
  `u32::MAX`; JSON escaping via `serde_json`; static allowlist only (`index.html`,`app.js`,
  `style.css`); `frontend/prompt` never served/embedded.
- DB: WAL + `synchronous=NORMAL`; one `Arc<Mutex<SqliteConnection>>` shared with the timer; one
  transaction per command; cache invalidated on every committed write.
- Quickcheck harness: `WorldState` is a valid spec world; `newest-first` is a permutation of all
  posts and each post's `replies` is exactly its children in seq-desc order (DB representation).

## Possible follow-ups (not started)
- Personal timeline cold at 100k posts (1.49 ms; density-dependent) — e.g. recursive per-followee
  top-n or a different plan.
- Read concurrency: the single `Mutex<SqliteConnection>` serialises requests (a read pool is
  possible but `:memory:` tests would need shared-cache; medium risk).
- `publish` cold ~47 µs (id probe + insert + fsyncless commit) — minor.
- `time-passes` has no Interface endpoint (internal timer only); `followers-only` default is
  unreachable via `register`; DB errors answer 500 `internal`; `collect-dead-posts` is commented
  out in the spec.
- Ignored local artifacts remain (e.g. `backend/src/formal-twitter.db`, `target/`, `result`);
  they are not tracked.
