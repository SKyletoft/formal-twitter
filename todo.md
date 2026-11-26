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
- [ ] T2a: review REJECTED (4 issues: unclosed delimiter, missing `#[quickcheck]`, missing
  `ReturnedTimeline` variant, weak `login` property). Fix subagent running in `wt-t2`.
  After it passes: implement `engine/auth.rs`, review, commit, merge.
- [ ] T2b plan: ACCEPTED (split T2b-1 store+proof-world scaffolding, T2b-2 tests+proofs, T2b-3 impl, review).
- [ ] T3 plan: ACCEPTED (split T3a social/`ReturnedTimeline`/`can_read_post`, T3b timelines).
- [ ] T4 plan: research subagent running (must include: serve ONLY index.html/app.js/style.css;
  `frontend/prompt` cannot be deleted due to sandbox policy, so it must be unreachable).

## State as of 2026-11-26
- `maki-loop-3` HEAD 28b5937 (T5 merged; T1 merged).
- `wt-t2` HEAD 099f531 + uncommitted T2a tests/proofs/skeleton being fixed.
- `wt-t5` removed after merge (branch `task/t5-frontend` retained).
- All worktrees live under `/home/u3836/git/formal-twitter.git/`.
- [x] T5: frontend reviewed and merged (merge 28b5937; branch e62e00c). The tracked
  `frontend/prompt` task-description file could NOT be deleted or emptied because the sandbox
  denies `rm`/writes outside the coordinator's own files; T4 must serve an explicit asset allowlist.

## Done (cont.)
- [x] T1: DB schema + persistence layer. Merged into `maki-loop-3` (merge 099f531, impl 3c12bd0). Review accepted.
- [x] T2 plan: accepted.
- [x] T3 plan: accepted.
- [x] T4 plan: accepted with corrections: signup success = 200 EMPTY body (`ok`), follow/unfollow unknown user = 200 success (no failure step).

## Decisions log
- Do NOT edit `spec/`. Implement defined behavior exactly.
- Token-less commands: implementation never returns `expired` (spec's `failed-access` is vacuously true there, but our choice is a derivable behavior for register/login; for anonymous reads the 403 choice is our documented decision).
- Anonymous `get-tweet` of absent/private/deleted post -> `403 access_denied` (documented deviation; spec has no constructor). Functional test only, no Agda property.
- T1 has NO quickcheck properties / Agda proofs: it only stores data; no `Step`/spec transition exists at this layer. Unit tests only. (Adding list lemmas would violate "useless proofs" rule.)
- Commit trailer on every commit: `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.
- T4 hint: `flake.nix` `prePatch` copies `frontend/` to the *parent* of the unpacked backend source, so `include_dir!("$CARGO_MANIFEST_DIR/../frontend")` (or rust-embed) is the intended way to embed static assets for `nix run`; serve them from Rocket without depending on cwd.

## Backlog (ordered)
- [ ] T2a: Engine — auth (register, authenticate, revoke-token) + failed-access. Fix→impl→review→merge.
- [ ] T2b-1: posts store helpers (`can_read`, `can_read_anonymous`, `post_view`, `delete_own`) + Agda `mk-world-posts` scaffolding.
- [ ] T2b-2: tests+proofs for publish/reply/delete/read-post (+ expired). Anonymous private/deleted/absent read: functional `403` only, NO Agda property (documented deviation).
- [ ] T2b-3: implement `engine/posts.rs`; review; merge.
- [ ] T3a: `EngineResult::ReturnedTimeline` (already added by T2a fix) + `active_user` helper + `store::can_read_post` + `engine/social.rs` (follow/unfollow/like/unlike) + tests/proofs P1-P6,P10.
- [ ] T3b: `engine/timeline.rs` (personal/private-global/anonymous-global) + P7-P9.
- [ ] T3-impl + review.
- [ ] T4: HTTP interface + wiring (Rocket routes, text/plain body parsing, exact responses/headers, static frontend mount serving an explicit allowlist, `nix run`, integration tests).
- [x] T5: merged frontend (28b5937); `frontend/prompt` remains but must never be served.
- [ ] T6: Benchmarks + performance hardening (create new tasks from results).

## Assumptions (recorded)
- T2 was split into T2a (auth, the current uncommitted work) and T2b (post lifecycle); the
  existing `tests/engine_auth.rs` covers only T2a, so T2b is treated as a separate task.
- Worktrees are recreated inside `formal-twitter.git/wt-*`; the stale `ft-wt-*` directories were
  removed (T1 was already merged, T5 was clean).
- Bash/file permissions are restrictive: `rm` is denied for everyone and writes are limited to the
  coordinator's own files. Do not plan tasks that require deleting tracked files; make them
  unreachable instead. Recorded for `frontend/prompt`.
- Commit trailer on every commit: `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`.

## Spec gaps / open decisions
- Anonymous `read-post` of a post that is absent/private/deleted has NO `Step` constructor in Twitter.agda (only `read-post-anonymously` for public+live). Implementation will answer `403 access_denied` (denied) for these undefined cases; needs user confirmation / possible spec fix.
- `time-passes` / session timeout is not exposed by Interface (no endpoint); sessions only become invalid via logout.
- Accounts are always created with `default-visibility = everyone`, so `followers-only` is unreachable via API; still implement faithfully.
