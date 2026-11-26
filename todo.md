# todo.md — formal-twitter backend

## Conventions
- Main branch: `maki-loop-3` (this worktree).
- Each task gets its own git worktree: `/home/u3836/git/ft-wt-<id>` with branch `task/<id>`.
- All commit messages must include the trailer:
  `Co-authored-by: maki@deepseek-v4.1-flash <maki@deepseek-v4.1-flash>`
- Commands run inside `nix develop --command ...`.
- Spec files readable: ONLY `spec/Twitter.agda` and `spec/Interface.agda`.

## Done
- [x] Environment/permissions unblocked (worktree + merge).
- [x] Baseline `cargo check` passes (hello world, rocket+diesel resolved).

## In progress
- [ ] T1: DB schema + persistence layer (diesel/sqlite, migrations, ids, store primitives, in-memory test harness).
  - Tests+skeleton committed (36cc6eb). Review accepted. Implementation subagent running.
- [ ] T5 (parallel): static frontend in worktree `/home/u3836/git/ft-wt-t5` (branch `task/t5-frontend`).
- [x] T2 plan: accepted (see conversation). Worktree after T1 merge.
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
- [ ] T2: Engine — auth + post lifecycle (register, authenticate, revoke-token, publish, delete, read-post) with quickcheck tests + Agda proofs.
- [ ] T3: Engine — social + timelines (follow, unfollow, like, unlike, personal/global timelines) with quickcheck tests + Agda proofs.
- [ ] T4: HTTP interface + wiring (Rocket routes, text/plain body parsing, exact responses/headers, static frontend mount, `nix run`, integration tests).
- [ ] T5: Frontend (static HTML/CSS/JS speaking the Interface API).
- [ ] T6: Benchmarks + performance hardening (create new tasks from results).

## Spec gaps / open decisions
- Anonymous `read-post` of a post that is absent/private/deleted has NO `Step` constructor in Twitter.agda (only `read-post-anonymously` for public+live). Implementation will answer `403 access_denied` (denied) for these undefined cases; needs user confirmation / possible spec fix.
- `time-passes` / session timeout is not exposed by Interface (no endpoint); sessions only become invalid via logout.
- Accounts are always created with `default-visibility = everyone`, so `followers-only` is unreachable via API; still implement faithfully.
