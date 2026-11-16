# todo.md — formal-twitter backend (kept in sync with the todo tool)

## Done
- Cargo project: Rocket 0.5 (rc line, rocket_codegen) + Diesel 2.4 (SQLite, bundled libsqlite link fix via flake/env).
- `src/db.rs`: SCHEMA (accounts/sessions/posts/likes/replies/follows/log), row structs, load_world/save_world/raw_dump/append_log/read_log.
- `src/main.rs`: run() = load → step → save → log → render; all Interface POST body routes (`data = "<body>"`) and query-style GET routes (`/api/get-tweet?<token>&<id>`, `/api/global-timeline?<token>&<len>`, `/api/private-timeline?<token>&<len>`); `/raw`, `/log`, static `/`, `/style.css`, `/app.js`; to_http mirrors spec/Interface.agda to-response.
- `src/world.rs` (~950 lines): World/Account/Post/SessionStatus model, predicates mirroring spec/Twitter.agda, `step()` for all 13 Commands, plus QuickCheck harness (splitmix64 `Rng`, `gen_world`, 12 `qc_*` tests + 2 unit tests) in `#[cfg(test)] mod tests`.
- Semantics fix vs spec: anonymous `read-post` of a non-public post returns `Expired` (the spec's `failed-access` premise is vacuous when `extract-sid cmd = nothing`, so `expired` is the uniquely derivable transition; `denied` is not in the Step relation there).
- `cargo build` clean (warnings only); `cargo test` green: 14 passed / 0 failed (`/tmp/test9.log`).
- Frontend verified: `frontend/app.js` GET query params (`token`,`id` / `token`,`len`) match the backend GET routes.
- `ImplProofs.agda` (~506 lines, ~35 inversion/classification lemmas, one group per Rust test) **typechecks cleanly with Agda 2.8** (exit 0). Verified command:
  `agda -i /home/u3836/git/formal-twitter/spec -i /nix/store/kqwya2vxhcpglw93xxs34xxacb40m9ig-standard-library-2.3/src ImplProofs.agda > /tmp/agda1.log 2>&1`
  (the other 2.3 store dir hits a stale `.agdaice` cache → AmbiguousTopLevelModuleName; use the kqwya one).
- Proof techniques used: record-vs-Σ term construction (`,` not `∧`), ∃-witnessed inversions, ⊎ classification lemmas for commands with extra `expired` transitions, result-pinning for coverage, exact arrow-chain mirroring of constructor field telescopes.

## Next
- Everything from the prompt is complete. Optional: manual server verification via background `cargo run` (curl disallowed here; behavior covered by qc tests).
