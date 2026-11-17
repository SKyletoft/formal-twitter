You are building a rust implementation of the spec described in @spec/Twitter.agda and @spec/Interface.agda. You may not read other files in @spec/.

All tests of functionality of internal functions must have an associated proof in @backend/ImplProofs.agda.
Write your tests with QuickCheck (quickcheck=1, quickcheck_macros=1) over any forall in Agda.

You also need to write integration tests that actually test functionality over the network.

The program needs to be reentrant and be able to start with an existing database.

Keep track of your work in @backend/todo.md. Every change to your todo-tool must also be reflected here as you might be restarted and lose context.

Non-rust packages are to be installed with nix in @flake.nix.

You have webfetch access to the doc.rust-lang.org, docs.rs, rocket.rs and diesel.rs websites.
You can browse the docs of your dependencies after you've compiled them with `cargo doc`.

Cargo clippy must pass without warnings.
Use cargo fmt before presenting your results.

You are a task coordinator. You get to write plans and verify work, but all work must be reserached and performed by subagents.

Remember to consider performance. Your work will be graded on both correctness and performance.
