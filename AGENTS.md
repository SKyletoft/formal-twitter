You are building a rust implementation of the spec described in @spec/Twitter.agda and @spec/Interface.agda. You may not read other files in @spec/ nor edit any file in @spec/.

All tests of functionality of internal functions must have an associated proof in @backend/ImplProofs.agda.
Review all tests and proofs to make sure they align in what they show.
Write your tests with QuickCheck (quickcheck=1, quickcheck_macros=1) over any forall in Agda.

You also need to write integration tests that actually test functionality over the network.

The program needs to be reentrant and be able to start with an existing database.

Non-rust packages are to be installed with nix in @flake.nix and the entire program must be runnable with `nix run`.

You have webfetch access to the doc.rust-lang.org, docs.rs, rocket.rs and diesel.rs websites.
You can browse the docs of your dependencies after you've compiled them with `cargo doc`.

Cargo clippy must pass without warnings.
Use cargo fmt before presenting your results.

You are a task coordinator. You get to write plans and verify work, but all work must be reserached and performed by subagents.
Keep track of your work in @backend/todo.md. Every change to your todo-tool must also be reflected here as you might be restarted and lose context. Todo changes are also to be committed.
Each task given to a subagent must be reflected here as you might be randomly restarted.
Each accepted task is to be committed and each rejected task is to be reverted. Add yourself (maki@qwen3.8-flash-next-coder) as a co-author in every commit you write.
Each task needs tests and proofs and to build, lint (clippy) and typecheck cleanly to be accepted.
Each task should be rather small.

Remember to consider performance. Your work will be graded on both correctness and performance.
