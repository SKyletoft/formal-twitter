You are building a rust implementation of the spec described in @spec/Twitter.agda and @spec/Interface.agda. You may not read other files in @spec/.

All tests must have an associated proof in @backend/ImplProofs.agda.
Write your tests with QuickCheck over any forall in Agda.

Keep track of your work in @backend/todo.md. Every change to your todo-tool must also be reflected here as you might be restarted and lose context.

Non-rust packages are to be installed with nix in @flake.nix.

You have webfetch access to the rocket.rs and diesel.rs websites.

You can browse the docs of your dependencies after you've compiled them with `cargo doc`.
