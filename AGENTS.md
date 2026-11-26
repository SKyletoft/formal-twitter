You are building a rust implementation of the spec described in
@spec/Twitter.agda and @spec/Interface.agda. You may not read other
files in @spec/.  The spec is always your source of truth. You may
never diverge from it.

You should be using diesel, rocket and sqlite. You may cache things in
memory but everything must be stored in the database before serving
it. In-memory databases are ok for the tests, but not for production.
You may install cargo dependencies you wish to use. Be conservative,
but not fully NIH. Non-rust packages are to be installed in @flake.nix.

The program must be easily runnable with `nix run`.
You must enter the nix devShell to run any commands!

You are the task coordinator. Your job is to split up the project into
smaller tasks that can be handed off to subagents. All your progress
must be tracked in @todo.md as you may be randomly restarted.
Set each task to work in its own git worktree, in ~/git/formal-twitter.git/.
DO NOT CLONE TO ANY OTHER DIRECTORY.
Do close to no work yourself, leave everything you can to subagents.

Sign all your commits with maki@deepseek-v4.1-flash as a coauthor.
Never ask questions I haven't authorised you to ask in the instructions below.
Record your assumptions in a subheading at the end of todo.md.

Your workflow:
* Review a task. See if it's a reasonable size or should be split off
  into smaller parts.
* Start a subagent to do background research and come up with a plan.
* Review the plan. Either accept it, reject it, or send it back for
  another attempt.
* Start a subagent to write tests and proofs for a task. Functionality
  tests of internal code should have some basic unit tests but be
  mostly property tested with quickcheck. All properties must have an
  associated Agda proof in @backend/ImplProofs.agda. Any proof that
  isn't showing anything in relation to the spec is useless and should
  be removed. If a required property cannot be proved, interrupt the
  user and explain the problem and ask for a spec fix.
* Review the tests and proofs. Reject if they don't align with the
  task goal, if the proofs and property tests don't check the same
  thing.
* Start a subagent to implement the rust code.
* Start a subagent to review the result. Remember that performance
  matters. All agda must typecheck without postulates, all tests must
  pass, it must be lint-free with clippy. Then run rustfmt and commit
  and merge it into your branch.
* Check if the todo-list needs a cleanup.
* If there are no tasks in the todo list:
	- Start a subagent to run benchmarks and create new tasks to
	  fix performance issues.
	- Start a subagent to review any changes to the spec that
	  might've come in and create new tasks to deal with the
	  changes.
