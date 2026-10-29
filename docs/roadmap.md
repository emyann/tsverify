# What comes next

In rough order:

- Integer division (`/` and `%` on bigints, which truncate toward zero): the first refusal a new project's first spec
  met, with a string's `length`, which is read now.
- A value read after a check of its tag, where it differs by path: a law that reads `calls.at(-1)` once it has checked
  `op === "put"`, when the last call is a `get` on one path and a `put` on another. Today a law reads a call at a place
  that holds the same operation on every path (`calls.at(1)`), and not `c.args[1]` inside
  `calls.every((c) => c.op !== "set" || …)`, where `c` may be a call with one argument.
- The next Effect forms, by how often they stop real code: `Effect.exit`, `mapError`, `catchCause`, `suspend`;
  destructuring with rest or defaults; `let` in a computation's body.
- A counterexample's `where` line for everything a run was given: it lists only the calls the run made, but a declared
  function's result (`assume`) or a clock read on a branch the run did not take is still listed. It needs the branch a
  run took followed through every expression, not only through statements.
- A loop of steps read through invariants over the trace, as a fold's loop is read through its own, so a law of such a
  contract can be proved and not only bounded.
- Contracts on operations, assumed by every caller and proved by each implementation (a layer, a class).
- More guesses, so fewer invariants are written: for `while` and `for` loops, for loops in a callee, and from a
  computation's laws over its trace.
- Termination: a `decreases` measure for `while` loops and recursion, as Verus has.
- Packs for the most-called libraries, each tested against its library; a check of a package's purity from its JavaScript.
- Equivalence as a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes.
- A first release: a version past 0.0.0, and npm.
