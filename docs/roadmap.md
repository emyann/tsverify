# What comes next

In rough order:

- The next Effect forms, by how often they stop real code: `Effect.exit`, `mapError`, `catchCause`, `suspend`;
  `let` in a computation's body.
- A loop of steps read through invariants over the trace, as a fold's loop is read through its own, so a law of such a
  contract can be proved and not only bounded.
- Contracts on operations, assumed by every caller and proved by each implementation (a layer, a class).
- `<` and `>` between strings, in the code-unit order JavaScript compares them by, which the solver now holds them in.
- More guesses, so fewer invariants are written: for `while` and `for` loops, for loops in a callee, and from a
  computation's laws over its trace.
- Termination: a `decreases` measure for `while` loops and recursion, as Verus has.
- Packs for the most-called libraries, each tested against its library; a check of a package's purity from its JavaScript.
- Equivalence as a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes.
- A first release: a version past 0.0.0, and npm.
