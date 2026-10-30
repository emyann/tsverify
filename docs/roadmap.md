# What comes next

In rough order:

- The core first, by the published Z3 problems it still refuses (`fixtures/corpus/`): a string's `split` and spread, by
  code units and by code points; `%` and `**` of computed values on `number`; arithmetic that rounds, read as IEEE 754
  rounds it, where it is now only an obligation that it does not.
- Folds on the proof side: `.join` and `.flatMap`, known there only of none or one element, and `.filter`'s count,
  only none or some, so their laws are bounded; a fold read by induction over the array, as a loop is read through its
  invariants.
- A `requires` that leaves out a path, found where it is written: the ends of a result say so today (`reaches:`, an end
  `unreachable`), for a union of strings or of records told apart by a tag; the same of each branch of the code.
- Collections the code changes: `Map.set`, `Set.add` and `delete` on a map the function allocated, its `size` and its
  iteration, by the keys it holds; and a dictionary's keys, values and entries (`Object.keys`), its keys held distinct
  and in JavaScript's order, integer-like keys first.
- A query's time, steadier: a proof that takes a second can take more than ten when Z3 meets the same formula in another
  order, as it does when terms are freed and their numbers reused. Each number the loops keep whole by construction (a
  counter) is held as an integer; the rest are held in parts the solver must reason about.
- The next Effect forms, by how often they stop real code: `Effect.exit`, `mapError`, `catchCause`, `suspend`; `let` in
  a computation's body.
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
