# What comes next

In rough order:

- A loop read key by key, its body read only where a law needs it: the facts the pass at a key brings, said under the
  branch that reads that key's entry, so a later loop that decides the key leaves them aside. Nemia's `inheritedLabels`
  proves five of its eight laws today, with its first loop's writes unknown; the other three need what that loop writes,
  and its body read at every key a law reads runs the solver out of work. The search side, at two elements, runs out
  of work on it too, and refutes none of its planted bugs there (`docs/design-2026-11-03-maps.md`, *The limit*).
- The core first, by the published Z3 problems it still refuses (`fixtures/corpus/`): a string's `split` and spread, by
  code units and by code points; `%` and `**` of computed values on `number`; arithmetic that rounds, read as IEEE 754
  rounds it, where it is now only an obligation that it does not.
- Checks on a spec alone, before any code: whether the laws decide every input, whether some input has no answer at
  all, and whether linked specs agree (`docs/design-2026-11-01-spec-checks.md`, proposed for 0.5.0).
- Folds on the proof side: `.join`, known there only of none or one element, and `.filter`'s count, only none or some,
  so their laws are bounded; a fold read by induction over the array, as a loop is read through its invariants.
- A `requires` that leaves out a path, found where it is written: the ends of a result say so today (`reaches:`, an end
  `unreachable`), for a union of strings or of records told apart by a tag; the same of each branch of the code.
- `Object.keys` of a record whose type names its fields, where the record is one the code built; a `Map` or a `Set` the
  code is given, changed after it is copied (`new Map(given)`).
- A function the code is given, declared pure where a spec says so: the same value for the same arguments, so a law can
  say what two calls of it give, as it can of a declaration's.
- A query's work, smaller: each number the loops keep whole by construction (a counter) is held as an integer; the rest
  are held in parts the solver must reason about.
- The next Effect forms, by how often they stop real code: `Effect.forEach` as a loop of steps, `forever` one pass at
  a time, `Schema.decode*`; `let` in a computation's body; `instanceof` of a package's class (`Error`); a method of a
  value the code is given, as an operation (a client a program calls through `Effect.try`).
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

Beside tsverify, not in it: what happens across steps, actors and crashes ("eventually settled", "one writer at a time")
is a model checker's question. An experiment with TLA+ or Quint on Nemia's daemon handover, and where the line between the
two falls, is in `docs/experiment-2026-11-02-tla-and-quint.md`.
