# How it works

A contract is read twice from source, through the TypeScript compiler API, into terms for the Z3 solver: once to prove,
once to search. Neither runs the code: the verifier never imports what it judges, so nothing in a module can change what
it reads.

## In logic

A spec of a function f : A₁ × … × Aₙ → R, with `requires` P and laws Q₁ … Qₖ, says for each law:

```text
∀ x̄ ∈ A₁ × … × Aₙ.  P(x̄)  ⟹  Qᵢ(x̄, f(x̄))
```

A law's parameters, the arguments and then the result, are x̄ and f(x̄). The README's `shipping`, over 𝔻, JavaScript's
numbers (`NaN` and ±∞ among them):

```text
∀ t ∈ 𝔻.  t ≥ 0  ⟹  ( t ≥ 50 ⟹ f(t) = 0 )      freeFrom50
∀ t ∈ 𝔻.  t ≥ 0  ⟹  ( t < 50 ⟹ f(t) = 5 )      smallOrdersPay
```

JavaScript has no implication, so a law writes A ⟹ B as `A ? B : true`, or as `!A || B`: `total < 50 || cost === 0`
is ¬(t ≥ 50) ∨ f(t) = 0.

The verifier never checks the ∀ itself. It lowers f's code to a term, f(t) = (t ≥ 50 ? 0 : 5), and asks Z3 whether the
negation has a model:

```text
∃ x̄.  P(x̄) ∧ ¬Qᵢ(x̄, f(x̄))
```

`unsat` is a proof: no input breaks the law. A model is an input that does, the counterexample: for `t > 50 ? 0 : 5` it is
t = 50. A law that would hold whatever f returned, ∀ x̄. P(x̄) ⟹ ∀ r. Qᵢ(x̄, r), is `vacuous`.

A computation's result depends on what its calls returned, so that is quantified too. With w the world, the outcome of
each call it makes, and (o, c) its outcome and the calls it made when it runs in w:

```text
∀ x̄, w.  P(x̄)  ⟹  Qᵢ(x̄, o, c)
```

A counterexample's `where names.get gave ""` is the part of w the model chose.

## The source

| File | Role |
|---|---|
| `src/contract.ts` | what a spec author writes (`tsverify`): `spec`, `Implementation`, `contract`, `computation`, `assume`, `invariant`, `assert`, `lemma` |
| `src/adapters/effect/contract.ts` | the same for an Effect program (`tsverify/effect`): `spec`, `computation` |
| `src/api.ts` | the verifier as a program calls it (`tsverify/api`): `loadProject`, `verify`, `openZ3`, `purityOf` |
| `src/mutants.ts` | laws against planted bugs, the solver beside property testing (`tsverify/mutants`) |
| `src/trust.ts` | the declarations in force, read from source, and the report's trusted base |
| `src/purity.ts` | the purity check of a declared function's source |
| `packs/` | declarations of a library's functions, tested against the library (`tsverify/packs/lodash`) |
| `examples/` | the worked examples: a charge written against its spec, an order's status, an account's ledger and a withdrawal, a program calling lodash |
| `src/project.ts` | the program (a file's text can be replaced or added in memory), diagnostics, a contract read from source |
| `src/symbolic.ts` | any value of a TypeScript type, built lazily: a field becomes an unknown only when read |
| `src/lower.ts` | pure TypeScript to symbolic values, with JavaScript's semantics, and the branch each runs on, which a division's obligation holds on |
| `src/exec.ts` | statements: state, places and ownership, loops through their invariants, and the obligations of the proof code and of each division |
| `src/ops.ts` | truthiness, `===`, `<`, `??` and conditional values, exactly as JavaScript defines them |
| `src/narrow.ts` | a field read where the type checker has narrowed its object: the paths whose value can have the read's type |
| `src/universe.ts` | the Z3 context, its unknowns (one function per path through arrays), assumptions and quantifier scopes |
| `src/concrete.ts` | model to JS values (replay), and JS values to constraints (the translator check) |
| `src/verify.ts` | the queries: laws, vacuity, reachability, the cross-check of every proof, and the loop invariants it guesses |
| `src/computation.ts` | outcomes, traces, operations, and the lowering of a computation's body step by step |
| `src/adapter.ts`, `src/adapters/` | the adapter interface and the three adapters |
| `src/cli.ts` | `tsverify`: every contract found, or one by name; the text report and `--json` |
| `bench/mutants.ts` | the planted-bug benchmark on the order example (`npm run bench`) |
| `bench/coverage.ts` | how much of a code base the verifier reads (`npm run coverage -- <tsconfig>`) |

## Two sides

Each contract is lowered twice:
- The **proof side** keeps arrays of any length and real quantifiers. It may over-approximate: a filtered array is modelled
  by its length as "none or some", and numbers as reals. Its `unsat` is a proof. Its models aren't trusted once an
  approximation was used.
- The **search side** holds arrays to 4 elements, writes quantifiers out element by element, counts filtered elements
  exactly, and keeps numbers to values a double holds exactly. Every model it finds is a real input.

A law the proof side can't settle in time, and the search side can't break, is reported as `bounded`, never as `proved`. A
law proved that no result could break is reported as `vacuous`.

**Every proof is checked against the search side.** The proof side's encoding (havoc, loops read through invariants) is
where a verifier's own bugs hide, and one did: a loop left early was once read as having run to its end. So each proof
is checked against the search side, whose every model is a real input: one query for all the proved laws, one for all the
proved obligations, each obligation asked as the first of the proof code to fail on a run. A proof the search side breaks
is reported `inconsistent`, with the input, as a bug of tsverify rather than a verdict on the code. It costs about a
second on the account fold.

**Numbers.** A `number` is a class (finite, NaN, +∞ or −∞) plus a real value. `===`, `<` and truthiness follow IEEE-754
exactly. Every double is such a value, so proofs cover all doubles. Exact IEEE floats in Z3 were tried first: comparing
one with an array length needs `fp.to_real`, which Z3 handled so poorly that queries timed out at 30 s. With the
real-valued model, the same queries take milliseconds.

Arithmetic is read where it is exact, as Verus reads machine integers: the exact result, with an obligation that the
double holds it (a whole number or a half within 2^53, from finite operands), so where a double would round, the input
that makes it round is a counterexample to the obligation, never a wrong verdict on a law. To reason about indexes the
solver must know when a sum is whole, which Z3 cannot prove of reals from facts about their summands. So each number is
held in parts: on the proof side, whether it is whole, the integer it is if so, and otherwise an integer and a fraction
strictly between 0 and 1; on the search side, an integer count of 1/1024. Whole numbers then add as integers do.

**Checked against the code.** The translator is the part everything else trusts, so the tests check it against the real
function on 300 random inputs, on both sides (`test/order.test.ts`). Every counterexample the benchmark and the tests find
is run on the planted code: a refutation the code does not confirm stops the run as the verifier's bug. Two bugs in the
verifier were caught that way while building it.

## Modes and trust, after Verus

Verus sorts code into three modes. The same three are here, in TypeScript:

| Verus | Here | Rule |
|---|---|---|
| `spec`: pure, deterministic, ghost | the laws and `requires` of a spec, and whatever they call | runs no computation, calls no operation, reads no clock, calls nothing declared `pure: false` |
| `proof`: lemmas, invariants, asserts | typed no-op calls in the program: `invariant(i => ...)`, `assert(() => ...)`, a lemma's call | each proved where it is written, then known; spec code inside |
| `exec`: the compiled code | the program | |
| `assume_specification`, `external_body` | `assume(fn, { pure, ensures? })` | trusted without proof, listed in every report |
| `vstd` | a pack (`tsverify/packs/lodash`) a spec imports | tested against the real library |

## The core and its adapters

The core knows computations, not libraries:
- **Values:** primitives, records, tagged unions, arrays.
- **Computations:** a body that runs steps (`yield*` or `await`) and ends in `{ _tag: "Success", value }` or
  `{ _tag: "Failure", error }`.
- **Operations:** methods of something the code is given. Each call is recorded in a trace `{ target, op, args, outcome }`
  and ends in any outcome its types allow.

An adapter (`src/adapter.ts`) tells the core which forms are which:

| Adapter | What it reads |
|---|---|
| `src/adapters/ts.ts` | `new Date()`, `Date.now()` (a fresh time per call); `Error` subclasses with field initializers |
| `src/adapters/async.ts` | async functions as computations; `await` steps; methods returning a promise as operations; `Rejects<A, E>` for what a promise rejects with |
| `src/adapters/effect/` | `Effect.fn(...)(function* ...)` and `fnUntraced`; `Effect.gen`, and a function that returns an Effect; `yield*`; `Context.Service` keys as services; methods returning an Effect as operations; `Effect.succeed`, `fail`, `void`, `sync`; `Effect.try` and `tryPromise`, the code they run not read (any value of its type, or what `catch` makes of a thrown `unknown`); `map`, `flatMap`, `catch`, `catchTag`, effect first or last; `x.pipe(f, g)` and `pipe(x, f, g)`; `Schema.TaggedError` and `Data.TaggedError` construction; a `computation` helper typed from the Effect |

A computation's body, in the core, whatever marks its steps: `const`, a step as a statement, `return`, `throw` (async),
`if`, blocks, `for (const x of xs)` over an array, and steps anywhere inside an expression, run in the order JavaScript
evaluates them and only on the paths that reach them.

The core never names a library. What no adapter reads is refused where the code uses it, naming the function: for Effect
today, `forEach`, `exit`, `mapError`, `catchCause`, `die`, concurrency, resources and defects; for promises, `.then` and
`.catch`; and, in a computation's body, `let`, `try`, `switch`, `for`, `while` and `break`.
