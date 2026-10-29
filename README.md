# effect-verify

A prototype verifier for ordinary TypeScript. A spec author writes laws as plain predicates. The verifier reads them,
and the code they're about, from source through the TypeScript compiler API. Z3 then proves each law for every input,
or returns an input that breaks it.

The starting point was a design handoff, `docs/handoff-2026-10-28.md`. That document is a hypothesis, and parts of it were
changed on evidence: see *What changed from the handoff*.

Pinned: Node ≥ 24.16, `z3-solver` 5.3.2, `typescript` 6.0.3, `effect` 4.0.6 (used only by the Phase 0 spike).

```sh
npm test            # 24 tests, ~4.5 s
npm run pilot       # verify Nemia's lifecycleOf against its laws
npm run bench       # planted bugs: the solver vs property testing (~20 s)
npm run verify -- <spec.ts> <export>
npm run typecheck
```

The pilot and the benchmark read `../hkb-v2` in place. They change nothing there.

## A spec

```ts
import { contract } from "../../src/contract.ts"
import { lifecycleOf } from "../../../hkb-v2/packages/agent-runtime/src/core/domain.ts"

export const lifecycle = contract(lifecycleOf, {
  ensures: {
    stopOutranks: (state, s) => state.settled !== null || !state.stopRequested || s === "stopping",
    inputRequiredNeedsHoldOpen: (state, s) => s !== "input-required" || (state.holdOpen === true && !state.closed),
    submittedHasNoAttemptThisTurn: (state, s) =>
      s !== "submitted" || !state.attempts.some((a) => (a.turn ?? 0) === state.inputs.length),
    // ...
  },
})
```

- `contract(fn, { requires?, ensures })` names the function. The type checker resolves that name to its declaration, which
  is the link from spec to code.
- Each law is `(args..., result) => boolean`, and is type-checked against the function's real signature.
- At run time the contract is a plain object, so the same laws work as a test oracle.
- The code under verification imports nothing from this package.

## The pilot: Nemia's `lifecycleOf`

`lifecycleOf` (agent-runtime, `src/core/domain.ts`) maps a task's journal state to one of 9 lifecycle states. It calls
`waitsForInput` and `turnOf`. The spec turns the six ordered rules of its doc comment into 10 laws. `npm run pilot` gives:

- **9 laws proved** for every state, with arrays of any length, each in 4–130 ms.
- **1 law refuted:** `inFlight`. The doc comment says "working once spawned", but the code tests `last.spawnedAt` by
  truthiness. An attempt whose `spawnedAt` is `""` therefore reads `starting`. The type (`string | null`) allows `""`; the
  runtime never writes it. Either the domain says `spawnedAt` is never empty, or the code says `!== null`. That choice is
  the code owner's.
- **All 9 lifecycle states are reachable.** Each comes with a concrete witness state, and the tests run that state through
  the real function.

### Benchmark: 17 planted bugs and one harmless control

`npm run bench` plants one-line bugs in the three functions and hunts each one two ways:
- the solver, with each counterexample replayed on the planted code;
- property testing over the same laws, on seeded random states from `pilots/lifecycle/generate.ts`. That generator is
  edge-biased: every literal, `""`, NaN, -0, Infinity, fractions, arrays of 0–4 elements.

A bug counts as caught when a law that holds on the original fails on the planted copy.

| | solver | property testing, 100 runs | property testing, 1,000–100,000 runs |
|---|---|---|---|
| bugs caught (of 17) | **10**, ~0.75 s each | 9 | 10 |
| missed bugs explained | **8 of 8** | — | — |

- **Both methods catch the same 10 bugs.** The solver's only lead is T2, which sampling first catches at run 110. On a pure
  function with a small state space, a well-tuned property tester is as good at *finding* bugs. That generator was tuned by
  someone who knew the edges: it reaches `input-required` in only 4 of 2,000 states.
- **The solver explains every miss; sampling explains none.** For each missed bug, it proves whether the planted
  `lifecycleOf` equals the original for every state:
  - **Harmless in context, proved:** W1 and W5 (a `waitsForInput` change that `lifecycleOf` returns before reaching) and
    the control E1.
  - **A gap in the laws, with a witness:** L6, W2, W3, W4 and T1. Each comes with a state whose result the bug changes
    while no law forbids it. For example, L6 turns `submitted` into `ending` for a held-open task with nothing attempted.
    This is the weak-spec signal the handoff thought formal methods could not give. Mutants plus equivalence give it
    concretely. A person still decides which behaviour is intended.

The value over property testing on this kind of code is therefore not catching more bugs. It is:
- proofs instead of samples;
- equivalence (is this change behaviour-preserving?);
- reachability with witnesses;
- gap witnesses that show where the spec is weak.

## How it works

| File | Role |
|---|---|
| `src/contract.ts` | `contract(fn, laws)`, what a spec author writes |
| `src/project.ts` | the program (a file's text can be replaced or added in memory), diagnostics, a contract read from source |
| `src/symbolic.ts` | any value of a TypeScript type, built lazily: a field becomes an unknown only when read |
| `src/lower.ts` | pure TypeScript to symbolic values, with JavaScript's semantics |
| `src/ops.ts` | truthiness, `===`, `<`, `??` and conditional values, exactly as JavaScript defines them |
| `src/universe.ts` | the Z3 context, its unknowns (one function per path through arrays), assumptions and quantifier scopes |
| `src/concrete.ts` | model to JS values (replay), and JS values to constraints (the translator check) |
| `src/verify.ts` | the queries: laws, reachability, the translator check |
| `src/cli.ts` | `npm run verify` |

**Two sides.** Each contract is lowered twice:
- The **proof side** keeps arrays of any length and real quantifiers. It may over-approximate: a filtered array is modelled
  by its length as "none or some", and numbers as reals. Its `unsat` is a proof. Its models aren't trusted once an
  approximation was used.
- The **search side** holds arrays to 4 elements, writes quantifiers out element by element, counts filtered elements
  exactly, and keeps numbers to values a double holds exactly. Every model it finds is a real input.

A law the proof side can't settle in time, and the search side can't break, is reported as `bounded`, never as `proved`.

**Numbers.** A `number` is a class (finite, NaN, +∞ or −∞) plus a real value. `===`, `<` and truthiness follow IEEE-754
exactly. Every double is such a value, so proofs cover all doubles. Arithmetic on `number` is refused, since its rounding
isn't modelled. Exact IEEE floats in Z3 were tried first: comparing one with an array length needs `fp.to_real`, which Z3
handled so poorly that queries timed out at 30 s. With the real-valued model, the same queries take milliseconds.

**Supported:**
- primitives, `null` and `undefined`, optional fields, string-literal unions;
- `const`, `if` with early returns, `?:`, `&&`, `||`, `!`, `??`, `===`, `!==`, comparisons;
- `+ - *` on bigints, `+` on strings;
- property access and optional chains;
- object and array literals;
- calls (inlined), closures;
- `.length`, `.at(k)`, `.filter(p).length`, `.some`, `.every` and `.includes` on arrays.

**Refused, with a file:line:**
- casts, `!` and `any`, which are claims the verifier would have to trust;
- a member read on a value the type checker hasn't narrowed to non-null at that spot;
- `number` arithmetic, and bigint `/` and `%`;
- `==`;
- `let`, loops and mutation;
- recursion;
- globals and packages;
- element access `a[i]`, string length, template strings.

**Checked against the code.** The translator is the part everything else trusts, so the tests check it against the real
function on 300 random states, on both sides. A deliberate bug planted in the translator (empty strings truthy) fails five
tests. It would also have produced a false proof of `inFlight`. In the benchmark, every counterexample is replayed on the
planted code, and two bugs in the verifier were caught that way while building it.

## What changed from the handoff

- **Contracts are read from source only.** Phase 0 imported the spec module to read its Effect Schema representation. A
  spec module's top-level code could then change what the verifier read (`x >= -100` for a source saying `>= 0n`), and a
  custom filter could claim any built-in's id. The verifier now never runs what it judges: `fixtures/never-imported.ts`
  throws on import and verifies.
- **Laws are plain predicates.** `Schema.makeFilter` is opaque at run time, so its meaning came from source anyway. The
  `Struct({ input, output }).check(...)` wrapper added ceremony and nothing more. Reading Effect Schema domains from source
  is not built yet.
- **The target is real code, not `charge`.** The handoff's examples restate the code: the `charge` proof reduced to
  `x = x`. `lifecycleOf` has string unions, optionals, numbers, arrays and calls, the shape of Nemia's pure core. `charge`
  remains as the bigint fixture.
- **Effect pipelines are not modelled.** Scenario B (`Effect.flatMap` composition) is deferred.
- **Not built:** Gate 1's "an output exists for every input" check. Satisfiability and reachability cover most of its value.

Phase 0's findings about Effect 4.0.6 still hold (`spike/dump-representations.ts`):
- built-in checks carry `{ id, payload }`;
- `makeFilter` is opaque at run time;
- `Schema.brand` leaves the representation unchanged;
- `representation` is a public annotation, so it can be forged.

## Caveats

- **The code is assumed to throw nothing.** A binding is evaluated only when read, so an exception in an unread binding is
  not seen.
- **Arguments are assumed to have their TypeScript types.** That is sound only for typed callers. Runtime validation is
  where Effect Schema would come in.
- **One code base.** The pilot is one function family. The benchmark's bugs were planted by the same person who wrote the
  laws, and the property-testing generator was tuned by that person too.
- **No certificate yet.** A result is not bound to hashes of the code, spec and tool versions, as the handoff asked.
- **The tool itself is plain TypeScript, not Effect.**

## Next

- Pin `inFlight`'s finding with the code owner: the domain says `spawnedAt` is never empty, or the code says `!== null`.
- Add the five laws the gap witnesses point to, then rerun the benchmark.
- A second real target with different shapes: `decide`'s `observe` (durations, numbers) or a verb guard.
- Turn equivalence into a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes, for a factory gate.
