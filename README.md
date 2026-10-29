# tsverify

Prove that TypeScript code keeps its laws for every input, or get an input that breaks one.

A spec says what a function must do: its type, and laws written as plain TypeScript predicates. The code takes the spec
as its type and carries nothing else of it. `tsverify` reads both from source, through the TypeScript compiler, and asks
the Z3 solver whether any input the spec allows breaks a law. It answers with a proof, or with the input.

It reads pure functions, loops, async functions and Effect programs over the operations they are given. What it does not
read, it refuses, saying where and what to write instead: it never takes a part it cannot read for one that is fine.

**A prototype.** Version 0.0.0, not on a registry, its API not settled. It reads a subset of TypeScript
([what it reads](docs/reads.md)). Every example in these pages is run by its tests, the output shown included.

## Install

`npm pack` here builds the package and writes `tsverify-0.0.0.tgz`, which a project installs as it would any tarball.

```sh
npm install --save-dev ./tsverify-0.0.0.tgz   # in the project; `effect` too for an Effect program
npx tsverify                                  # every spec and implementation under the current folder
```

It needs Node 24.16 or later. It brings its own `typescript` (6.0.3) and `z3-solver` (5.3.2); `effect` 4 and `lodash-es` 4
are optional peers, for Effect programs and for the lodash pack.

## Five minutes

The project needs two things of its `tsconfig.json`: `strictNullChecks`, on with `strict` and by default in TypeScript 6
(the verifier reads types with `null` and `undefined` in them, and refuses a project that turns it off), and a module
resolution that reads a package's `exports` (`nodenext`, `node16` or `bundler`). This one runs TypeScript files with Node directly:

<!-- file: tsconfig.json -->
```json
{
  "compilerOptions": {
    "target": "es2023",
    "module": "nodenext",
    "moduleResolution": "nodenext",
    "strict": true,
    "noEmit": true,
    "allowImportingTsExtensions": true,
    "skipLibCheck": true,
    "types": []
  }
}
```

The spec comes first: the function's type, what a caller promises (`requires`), and the laws (`ensures`), each a
predicate over the arguments and the result.

<!-- file: src/charge.spec.ts -->
```ts
import { spec } from "tsverify"

export const ChargeSpec = spec<(balance: bigint, amount: bigint) => bigint>({
  requires: (balance, amount) => balance >= 0n && amount >= 0n,
  ensures: {
    neverNegative: (_balance, _amount, left) => left >= 0n,
    takesWhatItCan: (balance, amount, left) => (amount > balance ? left === 0n : left === balance - amount),
  },
})
```

The code takes the spec as its type. The import is a type, so nothing of the spec runs, and `tsc` holds the code to the
spec's signature:

<!-- file: src/charge.ts -->
```ts
import type { Implementation } from "tsverify"
import type { ChargeSpec } from "./charge.spec.ts"

export const charge: Implementation<typeof ChargeSpec> = (balance, amount) => (amount > balance ? 0n : balance - amount)
```

<!-- run -->
```text
$ npx tsverify
src/charge.ts
  charge
    proved          neverNegative  (107 ms)
    proved          takesWhatItCan  (18 ms)

1 contract in 1 file: laws 2 proved
```

Each law is proved for every balance and amount the spec allows, not for a sample of them. Now break the code: drop the
guard.

<!-- file: src/charge.ts -->
```ts
import type { Implementation } from "tsverify"
import type { ChargeSpec } from "./charge.spec.ts"

export const charge: Implementation<typeof ChargeSpec> = (balance, amount) => balance - amount
```

<!-- run, exits 1 -->
```text
$ npx tsverify
src/charge.ts
  charge
    counterexample  neverNegative  (93 ms)
                    e.g. (0n, 1n)
    counterexample  takesWhatItCan  (12 ms)
                    e.g. (0n, 1n)

1 contract in 1 file: laws 2 counterexample
```

`charge(0n, 1n)` returns `-1n`. A counterexample is an input the real code breaks on, not a guess: the verifier takes one
only from a side that models JavaScript exactly. One that leans on a declaration says so, and holds of the function as
declared. The command exits 1, so a CI step or an agent knows the
code is not done.

## What it answers

| Verdict | What it means |
| --- | --- |
| `proved` | No input the spec allows breaks the law. |
| `counterexample` | One does, and `e.g.` gives it, with what each operation gave the code on that run. |
| `vacuous` | Proved, but no result of the function could break it: the law says nothing of the function. |
| `bounded` | Not proved, and no input with arrays of up to 4 elements breaks it. The reason says what stands in the way. |
| `unsupported` | The law uses something the verifier does not read. The reason says what to write instead. |
| `unknown` | The solver gave no answer, on either side. |
| `inconsistent` | The verifier contradicted itself: a bug of tsverify, never a verdict on the code. |

The command exits 0 only when every law, and every obligation of the proof code, is `proved`. [Reading a
report](docs/verdicts.md) has each verdict, what to do about it, and `--json`.

## Guides

- [Writing a spec](docs/specs.md): pure functions, async code and the calls it makes, code that already exists, and what a
  law may do.
- [Reading a report](docs/verdicts.md): each verdict and what to do next; the command, its exit codes, `--json`.
- [Effect programs](docs/effect.md): services as operations, typed errors, the forms the verifier reads.
- [Loops and proof code](docs/proofs.md): the invariants it guesses, and `invariant`, `assert` and lemmas for when a
  guess is not enough.
- [What it reads, refuses and trusts](docs/reads.md): the subset of TypeScript, each refusal and its fix, `assume`, the
  purity check, packs, and the caveats.
- [What the examples show](docs/measurements.md): the solver beside property testing, planted bugs, how much of a code base
  it reads.
- [How it works](docs/how-it-works.md): the two sides, the lowering to Z3, the adapters.

## Caveats

The ones that matter most; [all of them](docs/reads.md#caveats).

- **The arguments are taken to have their types**, and the code to throw only where it says so. That holds for typed
  callers; at the edge of a program, values need checking first.
- **A declaration is trusted.** What `assume` declares of a function, and every pack, is taken without proof, and every
  report lists it.
- **A loop is taken to end.** An invariant proves what holds if it ends; a `for…of` over an array always does.
- **The examples are the author's own**, so they show what the verifier reads and catches, not how it fares on code
  someone else wrote.

## In this repository

```sh
npm test            # 214 tests, ~50 s, the documentation's examples among them
npm run verify      # every contract below here, a line per law, then a total
npm run verify -- examples/account                                   # one folder, or one file
npm run verify -- examples/account/withdraw.ts withdraw              # one contract, with all it knows
npm run bench       # planted bugs: the solver beside property testing (~15 s)
npm run coverage -- <tsconfig.json> [--modular]                      # how much of a code base it reads
npm run typecheck
```

On this repository `npm run verify` exits 1, on purpose: two examples keep a law the solver refutes,
`examples/account/imports.spec.ts` keeps 8 laws bounded by a loop of steps, and `fixtures/vacuous` holds three vacuous
laws. `test/docs.test.ts` runs every example of the documentation: it writes each
page's files into a project of their own, in the page's order, runs each command the page shows, and compares what it
prints.

What a program imports, the first two being what a spec and its code import (the code only their types):
- `tsverify`: `spec` and `Implementation`; `contract` and `computation` for code that already exists; `assume`; the proof
  code `invariant`, `assert`, `lemma`; `brokenOn`, which tests a declaration against the real function; and the types a
law reads, `Outcome`, `Call`, `Rejects`. It has no dependencies.
- `tsverify/effect`: `spec` and `computation` for an Effect program, typed from the Effect.
- `tsverify/api`: the verifier as a program calls it (`loadProject`, `verify`, `openZ3`, `purityOf`). It changes with the
  verifier.
- `tsverify/mutants`: laws against planted bugs, the solver beside property testing. It changes with the verifier too.
- `tsverify/packs/lodash`: what the verifier may assume of the lodash functions it covers.

## Building and packing

The repository runs its TypeScript source and no build. Each entry of `exports` names its source under a condition of
its own, `tsverify-source`: `tsconfig.json` sets it in `customConditions`, and every script passes
`--conditions=tsverify-source`, so a test that imports `tsverify` gets `src/contract.ts`. A project that installs the
package sets no such condition and gets `dist/`: `npm run build` emits it (JavaScript and declarations, through
`tsconfig.build.json`), and `npm pack` runs the build first. The verifier knows its own modules by package, the nearest
`package.json` named `tsverify`, and by their path in it, source or built (`ownModule` in `src/project.ts`), so a spec
reads the same whether it imports this checkout, a linked copy or an installed one.

`test/install.test.ts` packs the package, installs the tarball into a new project with some of the examples copied in,
and asks the installed command what the source answers on the same files: the same verdicts. It also checks that the
tarball holds nothing but the build and the packs, and that a planted bug's counterexample breaks the installed code when
it runs. It needs `npm` and, when the npm cache lacks a dependency, the network.

## Next

- Integer division (`/` and `%` on bigints, which truncate toward zero) and a string's `length` (its UTF-16 code units):
  the first two refusals a new project's first spec met.
- A value read after a check of its tag, where it differs by path: a law that reads `calls.at(-1)` once it has checked
  `op === "put"`, when the last call is a `get` on one path and a `put` on another. Today a law reads a call at a place
  that holds the same operation on every path (`calls.at(1)`).
- The next Effect forms, by how often they stop real code: `Effect.exit`, `mapError`, `catchCause`, `suspend`;
  destructuring with rest or defaults; `let` in a computation's body.
- A loop of steps read through invariants over the trace, as a fold's loop is read through its own, so a law of such a
  contract can be proved and not only bounded.
- Contracts on operations, assumed by every caller and proved by each implementation (a layer, a class).
- More guesses, so fewer invariants are written: for `while` and `for` loops, for loops in a callee, and from a
  computation's laws over its trace.
- Termination: a `decreases` measure for `while` loops and recursion, as Verus has.
- Packs for the most-called libraries, each tested against its library; a check of a package's purity from its JavaScript.
- Equivalence as a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes.
- A first release: a license, a version past 0.0.0, and the registry.
