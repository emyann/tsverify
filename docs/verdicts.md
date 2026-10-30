# Reading a report

`npx tsverify` verifies every contract under the current folder; given files or folders, those; given a file and a name,
that one contract, with everything the verification knows of it. Each file is verified as a program of its own, through
the nearest `tsconfig.json` above it (or `--project`).

## A line per contract

Four small specs, one law of each kind:

<!-- file: src/cap.contract.ts -->
```ts
import { spec } from "tsverify"

const capSpec = spec<(value: bigint, limit: bigint) => bigint>({
  requires: (_value, limit) => limit >= 0n,
  ensures: {
    withinTheLimit: (_value, limit, capped) => capped <= limit,
    neverNegative: (_value, _limit, capped) => capped >= 0n,
    limitNotNegative: (_value, limit, _capped) => limit >= 0n,
  },
})
export type CapSpec = typeof capSpec
```

<!-- file: src/cap.ts -->
```ts
import type { Implementation } from "tsverify"
import type { CapSpec } from "./cap.contract.ts"

export const cap: Implementation<CapSpec> = (value, limit) => (value > limit ? limit : value)
```

<!-- file: src/label.contract.ts -->
```ts
import { spec } from "tsverify"

const labelSpec = spec<(name: string) => string>({
  ensures: {
    neverEmpty: (_name, label) => label !== "",
    unnamedWhenEmpty: (name, label) => (name === "" ? label == "(unnamed)" : true),
  },
})
export type LabelSpec = typeof labelSpec
```

<!-- file: src/label.ts -->
```ts
import type { Implementation } from "tsverify"
import type { LabelSpec } from "./label.contract.ts"

export const label: Implementation<LabelSpec> = (name) => (name === "" ? "(unnamed)" : name)
```

<!-- file: src/largest.contract.ts -->
```ts
import { spec } from "tsverify"

const largestSpec = spec<(xs: ReadonlyArray<bigint>) => bigint>({
  ensures: {
    noneLarger: (xs, largest) => xs.every((x) => x <= largest),
    oneOfThem: (xs, largest) => xs.length === 0 || xs.includes(largest),
  },
})
export type LargestSpec = typeof largestSpec
```

<!-- file: src/largest.ts -->
```ts
import type { Implementation } from "tsverify"
import type { LargestSpec } from "./largest.contract.ts"

export const largest: Implementation<LargestSpec> = (xs) => {
  let best = xs.at(0) ?? 0n
  for (const x of xs) if (x > best) best = x
  return best
}
```

<!-- file: src/score.contract.ts -->
```ts
import { spec } from "tsverify"

const scoreSpec = spec<(points: number) => number>({
  ensures: { notNegative: (_points, score) => score >= 0 },
})
export type ScoreSpec = typeof scoreSpec
```

<!-- file: src/score.ts -->
```ts
import type { Implementation } from "tsverify"
import type { ScoreSpec } from "./score.contract.ts"

export const score: Implementation<ScoreSpec> = (points) => Math.max(points, 0)
```

<!-- run, exits 1 -->
```text
$ npx tsverify
src/cap.ts
  ✗ cap  1 counterexample, 1 vacuous, 1 proved  (141 ms)
    ✗ neverNegative  (10 ms)
      e.g. (-1n, 0n)
    ○ limitNotNegative  (5 ms)
      no result breaks it, whatever the function returns: it says nothing of the function
src/label.ts
  ! label  1 unsupported, 1 proved  (25 ms)
    ! unnamedWhenEmpty  (0 ms)
      src/label.contract.ts:6:61: operator == is not modeled: write `===` (and `x === null || x === undefined` for a nullish check)
src/largest.ts
  ~ largest  1 bounded, 1 proved · 2 obligations  (769 ms)
    ~ oneOfThem  (51 ms)
      not proved: the loop at src/largest.ts:6:3 is read through its invariants alone, and none rules this run out: write one that does, first in its body (`invariant((i) => ...)`); no counterexample with arrays of at most 4 elements
src/score.ts
  ! score  not verified
    src/score.ts:4:61: `Math` is a binding the verifier cannot see (a `let` or a global): read it from a `const` or an argument, or move it into a function the spec declares with `assume`

✗ 1 counterexample · ! 1 unsupported · ~ 1 bounded · ○ 1 vacuous · ! 1 not verified
✓ 3 laws, 2 obligations proved
  4 contracts in 4 files · 2.4 s
```

Each file, then a line per contract: its verdict's mark (the worst of its laws'), its name, how many laws it holds and
how long it took. Under a contract with something to look at, a line per law that needs a look: its mark, its name, how
long it took, and, first, what it says when it is written `{ says, holds }`. A line under a law says why, or gives an
input. A law proved is counted, not listed, so what needs a look is what you read. A run of one file lists every law,
and `--verbose` every law of every file. The last lines count what needs a look, by verdict, then what was proved.

| Mark | Verdict |
| --- | --- |
| ✓ | `proved` |
| ✗ | `counterexample` |
| ○ | `vacuous` |
| ~ | `bounded` |
| ? | `unknown` |
| ! | `unsupported`, `not verified` or `inconsistent` |

## Each verdict, and what to do

### ✓ `proved`

No input the spec allows breaks the law: not of the inputs tried, of every one. Arrays of any length, every string, every
bigint. A proof is checked again on the exact side ([How it works](how-it-works.md)), and one that side breaks is
reported `inconsistent`, never `proved`.

### ✗ `counterexample`

An input the spec allows breaks the law, and `e.g.` gives it, as the arguments of a call: `cap(-1n, 0n)` is `-1n`. The
counterexample is real: the verifier takes one only from a model of JavaScript that is exact, and running the code on it
breaks the law. For a computation, a line `where …` says what each operation gave the code on that run. One that leans on
a declared function says so: it holds of the function as declared, and may not of the real one.

Then one of three things is wrong, and a person decides which:

- **the code**: here, `cap` passes a negative value through, and `value < 0n ? 0n : …` would mend it;
- **the law**: `neverNegative` may not be what `cap` is for;
- **`requires`**: callers may promise more, `value >= 0n`, and the spec should say so.

### ○ `vacuous`

Proved, and no result of the function could break it: the law says nothing of the function. `limitNotNegative` reads
only the inputs, which `requires` already settles. The verifier asks it of every law it proves, by giving the law any
value of the result's type in place of the function's. Rewrite the law to constrain the result, or drop it. A vacuous law
fails the command, as a law that says nothing should.

### ~ `bounded`

Not proved, and no input with arrays of up to 4 elements breaks it (`--bound` sets the length). The reason says what
stands in the way:

- **a loop**, read through its invariants alone, and none of them rules out the run the solver found. Write an invariant
  that does, first in the loop's body: `oneOfThem` needs `best` to be one of `xs` throughout, which
  [Loops and proof code](proofs.md) writes. The guessed invariants are listed under `proof code:`.
- **a loop of steps** over an array of unknown length in a computation, which the proof side runs at most 4 times. Its
  whole contract is bounded at best ([Effect programs](effect.md), *Loops of steps*).
- **a filtered array**, `.filter(p).length`, known on the proof side only as none or some;
- **a `number`**, any real on the proof side, where only the search side keeps to doubles;
- **the proof side's time**, run out before a proof, the search side finding nothing.

### ! `unsupported`

The law uses something the verifier does not read, at the place given, and the reason says what to write instead.
`==` converts its operands before it compares them, which is not modeled; `label === "(unnamed)"` asks what
`unnamedWhenEmpty` means. [What it reads](reads.md) lists every refusal and its fix.

### ! `not verified`

The contract could not be read at all, so no law of it was checked: the code, or its `requires`, uses something the
verifier does not read. Here `Math.max` is a global. Write it as the verifier reads it (`points > 0 ? points : 0`), or move
it into a function the spec declares with `assume`, whose laws are then trusted.

### ? `unknown`

Neither side answered: the solver gave up on each, out of time or on a query it cannot decide (quantifiers and
non-linear arithmetic can do that). The reason gives each side's. `--timeout` raises the time per query (10 s by
default); splitting a law into smaller ones, or a lemma, often helps more.

### ! `inconsistent`

The proof side proved the law, and the search side, which is exact, found an input that breaks it. One of the two is
wrong, which is a bug of tsverify, not a verdict on the code. The input is given; please report it.

## Proof code

`proof code:` lists what the verifier had to prove along the way, its *obligations*, each with a verdict of its own:

- `invariant on entry` and `invariant kept by each iteration`: a loop invariant, written or guessed (a guess names the
  law it restates, "of the elements gone through");
- `assert`: an `assert(() => …)` where it is written;
- `lemma's requires` where a lemma is called, and `lemma` for the lemma itself.

A law proved through an obligation that is not proved is reported `bounded`, `counterexample` or `unknown`, never
`proved`.

## Divisions

`divisions:` lists each bigint `/` and `%` the code runs, with the verdict on its divisor: `proved` other than `0n` on
the branch where the division runs, or a `counterexample`, the input that makes it `0n`, on which the real code throws.
A law is judged on the runs that return, so a division that can throw leaves the laws as they are, and fails the
command on its own ([What it reads](reads.md), *Divisions*).

## One contract, in full

Given a file and a name, the command prints everything it knows of that contract:

<!-- run, exits 1 -->
```text
$ npx tsverify src/cap.ts cap
✗ cap  1 counterexample, 1 vacuous, 1 proved  (138 ms)
  ✓ withinTheLimit  (90 ms)
  ✗ neverNegative  (10 ms)
    e.g. (-1n, 0n)
  ○ limitNotNegative  (5 ms)
    no result breaks it, whatever the function returns: it says nothing of the function
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
```

- `reaches:` the ends the code can come to, each with a witness: every value of a result that is a union of strings, and
  for a computation `Success` and each `Failure` tag its type allows. One the verifier proves out of reach is marked
  `unreachable`.
- `trusted:` each function a declaration covers, which the result leans on without proof: its purity, whether the purity
  was checked from source, its laws, and where it is declared ([What it reads](reads.md), *What it takes on trust*).
- `assumed:` what the model of JavaScript took for granted on the way, each kind once.

## The command

```text
tsverify [<file or folder>...] [--project tsconfig.json] [--bound N] [--timeout MS] [--verbose] [--json] [--watch]
tsverify <file.ts> <export> [--json] [--watch]
```

| Flag | |
| --- | --- |
| `--project` | the `tsconfig.json` every file is read through, instead of the nearest one above it |
| `--bound` | the longest array the search side tries, 4 by default |
| `--timeout` | the time each query may take, in milliseconds, 10,000 by default |
| `--verbose` | every law and every obligation of every contract, with what each trusted and assumed, as the one-contract form prints them |
| `--json` | one JSON document instead of the text, and nothing else on stdout |
| `--watch` | the same again on every change to the project's TypeScript, until stopped (below) |

| Exit | |
| --- | --- |
| 0 | every law and every obligation, each division's among them, is `proved` |
| 1 | one is not: a counterexample, or a law bounded, vacuous, unsupported, unknown or inconsistent, or a contract not verified |
| 2 | a usage error: a path that is not there, no file or no contract to verify, no `tsconfig.json` |
| 3 | the verifier itself failed, which says nothing of the code |

In a terminal the report is drawn live: each contract verified stays above a line naming the one being verified and how
far the run is, and a long line wraps to the window under its own first word. It is in colour: green for `proved`, red
for `counterexample`, yellow for a verdict that is neither, magenta for what was not read. Piped, as CI and coding agents
read it, or with `NO_COLOR` set, it is plain text, each line whole.

### `--watch`

Verify while you write, as a test runner watches: `npx tsverify --watch` runs again each time a TypeScript file of the
project, its `tsconfig.json` or its `package.json` changes, until you stop it, and each run ends with whether all is
proved. Each run is a process of its own, as a single run is, and a run a newer change makes stale is stopped.

```text
tsverify --watch · 8:07:10 PM · src/shipping.ts changed
src/shipping.ts
  ✓ shipping  2 laws  (131 ms)
    ✓ An order of 50 or more ships free  (freeFrom50, 114 ms)
    ✓ smallOrdersPay  (15 ms)

✓ 2 laws proved
  1 contract in 1 file · 1.1 s

all proved · waiting for a change (Ctrl+C to stop)
```

In a terminal the screen is redrawn for each run. Piped, each run's report follows the last one's under its own first
line, so a coding agent that runs it in the background edits, then reads the newest report, until all is proved. With
`--json`, each run is one line of JSON, the document `--json` prints.

## `--json`

The same verdicts as one document: `passed` (what the exit code says), `contracts` and `totals`.

```json
{
  "passed": false,
  "contracts": [
    {
      "file": "src/cap.ts",
      "contract": "cap",
      "laws": [
        { "name": "withinTheLimit", "status": "proved", "ms": 90.1 },
        { "name": "neverNegative", "status": "counterexample", "args": ["-1n", "0n"], "ms": 11.2 }
      ],
      "obligations": [],
      "trusted": [],
      "cover": [],
      "notes": ["…"],
      "passed": false
    }
  ],
  "totals": { "contracts": 1, "files": 1, "laws": { "proved": 1, "counterexample": 1 }, "obligations": {}, "unsupported": 0 }
}
```

A counterexample's values are JSON; a value JSON cannot hold is a string of its JavaScript text (`"-1n"`, `"undefined"`,
`"NaN"`, `"-0"`). Its `world`, for a computation, holds what each operation gave the code on that run, its outcome by call, and
for a declared function its result. Places in a reason are relative to the current folder, as `file` is.
