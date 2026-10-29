# What it reads, refuses and trusts

The verifier reads a subset of TypeScript and models it exactly as JavaScript runs it. What falls outside, it refuses,
at the place it meets it and with what to write instead, and the contract is then not proved. It never reads an unknown
part as a harmless one.

## What it reads

**Values and types.**
- `boolean`, `string` (its UTF-16 code units, as JavaScript's: an emoji is two), `bigint` (exact), `number` (see
  *Numbers*), `null` and `undefined`;
- unions of literals (`"open" | "closed"`), optional fields, and values that may be missing (`T | undefined`);
- unions of records, a check of the tag narrowing each as the type checker does (*Narrowing*, below);
- records and arrays of any length, read lazily: a field becomes an unknown only when something reads it; a tuple the
  code builds, though not one it is given;
- functions and closures, and computations (async functions, Effect programs);
- a value of type `unknown`, carried, stored and returned, never read: its truth, `===`, `??` and its fields are refused.

**Expressions.**
- `===`, `!==`, `<`, `<=`, `>`, `>=`, `!`, `&&`, `||`, `??`, `?:`, as JavaScript defines them, `NaN` and `-0` included;
- `+`, `-` and `*` on bigints, `+` on strings, and template strings (an unknown string of their parts);
- `/` and `%` on bigints, as JavaScript computes them: the quotient truncated toward zero, the remainder with the
  dividend's sign. A division by `0n` throws, so each divisor is proved other than `0n` on the branch where its division
  runs (*Divisions*, below);
- property access and optional chains, object and array literals, spreads;
- a string's `.length`, in UTF-16 code units, as JavaScript counts them;
- on arrays: `.length`, `.at(k)`, `.some`, `.every`, `.includes` (of a string, a boolean, a bigint or a count), `.find`,
  `.slice`, `.filter(p).length`, and a literal index on a tuple;
- calls of the program's functions, read from source and inlined, by name or through a namespace import
  (`laws.readsFirst`, from `import * as laws`), and of functions a declaration covers;
- a tuple's element at a literal index, a call's `args[0]` among them.

**Statements.** `const` and `let`, assignment and compound assignment, `if` with early returns, `switch` with
fallthrough, `for…of`, `for` and `while`, `delete`, `push`, and changes to what the function allocated, read as Rust's
borrow checker would ([Loops and proof code](proofs.md), *State*).

**Computations.** An async function's or an Effect program's body: `const`, `if`, `return`, `throw` (async), blocks,
`for (const x of xs)`, and steps anywhere inside an expression, in JavaScript's order. Effect's forms are in
[Effect programs](effect.md).

### Numbers

A `number` is a class (finite, `NaN`, `+∞` or `−∞`) and a real value. Comparisons, `===` and truthiness follow IEEE 754
exactly, and every double is such a value, so a proof covers every double. Arithmetic on `number` is refused: its rounding
is not modeled. A bigint is an integer of any size, exact.

### Divisions

A bigint division by `0n` throws a RangeError. Each `/` and `%` in the code is an obligation: its divisor is not `0n`
wherever the division runs, through the `if`, `?:`, `&&`, `||` or `??` that leads to it, and the steps of a computation
that succeeded before it. A report lists each under `divisions:`, proved, or with the input that makes the divisor `0n`
(and, in a computation, what each call returned on that run). A law is judged on the runs that return: one that throws
is reported as its division, not as a law broken. In a law or a `requires`, a division by `0n` makes it throw, so it does
not hold there: guard it, `b === 0n || …`.

### Narrowing

A check of a value's tag narrows it, as the type checker narrows it. A union whose members give one field different
kinds, `{ type: "add"; n: bigint } | { type: "name"; n: string }`, is held as one record per member, so `ev.n` is the
bigint once `ev.type === "add"`, and a counterexample is always one of the members. A call is narrowed by its `op` the
same way, wherever it stands: once `c.op === "set"`, `c.args[1]` is the `set`'s second argument, inside
`calls.every((c) => c.op !== "set" || …)` too, where on some runs the call at that place is a `get` of one argument.
A read takes the paths on which the value can have the type the checker gives the read; no run reaches it on the others.

## What it refuses, and what to write instead

Each refusal names the place, `file:line:column`, and the reason.

| Written | Refused because | Write instead |
| --- | --- | --- |
| `x as T`, `x!`, `any` | each is a claim the verifier would have to trust | a check whose result the type follows: `===`, `x !== undefined`, a `_tag` |
| `+ - * /` on `number` | its rounding is not modeled | `bigint` where the values are whole, or a function declared with `assume` |
| a bigint `/` or `%` inside `.some`, `.every`, `.find` or `.filter` | the element is any index's, read or not | the division in a `for…of` over the elements, or outside the callback |
| `==`, `!=` | not modeled | `===`, `!==`, and `x === null \|\| x === undefined` for a nullish check |
| a `let` of the module, a global (`Math`) | a binding the verifier cannot see | a `const` or an argument, or a function declared with `assume` |
| `xs[k]` on an array | its type says the element is there, which may be false | `xs.at(k)`, with a literal `k`, whose type says it may be missing |
| an element at a computed index, `xs[i]` or `xs.at(i)` | not modeled | `.find`, `.some`, `.every`, or a `for…of` over the elements |
| `.includes(x)` of a `number` | it finds `NaN`, which `===` does not | `.some((y) => y === x)` |
| a member of a value the type checker has not shown present | it may be missing | a check first, or `?.` |
| a field of a union whose kind differs by member, read before its tag is checked | it is no one value | a check of the tag first: `ev.type === "add" && ev.n > 0n` |
| recursion | not modeled | `assume(f, { pure: true, ensures })` |
| a package's function | the verifier does not read packages | `assume`, in the spec or a pack |
| a change to an argument, a second name for part of an object, a moved value, a change while borrowed | aliasing is kept out of the solver | build a new value and return it |
| `break` or `continue` to a label, `do…while`, `for…in`, `var`, `a[i] = …` with a computed index, array methods that change the array but `push` | not modeled | `for…of`, `push`, a new array |
| a step after `?.` | it runs only when what is before it is present | an `if` |
| a field read through a spread, where the spread value may lack it | its type does not say whether it is there | the field written after the spread, or a required one |
| in a computation's body: `let`, `try`, `switch`, `for`, `while`, `break` | not modeled yet | `const`, `if`, `for…of`, steps |
| in spec code: a computation, an operation, the clock, a function declared `pure: false` | spec code is pure and deterministic | read it in the program and pass the result to the law |

[Effect programs](effect.md) lists the Effect forms it does not read, each with what to write.

## What it takes on trust

### `assume`

`assume(fn, { pure, ensures? })` declares what the verifier may take of a function it does not read, or should not: a
package's, or a recursive one. It replaces the function's body wherever the function is called.

- **`pure: true`**: the same arguments give the same result, and a call changes nothing anyone sees. Where the program
  has the function's source, the verifier checks this (see *The purity check*); for a package's function it is trusted.
- **`pure: false`**: each call may give a different result, as the clock does. Spec code may not call it.
- **`ensures`**: laws over the arguments and the result, assumed at every call, without proof.
- **The type arguments are the view** the laws are written for: `assume<[xs: ReadonlyArray<string>], string[]>(uniq, …)`
  says what `uniq` does on strings, and `tsc` checks that `uniq` can be called so. A call no view covers is refused.

Counting a number's digits calls itself, which the verifier does not read. Declared, with what the rest of the program
needs of it:

<!-- file: src/digits.ts -->
```ts
/** How many digits `n` has, in base 10. */
export function digits(n: bigint): bigint {
  return n < 10n ? 1n : 1n + digits(n / 10n)
}

/** The spaces before `n` in a column eight wide. */
export const padding = (n: bigint): bigint => 8n - digits(n)
```

<!-- file: src/digits.contract.ts -->
```ts
import { assume, contract } from "tsverify"
import { digits, padding } from "./digits.ts"

export const digitsCount = assume(digits, { pure: true, ensures: { atLeastOne: (_n, count) => count >= 1n } })

export const paddingFits = contract(padding, { ensures: { atMostSeven: (_n, spaces) => spaces <= 7n } })
```

<!-- run -->
```text
$ npx tsverify src/digits.contract.ts paddingFits
paddingFits
  proved          atMostSeven  (104 ms)
  trusted (declared, not proved):
    - digits: pure, checked from source (read digits); laws atLeastOne — src/digits.contract.ts:4:28
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
    - A purity check takes on trust that a property read runs no getter; that a module constant it reads is never changed by other code; that it terminates.
```

The proof of `padding` holds of the real program only if `digits` does what `atLeastOne` says. Every report lists what it trusted,
so that is never hidden; `brokenOn(assumption, inputs)`, from `tsverify`, runs the real function on inputs and returns each
law it breaks, which is how a declaration is tested.

A declaration is in force across the whole program it is part of: the spec that declares it, and every file verified with
it.

### The purity check

Where `pure: true` declares a function of the program, the verifier reads its source and refuses it if it is not:

<!-- file: src/tags.ts -->
```ts
/** The tags, without the empty ones. */
export function cleaned(tags: Array<string>): Array<string> {
  tags.splice(0, tags.length, ...tags.filter((t) => t !== ""))
  return tags
}

export const firstTag = (tags: Array<string>): string => cleaned(tags).at(0) ?? "none"
```

<!-- file: src/tags.contract.ts -->
```ts
import { assume, contract } from "tsverify"
import { cleaned, firstTag } from "./tags.ts"

export const cleanedIsPure = assume(cleaned, { pure: true })

export const firstOrNone = contract(firstTag, { ensures: { neverEmpty: (_tags, tag) => tag !== "" } })
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/tags.contract.ts
src/tags.contract.ts
  firstOrNone: not verified — src/tags.ts:7:58: `cleaned` is declared pure and is not: src/tags.ts:3:3: changes its argument `tags`. Declare it `pure: false`, or change it so it changes only what it allocates

1 contract in 1 file: laws none; 1 not verified
```

It refuses an effect (`await`, `yield`, `this`, the clock, `Math.random`, the console, a module's `let`, a function it was
given, a method or a package function it does not know), a change to anything it did not allocate (its arguments, a
module's constants), and a cast or a type predicate, either of which would hide a value's type. It accepts a function that
changes only what it allocated, as a fold builds its state: it follows each value of the caller's stored into a fresh one,
by type, and refuses a change to an object that value could reach. It takes three things on trust, and every report that
leans on it says so: a property read runs no getter, a module constant is never changed by other code, and the function
ends.

### Packs

A pack declares a library's functions once, for every spec that imports it, as Verus's `vstd` does for Rust's standard
library. `tsverify/packs/lodash` declares `uniq` on strings and `clamp` on numbers: `import "tsverify/packs/lodash"` in a
spec puts it in force. A pack is tested against the library it declares (`brokenOn`), and is only as good as those tests:
a naive `clamp` law, "within its bounds", is broken by `NaN` and by bounds in the wrong order. A pack ships as TypeScript,
since the verifier reads its laws, so a project's `tsc` checks it with the project's options.

## Caveats

- **The arguments are taken to have their TypeScript types.** That holds for typed callers. At the edge of a program,
  where values come from outside, they need checking first: that is where a schema comes in.
- **A read the type checker has narrowed is taken on its word.** Where a check of a tag (`c.op === "set"`) narrows a
  value, the paths the checker rules out are taken not to reach the read. Casts and `!`, which could make it wrong, are
  refused.
- **The code is taken to throw only where it says so**, by a `throw`, a failure, or a division by `0n` (checked). An
  exception from anywhere else, a call or a binding never read, is not seen.
- **A spread copies each property its value's type requires**: the value is taken to be plain data, its properties its
  own, none a getter.
- **A declaration is trusted.** A law of `assume` is never proved, and a package's purity never checked.
- **A declaration is in force across the whole program**, wherever it is written. Two specs in one program share theirs.
- **A loop is taken to end.** An invariant proves what holds if the loop ends; a `while` loop's ending is not proved.
- **A loop of steps over an array of unknown length bounds its whole contract.** The proof side runs it at most 4
  times, so no law of that contract is proved, even one the loop has no part in.
- **What `Effect.try` runs is not read, nor recorded.** Its success is any value of its type; a law sees it through the
  outcome alone.
- **Proof calls run.** `invariant`, `assert` and a lemma's call do nothing, but they are calls, and their arguments are
  closures made each time.
- **The examples are the author's own.** The same hand wrote each example, its laws and its planted bugs, so they show
  what the verifier reads and catches, not how it fares on code someone else wrote.
- **No certificate yet.** A result is not bound to hashes of the code, the spec and the tool's version.
- **A long-lived process grows.** The terms a verification keys by are kept alive until the process ends, because Z3
  reuses the id of a term it has freed.
