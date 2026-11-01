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
- records and arrays of any length, read lazily: a field becomes an unknown only when something reads it; tuples, the
  code's and the caller's, but for one with an optional or a rest element;
- functions and closures, and computations (async functions, Effect programs); a function the code is given, as some
  function that changes nothing, each call some value of its return type, on which a counterexample leans;
- a dictionary the code is given, `Record<string, T>`, read at any key, and its keys, values and entries
  (*Dictionaries*, below);
- values of more than one primitive kind (`boolean | "strict"`), each the kind it is, `typeof` telling them apart
  (*Narrowing*, below);
- a `Date` the code is given, read through `getTime()` and `valueOf()`: `NaN` or a whole number of milliseconds within
  8.64e15 of 1970; a `Map` and a `Set`, given or built from an array (`new Set(["done", "failed"])`), read through `has`
  and `get` (*Collections*, below);
- a value of type `unknown`, carried, stored and returned, asked its kind by `typeof` and its class by `instanceof`,
  and read where the type checker has narrowed it (after `instanceof`, or a type predicate) as any value of the type
  it is narrowed to, of the class `instanceof` found; read back in a counterexample as a value of that kind. Its truth,
  `===`, `??` and its fields before it is narrowed are refused, and so is a read of it as a second type. A type
  parameter nothing constrains is read the same way, as a generic body can look no further into it;

**Expressions.**
- `===`, `!==`, `<`, `<=`, `>`, `>=`, `!`, `&&`, `||`, `??`, `?:`, as JavaScript defines them, `NaN` and `-0` included;
- `+`, `-` and `*` on bigints, `+` on strings, and template strings (an unknown string of their parts);
- `+`, `-`, `*` and `/` on `number`, where they are exact, each an obligation that it is (*Numbers*, below); its
  bitwise operators, `|`, `&`, `^`, `~`, `<<`, `>>` and `>>>`, on 32-bit integers as JavaScript makes them; and `**` of
  two literals (`2 ** 32`);
  `Math.floor`, `Math.ceil`, `Math.trunc`, `Math.round`, `Math.abs`, `Math.max`, `Math.min`, `Number.isInteger`,
  `Number.isSafeInteger`, `Number.isFinite`, `Number.isNaN`, and `Object.is`, which tells `-0` from `0`; `Date.parse`,
  as some function of its string;
- `typeof x`, and `Boolean(x)`, the truth a condition reads;
- `x instanceof C`, of a class the program declares: false of a primitive; of an `unknown`, whether it is one of the
  class's instances, never another's but where one class extends the other. Of a package's class (`Error`), whose
  ancestry its declarations need not show, it is refused;
- `Object.keys`, `Object.values` and `Object.entries` of a dictionary the code is given and of an object literal it
  wrote, in the order JavaScript lists them (*Dictionaries*, below);
- `"key" in obj`, of a key written as a string (*Narrowing*, below), and of any key of a dictionary;
- a record read at a key its type holds to a few names (`WORDS[phase]`, `phase: "waiting" | "running"`), as the field
  of the name it is;
- `/` and `%` on bigints, as JavaScript computes them: the quotient truncated toward zero, the remainder with the
  dividend's sign. A division by `0n` throws, so each divisor is proved other than `0n` on the branch where its division
  runs (*Divisions*, below);
- property access and optional chains, object and array literals, spreads;
- a string's `.length`, in UTF-16 code units, as JavaScript counts them, and its `startsWith`, `endsWith`, `includes`
  and `indexOf` of one string, `charAt(i)`, `at(i)`, `s[i]` (under `noUncheckedIndexedAccess`) and `slice`, each with
  JavaScript's positions: truncated, counted from the end where `at` and `slice` count so, `""` or `undefined` outside;
  and `trim`, `trimStart` and `trimEnd`, of the white space and line ends JavaScript takes off;
- on arrays: `.length`, an element at any index, `xs[i]` and `.at(i)` (*Indexes*, below), `.some`, `.every`, `.includes`
  (of a string, a boolean, a bigint or a count), `.find`, inside a `.some` or an `.every` too, `.slice` with
  JavaScript's positions, `.map`, `.toReversed()`,
  `.reverse()` of a copy made where it is called (`[...xs].reverse()`), and `.filter`, `.join` and `.flatMap` (*Folds*,
  below);
- calls of the program's functions, read from source and inlined, by name or through a namespace import
  (`laws.readsFirst`, from `import * as laws`), and of functions a declaration covers;
- a tuple's element at a literal index, a call's `args[0]` among them.

**Patterns.** Object and array patterns, in a `const` or `let`, a parameter, a callback's parameter and a `for…of` head
(`for (const [name, n] of pairs)`), nested, with defaults, holes and a rest: an array's element past its end is
`undefined` and takes the default, as `xs[k]` reads it (`noUncheckedIndexedAccess`, or a default, says it may be
missing), and `...rest` is a copy of the elements from there on.

**Statements.** `const` and `let`, assignment and compound assignment, `if` with early returns, `switch` with
fallthrough, `for…of`, `for` and `while`, `delete`, `push`, an element written at any index (`b[i] = v`), and changes
to what the function allocated, read as Rust's borrow checker would ([Loops and proof code](proofs.md), *State*).

**Computations.** An async function's or an Effect program's body: `const`, `if`, `return`, `throw` (async), blocks,
`for (const x of xs)`, and steps anywhere inside an expression, in JavaScript's order. Effect's forms are in
[Effect programs](effect.md).

### Numbers

A `number` is a class (finite, `NaN`, `+∞` or `−∞`), a real value, and whether it is `-0`. Comparisons, `===` and
truthiness follow IEEE 754 exactly, and every double is such a value, so a proof covers every double. `-0` is `0` to all
of them; `Object.is` tells it apart, and the model gives it where IEEE 754 does: `-0 + -0`, `-0 - 0`, a product or a
quotient that is 0 of one negative operand, `-x` of `0`, `Math.ceil` and `Math.trunc` of a fraction above −1, and
`Math.min` of two zeros. A bigint is an integer of any size, exact.

Arithmetic on `number` is read where it is exact: `+`, `-`, `*` and `/` (and `++`, `--`, `+=`, `-=`) of two finite
operands whose exact result a double holds, a whole number or a half within 2^53. There the double is the exact result,
and the model reads it so. Elsewhere a double rounds, which is not modeled, so each operation the code runs is an
obligation that it is exact where it runs, listed under `arithmetic:`: proved, or broken by an input on which it may
round or meets `NaN` or `±∞`. A law is judged on the runs where every operation is exact, and is proved only once each
is. `i + 1` is proved exact for a safe integer short of `2^53 − 1`, and refuted at `NaN` for any `number`.

In a law, a `requires` and proof code, arithmetic is part of what is said: a law, an invariant or an `assert` holds only
where its arithmetic is exact, and a `requires` is read as allowing an input where its own may round, for a proof, and
as ruling it out, for a counterexample. In other spec code (a declaration's laws, a guessed invariant), arithmetic on
`number` is read on counts and small whole literals alone, `i - 1`.

`Math.floor`, `Math.ceil`, `Math.trunc` and `Math.round` give the integral double JavaScript gives (`Math.round` takes a
half up, toward +∞, and -0.5 to `-0`). Of a quotient of two whole numbers, `Math.round(ms / 1000)` or
`Math.floor((lo + hi) / 2)`, each rounds the quotient's real value, which is what JavaScript gives while the dividend is
within 2^52: a quotient that is no exact double lies further from a whole number, and from a half, than the double it
rounds to strays from it. That the operands are whole and the dividend within 2^52 is the obligation, listed under
`arithmetic:` in the division's place. `Math.max` and `Math.min` are `NaN`
where an argument is, of any number of arguments; the `Number` checks read the class and the value. A bitwise operator
makes each operand a 32-bit integer as JavaScript does (`NaN`, the infinities and the zeros are 0, a fraction is
truncated, the rest wraps), so its result is exact and never `-0`: `(lo + hi) >>> 1` is proved between `lo` and `hi`
while their sum is below 2^32, and refuted past it. `%` on `number`, `**` of anything but two literals, and `Math`'s
other functions are refused. The `Number` checks of a value that may be missing say it is there and passes:
`d === undefined || Number.isInteger(d)` keeps every whole `d`.

### Indexes

`xs[i]` and `xs.at(i)` read the element at an index the code computes, `undefined` outside the array, as JavaScript does:
`xs[i]` is an element only where `i` is a whole number in range, and `.at(i)` truncates `i` (`NaN` is 0) and counts a
negative one from the end. `xs[i]` is read only under `noUncheckedIndexedAccess`, whose type says the element may be
missing; without it, the type says the element is there, and the read is refused.

An element written at a computed index, `b[i] = v`, is an obligation that `i` is a whole number inside the array, listed
under `element writes:`: elsewhere JavaScript grows the array, or adds a property no element holds. A law is judged on
the runs where every write lands inside, and is proved only once each does.

### Divisions

A bigint division by `0n` throws a RangeError. Each `/` and `%` in the code is an obligation: its divisor is not `0n`
wherever the division runs, through the `if`, `?:`, `&&`, `||` or `??` that leads to it, and the steps of a computation
that succeeded before it. A report lists each under `divisions:`, proved, or with the input that makes the divisor `0n`
(and, in a computation, what each call returned on that run). A law is judged on the runs that return: one that throws
is reported as its division, not as a law broken. In a law or a `requires`, a division by `0n` makes it throw, so it does
not hold there: guard it, `b === 0n || …`.

### Folds

`.map` keeps the length, and its element `i` is the callback's of element `i`; the callback runs on every element, as
JavaScript runs it, so what it obliges (an exact operation) it obliges of each. `.join` and `.flatMap` build their result
from every element. The search side writes them out over its arrays of at most 4 elements, exactly; the proof side
knows `.join` of none and one element (`""`, and the element itself) and `.flatMap` only as empty when its array is, so
a law about more is bounded at best, with the reason saying which call: `cells.join(",")` is known on the proof side
only for none or one element.

`.filter` keeps its elements in order. The search side writes it out: element `k` is kept where the predicate holds of
it, and the `j`-th kept is the one with `j` kept before it, so `xs.filter(p)[0]` and `.at(-1)` are exact. The proof side
counts the kept as none or some, and knows the `j`-th kept to be some element the predicate holds of, at an index that
rises with `j`.

### Collections

A `Map` or a `Set` is the array of its entries, read through `has` and `get`: a key is found as the collection finds it
(`NaN` finds `NaN`), a `Map` the code is given gives a key's first entry, and one built from pairs its last, as its
constructor keeps it. `get` is `undefined` where the key has no entry. A `Map` or a `Set` the code is given has keys
that are strings, booleans or bigints, and reads back in a counterexample as `new Map([...])` or `new Set([...])`. Its
`size`, its iteration and every change to it are refused.

### Dictionaries

A `Record<string, T>` the code is given is the array of its own entries, a key's the first that holds it, and reads back
in a counterexample as a plain object. `d[k]` is the value of `k`'s entry, `undefined` where it has none, read where its
type says it may be missing (`noUncheckedIndexedAccess`) or where a check the code made narrowed it
(`if (!d[k]) return`); with neither, it is refused, its type a claim the verifier would have to trust. Where `d` has no
entry for `k` and `k` is a name `Object.prototype` holds (`"toString"`, `"constructor"`), JavaScript finds that member,
a function: that the key is `d`'s own or none of those is an obligation, listed under `keys read:`
([Verdicts](verdicts.md)). `k in d` holds of an own key and of those names, `Object.hasOwn(d, k)` of an own key alone.
`Object.keys(d)`, `Object.values(d)` and `Object.entries(d)` list its entries as JavaScript does: each key once, the
names of array positions (`"0"`, `"12"`) first, by number, then the rest. Of an object literal the code wrote, without
a spread, they are its keys and values in that same order, a key written as a number (`1: "z"`) being the name
JavaScript gives it (`0x10` is `"16"`). Of a record the code is given whose type names its fields they are refused: it
may hold keys its type does not name.

### Narrowing

A check of a value's tag narrows it, as the type checker narrows it. A union whose members give one field different
kinds, `{ type: "add"; n: bigint } | { type: "name"; n: string }`, is held as one record per member, so `ev.n` is the
bigint once `ev.type === "add"`, and a counterexample is always one of the members. A call is narrowed by its `op` the
same way, wherever it stands: once `c.op === "set"`, `c.args[1]` is the `set`'s second argument, inside
`calls.every((c) => (c.op === "set" ? … : true))` too, where on some runs the call at that place is a `get` of one argument.
A read takes the paths on which the value can have the type the checker gives the read; no run reaches it on the others.

`"refused" in moved` reads which member a union is: a union whose members require different keys
(`{ to; action } | { refused }`) is held as one record per member too. Of an object the code built, `in` asks whether it
wrote the key; of one it is given, whether its type requires it, every value taken to hold the keys its type declares and
no other, as TypeScript's narrowing by `in` takes it, which the report lists among what it assumed. A key the type makes
optional is refused: an absent key and one holding `undefined` read alike.

A value of more than one primitive kind (`boolean | "strict" | "loose"`) is held as the kind it is and its value as each:
`typeof setting === "string"` narrows it, `===` compares it as JavaScript does (a string is no `0n`), and a
counterexample gives it as the kind it is. So is a field whose kind differs by member, read where no check of its
object's tag narrowed it.

## What it refuses, and what to write instead

Each refusal names the place, `file:line:column`, and the reason.

| Written | Refused because | Write instead |
| --- | --- | --- |
| `x as T`, `x!`, `any` | each is a claim the verifier would have to trust | a check whose result the type follows: `===`, `x !== undefined`, a `_tag` |
| `%` on `number` | not modeled | `bigint` where the values are whole, or `x & (2 ** k - 1)` for a remainder of a power of two |
| `**` of a value the code computes, bitwise operators on `bigint` | not modeled | a literal power (`2 ** 32`), shifts and masks on `number` |
| arithmetic on `number` in a declaration's laws or a guessed invariant, but on counts and small whole literals | its rounding is not modeled | the value computed in the program, or `bigint` |
| a bigint `/` or `%` by a value the code computes, inside a callback of `.some`, `.every`, `.find`, `.filter`, `.map` or `.flatMap` | which elements it runs on is not modeled | the division in a `for…of` over the elements, or outside the callback; a literal divisor (`x % 2n`) is read anywhere |
| `==`, `!=` | not modeled | `===`, `!==`, and `x === null \|\| x === undefined` for a nullish check |
| a `let` of the module, a global (`Date`, `Math.sqrt`, `JSON`) | a binding the verifier cannot see | a `const` or an argument, or a function declared with `assume` |
| a string's other methods (`split`, `replace`, `toUpperCase`), its spread `[...s]`, `indexOf(t, from)` | not modeled | the methods it reads, or a function declared with `assume` |
| `Object.is` of an object | it compares identity, which is not modeled | a field of each |
| `xs[i]` on an array, without `noUncheckedIndexedAccess` | its type says the element is there, which may be false | `noUncheckedIndexedAccess` turned on, or `xs.at(i)`, whose type says it may be missing |
| `.includes(x)` of a `number` | it finds `NaN`, which `===` does not | `.some((y) => y === x)` |
| `.reverse()` of an array something else holds | it turns that array around | `[...xs].reverse()` or `xs.toReversed()` |
| a `Map`'s or a `Set`'s `size`, its iteration, `set`, `add`, `delete`; a key that is a `number` or an object | not modeled | `has` and `get`; string keys |
| `"key" in obj` of a key the type makes optional | an absent key and one holding `undefined` read alike | `obj.key !== undefined` |
| a `Date`'s methods but `getTime()` and `valueOf()`; `new Date(x)` | not modeled | the time, `getTime()`, and arithmetic on it |
| a member of a value the type checker has not shown present | it may be missing | a check first, or `?.` |
| a field of a union whose kind differs by member, read before its tag is checked | it is no one value | a check of the tag first: `ev.type === "add" && ev.n > 0n` |
| recursion | not modeled | `assume(f, { pure: true, ensures })` |
| a package's function | the verifier does not read packages | `assume`, in the spec or a pack |
| a change to an argument, a second name for part of an object, a moved value, a change while borrowed | aliasing is kept out of the solver | build a new value and return it |
| a closure called after its function changes what it captures: a `let` assigned, an object lent to a call that may change it | a closure is read with what it captures where it is written | call it where it is written, or pass it the value; a part of a primitive kind (`step.name`) and a call of a function of the program the purity check finds pure change nothing |
| `break` or `continue` to a label, `do…while`, `for…in`, `var`, array methods that change the array but `push` | not modeled | `for…of`, `push`, a new array |
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
- **A function that implements a spec** (`const f: Implementation<S>`) needs none, and an `assume` of it is refused: its
  spec declares it (*A function that implements a spec*, below).

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
import { assume, contract } from "@emyann/tsverify"
import { digits, padding } from "./digits.ts"

export const digitsCount = assume(digits, { pure: true, ensures: { atLeastOne: ({ output }) => output >= 1n } })

export const paddingFits = contract(padding, { ensures: { atMostSeven: ({ output }) => output <= 7n } })
```

<!-- run -->
```text
$ npx tsverify src/digits.contract.ts paddingFits
✓ paddingFits  1 law  (143 ms)
  ✓ atMostSeven  (110 ms)
  trusted (declared, not proved):
    - digits: pure, checked from source (read digits); laws atLeastOne — src/digits.contract.ts:4:28
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
    - A purity check takes on trust that a property read runs no getter; that a module constant it reads is never changed by other code; that it terminates.
```

The proof of `padding` holds of the real program only if `digits` does what `atLeastOne` says. Every report lists what it trusted,
so that is never hidden; `brokenOn(assumption, inputs)`, from `@emyann/tsverify`, runs the real function on inputs and returns each
law it breaks, which is how a declaration is tested.

A declaration is in force across the whole program it is part of: the spec that declares it, and every file verified with
it.

### A function that implements a spec

A call of a function typed `Implementation<S>` takes what `S` says of it, and nothing of its body, as a caller in Dafny
takes a method's specification: each of its laws, where its `requires` holds at the call. Its own verification proves
those laws, so a caller leans on a proof, not on a declaration, and needs no `assume`. A spec the code calls is the whole
of what its callers know: what they need of the function is a law of its spec.

<!-- file: src/shipping.contract.ts -->
```ts
import { spec } from "@emyann/tsverify"

const shippingSpec = spec<(total: number) => number>({
  requires: ({ input: [total] }) => total >= 0,
  ensures: {
    freeFrom50: {
      description: "An order of 50 or more ships free",
      condition: ({ input: [total], output }) => (total >= 50 ? output === 0 : true),
    },
    smallOrdersPay: ({ input: [total], output }) => (total < 50 ? output === 5 : true),
  },
})
export type ShippingSpec = typeof shippingSpec
```

<!-- file: src/shipping.ts -->
```ts
import type { Implementation } from "@emyann/tsverify"
import type { ShippingSpec } from "./shipping.contract.ts"

export const shipping: Implementation<ShippingSpec> = (total) => (total >= 50 ? 0 : 5)
```

<!-- file: src/checkout.ts -->
```ts
import { shipping } from "./shipping.ts"

/** Whether an order ships free. */
export const shipsFree = (total: number): boolean => shipping(total) === 0
```

<!-- file: src/checkout.contract.ts -->
```ts
import { contract } from "@emyann/tsverify"
import { shipsFree } from "./checkout.ts"

export const freeExactlyFrom50 = contract(shipsFree, {
  ensures: { exactlyFrom50: ({ input: [total], output }) => output === total >= 50 },
})
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/checkout.contract.ts freeExactlyFrom50
✗ freeExactlyFrom50  1 counterexample  (315 ms)
  ✗ exactlyFrom50  (218 ms)
    e.g. (NaN)
    where shipping gave -0
    leans on ShippingSpec for shipping, not on its body: to rule this run out, meet that spec's `requires` here, or add the law it needs to the spec
  taken by their specs, each verified on its own:
    - shipping: ShippingSpec, pure, checked from source (read shipping); laws freeFrom50, smallOrdersPay — src/shipping.contract.ts:3:22
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
    - A purity check takes on trust that a property read runs no getter; that a module constant it reads is never changed by other code; that it terminates.
```

`NaN` is no total `shipping` takes: its `requires` fails, so its spec says nothing of what it gives, and the run leans on
that. The caller's `requires` meets the spec's, and the law is proved:

<!-- file: src/checkout.contract.ts -->
```ts
import { contract } from "@emyann/tsverify"
import { shipsFree } from "./checkout.ts"

export const freeExactlyFrom50 = contract(shipsFree, {
  requires: ({ input: [total] }) => total >= 0,
  ensures: { exactlyFrom50: ({ input: [total], output }) => output === total >= 50 },
})
```

<!-- run -->
```text
$ npx tsverify src/checkout.contract.ts freeExactlyFrom50
✓ freeExactlyFrom50  1 law  (581 ms)
  ✓ exactlyFrom50  (439 ms)
  taken by their specs, each verified on its own:
    - shipping: ShippingSpec, pure, checked from source (read shipping); laws freeFrom50, smallOrdersPay — src/shipping.contract.ts:3:22
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
    - A purity check takes on trust that a property read runs no getter; that a module constant it reads is never changed by other code; that it terminates.
```

The verifier reads the function's body instead, as it reads one with no spec, in two cases:

- **It leads back to the function being verified**: it calls it, or calls a function that does. Its spec would then be
  proved by leaning on itself, as two functions that call each other would each lean on the other's.
- **It is not pure**: a spec's laws speak of the result alone, and a call that changes something says more than that.

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
import { assume, contract } from "@emyann/tsverify"
import { cleaned, firstTag } from "./tags.ts"

export const cleanedIsPure = assume(cleaned, { pure: true })

export const firstOrNone = contract(firstTag, { ensures: { neverEmpty: ({ output }) => output !== "" } })
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/tags.contract.ts
src/tags.contract.ts
  ! firstOrNone  not verified
    src/tags.ts:7:58: `cleaned` is declared pure and is not: src/tags.ts:3:3: changes its argument `tags`. Declare it `pure: false`, or change it so it changes only what it allocates

! 1 not verified
  1 contract in 1 file · 0.7 s
```

It refuses an effect (`await`, `yield`, `this`, the clock, `Math.random`, the console, a module's `let`, a function it
cannot read, a method or a package function it does not know), a change to anything it did not allocate (its arguments, a
module's constants), and a cast or a type predicate, either of which would hide a value's type. A function it was given,
called or handed to a read that calls it (`xs.map(f)`), makes it pure where that function is: the check names the
arguments it calls, and a call of the declaration that passes there anything but a function that changes nothing — one
the code is given, or one it writes that the check reads as pure — is refused. It accepts a function that changes only
what it allocated, as a fold builds its state: a change to a literal or a fresh collection a local holds reaches nothing
else, and it follows each value of the caller's stored into a fresh one, by type, and refuses a change to an object that
value could reach. Two calls of a pure declaration that bind the same values give one result: a function written in
place with nothing of its scope in it is the function its text is, and a default is bound where `undefined` is passed. It takes three things on trust, and every report that
leans on it says so: a property read runs no getter, a module constant is never changed by other code, and the function
ends.

### Packs

A pack declares a library's functions once, for every spec that imports it, as Verus's `vstd` does for Rust's standard
library. `@emyann/tsverify/packs/lodash` declares `uniq` on strings and `clamp` on numbers: `import "@emyann/tsverify/packs/lodash"` in a
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
