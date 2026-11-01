// What the verifier takes on trust, rule by rule: a declared function's laws
// assumed at each call, a function nobody declared refused with what to write,
// a declaration of purity checked where the source is, `pure: false` fresh per
// call and kept out of laws, spec code kept from computations and the clock,
// the report's trusted base, and a function that implements a spec taken by
// that spec at each call: its laws, where its `requires` holds, with no
// `assume`, and its body read where the spec would close a loop or it is not
// pure.
import assert from "node:assert/strict"
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { verify, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/trusted.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const run = (name: string) => verify(z3, project, file, name)

it("the fixture type-checks", () => {
  assert.deepEqual(diagnostics(project, file), [])
})

describe("a declared function", () => {
  it("its law holds of every element of a quantifier, and the report names it as trusted, its purity checked", async () => {
    const v = await run("everyScoreNonNegative")
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["always", "proved"]],
    )
    assert.deepEqual(v.trusted, [
      { name: "score", declared: [v.trusted[0]!.declared[0]], purity: "checked", laws: ["nonNegative"], read: ["score"] },
    ])
    assert.match(v.trusted[0]!.declared[0]!, /fixtures\/trusted\.ts:\d+/)
  })

  it("what its laws do not say is not proved, and the counterexample says it leans on it", async () => {
    const v = await run("everyScorePositive")
    const law = v.laws[0]!
    assert.equal(law.status, "counterexample")
    assert.deepEqual(law.abstract, ["score"])
  })

  it("`pure: false`: each call its own result", async () => {
    const v = await run("twoReadsAgree")
    assert.equal(v.laws[0]!.status, "counterexample")
    assert.equal(v.trusted[0]!.purity, "impure")
  })
})

describe("refused, with what to write instead", () => {
  const cases: ReadonlyArray<readonly [string, RegExp]> = [
    [
      "undeclared",
      /`total` is not read \(`Math` is a binding the verifier cannot see.*\): declare what the verifier may assume of it, `assume\(total, \{ pure: true/,
    ],
    ["stamped", /`stamp` is declared pure and is not: .*changes its argument `log`\. Declare it `pure: false`/],
    ["appliedToATick", /`applied` is pure where the functions it is given are, and `tick` may change something: .*changes `ticks`/],
    [
      "uncovered",
      /`uniq \(lodash-es\)` is called with \(readonly number\[\]\), which no declaration covers: \(readonly string\[\]\) at packs\/lodash\.ts/,
    ],
    ["otherForm", /`clamp \(lodash-es\)` is called with \(number, 10\), which no declaration covers: \(number, number, number\)/],
    ["undeclaredPackage", /`compact` is a package's, which the verifier does not read: declare .*`assume\(compact/],
  ]
  for (const [name, why] of cases)
    it(name, async () => {
      const v = await run(name)
      assert.match(v.unsupported ?? "(verified)", why)
    })
})

it("a pure function given the same function twice, written alike, is called once", async () => {
  const v = await run("appliedTwice")
  assert.deepEqual(
    v.laws.map((l) => [l.name, l.status]),
    [["same", "proved"]],
  )
})

describe("spec code", () => {
  const laws: ReadonlyArray<readonly [string, RegExp]> = [
    ["lawReadsTheClockThroughADeclaration", /spec code is deterministic, and `nowMs` is declared `pure: false`/],
    ["lawReadsTheClock", /spec code is deterministic and does not read the clock/],
    ["lawRunsAComputation", /spec code runs no computation: `fetchOne` is one/],
  ]
  for (const [name, why] of laws)
    it(name, async () => {
      const v = await run(name)
      assert.equal(v.laws[0]!.status, "unsupported")
      assert.match(v.laws[0]!.reason ?? "", why)
    })

  it("reads what the program computed with the clock: a binding keeps the mode of the code that wrote it", async () => {
    const v = await run("stampedNow")
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["keeps", "proved"]],
    )
  })
})

describe("a function that implements a spec", () => {
  const CLAMP = {
    "clamp.contract.ts":
      `import { spec } from "@emyann/tsverify"\n\n` +
      `const clampSpec = spec<(x: bigint, hi: bigint) => bigint>({\n` +
      `  requires: ({ input: [, hi] }) => hi >= 0n,\n` +
      `  ensures: {\n    atMostHi: { description: "A clamped value is at most hi", condition: ({ input: [, hi], output }) => output <= hi },\n` +
      `    notNegative: ({ output }) => output >= 0n,\n  },\n})\n` +
      `export type ClampSpec = typeof clampSpec\n`,
    "clamp.ts":
      `import type { Implementation } from "@emyann/tsverify"\nimport type { ClampSpec } from "./clamp.contract.ts"\n\n` +
      `export const clamp: Implementation<ClampSpec> = (x, hi) => (x < 0n ? 0n : x > hi ? hi : x)\n`,
  }
  /** A project of its own under `.docs/`, a dot folder no command scans, importing `@emyann/tsverify` through this package's condition. */
  const projectOf = (files: Readonly<Record<string, string>>): string => {
    mkdirSync(path.join(root, ".docs"), { recursive: true })
    const dir = mkdtempSync(path.join(root, ".docs", "trust-"))
    const compilerOptions = {
      module: "nodenext",
      strict: true,
      noEmit: true,
      allowImportingTsExtensions: true,
      customConditions: ["tsverify-source"],
    }
    writeFileSync(path.join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions }))
    for (const [name, text] of Object.entries({ ...CLAMP, ...files })) writeFileSync(path.join(dir, name), text)
    return dir
  }
  const verified = async (dir: string, name: string) => {
    const f = path.join(dir, "use.ts")
    const p = loadProject([f], path.join(dir, "tsconfig.json"))
    assert.deepEqual(diagnostics(p, f), [])
    return verify(z3, p, f, name)
  }

  it("a call takes the spec's laws, with no `assume`, only where the spec's `requires` holds", async () => {
    const dir = projectOf({
      "use.ts":
        `import { contract } from "@emyann/tsverify"\nimport { clamp } from "./clamp.ts"\n\n` +
        `export const capped = (x: bigint): bigint => clamp(x, 10n)\n` +
        `export const cappedAtTen = contract(capped, { ensures: { atMostTen: ({ output }) => output <= 10n } })\n\n` +
        `export const anyCap = (x: bigint, hi: bigint): bigint => clamp(x, hi)\n` +
        `export const anyCapAtMostHi = contract(anyCap, { ensures: { atMostHi: ({ input: [, hi], output }) => output <= hi } })\n`,
    })
    try {
      const ten = await verified(dir, "cappedAtTen")
      assert.deepEqual(
        ten.laws.map((l) => [l.name, l.status]),
        [["atMostTen", "proved"]],
      )
      assert.deepEqual(
        ten.trusted.map((t) => [t.name, t.spec, t.purity, t.laws]),
        [["clamp", "ClampSpec", "checked", ["atMostHi", "notNegative"]]],
      )
      // `hi` may be negative here, where the spec proves nothing of `clamp`: the law is not taken, and its run is shown.
      const any = await verified(dir, "anyCapAtMostHi")
      const law = any.laws[0]!
      assert.equal(law.status, "counterexample", JSON.stringify(law.reason))
      assert.ok((law.args![1] as bigint) < 0n, String(law.args))
      assert.deepEqual(law.abstract, ["clamp"])
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("what the spec does not say is not taken from the body", async () => {
    const dir = projectOf({
      "use.ts":
        `import { contract } from "@emyann/tsverify"\nimport { clamp } from "./clamp.ts"\n\n` +
        `export const capped = (x: bigint): bigint => clamp(x, 10n)\n` +
        `export const inRangeKept = contract(capped, {\n  requires: ({ input: [x] }) => x >= 0n && x <= 10n,\n` +
        `  ensures: { kept: ({ input: [x], output }) => output === x },\n})\n`,
    })
    try {
      const law = (await verified(dir, "inRangeKept")).laws[0]!
      assert.equal(law.status, "counterexample", JSON.stringify(law.reason))
      assert.deepEqual(law.abstract, ["clamp"])
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("an `assume` of it is refused, with what to write instead", async () => {
    const dir = projectOf({
      "use.ts":
        `import { assume, contract } from "@emyann/tsverify"\nimport { clamp } from "./clamp.ts"\n\n` +
        `export const clampAssumed = assume(clamp, { pure: true, ensures: { atMostHi: ({ input: [, hi], output }) => output <= hi } })\n\n` +
        `export const capped = (x: bigint): bigint => clamp(x, 10n)\n` +
        `export const cappedAtTen = contract(capped, { ensures: { atMostTen: ({ output }) => output <= 10n } })\n`,
    })
    try {
      const v = await verified(dir, "cappedAtTen")
      assert.deepEqual(v.laws, [])
      assert.match(v.unsupported ?? "", /`clamp` implements `ClampSpec`, and every call takes what that spec proves of it/)
      assert.match(v.unsupported ?? "", /remove `clampAssumed`/)
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("a law with branches of its own holds at a call the code does not reach on every run", async () => {
    const dir = projectOf({
      "use.ts":
        `import { contract, type Implementation, spec } from "@emyann/tsverify"\n\n` +
        `const pickSpec = spec<(s: boolean) => number>({\n  ensures: {\n` +
        `    oneWhenNot: ({ input: [s], output }) => {\n      if (s) return true\n      return output === 1\n    },\n` +
        `    twoWhenSo: ({ input: [s], output }) => !s || output === 2,\n  },\n})\n` +
        `export type PickSpec = typeof pickSpec\n` +
        `export const pick: Implementation<PickSpec> = (s) => (s ? 2 : 1)\n\n` +
        `export const zeroWhenSo = (s: boolean): number => (s ? 0 : pick(s))\n` +
        `export const zeroed = contract(zeroWhenSo, { ensures: { zero: ({ input: [s], output }) => !s || output === 0 } })\n`,
    })
    try {
      const v = await verified(dir, "zeroed")
      assert.deepEqual(
        v.laws.map((l) => [l.name, l.status]),
        [["zero", "proved"]],
      )
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("its laws are read only where its spec's `requires` holds: a key they read is the spec's to keep", async () => {
    const dir = projectOf({
      "use.ts":
        `import { contract, type Implementation, spec } from "@emyann/tsverify"\n\n` +
        `type Counts = Readonly<Record<string, number | undefined>>\n` +
        `const countSpec = spec<(counts: Counts, key: string) => number>({\n` +
        `  requires: ({ input: [counts, key] }) => Object.hasOwn(counts, key),\n` +
        `  ensures: { itsCount: ({ input: [counts, key], output }) => output === (counts[key] ?? 0) },\n})\n` +
        `export type CountSpec = typeof countSpec\n` +
        `export const count: Implementation<CountSpec> = (counts, key) => counts[key] ?? 0\n\n` +
        `export const counted = (counts: Counts, key: string): number => count(counts, key)\n` +
        `export const countedOwn = contract(counted, {\n` +
        `  ensures: { itsOwn: ({ input: [counts, key], output }) => !Object.hasOwn(counts, key) || output === (counts[key] ?? 0) },\n})\n`,
    })
    try {
      const v = await verified(dir, "countedOwn")
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(
        v.laws.map((l) => [l.name, l.status]),
        [["itsOwn", "proved"]],
      )
      assert.deepEqual(
        v.obligations.map((o) => [o.kind, o.status]),
        [["key", "proved"]],
      )
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("its body is read where its spec would close a loop: two functions that call each other", async () => {
    const parity = (name: string, other: string, zero: string) =>
      `const ${name}Spec = spec<(n: bigint) => boolean>({\n  requires: ({ input: [n] }) => n >= 0n,\n` +
      `  ensures: { atZero: ({ input: [n], output }) => n !== 0n || output === ${zero} },\n})\n` +
      `export type ${name[0]!.toUpperCase()}${name.slice(1)}Spec = typeof ${name}Spec\n` +
      `export const ${name}: Implementation<${name[0]!.toUpperCase()}${name.slice(1)}Spec> = (n) => (n === 0n ? ${zero} : ${other}(n - 1n))\n`
    const dir = projectOf({
      "use.ts":
        `import { type Implementation, spec } from "@emyann/tsverify"\n\n` +
        parity("isEven", "isOdd", "true") +
        parity("isOdd", "isEven", "false"),
    })
    try {
      const v = await verified(dir, "isEven")
      assert.match(v.unsupported ?? "(verified)", /recursion is not modeled/)
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })
})
