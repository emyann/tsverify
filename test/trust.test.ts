// What the verifier takes on trust, rule by rule: a declared function's laws
// assumed at each call, a function nobody declared refused with what to write,
// a declaration of purity checked where the source is, `pure: false` fresh per
// call and kept out of laws, spec code kept from computations and the clock,
// the report's trusted base, and a declaration of a function that implements a
// spec held to that spec: its laws, and where its `requires` holds.
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

describe("a declaration of a function that implements a spec", () => {
  const CLAMP = {
    "clamp.contract.ts":
      `import { spec } from "@emyann/tsverify"\n\n` +
      `/** At most \`hi\`. */\nexport const atMostHi = (_x: bigint, hi: bigint, out: bigint): boolean => out <= hi\n\n` +
      `const clampSpec = spec<(x: bigint, hi: bigint) => bigint>({\n` +
      `  requires: (_x, hi) => hi >= 0n,\n  ensures: { atMostHi, notNegative: (_x, _hi, out) => out >= 0n },\n})\n` +
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
    return verify(z3, loadProject([f], path.join(dir, "tsconfig.json")), f, name)
  }

  it("takes the spec's own law, and only where the spec's `requires` holds at the call", async () => {
    const dir = projectOf({
      "use.ts":
        `import { assume, contract } from "@emyann/tsverify"\nimport { atMostHi } from "./clamp.contract.ts"\nimport { clamp } from "./clamp.ts"\n\n` +
        `export const clampAssumed = assume(clamp, { pure: true, ensures: { atMostHi } })\n\n` +
        `export const capped = (x: bigint): bigint => clamp(x, 10n)\n` +
        `export const cappedAtTen = contract(capped, { ensures: { atMostTen: (_x, out) => out <= 10n } })\n\n` +
        `export const anyCap = (x: bigint, hi: bigint): bigint => clamp(x, hi)\n` +
        `export const anyCapAtMostHi = contract(anyCap, { ensures: { atMostHi: (_x, hi, out) => out <= hi } })\n`,
    })
    try {
      const ten = await verified(dir, "cappedAtTen")
      assert.deepEqual(
        ten.laws.map((l) => [l.name, l.status]),
        [["atMostTen", "proved"]],
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

  it("refuses a law its spec does not ensure, written again or new, with what to write", async () => {
    const dir = projectOf({
      "use.ts":
        `import { assume, contract } from "@emyann/tsverify"\nimport { clamp } from "./clamp.ts"\n\n` +
        `export const clampAssumed = assume(clamp, { pure: true, ensures: { atMostHi: (_x, hi, out) => out <= hi } })\n\n` +
        `export const capped = (x: bigint): bigint => clamp(x, 10n)\n` +
        `export const cappedAtTen = contract(capped, { ensures: { atMostTen: (_x, out) => out <= 10n } })\n`,
    })
    try {
      const v = await verified(dir, "cappedAtTen")
      assert.deepEqual(v.laws, [])
      assert.match(v.unsupported ?? "", /`clampAssumed` assumes `atMostHi` of `clamp`, which implements `ClampSpec`/)
      assert.match(v.unsupported ?? "", /name one of them here .* or add this law to the spec's `ensures`/)
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })
})
