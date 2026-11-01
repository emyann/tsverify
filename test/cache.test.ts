// What a run asks the solver. The cover only when asked for: without it, the laws' verdicts are the same. And with a
// folder of verdicts (`src/cache.ts`), a contract verified before is answered from it: a run again verifies nothing and
// gives the same verdicts; a change to a file verifies again each contract whose program reads it, and only those, and
// gives the counterexample the change brings; that counterexample comes back as it was; a counterexample's values,
// whatever their kind, are kept as they were; and a verdict the solver ran out of work on is not kept.
import assert from "node:assert/strict"
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { verdictsIn, type Cache } from "../src/cache.ts"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

/** A verdict with nothing in it but `parts`. */
const verdict = (parts: Partial<Verification>): Verification => ({
  contract: "c",
  laws: [],
  cover: [],
  notes: [],
  trusted: [],
  obligations: [],
  ...parts,
})

/** The laws as a report gives them, without their times. */
const verdicts = (v: Verification) => v.laws.map(({ ms: _, ...l }) => l)

/** A cache in `dir` that counts what it is asked. */
const counting = (dir: string) => {
  const inner = verdictsIn(dir)
  const asked = { hits: 0, misses: 0, kept: 0 }
  const cache: Cache = {
    get: (key) => {
      const a = inner.get(key)
      if (a === undefined) asked.misses++
      else asked.hits++
      return a
    },
    set: (key, answer) => {
      asked.kept++
      inner.set(key, answer)
    },
  }
  return { cache, asked }
}

/** A project of its own under `.docs/`, a dot folder no command scans, importing `@emyann/tsverify` through this package's condition. */
const project = (files: Readonly<Record<string, string>>): string => {
  mkdirSync(path.join(root, ".docs"), { recursive: true })
  const dir = mkdtempSync(path.join(root, ".docs", "cache-"))
  const compilerOptions = {
    module: "nodenext",
    strict: true,
    noEmit: true,
    allowImportingTsExtensions: true,
    customConditions: ["tsverify-source"],
  }
  writeFileSync(path.join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions }))
  for (const [name, text] of Object.entries(files)) writeFileSync(path.join(dir, name), text)
  return dir
}

const math = (clampBody: string) =>
  `/** \`x\`, kept between \`lo\` and \`hi\`. */\nexport const clamp = (x: bigint, lo: bigint, hi: bigint): bigint => ${clampBody}\n\n` +
  `/** Twice \`x\`. */\nexport const twice = (x: bigint): bigint => x * 2n\n`
const FILES = {
  "math.ts": math("(x < lo ? lo : x > hi ? hi : x)"),
  "grade.ts":
    `import { contract } from "@emyann/tsverify"\n\n` +
    `export const grade = (x: bigint): "low" | "high" => (x < 50n ? "low" : "high")\n\n` +
    `export const gradeIsLowBelowFifty = contract(grade, { ensures: { low: (x, out) => x >= 50n || out === "low" } })\n`,
  "score.contract.ts":
    `import { spec } from "@emyann/tsverify"\n\n` +
    `const scoreSpec = spec<(x: bigint) => bigint>({ ensures: { inRange: (_x, out) => out >= 0n && out <= 100n } })\n` +
    `export type ScoreSpec = typeof scoreSpec\n`,
  "score.ts":
    `import type { Implementation } from "@emyann/tsverify"\nimport { clamp } from "./math.ts"\nimport type { ScoreSpec } from "./score.contract.ts"\n\n` +
    `export const score: Implementation<ScoreSpec> = (x) => clamp(x, 0n, 100n)\n`,
  "even.contract.ts":
    `import { spec } from "@emyann/tsverify"\n\n` +
    `const evenSpec = spec<(x: bigint) => bigint>({ ensures: { even: (_x, out) => out % 2n === 0n } })\n` +
    `export type EvenSpec = typeof evenSpec\n`,
  "even.ts":
    `import type { Implementation } from "@emyann/tsverify"\nimport type { EvenSpec } from "./even.contract.ts"\n\n` +
    `export const even: Implementation<EvenSpec> = (x) => x * 2n\n`,
}

describe("the cover", () => {
  it("is left out when not asked for, and the laws' verdicts are the same", async () => {
    const dir = project(FILES)
    try {
      const file = path.join(dir, "grade.ts")
      const p = loadProject([file], path.join(dir, "tsconfig.json"))
      const asked = await verify(z3, p, file, "gradeIsLowBelowFifty")
      const not = await verify(z3, p, file, "gradeIsLowBelowFifty", { cover: false })
      assert.deepEqual(
        asked.cover.map((c) => [c.value, c.status]),
        [
          ["low", "reachable"],
          ["high", "reachable"],
        ],
      )
      assert.deepEqual(not.cover, [])
      assert.deepEqual(verdicts(not), verdicts(asked))
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })
})

describe("a folder of answers", () => {
  it("answers a run again from the folder; a change verifies again only what reads it, and gives its counterexample", async () => {
    const dir = project(FILES)
    const answers = mkdtempSync(path.join(tmpdir(), "tsverify-answers-"))
    try {
      const tsconfig = path.join(dir, "tsconfig.json")
      const run = async (name: "score" | "even") => {
        const file = path.join(dir, `${name}.ts`)
        const { cache, asked } = counting(answers)
        const v = await verify(z3, loadProject([file], tsconfig), file, name, { cache })
        return { v, asked }
      }

      const first = { score: await run("score"), even: await run("even") }
      for (const r of Object.values(first)) {
        assert.deepEqual(
          r.v.laws.map((l) => l.status),
          ["proved"],
        )
        assert.deepEqual(r.asked, { hits: 0, misses: 1, kept: 1 })
      }

      // The same code again: each contract answered from the folder, the same verdict.
      for (const name of ["score", "even"] as const) {
        const again = await run(name)
        assert.deepEqual(again.asked, { hits: 1, misses: 0, kept: 0 })
        assert.deepEqual(verdicts(again.v), verdicts(first[name].v))
        assert.deepEqual(again.v.cover, first[name].v.cover)
      }

      // `clamp` broken in the module `score` imports: `score` is verified again, `even`, whose program does not read it, is not.
      writeFileSync(path.join(dir, "math.ts"), math("(x < lo ? lo : x > hi ? hi + 1n : x)"))
      const broken = await run("score")
      assert.deepEqual(broken.asked, { hits: 0, misses: 1, kept: 1 })
      const law = broken.v.laws[0]!
      assert.equal(law.status, "counterexample")
      const [x] = law.args as [bigint]
      assert.ok(x > 100n, String(x))
      const untouched = await run("even")
      assert.deepEqual(untouched.asked, { hits: 1, misses: 0, kept: 0 })
      assert.deepEqual(verdicts(untouched.v), verdicts(first.even.v))

      // The broken one again: its counterexample answered from the folder, as it was found.
      const twiceBroken = await run("score")
      assert.deepEqual(twiceBroken.asked, { hits: 1, misses: 0, kept: 0 })
      assert.deepEqual(verdicts(twiceBroken.v), verdicts(broken.v))
    } finally {
      rmSync(dir, { recursive: true, force: true })
      rmSync(answers, { recursive: true, force: true })
    }
  })

  it("keeps a counterexample's values as they were, of every kind a model is read back as", () => {
    const answers = mkdtempSync(path.join(tmpdir(), "tsverify-verdicts-"))
    try {
      const own: Record<string, unknown> = {}
      Object.defineProperty(own, "__proto__", { value: 1n, enumerable: true, writable: true, configurable: true })
      const args = [
        Number.NaN,
        -0,
        Number.POSITIVE_INFINITY,
        2.5,
        12n,
        undefined,
        null,
        "~set",
        ["~set", "a tag's word in an array"],
        new Map<unknown, unknown>([[1n, { a: [true] }]]),
        new Set(["x"]),
        new Date(Number.NaN),
        new Date(86_400_000),
        own,
      ]
      const world = { "clock!0": 3, "rows!1": { _tag: "Success", value: [] } }
      const law = { name: "inRange", status: "counterexample" as const, args, world, abstract: ["uniq"], ms: 1 }
      const cache = verdictsIn(answers)
      cache.set("k", verdict({ laws: [law] }))
      const back = cache.get("k")
      assert.deepEqual(back, verdict({ laws: [law] }))
      const kept = back?.laws[0]?.args?.[13]
      assert.ok(typeof kept === "object" && kept !== null && Object.hasOwn(kept, "__proto__"))

      cache.set("s", verdict({ laws: [{ ...law, args: [Symbol("tsverify"), () => undefined] }] }))
      const [symbol, fn] = cache.get("s")!.laws[0]!.args!
      assert.equal(typeof symbol, "symbol")
      assert.equal(typeof fn, "function")
    } finally {
      rmSync(answers, { recursive: true, force: true })
    }
  })

  it("keeps no verdict the solver ran out of work on, and reads nothing for a key never kept", () => {
    const answers = mkdtempSync(path.join(tmpdir(), "tsverify-verdicts-"))
    try {
      const cache = verdictsIn(answers)
      const unknown = { name: "l", status: "unknown" as const, reason: "out of work", ms: 1 }
      cache.set("law", verdict({ laws: [unknown] }))
      cache.set("cover", verdict({ cover: [{ value: "low", status: "unknown" }] }))
      cache.set(
        "obligation",
        verdict({ obligations: [{ kind: "division", text: "x / y", at: "a.ts:1:1", phase: "here", status: "unknown" }] }),
      )
      for (const key of ["law", "cover", "obligation", "never"]) assert.equal(cache.get(key), undefined, key)
      cache.set("proved", verdict({ laws: [{ name: "l", status: "proved", ms: 1 }] }))
      assert.deepEqual(cache.get("proved"), verdict({ laws: [{ name: "l", status: "proved", ms: 1 }] }))
    } finally {
      rmSync(answers, { recursive: true, force: true })
    }
  })
})
