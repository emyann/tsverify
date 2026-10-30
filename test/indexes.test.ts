// Arrays at a computed index and the arithmetic that makes it (fixtures/indexes.ts): every law proved where it holds,
// the one that leans on inexact arithmetic not proved; the laws hold when the functions run; a bug planted in each is
// caught, the planted code misbehaving when run on the input reported; and a read whose type claims the element is
// there, without `noUncheckedIndexedAccess`, refused.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import * as fixture from "../fixtures/indexes.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/indexes.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([file], tsconfig)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
type Fixture = typeof fixture
type Contract = "theLargest" | "reversesIt" | "atCounts" | "nextOfWhole"
const ARRAYS: ReadonlyArray<ReadonlyArray<bigint>> = [[], [1n], [2n, 1n], [1n, 3n, 2n], [3n, 3n, 1n], [5n, -1n, 9n, 0n, 9n]]
/** Each contract's inputs. */
const INPUTS: Readonly<Record<Contract, ReadonlyArray<ReadonlyArray<unknown>>>> = {
  theLargest: ARRAYS.map((xs) => [xs]),
  reversesIt: ARRAYS.map((xs) => [xs]),
  atCounts: [[], ["a"], ["a", "b", "c"]].flatMap((xs) => [-4, -3, -1, -0, 0, 1, 2, 3, 0.5, Number.NaN, Infinity].map((i) => [xs, i])),
  nextOfWhole: [[0], [1], [-5], [9007199254740990]],
}
/** The laws of `name` that the module `f`'s function breaks on the inputs. */
const brokenBy = (f: Fixture, name: Contract): Set<string> => {
  const c = f[name] as unknown as {
    fn: (...a: Array<unknown>) => unknown
    requires?: (...a: Array<unknown>) => boolean
    ensures: Record<string, Parameters<typeof holds>[0]>
  }
  const broken = new Set<string>()
  for (const args of INPUTS[name]) {
    if (c.requires !== undefined && !c.requires(...args)) continue
    const out = c.fn(...args)
    for (const [law, l] of Object.entries(c.ensures)) if (!(holds(l) as (...a: Array<unknown>) => boolean)(...args, out)) broken.add(law)
  }
  return broken
}

describe("arrays at a computed index, verified", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })
  for (const name of Object.keys(INPUTS))
    it(`${name}: every law proved, and every obligation`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.ok(
        v.laws.every((l) => l.status === "proved"),
        JSON.stringify(statuses(v)),
      )
      assert.ok(
        v.obligations.every((o) => o.status === "proved"),
        JSON.stringify(v.obligations.map((o) => [o.kind, o.text, o.status])),
      )
    })
  it("`i + 1` of any number is not proved: it is not exact at NaN, and the law that leans on it is not proved", async () => {
    const v = await verify(z3, project, file, "nextOfAny")
    assert.equal(v.laws[0]?.status, "bounded")
    const exact = v.obligations.find((o) => o.kind === "exact")
    assert.equal(exact?.status, "counterexample")
    assert.ok(exact?.args !== undefined && Number.isNaN(exact.args[0]))
  })
  it("without `noUncheckedIndexedAccess`, `xs[0]` is refused: its type says the element is there", async () => {
    const unchecked = path.join(root, "fixtures/unchecked/first.ts")
    const v = await verify(z3, loadProject([unchecked], path.join(root, "fixtures/unchecked/tsconfig.json")), unchecked, "firstIsA")
    assert.match(
      v.unsupported ?? "(verified)",
      /`xs\[0\]` on an array is read where its type says it may be missing: turn on `noUncheckedIndexedAccess`/,
    )
  })
  it("so is a dictionary's entry, unless its type says it may be missing", async () => {
    const unchecked = path.join(root, "fixtures/unchecked/first.ts")
    const project = loadProject([unchecked], path.join(root, "fixtures/unchecked/tsconfig.json"))
    const refused = await verify(z3, project, unchecked, "entryIsA")
    assert.match(refused.unsupported ?? "(verified)", /`t\[k\]` on a record keyed by any string .*turn on `noUncheckedIndexedAccess`/)
    const read = await verify(z3, project, unchecked, "checkedEntryIsA")
    assert.equal(read.unsupported, undefined)
    assert.deepEqual(
      read.obligations.map((o) => [o.kind, o.status]),
      [["key", "proved"]],
    )
  })
})

describe("the laws hold when the functions run", () => {
  for (const name of Object.keys(INPUTS) as Array<Contract>)
    it(name, () => {
      assert.deepEqual([...brokenBy(fixture, name)], [])
    })
})

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  readonly contract: Contract
}
const PLANTS: ReadonlyArray<Plant> = [
  {
    id: "L1",
    what: "the smallest kept in place of the largest",
    change: ["(xs[i] ?? 0n) > (xs[best] ?? 0n)", "(xs[i] ?? 0n) < (xs[best] ?? 0n)"],
    contract: "theLargest",
  },
  { id: "R1", what: "each element read one place on", change: ["= xs[i] ?? 0n", "= xs[i + 1] ?? 0n"], contract: "reversesIt" },
  { id: "A1", what: "`.at` counted the other way", change: ["return xs.at(i)", "return xs.at(-i)"], contract: "atCounts" },
  { id: "N1", what: "one taken away in place of added", change: ["return i + 1\n", "return i - 1\n"], contract: "nextOfWhole" },
]

describe("a bug planted in each", () => {
  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: caught, and the planted code breaks a law it refutes when run`, async () => {
      const original = readFileSync(file, "utf8")
      assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
      const text = original.replace(p.change[0], p.change[1])
      const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, p.contract)
      assert.equal(v.unsupported, undefined)
      const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
      assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
      const planted = path.join(root, `fixtures/indexes.planted-${p.id}.ts`)
      writeFileSync(planted, text)
      try {
        const seen = brokenBy((await import(pathToFileURL(planted).href)) as Fixture, p.contract)
        assert.ok(
          refuted.some((l) => seen.has(l)),
          `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`,
        )
      } finally {
        rmSync(planted)
      }
    })
  it("W1, a write one place past where it belongs: the write is refuted, and running it grows the array", async () => {
    const original = readFileSync(file, "utf8")
    const text = original.replace("b[n - 1 - i] = xs[i] ?? 0n", "b[n - i] = xs[i] ?? 0n")
    const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, "reversesIt")
    const write = v.obligations.find((o) => o.kind === "write")
    assert.equal(write?.status, "counterexample", JSON.stringify(v.obligations.map((o) => [o.kind, o.status])))
    assert.ok(
      v.laws.every((l) => l.status !== "proved"),
      JSON.stringify(statuses(v)),
    )
    const planted = path.join(root, "fixtures/indexes.planted-W1.ts")
    writeFileSync(planted, text)
    try {
      const f = (await import(pathToFileURL(planted).href)) as Fixture
      const xs = write?.args?.[0]
      assert.ok(Array.isArray(xs))
      assert.notEqual(f.reversed(xs as Array<bigint>).length, xs.length)
    } finally {
      rmSync(planted)
    }
  })
})
