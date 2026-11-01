// Default values and rests (fixtures/destructuring.ts): a parameter's default, a
// default inside an object pattern, and an object rest. Every law proved; the
// laws hold when the functions run, on inputs that leave each default out, give
// it as `undefined`, and give a value; and a bug planted in each is caught, the
// planted code breaking a law it refutes when run. A default taken where an
// argument is `undefined`, and not only where it is left out, is what made the
// first plant catchable: before, `n: bigint = 5n` was proved to give 2n.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { Effect, Layer } from "effect"
import * as fixture from "../fixtures/destructuring.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/destructuring.ts")
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
const user: fixture.User = { id: "u-1", name: "Ada", secret: "s3cret" }

/** Each contract's runs: the arguments its laws take, and what running its function on them gave, with the calls it made. */
const RUNS = {
  nextOfOne: (f: Fixture) => [undefined, 0n, 7n].map((n) => ({ args: [n], out: f.next(n) })),
  pageOfTwenty: (f: Fixture) => [undefined, {}, { size: undefined }, { size: 5n }].map((o) => ({ args: [o], out: f.pageSize(o) })),
  labelOrNone: (f: Fixture) =>
    [{}, { label: undefined }, { label: null }, { label: "" }, { label: "x" }].map((item) => ({ args: [item], out: f.labelled(item) })),
  shownWithoutTheSecret: (f: Fixture) => [{ args: [user], out: f.shown(user) }],
  renamedKeepsTheSecret: (f: Fixture) => ["Grace", ""].map((name) => ({ args: [user, name], out: f.renamed(user, name) })),
  listedTen: async (f: Fixture) => {
    const runs = []
    for (const o of [undefined, {}, { limit: undefined }, { limit: 3n }]) {
      const calls: Array<{ op: "list"; args: ReadonlyArray<unknown>; outcome: { _tag: "Success"; value: ReadonlyArray<string> } }> = []
      const store = fixture.Store.of({
        list: (prefix, limit) => {
          calls.push({ op: "list", args: [prefix, limit], outcome: { _tag: "Success", value: [] } })
          return Effect.succeed([])
        },
      })
      const value = await Effect.runPromise(f.listed("k/", o).pipe(Effect.provide(Layer.succeed(fixture.Store)(store))))
      runs.push({ args: ["k/", o], out: { _tag: "Success", value }, calls })
    }
    return runs
  },
} as const
type Contract = keyof typeof RUNS

/** The laws of `name` that its function breaks on its runs, run from `f`. */
const brokenBy = async (f: Fixture, name: Contract): Promise<Set<string>> => {
  const broken = new Set<string>()
  const laws = (fixture[name] as unknown as { ensures: Record<string, Parameters<typeof holds>[0]> }).ensures
  for (const r of await RUNS[name](f)) {
    const run = "calls" in r ? { input: r.args, output: r.out, calls: r.calls } : { input: r.args, output: r.out }
    for (const [law, l] of Object.entries(laws)) if (!(holds(l) as (run: unknown) => boolean)(run)) broken.add(law)
  }
  return broken
}

describe("defaults and rests, verified", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })
  for (const name of Object.keys(RUNS))
    it(`${name}: every law proved`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.ok(
        v.laws.every((l) => l.status === "proved"),
        JSON.stringify(statuses(v)),
      )
    })
  it("a rest is taken to copy plain data, as the report says", async () => {
    const v = await verify(z3, project, file, "shownWithoutTheSecret")
    assert.ok(v.notes.some((n) => /object rest copies each property but those named/.test(n)))
  })
})

describe("the laws hold when the functions run", () => {
  for (const name of Object.keys(RUNS) as Array<Contract>)
    it(name, async () => {
      assert.deepEqual([...(await brokenBy(fixture, name))], [])
    })
})

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  readonly contract: Contract
}
const PLANTS: ReadonlyArray<Plant> = [
  { id: "D1", what: "a parameter's default changed", change: ["n: bigint = 1n", "n: bigint = 5n"], contract: "nextOfOne" },
  { id: "D2", what: "a default in a parameter's pattern changed", change: ["{ size = 20n }", "{ size = 21n }"], contract: "pageOfTwenty" },
  {
    id: "D3",
    what: "a default in a `const`'s pattern changed",
    change: ['{ label = "none" }', '{ label = "None" }'],
    contract: "labelOrNone",
  },
  {
    id: "R1",
    what: "the rest of a record the code built, its secret blanked",
    change: ["= { ...user, name }", '= { ...user, name, secret: "" }'],
    contract: "renamedKeepsTheSecret",
  },
  {
    id: "R2",
    what: "a spread after the rest's key: the old name wins",
    change: ["= { ...user, name }", "= { name, ...user }"],
    contract: "renamedKeepsTheSecret",
  },
  {
    id: "C1",
    what: "a computation's default in its pattern changed",
    change: ["{ limit = 10n }", "{ limit = 100n }"],
    contract: "listedTen",
  },
  {
    id: "C2",
    what: "a computation's parameter defaulted to a limit of its own",
    change: ["{ limit?: bigint } = {}", "{ limit?: bigint } = { limit: 5n }"],
    contract: "listedTen",
  },
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
      const planted = path.join(root, `fixtures/destructuring.planted-${p.id}.ts`)
      writeFileSync(planted, text)
      try {
        const seen = await brokenBy((await import(pathToFileURL(planted).href)) as Fixture, p.contract)
        assert.ok(
          refuted.some((l) => seen.has(l)),
          `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`,
        )
      } finally {
        rmSync(planted)
      }
    })
})
