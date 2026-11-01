// A ternary of two computations (fixtures/chosen.ts): the one taken runs, the
// other leaves nothing. Every law proved; the laws hold when the functions run,
// on a store that has every key and on one that has none; and a bug planted in
// each choice is caught, the planted code breaking a law it refutes when run.
// Before, a choice of two computations was refused, whatever its laws.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import * as fixture from "../fixtures/chosen.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/chosen.ts")
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
type Out = { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: unknown }
type Call = { readonly op: "get"; readonly args: ReadonlyArray<unknown>; readonly outcome: Out }

/** A store that has every key, or none, and the calls made of it. */
const storeOf = (f: Fixture, has: boolean) => {
  const calls: Array<Call> = []
  const store: fixture.Store = {
    get: async (key) => {
      const outcome: Out = has ? { _tag: "Success", value: `${key}'s value` } : { _tag: "Failure", error: new f.Missing(key) }
      calls.push({ op: "get", args: [key], outcome })
      if (outcome._tag === "Failure") throw outcome.error
      return `${key}'s value`
    },
  }
  return { store, calls }
}
const ended = async (p: Promise<unknown>): Promise<Out> => {
  try {
    return { _tag: "Success", value: await p }
  } catch (error) {
    return { _tag: "Failure", error }
  }
}

/** Each contract's runs: its laws' arguments, what the function gave, and the calls it made. */
const RUNS = {
  pick: async (f: Fixture) => {
    const runs = []
    for (const has of [true, false])
      for (const primary of [true, false]) {
        const { store, calls } = storeOf(f, has)
        runs.push({ args: [store, primary, "k"], out: await ended(f.pick(store, primary, "k")), calls })
      }
    return runs
  },
  from: async (f: Fixture) => {
    const runs = []
    for (const has of [true, false])
      for (const primary of [true, false])
        for (const backup of [true, false]) {
          const { store, calls } = storeOf(f, has)
          runs.push({ args: [store, primary, backup, "k"], out: await ended(f.from(store, primary, backup, "k")), calls })
        }
    return runs
  },
} as const
type Contract = keyof typeof RUNS
/** The laws of `name`'s spec, as the module `f` declares them. */
const lawsOf = (f: Fixture, name: Contract) =>
  (f[`${name}Spec`] as unknown as { ensures: Record<string, Parameters<typeof holds>[0]> }).ensures

/** The laws of `name` its function breaks on its runs, the function and its laws both read from `f`. */
const brokenBy = async (f: Fixture, name: Contract): Promise<Set<string>> => {
  const broken = new Set<string>()
  for (const r of await RUNS[name](f))
    for (const [law, l] of Object.entries(lawsOf(f, name)))
      if (!(holds(l) as (run: unknown) => boolean)({ input: r.args, output: r.out, calls: r.calls })) broken.add(law)
  return broken
}

describe("a choice of two computations, verified", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })
  for (const name of Object.keys(RUNS))
    it(`${name}: every law proved`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.ok(v.laws.length > 0 && v.laws.every((l) => l.status === "proved"), JSON.stringify(statuses(v)))
    })
})

describe("the laws hold when the functions run", () => {
  for (const name of Object.keys(RUNS) as Array<Contract>)
    it(`${name}, on a store that has every key and on one that has none`, async () => {
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
  {
    id: "P1",
    what: "the two sides of the choice swapped",
    change: [
      'primary ? store.get(key) : store.get("backup/" + key)\n  return',
      '!primary ? store.get(key) : store.get("backup/" + key)\n  return',
    ],
    contract: "pick",
  },
  {
    id: "P2",
    what: "the side not taken reads the same key",
    change: ['primary ? store.get(key) : store.get("backup/" + key)\n  return', "primary ? store.get(key) : store.get(key)\n  return"],
    contract: "pick",
  },
  {
    id: "F1",
    what: "the nested choice's sides swapped",
    change: [
      'backup ? store.get("backup/" + key) : store.get("last/" + key)',
      'backup ? store.get("last/" + key) : store.get("backup/" + key)',
    ],
    contract: "from",
  },
]

describe("a bug planted in each choice", () => {
  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: caught, and the planted code breaks a law it refutes when run`, async () => {
      const original = readFileSync(file, "utf8")
      assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
      const text = original.replace(p.change[0], p.change[1])
      const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, p.contract)
      assert.equal(v.unsupported, undefined)
      const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
      assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
      const planted = path.join(root, `fixtures/chosen.planted-${p.id}.ts`)
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
