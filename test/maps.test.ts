// A map the code builds at keys it computes (fixtures/maps.ts): Nemia's `inheritedLabels`, copied as it is written. Its
// laws are left bounded or unknown, never refuted on the code as written, and two laws that do not hold are refuted, each
// counterexample breaking the law when the code runs on it. Each construct it takes is checked against JavaScript on its
// own, in a process of its own (`maps-constructs.test.ts`).
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as fixture from "../fixtures/maps.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/maps.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([file], tsconfig)
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

/**
 * What the contract is verified with: the search side's arrays of one element, and a third of a query's usual work.
 * At two elements the search side runs out of work on this function; with the usual work, the queries that do not end
 * hold enough of Z3's memory, one after another, to run it out.
 */
const SETTINGS = { bound: 1, work: 5_000_000, cover: false } as const

type Start = Parameters<typeof fixture.inheritedLabels>[0]
type Contract = typeof fixture.inheritedLabelsLaws | typeof fixture.inheritedLabelsWrong
type Law = (run: { readonly input: ReadonlyArray<unknown>; readonly output: unknown }) => boolean

/** Whether running `inherited` on `args` breaks `law` of `contract`, `requires` holding there. */
const breaks = (contract: Contract, inherited: (s: Start) => fixture.Inherited, law: string, args: ReadonlyArray<unknown>): boolean => {
  const [start] = args as [Start]
  assert.ok(contract.requires?.({ input: [start] }) ?? true, "the counterexample meets `requires`")
  const l = (contract.ensures as Record<string, Parameters<typeof holds>[0]>)[law]!
  return !(holds(l) as Law)({ input: [start], output: inherited(start) })
}

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("inheritedLabels, as Nemia writes it", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("no law is refuted on the code as written: each is bounded or unknown", async () => {
    const v = await verify(z3, project, file, "inheritedLabelsLaws", SETTINGS)
    assert.equal(v.unsupported, undefined)
    assert.equal(v.laws.length, 8)
    for (const l of v.laws) assert.ok(["bounded", "unknown"].includes(l.status), `${l.name}: ${l.status}`)
    assert.ok(
      v.obligations.every((o) => o.status === "proved"),
      JSON.stringify(v.obligations),
    )
  })

  it("two laws that do not hold are refuted", async () => {
    const w = await verify(z3, project, file, "inheritedLabelsWrong", SETTINGS)
    assert.deepEqual(statuses(w), { typedNeverHeld: "counterexample", agreedNeverHeld: "counterexample" })
    for (const l of w.laws) assert.ok(breaks(fixture.inheritedLabelsWrong, fixture.inheritedLabels, l.name, l.args ?? []), l.name)
  })
})
