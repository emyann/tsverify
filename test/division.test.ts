// Bigint `/` and `%` (fixtures/division.ts): the lowering computes what
// JavaScript computes, on both sides; a divisor is proved other than 0n on the
// branch where its division runs, through every form a branch takes; one that
// may be 0n is shown with an input, on which the real code throws; a law is
// judged on the runs that return, and a law that divides by 0n does not hold.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as division from "../fixtures/division.ts"
import { diagnostics, loadProject, readContract } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { disagreements, lowerSide, openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/division.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const divisions = (v: Verification) => v.obligations.filter((o) => o.kind === "division")

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("bigint division", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  // Every sign of each, and a divisor of 0n, which the code steps around.
  const pairs = [-7n, -6n, -5n, -1n, 0n, 1n, 5n, 6n, 7n].flatMap((a) => [-3n, -2n, -1n, 0n, 1n, 2n, 3n].map((b) => [a, b] as const))
  for (const name of ["quotient", "remainder"] as const)
    it(`${name}: the lowering computes what JavaScript computes, on both sides, and its law is proved`, async () => {
      const real = division[name].fn
      const run = ([a, b]: ReadonlyArray<unknown>) => real(a as bigint, b as bigint)
      for (const bound of [undefined, 4])
        assert.deepEqual(await disagreements(lowerSide(z3, project, readContract(project, file, name), bound), pairs, run), [])
      const v = await verify(z3, project, file, name)
      assert.ok(v.laws.every((l) => l.status === "proved") && divisions(v).every((o) => o.status === "proved"), JSON.stringify(v.laws))
    })

  const guarded = ["byConditional", "byAnd", "byOr", "byNullish", "byIf", "byField", "byLoop", "byCompound", "perItemGuarded"]
  for (const name of guarded)
    it(`${name}: the divisor is proved other than 0n on the branch where it runs`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.equal(divisions(v).length, 1)
      assert.deepEqual(
        divisions(v).map((o) => o.status),
        ["proved"],
      )
      assert.ok(
        Object.values(statuses(v)).every((s) => s === "proved"),
        JSON.stringify(statuses(v)),
      )
    })

  it("a divisor that may be 0n is shown with the input, on which the real code throws; the law holds of the runs that return", async () => {
    const v = await verify(z3, project, file, "unguarded")
    const [d] = divisions(v)
    assert.equal(d?.status, "counterexample")
    const [a, b] = d.args as [bigint, bigint]
    assert.equal(b, 0n)
    assert.throws(() => division.unguarded.fn(a, b), RangeError)
    assert.deepEqual(statuses(v), { atMostA: "proved" })
  })

  it("after a step: the divisor the step gave is shown with the run, which throws when it is run", async () => {
    const v = await verify(z3, project, file, "perItemUnguarded")
    const [d] = divisions(v)
    assert.equal(d?.status, "counterexample")
    const given = Object.entries(d.world ?? {}).map(([k, x]) => [k.replace(/!\d+$/, ""), x])
    assert.deepEqual(given, [["counter.count", { _tag: "Success", value: 0n }]])
    const counter = { count: async () => 0n }
    await assert.rejects(division.perItemUnguarded.fn(counter, (d.args as [unknown, bigint])[1]), RangeError)
    assert.deepEqual(statuses(v), { readsOnce: "proved" })
  })

  it("a law that divides is read where it is defined: guarded, it is proved; unguarded, it throws on the input shown", async () => {
    assert.deepEqual(statuses(await verify(z3, project, file, "lawGuarded")), { same: "proved" })
    const v = await verify(z3, project, file, "lawUnguarded")
    const law = v.laws.find((l) => l.name === "same")
    assert.equal(law?.status, "counterexample")
    const [a, b] = law.args as [bigint, bigint]
    const same = division.lawUnguarded.ensures.same
    assert.throws(() => same(a, b, division.lawUnguarded.fn(a, b)), RangeError)
  })

  it("a division inside `.every` is refused, saying where to divide instead", async () => {
    const v = await verify(z3, project, file, "inEvery")
    assert.match(v.unsupported ?? "(verified)", /inside `\.some`, `\.every`, `\.find` or `\.filter` is not modeled: divide in a `for…of`/)
  })
})
