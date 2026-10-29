// A program that calls lodash, verified against the pack that declares what
// lodash does; and the pack, trusted by the verifier, run against lodash.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { clamp } from "lodash-es"
import { clampOfNumbers, uniqOfStrings } from "../packs/lodash.ts"
import * as program from "../examples/lodash/labels.ts"
import { assume, brokenOn } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { verify, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "examples/lodash/labels.contract.ts")
const project = loadProject([spec], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

it("the spec type-checks", () => {
  assert.deepEqual(diagnostics(project, spec), [])
})

describe("the program, against what the pack declares", () => {
  it("labelCount: none exactly when empty, proved; several only with two different labels, not provable from the pack", async () => {
    const v = await verify(z3, project, spec, "labels")
    const byName = Object.fromEntries(v.laws.map((l) => [l.name, l]))
    assert.equal(byName.noneExactlyWhenEmpty?.status, "proved")
    const several = byName.severalOnlyWithTwoDifferent!
    assert.equal(several.status, "counterexample")
    assert.deepEqual(several.abstract, ["uniq (lodash-es)"])
    // The counterexample is one lodash does not share: its labels are all alike, and lodash counts them as one.
    const [labels] = several.args as [ReadonlyArray<string>]
    assert.ok(labels.every((l) => l === labels[0]))
    assert.equal(program.labelCount(labels), "one")
    assert.deepEqual(
      v.trusted.map((t) => [t.name, t.purity]),
      [["uniq (lodash-es)", "unchecked"]],
    )
  })

  it("progress: within the total, none without one, all of it when done; every law proved", async () => {
    const v = await verify(z3, project, spec, "progressWithinTotal")
    assert.deepEqual(
      v.laws.map((l) => l.status),
      ["proved", "proved", "proved"],
    )
  })
})

describe("the pack, against lodash", () => {
  it("uniq's laws hold on every sample", () => {
    const samples: ReadonlyArray<[ReadonlyArray<string>]> = [
      [[]],
      [["a"]],
      [["a", "a"]],
      [["b", "a", "b"]],
      [["", ""]],
      [["x", "y", "z", "y", "x"]],
    ]
    assert.deepEqual(brokenOn(uniqOfStrings, samples), [])
  })

  const numbers: ReadonlyArray<[number, number, number]> = [
    [5, 0, 10],
    [-1, 0, 10],
    [11, 0, 10],
    [Number.NaN, 0, 10],
    [5, 10, 0],
    [5, Number.NaN, 10],
    [5, 0, Number.NaN],
    [Number.POSITIVE_INFINITY, 0, 10],
    [Number.NEGATIVE_INFINITY, 0, 10],
    [-0, 0, 5],
    [3, 3, 3],
    [0.5, 0.25, 0.75],
  ]
  it("clamp's laws hold on every sample, NaN and reversed bounds among them", () => {
    assert.deepEqual(brokenOn(clampOfNumbers, numbers), [])
  })

  it("a law lodash does not keep is caught: clamp within its bounds whatever they are", () => {
    const naive = assume<[n: number, lower: number, upper: number], number>(clamp, {
      pure: true,
      ensures: { within: (_n, lower, upper, out) => lower <= out && out <= upper },
    })
    const broken = brokenOn(naive, numbers).map((b) => b.input)
    assert.deepEqual(broken, [
      [Number.NaN, 0, 10],
      [5, 10, 0],
      [5, Number.NaN, 10],
      [5, 0, Number.NaN],
    ])
  })
})
