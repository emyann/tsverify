// Wrong verdicts the verifier once gave (fixtures/soundness.ts): a proof that a
// plain promise never rejects, a counterexample no double makes, a proof that a
// write past an array's end keeps its length, one that an element past the end
// is there, and an `inconsistent` and a counterexample of laws over a list grown
// past the search bound by a conditional.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const shown = (x: unknown): string => JSON.stringify(x, (_, v) => (typeof v === "bigint" ? `${v}n` : v))
const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/soundness.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("verdicts the verifier once got wrong", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("an operation returning a plain promise may reject: 'it always succeeds' is refuted, and failure is reachable", async () => {
    const v = await verify(z3, project, file, "alwaysSucceeds")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(
      v.laws.map((l) => l.status),
      ["counterexample"],
    )
    assert.equal(v.cover.find((c) => c.value === "Failure")?.status, "reachable")
  })

  it("a real no double holds is no counterexample: a law true of every double is not refuted", async () => {
    const v = await verify(z3, project, file, "noneBetween")
    const [law] = v.laws
    assert.notEqual(law?.status, "counterexample", JSON.stringify(law))
    assert.ok(law?.status === "proved" || law?.status === "bounded", JSON.stringify(law))
  })

  it("a write past the end grows the array: 'the length is kept' is not proved, and the write is refuted at []", async () => {
    const v = await verify(z3, project, file, "growKeepsLength")
    assert.equal(v.unsupported, undefined)
    assert.notEqual(v.laws[0]?.status, "proved")
    const write = v.obligations.find((o) => o.kind === "write")
    assert.equal(write?.status, "counterexample")
    assert.deepEqual(write?.args, [[]])
  })

  it("an element borrowed past the end is missing: 'it is always there' is refuted at []", async () => {
    const v = await verify(z3, project, file, "secondAlwaysThere")
    assert.deepEqual(
      v.laws.map((l) => [l.status, l.args]),
      [["counterexample", [[]]]],
    )
  })

  it("a list grown past the search bound, merged with one it was not, is searched whole: a law that holds is proved", async () => {
    const v = await verify(z3, project, file, "appendedHoldsIt")
    assert.equal(v.unsupported, undefined)
    const [law] = v.laws
    assert.equal(law?.status, "proved", shown(law))
  })

  it("an element of the given list pushed past the bound is found: a law that holds is not refuted", async () => {
    const v = await verify(z3, project, file, "prependedKeepsTheLast")
    assert.equal(v.unsupported, undefined)
    const [law] = v.laws
    assert.equal(law?.status, "proved", shown(law))
  })
})
