// A proof is checked against the search side: when the proof side is made
// unsound (here by an assumption of `false`, which proves everything), every
// false law and every broken obligation is reported `inconsistent` with an
// input that breaks it, and what is true stays proved. The rest of the suite
// shows the other half: on sound sides, nothing is ever reported inconsistent.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { ADAPTERS } from "../src/verify.ts"
import { trustOf } from "../src/lower.ts"
import { loadProject, readContract } from "../src/project.ts"
import { readAssumptions } from "../src/trust.ts"
import type { Ctx } from "../src/value.ts"
import { judge, lowerSide, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/loops.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

/** The contract judged with its proof side made to prove anything. */
const unsoundly = async (name: string) => {
  const trust = trustOf(readAssumptions(project))
  const source = readContract(project, file, name)
  const proof = lowerSide(z3, project, source, undefined, ADAPTERS, trust)
  const search = lowerSide(z3, project, source, 4, ADAPTERS, trust)
  proof.u.assume(z3.Bool.val(false))
  return judge(z3, project, file, proof, search, trust)
}

it("a false law the proof side proves is reported inconsistent, with an input that breaks it", async () => {
  const v = await unsoundly("neverFindsOne")
  const law = v.laws.find((l) => l.name === "neverFinds")!
  assert.equal(law.status, "inconsistent")
  const [xs] = law.args as [ReadonlyArray<bigint>]
  assert.ok(
    xs.some((x) => x < 0n),
    JSON.stringify(law.args, (_, x) => (typeof x === "bigint" ? `${x}n` : x)),
  )
  // Its invariant is true: no run breaks it, so it stays proved.
  assert.deepEqual(
    v.obligations.map((o) => `${o.phase}: ${o.status}`),
    ["entry: proved", "kept: proved"],
  )
})

it("a broken invariant the proof side proves is reported inconsistent; its inductive step, true, stays proved", async () => {
  // `total > 0n` fails on entry, and an iteration from a state that meets it keeps it.
  const v = await unsoundly("sumFromNothingNonNegative")
  assert.deepEqual(
    v.obligations.map((o) => `${o.phase}: ${o.status}`),
    ["entry: inconsistent", "kept: proved"],
  )
  assert.deepEqual(v.obligations[0]!.args, [[]])
})
