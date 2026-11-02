// A counterexample is pinned back onto a side's leaves (`pin`, `./concrete.ts`) to ask what the laws allow there. A value
// that does not fit a leaf is refused, never looped on: a counterexample read back as `tryRaise: {}` once left the number
// leaf under it `undefined`, and `exactRational` doubled NaN for ten minutes, a loop no time limit can stop.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { pin } from "../src/concrete.ts"
import { trustOf } from "../src/lower.ts"
import { loadProject, readContract } from "../src/project.ts"
import { readAssumptions } from "../src/trust.ts"
import { type Ctx, exactRational } from "../src/value.ts"
import { ADAPTERS, lowerSide, openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/unmeetable/unread.contract.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

it("exactRational: a finite double's exact fraction, and anything else refused", () => {
  assert.deepEqual(exactRational(3), { numerator: 3n, denominator: 1n })
  assert.deepEqual(exactRational(0.5), { numerator: 1n, denominator: 2n })
  assert.deepEqual(exactRational(0.1), { numerator: 3602879701896397n, denominator: 36028797018963968n })
  assert.deepEqual(exactRational(5e-324), { numerator: 1n, denominator: 2n ** 1074n })
  for (const x of [Number.NaN, Infinity, -Infinity, undefined, "1", {}])
    assert.throws(() => exactRational(x as number), RangeError, String(x))
})

it("pin refuses a value that leaves out a number the side holds a leaf for", () => {
  const source = readContract(project, file, "raised")
  const proof = lowerSide(z3, project, source, undefined, ADAPTERS, trustOf(readAssumptions(project)))
  assert.ok(pin(proof.u, "a", { called: false, loop: false, tryRaise: { above: 2 } }).length > 0, "a whole value is pinned")
  assert.throws(() => pin(proof.u, "a", { called: false, loop: false, tryRaise: {} }), TypeError)
  assert.throws(() => pin(proof.u, "a", { called: false, loop: false, tryRaise: { above: "2" } }), TypeError)
})

it("the stub's contract ends with a verdict for every law", async () => {
  const v = await verify(z3, project, file, "raised")
  assert.deepEqual(
    v.laws.map((l) => l.name),
    ["byRetryExactlyWhenTheTryCarriesOne", "retryAboveTheTrys", "neverBelowNothing"],
  )
  assert.ok(
    v.laws.every((l) => l.status !== "proved"),
    JSON.stringify(v.laws.map((l) => [l.name, l.status])),
  )
})
