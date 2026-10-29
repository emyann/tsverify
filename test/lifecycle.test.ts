// The pilot: Nemia's own `lifecycleOf` (hkb-v2, agent-runtime/src/core/domain.ts),
// read in place, against laws taken from its doc comment. Every counterexample
// and every witness is replayed on the real function, and the lowering is
// checked against the real function on random states.
import assert from "node:assert/strict"
import { after, before, describe, it } from "node:test"
import { init, killThreads } from "z3-solver"
import type { State } from "../../hkb-v2/packages/agent-runtime/src/core/domain.ts"
import { states } from "../pilots/lifecycle/generate.ts"
import { lifecycle } from "../pilots/lifecycle/lifecycle.spec.ts"
import { diagnostics, loadProject, readContract } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, disagreements, lowerSide, verify } from "../src/verify.ts"

const spec = new URL("../pilots/lifecycle/lifecycle.spec.ts", import.meta.url).pathname
const project = loadProject([spec], new URL("../tsconfig.json", import.meta.url).pathname)

let api: Awaited<ReturnType<typeof init>>
let z3: Ctx
let v: Verification
before(async () => {
  api = await init()
  z3 = api.Context("main")
  v = await verify(z3, project, spec, "lifecycle")
})
after(() => killThreads(api.em))

const asState = (x: unknown): State => x as State

describe("lifecycleOf against its doc comment", () => {
  it("is read from a spec that type-checks", () => {
    assert.deepEqual(diagnostics(project, spec), [])
    assert.equal(v.unsupported, undefined)
  })

  it("proves nine laws and refutes one", () => {
    const status = Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
    assert.deepEqual(status, {
      terminalExactlyWhenSettled: "proved",
      succeededCompletes: "proved",
      stoppedCancels: "proved",
      stopOutranks: "proved",
      stoppingOnlyWhenAsked: "proved",
      inFlight: "counterexample",
      workingMeansInFlight: "proved",
      inputRequiredNeedsHoldOpen: "proved",
      notHeldOpenNeverWaits: "proved",
      submittedHasNoAttemptThisTurn: "proved",
    })
  })

  it("refutes `inFlight` with an attempt whose spawnedAt is the empty string, and the real code agrees", () => {
    const law = v.laws.find((l) => l.name === "inFlight")!
    const state = asState(law.args?.[0])
    assert.equal(state.attempts.at(-1)?.spawnedAt, "")
    assert.equal(lifecycle.fn(state), "starting") // `last.spawnedAt ? 'working' : 'starting'`
    assert.equal(lifecycle.ensures["inFlight"]!(state, lifecycle.fn(state)), false)
  })

  it("reaches every lifecycle state, each witness confirmed by the real code", () => {
    assert.equal(v.cover.length, 9)
    for (const c of v.cover) {
      assert.equal(c.status, "reachable", c.value)
      assert.equal(lifecycle.fn(asState(c.args?.[0])), c.value)
    }
  })
})

describe("the lowering of lifecycleOf", () => {
  const inputs = states(7, 300).map((s) => [s] as const)
  const run = ([s]: ReadonlyArray<unknown>) => lifecycle.fn(asState(s))

  it("computes what the real function computes on 300 random states (the proof side)", async () => {
    const side = lowerSide(z3, project, readContract(project, spec, "lifecycle"))
    assert.deepEqual(await disagreements(side, inputs, run), [])
  })

  it("and on the search side, whose arrays hold at most 4 elements", async () => {
    const side = lowerSide(z3, project, readContract(project, spec, "lifecycle"), 4)
    assert.deepEqual(await disagreements(side, inputs, run), [])
  })
})
