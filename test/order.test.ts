// A state machine read as laws: an order's status (examples/order). Every
// counterexample and every witness is run on the real function, and the
// lowering is checked against the real function on random orders.
import assert from "node:assert/strict"
import { after, before, describe, it } from "node:test"
import { orders } from "../examples/order/generate.ts"
import type { Order } from "../examples/order/order.ts"
import { status } from "../examples/order/order.contract.ts"
import { diagnostics, loadProject, readContract } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, disagreements, lowerSide, openZ3, verify } from "../src/verify.ts"

const spec = new URL("../examples/order/order.contract.ts", import.meta.url).pathname
const project = loadProject([spec], new URL("../tsconfig.json", import.meta.url).pathname)

let z3: Ctx
let close: () => Promise<void>
let v: Verification
before(async () => {
  ;({ z3, close } = await openZ3())
  v = await verify(z3, project, spec, "status")
})
after(() => close())

const asOrder = (x: unknown): Order => x as Order

describe("statusOf against its doc comment", () => {
  it("is read from a spec that type-checks", () => {
    assert.deepEqual(diagnostics(project, spec), [])
    assert.equal(v.unsupported, undefined)
  })

  it("proves nine laws and refutes one", () => {
    assert.deepEqual(Object.fromEntries(v.laws.map((l) => [l.name, l.status])), {
      finalExactlyWhenResolved: "proved",
      fulfilledCompletes: "proved",
      refundedRefunds: "proved",
      cancelOutranks: "proved",
      cancelingOnlyWhenAsked: "proved",
      onItsWay: "counterexample",
      movingMeansAnOpenShipment: "proved",
      awaitingNeedsASubscription: "proved",
      noSubscriptionNeverWaits: "proved",
      placedHasNoShipmentThisRound: "proved",
    })
  })

  it("refutes `onItsWay` with a pickup time that is the empty string, and the real code agrees", () => {
    // The law says picked up when `pickedUpAt` is not null; the code asks whether it is truthy.
    const order = asOrder(v.laws.find((l) => l.name === "onItsWay")!.args?.[0])
    assert.equal(order.shipments.at(-1)?.pickedUpAt, "")
    assert.equal(status.fn(order), "awaiting-pickup")
    assert.equal(status.ensures["onItsWay"]!(order, status.fn(order)), false)
  })

  it("reaches every status, each witness confirmed by the real code", () => {
    assert.equal(v.cover.length, 10)
    for (const c of v.cover) {
      assert.equal(c.status, "reachable", c.value)
      assert.equal(status.fn(asOrder(c.args?.[0])), c.value)
    }
  })
})

describe("the lowering of statusOf", () => {
  const inputs = orders(7, 300).map((o) => [o] as const)
  const run = ([o]: ReadonlyArray<unknown>) => status.fn(asOrder(o))

  it("computes what the real function computes on 300 random orders (the proof side)", async () => {
    assert.deepEqual(await disagreements(lowerSide(z3, project, readContract(project, spec, "status")), inputs, run), [])
  })

  it("and on the search side, whose arrays hold at most 4 elements", async () => {
    assert.deepEqual(await disagreements(lowerSide(z3, project, readContract(project, spec, "status"), 4), inputs, run), [])
  })
})
