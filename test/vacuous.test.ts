// A law no result could break is reported `vacuous`, not `proved`: it would hold
// of any function with the same signature (fixtures/vacuous/sign.contract.ts).
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "fixtures/vacuous/sign.contract.ts")
const project = loadProject([spec], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = async (name: string) => Object.fromEntries((await verify(z3, project, spec, name)).laws.map((l) => [l.name, l.status]))

it("a law over the input alone, or whose condition is never met, is vacuous; one a wrong result would break is proved", async () => {
  assert.deepEqual(await statuses("signed"), { zeroOnlyAtZero: "proved", squareNotNegative: "vacuous", neverAsked: "vacuous" })
})

it("a law whose condition `requires` rules out is vacuous", async () => {
  assert.deepEqual(await statuses("positive"), { pos: "proved", negativeIsNeg: "vacuous" })
})
