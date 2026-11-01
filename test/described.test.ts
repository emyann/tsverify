// A law that says what it means (fixtures/described.ts): `{ description, condition }` is read
// as its predicate, in each kind of contract, written in place or as a `const`;
// its sentence is carried to the result, printed by the command, and kept in
// `--json`; `holds` gives a law's predicate whichever way it is written; a
// `description` that is not a string written in place is refused, saying how to write
// it; and `says` and `holds`, the names before 0.3, are refused with what they are now.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as described from "../fixtures/described.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/described.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))
const read = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, [l.status, l.description]]))
const { FORCE_COLOR: _, ...plain } = process.env
const cli = (...args: Array<string>) =>
  spawnSync(process.execPath, ["--conditions=tsverify-source", path.join(root, "src/cli.ts"), ...args], {
    cwd: root,
    env: plain,
    encoding: "utf8",
    timeout: 300_000,
  })

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("a law that says what it means", () => {
  it("the fixture type-checks, each law's parameters typed from the function in either form", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("is read as its predicate, its sentence kept: in place, from a const, and beside a law that says nothing", async () => {
    assert.deepEqual(read(await verify(z3, project, file, "shipped")), {
      freeFrom50: ["proved", "An order of 50 or more ships free"],
      smallOrdersPay: ["proved", "A smaller order pays 5"],
      notNegative: ["proved", undefined],
    })
  })

  it("in an async computation and an Effect program", async () => {
    assert.deepEqual(read(await verify(z3, project, file, "renamed")), {
      emptyNameTouchesNothing: ["proved", "An empty name never reaches the store"],
    })
    assert.deepEqual(read(await verify(z3, project, file, "readsWhenAsked")), {
      readsOnlyWhenAsked: ["proved", "It reads the store only when asked to"],
    })
  })

  it("a law broken is shown with its sentence, and `holds` runs it on the input shown", async () => {
    const v = await verify(z3, project, file, "shippedLate")
    const law = v.laws[0]
    assert.equal(law?.status, "counterexample")
    assert.equal(law.description, "An order of 50 or more ships free")
    const [total] = law.args as [number]
    assert.equal(holds(described.shippedLate.ensures.freeFrom50)({ input: [total], output: described.shippedLate.fn(total) }), false)
  })

  it("`holds` gives the predicate of a law written either way", () => {
    assert.equal(holds(described.shipped.ensures.freeFrom50)({ input: [60], output: 0 }), true)
    assert.equal(holds(described.shipped.ensures.notNegative)({ input: [60], output: -1 }), false)
  })

  it("the command prints the sentence, then the name; `--json` keeps both", () => {
    const text = cli("fixtures/described.ts")
    assert.match(text.stdout, /\n {4}✗ An order of 50 or more ships free {2}\(freeFrom50, \d+ ms\)\n {6}e\.g\. \(50\)\n/)
    assert.match(text.stdout, /\n {4}✓ notNegative {2}\(\d+ ms\)\n/)
    const json = JSON.parse(cli("fixtures/described.ts", "--json").stdout) as {
      contracts: ReadonlyArray<{ contract: string; laws: ReadonlyArray<{ name: string; description?: string }> }>
    }
    assert.deepEqual(
      json.contracts.find((c) => c.contract === "shipped")?.laws.map((l) => [l.name, l.description]),
      [
        ["freeFrom50", "An order of 50 or more ships free"],
        ["smallOrdersPay", "A smaller order pays 5"],
        ["notNegative", undefined],
      ],
    )
  })

  it("a sentence that is not a string written in place is refused, saying how to write it", async () => {
    const v = await verify(z3, project, file, "describedComputed")
    assert.match(v.unsupported ?? "(verified)", /a law's `description` is a string written in place/)
  })

  it("`says` and `holds`, the names before 0.3, are refused, saying what each is now", async () => {
    const v = await verify(z3, project, file, "describedTheOldWay")
    assert.match(v.unsupported ?? "(verified)", /a law's `says` is `description` since 0\.3/)
  })
})
