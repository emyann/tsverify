// Defects and the forms around them (fixtures/defects.ts): a run that dies is judged by no law, and its end is listed;
// `instanceof` of what was thrown tells its classes apart, and the type it is narrowed to keeps the class it found;
// `Effect.exit` and `catchCause` see a cause as Effect writes one, which the programs, run, confirm; the combinators,
// logs, spans and metrics read as Effect runs them.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { Effect } from "effect"
import * as defects from "../fixtures/defects.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/defects.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const ends = (v: Verification) => v.cover.map((c) => `${c.value} ${c.status}`).sort()

describe("defects, verified", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("a read that throws fails with each refusal and dies of anything else; a law is judged on the runs that do not die", async () => {
    const v = await verify(z3, project, file, "refusesOrDies")
    assert.equal(v.unsupported, undefined)
    // Its failure's type says it fails with a refusal: the law says nothing the type does not.
    assert.deepEqual(statuses(v), { failsOnlyWithARefusal: "vacuous", neverConflicts: "counterexample" })
    assert.deepEqual(ends(v), ["Die reachable", "Failure Conflict reachable", "Failure Missing reachable", "Success reachable"])
    assert.ok(v.notes.some((n) => /judged by no law/.test(n)))
  })

  it("`instanceof` tells the classes apart, and a value narrowed to their union keeps the one it found", async () => {
    const v = await verify(z3, project, file, "tellsTheClassesApart")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), { neverThree: "proved", neverTwo: "counterexample" })
  })

  it("`Effect.exit` succeeds with Effect's own `Exit`: a cause of one reason, `Fail` or `Die`", async () => {
    const v = await verify(z3, project, file, "exitsSay")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), { alwaysSucceeds: "proved", oneReason: "proved", neverDies: "counterexample" })
  })

  it("`catchCause` and `failCause` keep a run's ends; `orDie` and `Cause.squash` make each failure a defect", async () => {
    const passes = await verify(z3, project, file, "passesItsCause")
    assert.deepEqual(statuses(passes), { failsOnlyWithARefusal: "vacuous" })
    assert.ok(ends(passes).includes("Die reachable"), JSON.stringify(ends(passes)))
    for (const name of ["diesOfItsFailures", "diesOfItsCause"]) {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined, name)
      assert.deepEqual(statuses(v), { neverFails: "proved" }, name)
    }
  })

  it("a `throw` in a generator dies: a law that its runs all succeed is proved, and its ends say it can die", async () => {
    const v = await verify(z3, project, file, "throwsADefect")
    assert.deepEqual(statuses(v), { alwaysSucceeds: "proved", notNegative: "proved" })
    assert.deepEqual(ends(v), ["Die reachable", "Failure unreachable", "Success reachable"])
  })

  it("`mapError`, `tap`, `andThen`, `as`, `asVoid` and `suspend` read as Effect runs them", async () => {
    for (const name of ["combines", "touches", "voids"]) {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined, name)
      assert.ok(
        v.laws.every((l) => l.status === "proved"),
        `${name}: ${JSON.stringify(statuses(v))}`,
      )
    }
  })

  it("what was thrown, narrowed only to `{}` by `!= null`, may still be a string; a generic value is read narrowed again", async () => {
    const open = await verify(z3, project, file, "keepsWhatWasThrownOpen")
    assert.equal(open.unsupported, undefined)
    assert.deepEqual(statuses(open), { neverAString: "counterexample" })
    const narrowed = await verify(z3, project, file, "narrowsAGenericValue")
    assert.equal(narrowed.unsupported, undefined)
    assert.deepEqual(statuses(narrowed), { notNegative: "proved" })
  })

  it("logs, spans and metrics change nothing a law reads, and an argument of one that changes something is refused", async () => {
    const v = await verify(z3, project, file, "observes")
    assert.deepEqual(statuses(v), { readsOnce: "proved" })
    assert.ok(v.notes.some((n) => /its arguments are not read/.test(n)))
    const loud = await verify(z3, project, file, "logsLoudly")
    assert.match(loud.unsupported ?? "", /an argument of a log, a span or a metric that changes something/)
  })
})

describe("defects, run", () => {
  const thrown = (x: unknown) => () => {
    throw x
  }
  it("an `Exit`'s cause has one reason, `Fail` of a refusal and `Die` of anything else, as the model reads it", () => {
    const end = (read: () => number) => Effect.runSync(defects.endOf(read))
    assert.equal(
      end(() => 1),
      "read",
    )
    assert.equal(end(thrown(new defects.Missing({ message: "m" }))), "Fail")
    assert.equal(end(thrown("boom")), "Die")
  })
  it("`instanceof` of what was thrown: 1 for a `Missing`, 2 for a `Conflict`", () => {
    const kind = (read: () => number) => Effect.runSync(defects.kindOf(read))
    assert.equal(kind(thrown(new defects.Missing({ message: "m" }))), 1)
    assert.equal(kind(thrown(new defects.Conflict({ message: "c" }))), 2)
    assert.equal(
      kind(() => 7),
      0,
    )
  })
})
