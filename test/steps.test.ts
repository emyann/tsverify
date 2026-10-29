// Steps inside expressions (fixtures/steps.ts): proved where they run in
// JavaScript's order and only on the paths that reach them, a step whose value
// nothing reads among them; the laws hold when
// the programs run against a stand-in store; a step after `?.` is refused, and
// so is a law that reads an error of type `unknown`.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { Effect, Layer } from "effect"
import * as steps from "../fixtures/steps.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/steps.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

describe("steps inside expressions, verified", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  // `readsWhatItDrops`: a step whose value nothing reads runs all the same, its call in the trace.
  for (const name of ["readsOnlyWhenAsked", "fallsBack", "putsWhereAsked", "copies", "readsWhatItDrops"])
    it(`${name}: every law proved`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.ok(v.laws.every((l) => l.status === "proved"), JSON.stringify(statuses(v)))
    })

  it("a step after `?.` is refused, naming what to write instead", async () => {
    const v = await verify(z3, project, file, "optional")
    assert.match(v.unsupported ?? "", /a step after `\?\.` runs only when what is before it is present.*write an `if`/)
  })

  it("an `unknown` error is carried: a law that does not read it is proved, one that does is refused", async () => {
    const v = await verify(z3, project, file, "parsed")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), { callsNothing: "proved", readsTheError: "unsupported" })
    assert.match(v.laws.find((l) => l.name === "readsTheError")!.reason!, /`===` of a value of type `unknown` is not modeled: .*give it a type where it is made/)
  })

  it("a `catch` that reads what was thrown gives any error of its type: a law its type alone implies is vacuous", async () => {
    const v = await verify(z3, project, file, "parsedTagged")
    assert.deepEqual(statuses(v), { failsAsAParseError: "vacuous" })
  })
})

// The runs: a store whose keys hold what each run says.
type Call = { readonly op: "get" | "put"; readonly args: readonly string[]; readonly outcome: { readonly _tag: "Success"; readonly value: unknown } }
type Out = { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: unknown }
const STORES: ReadonlyArray<Readonly<Record<string, string>>> = [{}, { a: "1" }, { b: "2" }, { a: "1", b: "2" }]

const running = async <A, E>(program: Effect.Effect<A, E, steps.Store>, held: Readonly<Record<string, string>>): Promise<{ out: Out; calls: Array<Call> }> => {
  const calls: Array<Call> = []
  const kept = new Map(Object.entries(held))
  const store = steps.Store.of({
    get: (key) =>
      Effect.sync(() => {
        const value = kept.get(key)
        calls.push({ op: "get", args: [key], outcome: { _tag: "Success", value } })
        return value
      }),
    put: (key, value) =>
      Effect.sync(() => {
        kept.set(key, value)
        calls.push({ op: "put", args: [key, value], outcome: { _tag: "Success", value: undefined } })
      }),
  })
  const result = await Effect.runPromise(Effect.result(program.pipe(Effect.provide(Layer.succeed(steps.Store)(store)))))
  return { out: result._tag === "Success" ? { _tag: "Success", value: result.success } : { _tag: "Failure", error: result.failure }, calls }
}

// `any`: each contract's laws take its own arguments, and a run passes them back as they came.
type Laws = Readonly<Record<string, (...a: any[]) => boolean>>
const broken = (laws: Laws, args: ReadonlyArray<unknown>, ran: { out: Out; calls: Array<Call> }) =>
  Object.entries(laws)
    .filter(([, law]) => !law(...args, ran.out, ran.calls))
    .map(([l]) => l)

it("the laws hold when the programs run", async () => {
  for (const held of STORES)
    for (const flag of [false, true]) {
      const runs: ReadonlyArray<readonly [Laws, ReadonlyArray<unknown>, Effect.Effect<unknown, unknown, steps.Store>]> = [
        [steps.readsOnlyWhenAsked.ensures, [flag, "a"], steps.readIf(flag, "a")],
        [steps.fallsBack.ensures, ["a", "b"], steps.orElse("a", "b")],
        [steps.putsWhereAsked.ensures, [flag, "a", "b", "v"], steps.putThenGet(flag, "a", "b", "v")],
        [steps.copies.ensures, ["a", "b"], steps.copy("a", "b")],
        [steps.readsWhatItDrops.ensures, ["a"], steps.readAndDrop("a")],
      ]
      for (const [laws, args, program] of runs) assert.deepEqual(broken(laws, args, await running(program, held)), [], JSON.stringify({ held, args }))
    }
})
