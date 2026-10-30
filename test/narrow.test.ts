// A field read once its object's tag is checked (fixtures/narrow.ts): a law
// reads the argument or the result of a call of one operation, at a place where
// another operation's call stands on some paths, and code reads a member of a
// union whose members give one field different kinds. Each is proved; a bug
// planted in each is shown with an input the planted code breaks the law on; the
// lowering of a union computes what JavaScript computes; and a read the type
// checker has not narrowed to one kind is still refused, saying what to write.
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as narrow from "../fixtures/narrow.ts"
import { diagnostics, loadProject, readContract } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { disagreements, lowerSide, openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/narrow.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([file], tsconfig)
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const world = (law: Verification["laws"][number] | undefined) =>
  Object.fromEntries(Object.entries(law?.world ?? {}).map(([k, x]) => [k.replace(/!\d+$/, ""), x]))

/** The fixture with `from` changed to `to`, which must occur once in it. */
const planted = async (name: string, from: string, to: string): Promise<Verification> => {
  const text = readFileSync(file, "utf8")
  assert.equal(text.split(from).length - 1, 1, `the text to change must occur once: ${from}`)
  return await verify(z3, loadProject([file], tsconfig, new Map([[file, text.replace(from, to)]])), file, name)
}

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("a read narrowed by a check of its tag", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  for (const [name, laws] of [
    ["renamed", ["writesWhatWasAsked", "writesNoEmptyName", "lastIsTheWrite"]],
    ["renamedUser", ["lastWritesTheName", "everyPutTheName"]],
    ["touched", ["bumpsUp", "labelsTheId", "lastBumpIsBy", "returnsTheBump"]],
    ["applied", ["namesKeep", "addsAdd", "subsSub"]],
    ["summed", ["notNegative"]],
  ] as const)
    it(`${name}: every law is proved`, async () => {
      const v = await verify(z3, project, file, name)
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(statuses(v), Object.fromEntries(laws.map((l) => [l, "proved"])))
      assert.ok(
        v.obligations.every((o) => o.status === "proved"),
        JSON.stringify(v.obligations),
      )
    })

  it('a law reading `c.args[1]` once `c.op === "set"`: a write of another name is shown, with what the read gave', async () => {
    const v = await planted("renamed", "await names.set(id, name)", "await names.set(id, current)")
    const law = v.laws.find((l) => l.name === "writesWhatWasAsked")
    assert.equal(law?.status, "counterexample")
    assert.equal(statuses(v).lastIsTheWrite, "counterexample")
    // The planted code writes what `get` gave, which the input's name is not.
    const [, , name] = law.args as [unknown, string, string]
    const gave = world(law)["names.get"] as { _tag: string; value: string }
    assert.equal(gave._tag, "Success")
    assert.notEqual(gave.value, name)
  })

  it('a law reading `c.args[0].name` once `c.op === "put"`, where a `get`\'s is a string: a write of the old name is shown', async () => {
    const v = await planted("renamedUser", "await users.put({ ...user, name })", "await users.put(user)")
    assert.deepEqual(statuses(v), { lastWritesTheName: "counterexample", everyPutTheName: "counterexample" })
    const law = v.laws.find((l) => l.name === "everyPutTheName")
    assert.equal(law?.status, "counterexample")
    const [, , name] = law.args as [unknown, string, string]
    const gave = world(law)["users.get"] as { _tag: string; value: { name: string } }
    assert.notEqual(gave.value.name, name)
  })

  it('a law reading `c.args[0]` once `c.op === "bump"`, where a `label`\'s is a string: a bump by less is shown', async () => {
    const v = await planted("touched", "await store.bump(by)", "await store.bump(by - 1n)")
    assert.deepEqual(statuses(v), {
      bumpsUp: "counterexample",
      labelsTheId: "proved",
      lastBumpIsBy: "counterexample",
      returnsTheBump: "proved",
    })
    // A bump by `by - 1n` is not above 0n only when `by` is 1n.
    const law = v.laws.find((l) => l.name === "bumpsUp")
    assert.equal(law?.status, "counterexample")
    assert.equal((law.args as [unknown, string, bigint])[2], 1n)
  })

  it("a union read once its tag is checked: the counterexample is a member of the union, and the planted code breaks the law on it", async () => {
    // The bug is in the second member's branch: the counterexample is a `sub`, which the first member is not.
    const v = await planted("applied", "? total - ev.n :", "? total + ev.n :")
    assert.deepEqual(statuses(v), { namesKeep: "proved", addsAdd: "proved", subsSub: "counterexample" })
    const law = v.laws.find((l) => l.name === "subsSub")
    assert.equal(law?.status, "counterexample")
    const [total, ev] = law.args as [bigint, narrow.Event]
    assert.deepEqual(Object.keys(ev).sort(), ["n", "type"])
    assert.equal(ev.type, "sub")
    assert.equal(typeof ev.n, "bigint")
    const plantedFn = (t: bigint, e: narrow.Event) => (e.type === "add" ? t + e.n : e.type === "sub" ? t + e.n : t)
    assert.equal(narrow.applied.ensures.subsSub(total, ev, plantedFn(total, ev)), false)
  })

  it("a union in an array, destructured in a loop: each element is a member, and the planted code breaks the law on them", async () => {
    const v = await planted("summed", "total += n", "total -= n")
    const law = v.laws.find((l) => l.name === "notNegative")
    assert.equal(law?.status, "counterexample")
    const [events] = law.args as [ReadonlyArray<narrow.Event>]
    for (const e of events) assert.equal(typeof e.n, e.type === "name" ? "string" : "bigint")
    const plantedSum = (es: ReadonlyArray<narrow.Event>) => es.reduce((t, e) => (e.type === "add" ? t - e.n : t), 0n)
    assert.ok(plantedSum(events) < 0n)
  })

  it("a union's lowering computes what JavaScript computes, on both sides, for each member", async () => {
    const inputs: Array<[bigint, narrow.Event]> = [
      [5n, { type: "add", n: 2n }],
      [5n, { type: "add", n: -7n }],
      [5n, { type: "sub", n: 2n }],
      [5n, { type: "name", n: "x" }],
      [0n, { type: "name", n: "" }],
    ]
    const run = ([total, ev]: ReadonlyArray<unknown>) => narrow.apply(total as bigint, ev as narrow.Event)
    for (const bound of [undefined, 4]) {
      const side = () => lowerSide(z3, project, readContract(project, file, "applied"), bound)
      assert.deepEqual(await disagreements(side(), inputs, run), [])
      // Each input pins a value the lowering holds: a wrong result is told apart on every one.
      const wrong = await disagreements(side(), inputs, (args) => run(args) + 1n)
      assert.equal(wrong.length, inputs.length)
    }
  })

  it("a read the checker has not narrowed to one kind is a value of either kind: a string is no `0n`", async () => {
    const v = await verify(z3, project, file, "either")
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["onlyACount", "proved"]],
    )
    const zero = await verify(z3, project, file, "eitherZero")
    const [law] = zero.laws
    assert.equal(law?.status, "counterexample")
    const [ev] = law.args as [narrow.Event]
    assert.equal(ev.n, 0n)
  })
})
