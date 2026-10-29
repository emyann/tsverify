// Proof mode: loops read through their invariants, asserts, lemmas, and the
// state a function changes. Each fixture contract, its expected verdict, and,
// for the hints, each obligation's.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as loops from "../fixtures/loops.ts"
import * as state from "../fixtures/state.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, verify, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const files = { loops: path.join(root, "fixtures/loops.ts"), state: path.join(root, "fixtures/state.ts") }
const project = loadProject(Object.values(files), path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const laws = (v: Verification) => v.laws.map((l) => l.status)
const proofCode = (v: Verification) => v.obligations.map((o) => `${o.kind}${o.phase === "here" ? "" : ` ${o.phase}`}: ${o.status}`)

it("the fixtures type-check", () => {
  for (const f of Object.values(files)) assert.deepEqual(diagnostics(project, f), [])
})

describe("loops, through their invariants", () => {
  const cases: ReadonlyArray<readonly [string, ReadonlyArray<string>, ReadonlyArray<string>]> = [
    ["sumNonNegative", ["proved"], ["invariant entry: proved", "invariant kept: proved"]],
    // No invariant written: the law, restated for the elements gone through, is guessed and proved.
    ["sumBareNonNegative", ["proved"], ["invariant entry: proved", "invariant kept: proved"]],
    // A guess not true on entry is dropped: the law is bounded, and no obligation is left.
    ["sumPlusOneAtLeastOne", ["bounded"], []],
    ["sumCappedNonNegative", ["bounded"], ["invariant entry: proved", "invariant kept: counterexample"]],
    ["sumFromNothingNonNegative", ["bounded"], ["invariant entry: counterexample", "invariant kept: proved"]],
    // One invariant written, for `oneOfThem`: `noneLarger` is still guessed beside it, and both are proved.
    [
      "largestOneOfThem",
      ["proved", "proved"],
      ["invariant entry: proved", "invariant entry: proved", "invariant kept: proved", "invariant kept: proved"],
    ],
    ["maxIsAnUpperBound", ["proved"], ["invariant entry: proved", "invariant kept: proved"]],
    ["positivesNoMore", ["proved"], ["invariant entry: proved", "invariant kept: proved"]],
    ["firstNegativeIsNegative", ["proved", "proved"], ["invariant entry: proved", "invariant kept: proved"]],
    ["countReaches", ["proved"], ["invariant entry: proved", "invariant kept: proved"]],
    // What holds at a loop's end is not known on a path that returned before it.
    ["neverFindsOne", ["counterexample"], ["invariant entry: proved", "invariant kept: proved"]],
    ["doubleAbove", ["proved", "counterexample"], ["invariant entry: proved", "invariant kept: proved"]],
  ]
  for (const [name, want, hints] of cases)
    it(name, async () => {
      const v = await verify(z3, project, files.loops, name)
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(laws(v), want)
      assert.deepEqual(proofCode(v), hints)
    })

  it("a broken invariant's counterexample is an input on which it fails, run for real", async () => {
    const v = await verify(z3, project, files.loops, "sumCappedNonNegative")
    const [xs] = v.obligations.find((o) => o.status === "counterexample")!.args as [ReadonlyArray<bigint>]
    // Some prefix of it sums to 10 or more: the invariant `total < 10n` is false at the head of the next iteration.
    let total = 0n
    const heads = [total]
    for (const x of xs.slice(0, -1)) heads.push((total += x))
    assert.ok(
      heads.some((t) => t >= 10n),
      JSON.stringify(xs, (_, x) => (typeof x === "bigint" ? `${x}n` : x)),
    )
  })
})

describe("asserts and lemmas", () => {
  const cases: ReadonlyArray<readonly [string, ReadonlyArray<string>, ReadonlyArray<string>]> = [
    ["halveGiven", ["proved"], ["assert: proved"]],
    // The assert is false for a negative `n`; the law does not lean on it, and is still searched.
    ["halveAnything", ["bounded"], ["assert: counterexample"]],
    ["areaNonNegative", ["proved"], ["requires: proved", "lemma: proved"]],
    ["areaOfAnything", ["counterexample"], ["requires: counterexample", "lemma: proved"]],
    ["leansOnAFalseLemma", ["counterexample"], ["lemma: counterexample"]],
    ["productNonNegative", ["proved"], []],
    ["everyNumberPositive", ["counterexample"], []],
  ]
  for (const [name, want, hints] of cases)
    it(name, async () => {
      const v = await verify(z3, project, files.loops, name)
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(laws(v), want)
      assert.deepEqual(proofCode(v), hints)
    })

  it("no hint proves itself: an assert false of some input is never proved by its own fact", async () => {
    const v = await verify(z3, project, files.loops, "halveAnything")
    assert.deepEqual(v.obligations[0]!.args, [-1n])
    assert.equal(loops.halve(-1n), -1n)
  })
})

describe("state", () => {
  for (const name of ["twiceIsTwo", "markedWhenFound", "kinds", "stampKept"])
    it(`${name}: proved`, async () => {
      const v = await verify(z3, project, files.state, name)
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(
        laws(v),
        v.laws.map(() => "proved"),
      )
    })

  it("and each is what the code does when it runs", () => {
    assert.equal(state.twice(), 2n)
    assert.deepEqual([0n, 1n, 2n, 3n].map(state.mark), [false, true, true, false])
    assert.deepEqual((["a", "b", "c", "d"] as const).map(state.kindOf), [1n, 1n, 12n, 10n])
    assert.equal(state.stamps("now"), "now")
  })

  const refused: ReadonlyArray<readonly [string, RegExp]> = [
    ["argument", /changes `xs`, which the function did not allocate/],
    ["secondName", /`b` would be a second name for `a`/],
    ["twice_", /stores `s\.a`, a part of an object the function holds, in a second place/],
    ["moved", /`item` was stored in `list`; read it from there/],
    ["borrowed", /replaces `s\.xs` while `a` refers into it/],
    ["closure", /a closure kept for later over `n`, which its function changes/],
    ["shorthand", /a closure kept for later over `n`, which its function changes/],
  ]
  for (const [name, why] of refused)
    it(`refused: ${name}`, async () => {
      const v = await verify(z3, project, files.state, name)
      const reason = v.unsupported ?? v.laws.find((l) => l.status === "unsupported")?.reason ?? "(verified)"
      assert.match(reason, why)
    })
})
