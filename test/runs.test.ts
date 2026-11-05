// A pure function's laws run on seeded inputs in a child process of its own, before any proof (fixtures/runs): a law
// broken comes back with a real input that breaks it, shrunk, a generated function shown by the calls it answered;
// the strings of one input drawn from a few of the program's own, so a `requires` over keys is met; a function that is
// not pure, or a module that cannot load, is not run, and says why; the child's HOME is a throwaway one; the same plan
// answers the same; a child that never ends is stopped.
import assert from "node:assert/strict"
import { existsSync, readdirSync, rmSync } from "node:fs"
import os from "node:os"
import path from "node:path"
import { after, before, it } from "node:test"
import * as fc from "fast-check"
import { trustOf } from "../src/lower.ts"
import { loadProject, readContract } from "../src/project.ts"
import { arbitraryOf } from "../src/run/arbitrary.ts"
import { type RunPlan, planOf, runContract } from "../src/run/runs.ts"
import { NotRunnable, type Shape, shapeOf } from "../src/run/shape.ts"
import ts from "typescript"
import { readAssumptions } from "../src/trust.ts"
import type { Ctx } from "../src/value.ts"
import { type Options, openZ3, verify } from "../src/verify.ts"
import { price } from "../fixtures/runs/broken.contract.ts"
import { label } from "../fixtures/runs/lookup.contract.ts"
import { half } from "../fixtures/runs/implemented.contract.ts"

const root = path.resolve(import.meta.dirname, "..")
const fixture = (name: string) => path.join(root, "fixtures/runs", `${name}.contract.ts`)
const NAMES = ["broken", "lookup", "keyed", "impure", "enum", "home", "bounded", "wrong-assume", "throws", "implemented", "stuck"]
const project = loadProject(NAMES.map(fixture), path.join(root, "tsconfig.json"))
const SEED = 20_261_105

const plan = (name: string, contract: string, opts: Options = {}): RunPlan | { readonly why: string } => {
  const source = readContract(project, fixture(name), contract)
  return planOf(project, source, trustOf(readAssumptions(project).forTarget(source.target)), opts, SEED)
}
const planned = (name: string, contract: string, opts: Options = {}): RunPlan => {
  const p = plan(name, contract, opts)
  if ("why" in p) assert.fail(`${contract} not planned: ${p.why}`)
  return p
}
const ranOf = async (name: string, contract: string, opts: Options = {}) => runContract(planned(name, contract, opts))
const ranTrue = (r: Awaited<ReturnType<typeof runContract>>) => {
  if (!r.ran.ran) assert.fail(`not run: ${r.ran.why}`)
  return r.ran
}

it("a broken law comes back with an input that breaks it, the real function called on it; a kept law does not", async () => {
  const r = await ranOf("broken", "priced")
  const ran = ranTrue(r)
  assert.deepEqual(Object.keys(r.broken), ["tenEach"])
  const [qty] = r.broken.tenEach!.args as [number]
  assert.notEqual(price(qty), qty * 10)
  // Shrunk: the least count past ten.
  assert.equal(qty, 11)
  assert.ok(ran.inputs > 0 && ran.discarded > 0, JSON.stringify(ran))
  assert.ok(ran.modules.includes("fixtures/runs/broken.contract.ts"), ran.modules.join(", "))
  assert.ok(ran.modules.includes("@emyann/tsverify"), ran.modules.join(", "))
  assert.deepEqual(
    [...ran.env].toSorted(),
    ["HOME", "PATH", "TMPDIR", "USERPROFILE"].filter((n) => n !== "PATH" || process.env.PATH !== undefined),
  )
  // A free result breaks each law: both say something.
  assert.deepEqual(r.saysSomething, ["notNegative", "tenEach"])
})

it("a law broken through a function parameter shows the calls the generated function answered, the same on every run", async () => {
  const r = await ranOf("lookup", "labelled")
  ranTrue(r)
  const args = r.broken.alwaysA?.args as [string, { "~calls": Array<[[string], "a" | "b"]> }] | undefined
  assert.ok(args !== undefined, JSON.stringify(r))
  const calls = args[1]["~calls"]
  assert.ok(calls.length > 0, JSON.stringify(args))
  const rebuilt = (k: string) => calls.find(([[a]]) => a === k)![1]
  assert.equal(label(args[0], rebuilt), "b")
  const again = await ranOf("lookup", "labelled")
  assert.deepEqual(again.broken, r.broken)
})

it("a `requires` that every name be a key of the record is met, and the law behind it broken", async () => {
  const r = await ranOf("keyed", "weighed")
  const ran = ranTrue(r)
  assert.ok(ran.inputs > 0, JSON.stringify(ran))
  const args = r.broken.fewSteps?.args as [Record<string, number>, ReadonlyArray<{ name: string }>] | undefined
  assert.ok(args !== undefined, JSON.stringify(r))
  assert.ok(args[1].length >= 3 && args[1].every((s) => Object.hasOwn(args[0], s.name)))
})

it("a function that reads a module's `let` is not run, and says so", () => {
  const p = plan("impure", "scaledUp")
  assert.ok("why" in p)
  assert.match(p.why, /rate/)
})

it("a module that cannot load is not run, naming the module and the error", async () => {
  const r = await ranOf("enum", "leveled")
  assert.equal(r.ran.ran, false)
  if (r.ran.ran) return
  assert.match(r.ran.why, /fixtures\/runs\/enum\.ts/)
  assert.match(r.ran.why, /ERR_UNSUPPORTED_TYPESCRIPT_SYNTAX/)
  assert.deepEqual(r.broken, {})
})

it("a module that writes under the home folder writes in a throwaway one, removed after", async () => {
  const stray = path.join(os.homedir(), ".tsverify-runs-home-fixture")
  rmSync(stray, { force: true })
  const ours = () => new Set(readdirSync(os.tmpdir()).filter((f) => f.startsWith("tsverify-run-")))
  const before = ours()
  const r = await ranOf("home", "doubled")
  const ran = ranTrue(r)
  const exists = existsSync(stray)
  rmSync(stray, { force: true })
  assert.equal(exists, false, `${stray} written`)
  assert.ok(ran.modules.includes("fixtures/runs/home.contract.ts"), ran.modules.join(", "))
  assert.deepEqual(
    [...ours()].filter((f) => !before.has(f)),
    [],
  )
  assert.deepEqual(r.broken, {})
})

it("no array is longer than the bound", async () => {
  const at2 = await ranOf("bounded", "short", { bound: 2 })
  ranTrue(at2)
  assert.deepEqual(at2.broken, {})
  const at3 = await ranOf("bounded", "short", { bound: 3 })
  assert.equal((at3.broken.underThree?.args[0] as ReadonlyArray<number> | undefined)?.length, 3)
})

it("a generated function answers the same result for the same arguments", () => {
  const [f] = fc.sample(arbitraryOf({ kind: "function", returns: { kind: "number" } }, fc.string(), 4), { seed: 7, numRuns: 1 }) as [
    (...args: Array<unknown>) => number,
  ]
  for (const args of [["a"], ["b", 1], [], [{ k: 2n }]]) {
    const first = f(...args)
    for (let i = 0; i < 100; i++) assert.ok(Object.is(f(...args), first))
  }
})

it("a spec no module exports is read through the loader, and its implementation's broken law found", async () => {
  const p = planned("implemented", "half")
  assert.equal(p.spec?.name, "halfSpec")
  const r = await runContract(p)
  ranTrue(r)
  assert.deepEqual(Object.keys(r.broken), ["twiceIsWhole"])
  const [n] = r.broken.twiceIsWhole!.args as [bigint]
  assert.notEqual(half(n) * 2n, n)
})

it("a declaration the real function breaks is found broken by running it", async () => {
  const r = await ranOf("wrong-assume", "scored")
  ranTrue(r)
  assert.deepEqual(r.broken.nonNegative?.args, ["a"])
})

it("an input on which the function throws is skipped and counted, never a counterexample", async () => {
  const r = await ranOf("throws", "divided")
  const ran = ranTrue(r)
  assert.ok(ran.threw > 0, JSON.stringify(ran))
  assert.deepEqual(r.broken, {})
  // Whether it says something is of the spec alone: at 0n, where the code throws, a free result breaks it.
  assert.deepEqual(r.saysSomething, ["atZero"])
})

it("a child that never ends is stopped", async () => {
  const r = await runContract(planned("stuck", "endless"), { stuckMs: 3000 })
  assert.deepEqual(r.ran.ran ? undefined : r.ran.stuck, true)
})

it("each type's shape: brands as their primitive, a library's mapped type as the object, recursion cut; the rest refused, named", () => {
  const file = path.join(root, "fixtures/runs/shapes.ts")
  const p = loadProject([file], path.join(root, "tsconfig.json"))
  const sf = p.program.getSourceFile(file)!
  const shape = (name: string) => {
    const d = sf.statements.find((s): s is ts.TypeAliasDeclaration => ts.isTypeAliasDeclaration(s) && s.name.text === name)!
    return shapeOf(p.checker, p.checker.getTypeAtLocation(d.name))
  }
  assert.deepEqual(shape("Flag"), { kind: "boolean" })
  assert.deepEqual(shape("Id"), { kind: "string" })
  assert.deepEqual(shape("Ledger"), { kind: "dictionary", of: { kind: "number" } })
  assert.deepEqual(shape("Pair"), { kind: "tuple", of: [{ kind: "string" }], rest: { kind: "bigint" } })
  assert.deepEqual(shape("Lookup"), {
    kind: "function",
    returns: {
      kind: "union",
      of: [
        { kind: "literal", value: "a" },
        { kind: "literal", value: "b" },
      ],
    },
  })
  const order = shape("Order")
  assert.equal(order.kind, "record")
  if (order.kind === "record") {
    assert.deepEqual(order.fields.id, { kind: "string" })
    assert.deepEqual(order.fields.lines, { kind: "array", of: { kind: "record", fields: { qty: { kind: "number" } }, optional: [] } })
    assert.deepEqual(order.fields.tags, { kind: "set", of: { kind: "string" } })
    assert.equal(order.fields.by?.kind, "map")
  }
  // Four records deep, then the optional child is cut: only ever left out.
  let tree: Shape | undefined = shape("Tree")
  let records = 0
  while (tree?.kind === "record") {
    records++
    const c: Shape | undefined = tree.fields.children
    tree = c?.kind === "union" ? c.of.find((m) => m.kind === "record") : c
  }
  assert.equal(records, 4)
  assert.deepEqual(tree, { kind: "undefined" })
  // `unknown` is any value: a run gives it the primitives, each a value it may be.
  const primitives = {
    kind: "union",
    of: [{ kind: "undefined" }, { kind: "null" }, { kind: "boolean" }, { kind: "number" }, { kind: "string" }],
  }
  assert.deepEqual(shape("Anything"), primitives)
  // `object`: an empty one is a value of it.
  assert.deepEqual(shape("Some"), { kind: "record", fields: {}, optional: [] })
  // Fields beside keys of its own: the fields alone, a value of the type with no other key.
  assert.deepEqual(shape("Schema"), {
    kind: "record",
    fields: { type: { kind: "literal", value: "object" }, required: { kind: "array", of: { kind: "string" } } },
    optional: [],
  })
  for (const [name, text] of [
    ["When", "Date"],
    ["Loose", "any"],
    ["Held", "Account"],
  ] as const)
    assert.throws(
      () => shape(name),
      (e: unknown) => e instanceof NotRunnable && e.message.includes(text),
    )
})

// Through `verify`: a run is asked before any proof, and what it settles Z3 is not asked.
let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const verified = (name: string, contract: string, opts: Options = {}) => verify(z3, project, fixture(name), contract, opts)

it("a law a run breaks is a counterexample by running, never asked of Z3; the law it keeps is proved by Z3", async () => {
  const v = await verified("broken", "priced", { run: true })
  const broken = v.laws.find((l) => l.name === "tenEach")!
  assert.deepEqual([broken.status, broken.by], ["counterexample", "run"])
  const [qty] = broken.args as [number]
  assert.notEqual(price(qty), qty * 10)
  assert.ok(!broken.asked?.some((a) => a.question === "proof" || a.question === "search"), JSON.stringify(broken.asked))
  const kept = v.laws.find((l) => l.name === "notNegative")!
  assert.deepEqual([kept.status, kept.by], ["proved", "z3"])
  // Shown to say something by a run: no says-anything query for Z3.
  assert.ok(
    kept.asked?.some((a) => a.question === "says-anything" && a.by === "run"),
    JSON.stringify(kept.asked),
  )
  assert.ok(!kept.asked?.some((a) => a.question === "says-anything" && a.by === "z3"), JSON.stringify(kept.asked))
  assert.equal(v.ran?.ran, true)
  // Without `run`, nothing runs: the same verdicts, each by Z3.
  const alone = await verified("broken", "priced")
  assert.equal(alone.ran, undefined)
  assert.deepEqual(
    alone.laws.map((l) => [l.status, l.by]),
    [
      ["proved", "z3"],
      ["counterexample", "z3"],
    ],
  )
})

it("a contract whose module cannot load is not run, says why, and keeps the verdicts Z3 alone gives", async () => {
  const v = await verified("enum", "leveled", { run: true })
  assert.ok(v.ran?.ran === false && v.ran.why.includes("ERR_UNSUPPORTED_TYPESCRIPT_SYNTAX"), JSON.stringify(v.ran))
  const alone = await verified("enum", "leveled")
  assert.ok(alone.laws.length > 0 && alone.unsupported === undefined, JSON.stringify(alone))
  assert.deepEqual(
    v.laws.map((l) => [l.status, l.by]),
    alone.laws.map((l) => [l.status, l.by]),
  )
})

it("a counterexample longer than the bound is Z3's to find", async () => {
  const v = await verified("bounded", "short", { run: true, bound: 2 })
  const l = v.laws[0]!
  assert.deepEqual([l.status, l.by], ["counterexample", "z3"])
  assert.equal((l.args![0] as ReadonlyArray<number>).length, 3)
})

it("a law a run breaks and Z3 proves at that input names the declaration it leaned on", async () => {
  const v = await verified("wrong-assume", "scored", { run: true })
  const l = v.laws[0]!
  assert.deepEqual([l.status, l.by], ["counterexample", "run"])
  assert.ok(l.reason?.includes("scoreIsPure") === true || l.reason?.includes("score") === true, l.reason)
  assert.ok(
    l.asked?.some((a) => a.question === "cross-check" && a.by === "z3"),
    JSON.stringify(l.asked),
  )
  // Z3 alone proves it, leaning on the declaration.
  assert.equal((await verified("wrong-assume", "scored")).laws[0]!.status, "proved")
})
