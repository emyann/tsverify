// The Effect forms beyond `Effect.fn`: `Effect.gen` returned by a function,
// `.pipe` and `pipe`, `map`, `flatMap`, `catch`, `catchTag` and `sync`
// (examples/account/effects.ts). Every law proved, every end reached; the laws
// hold when the programs run against a stand-in ledger; and a bug planted in
// each form is caught, the planted program breaking a law it refutes when run.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { Effect, Layer } from "effect"
import type { Entry } from "../examples/account/account.ts"
import * as programs from "../examples/account/effects.ts"
import * as spec from "../examples/account/effects.spec.ts"
import { Ledger, LedgerError } from "../examples/account/withdraw.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const specFile = path.join(root, "examples/account/effects.spec.ts")
const source = path.join(root, "examples/account/effects.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([specFile], tsconfig)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const CONTRACTS = {
  balance: ["Success", "Failure LedgerError"],
  // `catch` handles every failure: the verifier proves none is left.
  balanceOrNothing: ["Success", "Failure unreachable"],
  doubled: ["Success", "Failure LedgerError"],
  deposited: ["Success", "Failure DepositRefused", "Failure LedgerError"],
} as const

describe("the Effect forms, verified", () => {
  it("the spec type-checks", () => {
    assert.deepEqual(diagnostics(project, specFile), [])
  })
  for (const [name, ends] of Object.entries(CONTRACTS))
    it(`${name}: every law proved, every end it can come to reached`, async () => {
      const v = await verify(z3, project, specFile, name)
      assert.equal(v.unsupported, undefined)
      assert.ok(v.laws.every((l) => l.status === "proved"), JSON.stringify(statuses(v)))
      const want = ends.map((e) => (e.endsWith(" unreachable") ? e : `${e} reachable`))
      assert.deepEqual(v.cover.map((c) => `${c.value} ${c.status}`).sort(), want.sort())
    })
})

// The runs: ledgers a stand-in serves, read and append each able to fail.
type Call = {
  readonly op: "read" | "append"
  readonly args: readonly unknown[]
  readonly outcome: { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: unknown }
}
type Out = { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: { readonly _tag: string } }
const at = "2026-10-29T12:00:00.000Z"
const opened: Entry = { kind: "opened", at, owner: "ada" }
const LEDGERS: ReadonlyArray<ReadonlyArray<Entry>> = [[], [opened], [opened, { kind: "deposited", at, id: "d1", amount: 70n }], [opened, { kind: "closed", at }]]
const RUNS = LEDGERS.flatMap((entries) =>
  [false, true].flatMap((failRead) =>
    [false, true].flatMap((failAppend) => [30n, 0n].map((amount) => ({ accountId: "a-1", entries, failRead, failAppend, amount }))),
  ),
)
type Run = (typeof RUNS)[number]

const running = async <A, E>(program: Effect.Effect<A, E, Ledger>, r: Run): Promise<{ out: Out; calls: Array<Call> }> => {
  const calls: Array<Call> = []
  const ledger = Ledger.of({
    read: (id) => {
      const error = new LedgerError({ accountId: id, message: "unreadable" })
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.entries } })
      return r.failRead ? Effect.fail(error) : Effect.succeed(r.entries)
    },
    append: (id, entry) => {
      const error = new LedgerError({ accountId: id, message: "unwritable" })
      calls.push({ op: "append", args: [id, entry], outcome: r.failAppend ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      return r.failAppend ? Effect.fail(error) : Effect.void
    },
  })
  const result = await Effect.runPromise(Effect.result(program.pipe(Effect.provide(Layer.succeed(Ledger)(ledger)))))
  return { out: result._tag === "Success" ? { _tag: "Success", value: result.success } : { _tag: "Failure", error: result.failure as { _tag: string } }, calls }
}

type Programs = typeof programs
/** Each contract's program, run on `r`, and the laws of its contract it breaks. */
const brokenBy = async (p: Programs, r: Run): Promise<Record<string, Array<string>>> => {
  const ran = {
    balance: [[r.accountId], await running(p.balanceOf(r.accountId), r)],
    balanceOrNothing: [[r.accountId], await running(p.balanceOrZero(r.accountId), r)],
    doubled: [[r.accountId], await running(p.doubledBalance(r.accountId), r)],
    deposited: [[r.accountId, "d2", r.amount], await running(p.deposit(r.accountId, "d2", r.amount), r)],
  } as const
  const out: Record<string, Array<string>> = {}
  for (const [name, [args, { out: o, calls }]] of Object.entries(ran)) {
    const laws = (spec as unknown as Record<string, { ensures: Record<string, (...a: unknown[]) => boolean> }>)[name]!.ensures
    out[name] = Object.entries(laws)
      .filter(([, law]) => !law(...args, o, calls))
      .map(([l]) => l)
  }
  return out
}

describe("the laws hold when the programs run", () => {
  it(`on ${RUNS.length} runs of each`, async () => {
    for (const r of RUNS) assert.deepEqual(await brokenBy(programs, r), { balance: [], balanceOrNothing: [], doubled: [], deposited: [] }, JSON.stringify(r, (_, x) => (typeof x === "bigint" ? `${x}n` : x)))
  })
})

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  readonly contract: keyof typeof CONTRACTS
}
const PLANTS: ReadonlyArray<Plant> = [
  { id: "G1", what: "Effect.gen: reads the ledger twice", change: ["    const entries = yield* ledger.read(accountId)\n", "    yield* ledger.read(accountId)\n    const entries = yield* ledger.read(accountId)\n"], contract: "balance" },
  { id: "C1", what: "Effect.catch: an unreadable ledger reads as 1", change: ["Effect.catch(() => Effect.succeed(0n))", "Effect.catch(() => Effect.succeed(1n))"], contract: "balanceOrNothing" },
  { id: "P1", what: "pipe and Effect.map: three times, not twice", change: ["Effect.map((b) => b + b)", "Effect.map((b) => b + b + b)"], contract: "doubled" },
  { id: "M1", what: "Effect.map: the guard asked of 1, not the amount", change: ["depositRefusalOf(accountOf(entries), amount)", "depositRefusalOf(accountOf(entries), 1n)"], contract: "deposited" },
  { id: "T1", what: "Effect.catchTag: an unreadable ledger is no refusal", change: ['Effect.succeed("the ledger cannot be read now: try again later")', "Effect.succeed(undefined)"], contract: "deposited" },
  { id: "T2", what: "Effect.catchTag left out", change: ['    Effect.catchTag("LedgerError", () => Effect.succeed("the ledger cannot be read now: try again later")),\n', ""], contract: "deposited" },
  { id: "F1", what: "Effect.flatMap: writes twice the amount", change: ['{ kind: "deposited", at, id, amount }', '{ kind: "deposited", at, id, amount: amount + amount }'], contract: "deposited" },
  { id: "F2", what: "Effect.catch: a failed write is swallowed", change: ['(at) => ledger.append(accountId, { kind: "deposited", at, id, amount }),\n  )', '(at) => ledger.append(accountId, { kind: "deposited", at, id, amount }),\n  ).pipe(Effect.catch(() => Effect.void))'], contract: "deposited" },
]

describe("a bug planted in each form", () => {
  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: caught, and the planted program breaks a law it refutes when run`, async () => {
      const original = readFileSync(source, "utf8")
      assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
      const text = original.replace(p.change[0], p.change[1])
      const v = await verify(z3, loadProject([specFile], tsconfig, new Map([[source, text]])), specFile, p.contract)
      assert.equal(v.unsupported, undefined)
      const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
      assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
      const file = path.join(root, `examples/account/effects.planted-${p.id}.ts`)
      writeFileSync(file, text)
      try {
        const planted = (await import(pathToFileURL(file).href)) as Programs
        const seen = new Set<string>()
        for (const r of RUNS) for (const l of (await brokenBy(planted, r))[p.contract]!) seen.add(l)
        assert.ok(refuted.some((l) => seen.has(l)), `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`)
      } finally {
        rmSync(file)
      }
    })
})
