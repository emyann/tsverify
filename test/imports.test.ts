// The programs that take text written elsewhere (examples/account/imports.ts):
// `Effect.try` with a typed error and with an `unknown` one, a step inside an
// expression, a loop of steps over an array of known length and over one of
// unknown length; and their async twins (imports.async.ts), an `await` inside
// an expression and a loop of them, read by the same core. What can be proved
// is; a loop over unknown length is bounded, and says why; the laws hold when
// the programs run against a stand-in ledger; and a bug planted in each form
// is caught, the planted program breaking a law it refutes when run.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { Effect, Layer } from "effect"
import type { Entry } from "../examples/account/account.ts"
import * as asyncPrograms from "../examples/account/imports.async.ts"
import * as programs from "../examples/account/imports.ts"
import * as spec from "../examples/account/imports.contract.ts"
import { Ledger, LedgerError } from "../examples/account/withdraw.ts"
import * as port from "../examples/account/withdraw.async.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const specFile = path.join(root, "examples/account/imports.contract.ts")
const source = path.join(root, "examples/account/imports.ts")
const asyncSource = path.join(root, "examples/account/imports.async.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([specFile], tsconfig)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const ends = (v: Verification) => v.cover.map((c) => `${c.value}: ${c.status}`).sort()

describe("the programs that take text, verified", () => {
  it("the spec type-checks", () => {
    assert.deepEqual(diagnostics(project, specFile), [])
  })

  it("typed (`Effect.try` with a typed error, a step inside an expression): every law proved, every end reached", async () => {
    const v = await verify(z3, project, specFile, "typed")
    assert.equal(v.unsupported, undefined)
    assert.ok(
      v.laws.every((l) => l.status === "proved"),
      JSON.stringify(statuses(v)),
    )
    assert.deepEqual(ends(v), [
      "Failure AmountUnreadable: reachable",
      "Failure DepositRefused: reachable",
      "Failure LedgerError: reachable",
      "Success: reachable",
    ])
  })

  it("opened (a loop over an array of known length): every law proved, every end reached", async () => {
    const v = await verify(z3, project, specFile, "opened")
    assert.equal(v.unsupported, undefined)
    assert.ok(
      v.laws.every((l) => l.status === "proved"),
      JSON.stringify(statuses(v)),
    )
    assert.deepEqual(ends(v), ["Failure DepositRefused: reachable", "Failure LedgerError: reachable", "Success: reachable"])
  })

  it("imported (a loop over an array of unknown length, an `unknown` error): every law bounded, the loop named as why", async () => {
    const v = await verify(z3, project, specFile, "imported")
    assert.equal(v.unsupported, undefined)
    assert.ok(
      v.laws.every((l) => l.status === "bounded"),
      JSON.stringify(statuses(v)),
    )
    for (const name of ["writesOnlyDepositsHere", "stopsAtAFailedWrite", "failsOnlyWhereItStopped"])
      assert.match(v.laws.find((l) => l.name === name)!.reason!, /runs a loop in a computation at most 4 times \(.*imports\.ts:35:3\)/)
    // An error of type `unknown` has no `_tag` to name: one failure, undistinguished.
    assert.deepEqual(ends(v), ["Failure: reachable", "Success: reachable"])
  })

  it("balanced (async, an `await` inside an expression): every law proved", async () => {
    const v = await verify(z3, project, specFile, "balanced")
    assert.equal(v.unsupported, undefined)
    assert.ok(
      v.laws.every((l) => l.status === "proved"),
      JSON.stringify(statuses(v)),
    )
  })

  it("copied (async, a loop of `await`s over an array of unknown length): every law bounded", async () => {
    const v = await verify(z3, project, specFile, "copied")
    assert.equal(v.unsupported, undefined)
    assert.ok(
      v.laws.every((l) => l.status === "bounded"),
      JSON.stringify(statuses(v)),
    )
    assert.match(
      v.laws.find((l) => l.name === "writesOnlyDepositsToTheTarget")!.reason!,
      /runs a loop in a computation at most 4 times \(.*imports\.async\.ts:13:3\)/,
    )
  })
})

// The runs: texts a person typed, exports another system wrote, and a stand-in ledger whose read can fail and whose
// append can fail at a given call.
type Call = {
  readonly op: "read" | "append"
  readonly args: readonly unknown[]
  readonly outcome: { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: unknown }
}
type Out = { readonly _tag: "Success"; readonly value: unknown } | { readonly _tag: "Failure"; readonly error: unknown }
const at = "2026-10-29T12:00:00.000Z"
const opened: Entry = { kind: "opened", at, owner: "ada" }
const funded: ReadonlyArray<Entry> = [opened, { kind: "deposited", at, id: "d1", amount: 70n }]
const exported = (entries: ReadonlyArray<Entry>) => JSON.stringify(entries, (_, x) => (typeof x === "bigint" ? String(x) : x))
const EXPORTS = [
  "[]",
  "not json",
  exported([{ kind: "deposited", at, id: "d1", amount: 5n }]),
  exported([
    opened,
    { kind: "deposited", at, id: "d1", amount: 5n },
    { kind: "withdrawn", at, id: "w1", amount: 2n },
    { kind: "deposited", at, id: "d2", amount: 7n },
  ]),
]
const RUNS = [[], funded].flatMap((entries) =>
  [false, true].flatMap((failRead) =>
    [undefined, 0, 1].flatMap((failAppendAt) =>
      ["30", "0", "x", ""].flatMap((text) => EXPORTS.map((json) => ({ accountId: "a-1", entries, failRead, failAppendAt, text, json }))),
    ),
  ),
)
type Run = (typeof RUNS)[number]

const running = async <A, E>(program: Effect.Effect<A, E, Ledger>, r: Run): Promise<{ out: Out; calls: Array<Call> }> => {
  const calls: Array<Call> = []
  let appends = 0
  const ledger = Ledger.of({
    read: (id) => {
      const error = new LedgerError({ accountId: id, message: "unreadable" })
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.entries } })
      return r.failRead ? Effect.fail(error) : Effect.succeed(r.entries)
    },
    append: (id, entry) => {
      const fails = appends++ === r.failAppendAt
      const error = new LedgerError({ accountId: id, message: "unwritable" })
      calls.push({ op: "append", args: [id, entry], outcome: fails ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      return fails ? Effect.fail(error) : Effect.void
    },
  })
  const result = await Effect.runPromise(Effect.result(program.pipe(Effect.provide(Layer.succeed(Ledger)(ledger)))))
  return { out: result._tag === "Success" ? { _tag: "Success", value: result.success } : { _tag: "Failure", error: result.failure }, calls }
}

/** The same stand-in, as the async programs' port: what fails is thrown. */
const runningAsync = async <A>(program: (ledger: port.LedgerPort) => Promise<A>, r: Run): Promise<{ out: Out; calls: Array<Call> }> => {
  const calls: Array<Call> = []
  let appends = 0
  const ledger: port.LedgerPort = {
    read: async (id) => {
      const error = new port.LedgerError("unreadable")
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.entries } })
      if (r.failRead) throw error
      return r.entries
    },
    append: async (id, entry) => {
      const fails = appends++ === r.failAppendAt
      const error = new port.LedgerError("unwritable")
      calls.push({ op: "append", args: [id, entry], outcome: fails ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      if (fails) throw error
    },
  }
  try {
    return { out: { _tag: "Success", value: await program(ledger) }, calls }
  } catch (error) {
    return { out: { _tag: "Failure", error }, calls }
  }
}

type Programs = typeof programs
type AsyncPrograms = typeof asyncPrograms
const CONTRACTS = ["typed", "imported", "opened", "balanced", "copied"] as const
type Contract = (typeof CONTRACTS)[number]
/** Each contract's program, run on `r`, and the laws of its contract it breaks. */
const brokenBy = async (p: Programs, a: AsyncPrograms, r: Run): Promise<Record<Contract, Array<string>>> => {
  const amount = /^-?\d+$/.test(r.text) ? BigInt(r.text) : 30n
  const ran = {
    typed: [[r.accountId, "d2", r.text], await running(p.depositTyped(r.accountId, "d2", r.text), r)],
    imported: [[r.accountId, r.json], await running(p.importDeposits(r.accountId, r.json), r)],
    opened: [[r.accountId, "ada", "d1", amount], await running(p.openWith(r.accountId, "ada", "d1", amount), r)],
    // The port is the first argument; the laws do not read it.
    balanced: [[undefined, r.accountId], await runningAsync((l) => a.balanceOf(l, r.accountId), r)],
    copied: [[undefined, r.accountId, "b-2"], await runningAsync((l) => a.copyDeposits(l, r.accountId, "b-2"), r)],
  } as const
  const out = Object.fromEntries(CONTRACTS.map((c) => [c, []])) as unknown as Record<Contract, Array<string>>
  for (const name of CONTRACTS) {
    const [args, { out: o, calls }] = ran[name]
    const laws = (spec as unknown as Record<string, { ensures: Record<string, (run: unknown) => boolean> }>)[name]!.ensures
    out[name] = Object.entries(laws)
      .filter(([, law]) => !law({ input: args, output: o, calls }))
      .map(([l]) => l)
  }
  return out
}

const shown = (x: unknown) => JSON.stringify(x, (_, v) => (typeof v === "bigint" ? `${v}n` : v))

describe("the laws hold when the programs run", () => {
  it(`on ${RUNS.length} runs of each`, async () => {
    const none = Object.fromEntries(CONTRACTS.map((c) => [c, []]))
    for (const r of RUNS) assert.deepEqual(await brokenBy(programs, asyncPrograms, r), none, shown(r))
  })
})

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  readonly contract: Contract
  /** The async programs' file, not the Effect programs'. */
  readonly async?: true
}
const PLANTS: ReadonlyArray<Plant> = [
  {
    id: "Y1",
    what: "Effect.try: the error names no text",
    change: ["new AmountUnreadable({ text })", 'new AmountUnreadable({ text: "" })'],
    contract: "typed",
  },
  {
    id: "Y2",
    what: "Effect.try: an unreadable amount is a refusal",
    change: ["new AmountUnreadable({ text })", "new DepositRefused({ message: text })"],
    contract: "typed",
  },
  {
    id: "S1",
    what: "a step inside an expression: the ledger read before the amount is parsed",
    change: ["yield* amountOf(text))", "yield* (yield* Ledger).read(accountId).pipe(Effect.flatMap(() => amountOf(text))))"],
    contract: "typed",
  },
  {
    id: "L1",
    what: "a loop of steps: writes to another account",
    change: ["yield* ledger.append(accountId, e)", 'yield* ledger.append("*", e)'],
    contract: "imported",
  },
  {
    id: "L2",
    what: "a loop of steps: writes every entry, not only the deposits",
    change: ['if (e.kind === "deposited") yield* ledger.append', "yield* ledger.append"],
    contract: "imported",
  },
  {
    id: "L3",
    what: "a loop of steps: a failed write is passed over",
    change: ["yield* ledger.append(accountId, e)", "yield* ledger.append(accountId, e).pipe(Effect.catch(() => Effect.void))"],
    contract: "imported",
  },
  {
    id: "L4",
    what: "a loop over a known array: the deposit before the opening",
    change: ['    { kind: "opened", at, owner },\n', ""],
    contract: "opened",
  },
  {
    id: "A1",
    what: "async, an `await` inside an expression: the ledger read twice",
    change: ["accountOf(await ledger.read(accountId))", "accountOf(await ledger.read(accountId) && (await ledger.read(accountId)))"],
    contract: "balanced",
    async: true,
  },
  {
    id: "A2",
    what: "async, a loop of `await`s: copies into the source",
    change: ["await ledger.append(to, e)", "await ledger.append(from, e)"],
    contract: "copied",
    async: true,
  },
  {
    id: "A3",
    what: "async, a loop of `await`s: copies every entry, not only the deposits",
    change: ['if (e.kind === "deposited") await', "await"],
    contract: "copied",
    async: true,
  },
]

/** The planted program, written beside the original so its imports resolve, loaded, then removed. */
const loaded = async <M>(file: string, id: string, text: string): Promise<M> => {
  const planted = file.replace(/\.ts$/, `.planted-${id}.ts`).replace("imports.async.planted", "imports.planted-async")
  writeFileSync(planted, text)
  try {
    return (await import(pathToFileURL(planted).href)) as M
  } finally {
    rmSync(planted)
  }
}

describe("a bug planted in each form", () => {
  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: caught, and the planted program breaks a law it refutes when run`, async () => {
      const file = p.async ? asyncSource : source
      const original = readFileSync(file, "utf8")
      assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
      const text = original.replace(p.change[0], p.change[1])
      const v = await verify(z3, loadProject([specFile], tsconfig, new Map([[file, text]])), specFile, p.contract)
      assert.equal(v.unsupported, undefined)
      const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
      assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
      const [effects, asyncs] = p.async
        ? [programs, await loaded<AsyncPrograms>(file, p.id, text)]
        : [await loaded<Programs>(file, p.id, text), asyncPrograms]
      const seen = new Set<string>()
      for (const r of RUNS) for (const l of (await brokenBy(effects, asyncs, r))[p.contract]) seen.add(l)
      assert.ok(
        refuted.some((l) => seen.has(l)),
        `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`,
      )
    })
})
