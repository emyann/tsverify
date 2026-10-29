// One withdrawal written twice, as an Effect program and as async TypeScript
// (examples/account), each typed by its spec (withdraw.spec.ts), the specs
// holding the same five laws. Proved on both; every end
// each can come to reached; the laws hold when the programs run against a
// stand-in ledger; and eight bugs planted in each are caught by the solver,
// each confirmed by running the planted program.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { Effect, Layer } from "effect"
import type { Entry } from "../examples/account/account.ts"
import * as laws from "../examples/account/laws.ts"
import type { LedgerCall, WithdrawOutcome } from "../examples/account/laws.ts"
import * as effectProgram from "../examples/account/withdraw.ts"
import * as asyncProgram from "../examples/account/withdraw.async.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "examples/account/withdraw.spec.ts")
const tsconfig = path.join(root, "tsconfig.json")
const effectFile = path.join(root, "examples/account/withdraw.ts")
const asyncFile = path.join(root, "examples/account/withdraw.async.ts")
const project = loadProject([spec, effectFile, asyncFile], tsconfig)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const LAWS = ["readsFirst", "readFailurePassesThrough", "refusedWritesNothing", "paidWritesOneWithdrawal", "refusedExactlyWhenTheGuardSays"] as const
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

describe("a withdrawal, as an Effect program and as async TypeScript, under the same five laws", () => {
  it("the spec type-checks against both programs' types", () => {
    assert.deepEqual(diagnostics(project, spec), [])
  })

  for (const [kind, file, ends] of [
    ["the Effect program", effectFile, ["Success", "Failure LedgerError", "Failure WithdrawalRefused"]],
    ["the async program", asyncFile, ["Success", "Failure"]],
  ] as const)
    it(`${kind}, typed by its spec: all five laws proved, every end it can come to reached`, async () => {
      const v = await verify(z3, project, file, "withdraw")
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(statuses(v), Object.fromEntries(LAWS.map((l) => [l, "proved"])))
      assert.deepEqual(v.cover.map((c) => `${c.value} ${c.status}`).sort(), ends.map((e) => `${e} reachable`).sort())
      // The fold is declared, not read here; the report names the declaration and says its purity was checked.
      assert.deepEqual(v.trusted.map((t) => [t.name, t.purity, t.laws]), [["accountOf", "checked", []]])
    })
})

describe("the spec's type constrains the code", () => {
  it("an Effect implementation failing with an error its spec does not declare does not type-check", () => {
    const text = readFileSync(effectFile, "utf8").replace("new WithdrawalRefused({ message: refused })", "new Error(refused)")
    const errors = diagnostics(loadProject([effectFile], tsconfig, new Map([[effectFile, text]])), effectFile)
    assert.ok(errors.some((e) => /Implementation|not assignable/.test(e)), errors.join("\n"))
  })
})

// The runs: ledgers a stand-in serves, read and append each able to fail.
const at = "2026-10-29T12:00:00.000Z"
const opened: Entry = { kind: "opened", at, owner: "ada" }
const funded: Entry = { kind: "deposited", at, id: "d1", amount: 100n }
const LEDGERS: ReadonlyArray<ReadonlyArray<Entry>> = [
  [],
  [opened],
  [opened, funded],
  [opened, funded, { kind: "frozen", at, reason: "audit" }],
  [opened, funded, { kind: "closed", at }],
]
const RUNS = ["a-1", ""].flatMap((accountId) =>
  LEDGERS.flatMap((entries) =>
    [50n, 500n, 0n].flatMap((amount) => [
      { accountId, entries, amount, failRead: false, failAppend: false },
      { accountId, entries, amount, failRead: true, failAppend: false },
      { accountId, entries, amount, failRead: false, failAppend: true },
    ]),
  ),
)
type Run = (typeof RUNS)[number]
type Ran = { readonly out: WithdrawOutcome; readonly calls: ReadonlyArray<LedgerCall> }

const failureOf = (e: unknown): WithdrawOutcome => ({ _tag: "Failure", error: e as { _tag: string } })

const runEffect = async (program: typeof effectProgram, r: Run): Promise<Ran> => {
  const calls: Array<LedgerCall> = []
  const ledger = program.Ledger.of({
    read: (id) => {
      const error = new program.LedgerError({ accountId: id, message: "unreadable" })
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.entries } })
      return r.failRead ? Effect.fail(error) : Effect.succeed(r.entries)
    },
    append: (id, entry) => {
      const error = new program.LedgerError({ accountId: id, message: "unwritable" })
      calls.push({ op: "append", args: [id, entry], outcome: r.failAppend ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      return r.failAppend ? Effect.fail(error) : Effect.void
    },
  })
  const withdrawal = program.withdraw(r.accountId, "w1", r.amount).pipe(Effect.provide(Layer.succeed(program.Ledger)(ledger)))
  const result = await Effect.runPromise(Effect.result(withdrawal))
  return { out: result._tag === "Success" ? { _tag: "Success", value: undefined } : failureOf(result.failure), calls }
}

const runAsync = async (program: typeof asyncProgram, r: Run): Promise<Ran> => {
  const calls: Array<LedgerCall> = []
  const ledger: asyncProgram.LedgerPort = {
    read: async (id) => {
      const error = new program.LedgerError("unreadable")
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.entries } })
      if (r.failRead) throw error
      return r.entries
    },
    append: async (id, entry) => {
      const error = new program.LedgerError("unwritable")
      calls.push({ op: "append", args: [id, entry], outcome: r.failAppend ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      if (r.failAppend) throw error
    },
  }
  try {
    await program.withdraw(ledger, r.accountId, "w1", r.amount)
    return { out: { _tag: "Success", value: undefined }, calls }
  } catch (e) {
    return { out: failureOf(e), calls }
  }
}

/** The laws a run breaks. */
const broken = (r: Run, ran: Ran): Array<string> => LAWS.filter((l) => !laws[l](r.accountId, "w1", r.amount, ran.out, ran.calls))

describe("the laws hold when the programs run", () => {
  it(`the Effect program, on ${RUNS.length} runs`, async () => {
    for (const r of RUNS) assert.deepEqual(broken(r, await runEffect(effectProgram, r)), [], JSON.stringify(r, (_, x) => (typeof x === "bigint" ? `${x}n` : x)))
  })
  it("the async program, on the same runs", async () => {
    for (const r of RUNS) assert.deepEqual(broken(r, await runAsync(asyncProgram, r)), [], JSON.stringify(r, (_, x) => (typeof x === "bigint" ? `${x}n` : x)))
  })
})

// Planted bugs: one text change in each program, the same bug in both.
interface Plant {
  readonly id: string
  readonly what: string
  readonly effect: readonly [string, string]
  readonly async: readonly [string, string]
}
const E_GUARD = "  if (refused) return yield* Effect.fail(new WithdrawalRefused({ message: refused }))\n"
const E_WRITE = '  yield* ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })\n'
const A_GUARD = "  if (refused) throw new WithdrawalRefused(refused)\n"
const A_WRITE = '  await ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })\n'
const PLANTS: ReadonlyArray<Plant> = [
  { id: "B1", what: "writes before the guard", effect: [E_GUARD + E_WRITE, E_WRITE + E_GUARD], async: [A_GUARD + A_WRITE, A_WRITE + A_GUARD] },
  {
    id: "B2",
    what: "the guard inverted",
    effect: ["if (refused) return yield* Effect.fail(new WithdrawalRefused({ message: refused }))", 'if (!refused) return yield* Effect.fail(new WithdrawalRefused({ message: "no" }))'],
    async: ["if (refused) throw new WithdrawalRefused(refused)", 'if (!refused) throw new WithdrawalRefused("no")'],
  },
  { id: "B3", what: "writes a deposit", effect: ['kind: "withdrawn"', 'kind: "deposited"'], async: ['kind: "withdrawn"', 'kind: "deposited"'] },
  { id: "B4", what: "writes to another account", effect: ["ledger.append(accountId,", 'ledger.append("*",'], async: ["ledger.append(accountId,", 'ledger.append("*",'] },
  { id: "B5", what: "writes twice", effect: [E_WRITE, E_WRITE + E_WRITE], async: [A_WRITE, A_WRITE + A_WRITE] },
  { id: "B6", what: "refuses only an empty account id", effect: ["if (refused) return", 'if (refused && accountId === "") return'], async: ["if (refused) throw", 'if (refused && accountId === "") throw'] },
  { id: "B7", what: "reads another account", effect: ["ledger.read(accountId)", 'ledger.read("*")'], async: ["ledger.read(accountId)", 'ledger.read("*")'] },
  { id: "B8", what: "writes a fixed amount", effect: ["id, amount })", "id, amount: 1n })"], async: ["id, amount })", "id, amount: 1n })"] },
]

/** `text` with `[find, replace]` applied, where `find` must occur exactly once. */
const plant = (text: string, [find, replace]: readonly [string, string], id: string): string => {
  assert.equal(text.split(find).length - 1, 1, `${id}: \`${find}\` must occur once`)
  return text.replace(find, replace)
}

/** The planted program, written beside the original so its imports resolve, loaded, then removed. */
const loaded = async <M>(file: string, id: string, text: string): Promise<M> => {
  const planted = file.replace(/\.ts$/, `.planted-${id}.ts`).replace("withdraw.async.planted", "withdraw.planted-async")
  writeFileSync(planted, text)
  try {
    return (await import(pathToFileURL(planted).href)) as M
  } finally {
    rmSync(planted)
  }
}

describe("planted bugs", () => {
  for (const p of PLANTS)
    for (const [kind, file, change] of [
      ["the Effect program", effectFile, p.effect],
      ["the async program", asyncFile, p.async],
    ] as const)
      it(`${p.id}, ${p.what}: caught in ${kind}, and the planted program breaks a law it refutes when run`, async () => {
        const text = plant(readFileSync(file, "utf8"), change, p.id)
        const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, "withdraw")
        assert.equal(v.unsupported, undefined)
        const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
        assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
        const seen = new Set<string>()
        if (file === effectFile) {
          const program = await loaded<typeof effectProgram>(file, p.id, text)
          for (const r of RUNS) for (const l of broken(r, await runEffect(program, r))) seen.add(l)
        } else {
          const program = await loaded<typeof asyncProgram>(file, p.id, text)
          for (const r of RUNS) for (const l of broken(r, await runAsync(program, r))) seen.add(l)
        }
        assert.ok(refuted.some((l) => seen.has(l)), `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`)
      })
})
