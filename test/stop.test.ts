// The design's proof: Nemia's Effect verb `requestStop`, read in place, and
// its async twin, held to the same five laws. Proved on both; every end each
// can come to reached; the laws hold when the real programs run against a
// stand-in journal; and seven bugs planted in each are caught by the solver,
// those in the twin confirmed by running the planted code.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { Effect, Layer } from "effect"
import { init, killThreads } from "z3-solver"
import type { Event } from "../../hkb-v2/packages/agent-runtime/src/core/domain.ts"
import { requestStop } from "../../hkb-v2/packages/agent-runtime/src/core/engine/filing.ts"
import { Journal, JournalError } from "../../hkb-v2/packages/agent-runtime/src/core/engine/journal.ts"
import * as laws from "../pilots/stop/laws.ts"
import type { StopCall, StopOutcome } from "../pilots/stop/laws.ts"
import * as twin from "../pilots/stop/stop.async.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "pilots/stop/stop.spec.ts")
const tsconfig = path.join(root, "tsconfig.json")
const filing = path.resolve(root, "../hkb-v2/packages/agent-runtime/src/core/engine/filing.ts")
const twinFile = path.join(root, "pilots/stop/stop.async.ts")
const project = loadProject([spec], tsconfig)

let api: Awaited<ReturnType<typeof init>>
let z3: Ctx
before(async () => {
  api = await init()
  z3 = api.Context("main")
})
after(() => killThreads(api.em))

const LAWS = ["readsFirst", "readFailurePassesThrough", "refusedWritesNothing", "acceptedWritesOneStop", "refusedExactlyWhenTheGuardSays"]
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

describe("requestStop and its async twin, under the same five laws", () => {
  it("the spec type-checks against both programs' real types", () => {
    assert.deepEqual(diagnostics(project, spec), [])
  })

  for (const [name, ends] of [
    ["effectStop", ["Success", "Failure JournalError", "Failure StopRefused"]],
    ["asyncStop", ["Success", "Failure"]],
  ] as const)
    it(`${name}: all five laws proved, every end it can come to reached`, async () => {
      const v = await verify(z3, project, spec, name)
      assert.equal(v.unsupported, undefined)
      assert.deepEqual(statuses(v), Object.fromEntries(LAWS.map((l) => [l, "proved"])))
      assert.deepEqual(
        v.cover.map((c) => [c.value, c.status]).sort(),
        ends.map((e) => [e, "reachable"]).sort(),
      )
      // What was not read is said, by name.
      assert.ok(v.notes.some((n) => n.startsWith("`fold` was not read")))
    })
})

// The runs: journals a stand-in serves, read and append each able to fail.
const at = "2026-10-28T00:00:00.000Z"
const filed: Event = { kind: "filed", at, brief: "b", cwd: "/r", queued: false }
const JOURNALS: ReadonlyArray<ReadonlyArray<Event>> = [
  [],
  [filed],
  [filed, { kind: "stop-requested", at }],
  [filed, { kind: "settled", at, outcome: "succeeded" }],
]
const RUNS = ["t-1", ""].flatMap((taskId) =>
  JOURNALS.flatMap((events) => [
    { taskId, events, failRead: false, failAppend: false },
    { taskId, events, failRead: true, failAppend: false },
    { taskId, events, failRead: false, failAppend: true },
  ]),
)
type Run = (typeof RUNS)[number]

const failureOf = (e: unknown): StopOutcome => ({ _tag: "Failure", error: e as { _tag: string } })

const runEffect = async (r: Run): Promise<{ out: StopOutcome; calls: Array<StopCall> }> => {
  const calls: Array<StopCall> = []
  const journal = Journal.of({
    read: (id: string) => {
      const error = new JournalError({ taskId: id, message: "unreadable" })
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.events } })
      return r.failRead ? Effect.fail(error) : Effect.succeed([...r.events])
    },
    append: (id: string, event: Event) => {
      const error = new JournalError({ taskId: id, message: "unwritable" })
      calls.push({ op: "append", args: [id, event], outcome: r.failAppend ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      return r.failAppend ? Effect.fail(error) : Effect.void
    },
  } as never)
  const result = await Effect.runPromise(Effect.result(requestStop(r.taskId)).pipe(Effect.provide(Layer.succeed(Journal)(journal))))
  return { out: result._tag === "Success" ? { _tag: "Success", value: undefined } : failureOf(result.failure), calls }
}

const runAsync = async (program: typeof twin.requestStop, r: Run): Promise<{ out: StopOutcome; calls: Array<StopCall> }> => {
  const calls: Array<StopCall> = []
  const journal: twin.JournalPort = {
    read: async (id) => {
      const error = new twin.JournalError("unreadable")
      calls.push({ op: "read", args: [id], outcome: r.failRead ? { _tag: "Failure", error } : { _tag: "Success", value: r.events } })
      if (r.failRead) throw error
      return r.events
    },
    append: async (id, event) => {
      const error = new twin.JournalError("unwritable")
      calls.push({ op: "append", args: [id, event], outcome: r.failAppend ? { _tag: "Failure", error } : { _tag: "Success", value: undefined } })
      if (r.failAppend) throw error
    },
  }
  try {
    await program(journal, r.taskId)
    return { out: { _tag: "Success", value: undefined }, calls }
  } catch (e) {
    return { out: failureOf(e), calls }
  }
}

/** The laws a run breaks. */
const broken = (r: Run, ran: { out: StopOutcome; calls: Array<StopCall> }): Array<string> =>
  LAWS.filter((l) => !(laws as unknown as Record<string, typeof laws.readsFirst>)[l]!(r.taskId, ran.out, ran.calls))

describe("the laws hold when the real programs run", () => {
  it(`requestStop, Nemia's verb, on ${RUNS.length} runs`, async () => {
    for (const r of RUNS) assert.deepEqual(broken(r, await runEffect(r)), [], JSON.stringify(r))
  })
  it(`its async twin, on the same runs`, async () => {
    for (const r of RUNS) assert.deepEqual(broken(r, await runAsync(twin.requestStop, r)), [], JSON.stringify(r))
  })
})

// Planted bugs: one text change inside the program, the same bug in both.
interface Plant {
  readonly id: string
  readonly what: string
  readonly effect: readonly [string, string]
  readonly twin: readonly [string, string]
}
const E_GUARD = "  if (refused) return yield* Effect.fail(new StopRefused({ message: refused }));\n"
const E_WRITE = "  yield* journal.append(taskId, { kind: 'stop-requested', at: new Date().toISOString() });\n"
const T_GUARD = "  if (refused) throw new StopRefused(refused)\n"
const T_WRITE = '  await journal.append(taskId, { kind: "stop-requested", at: new Date().toISOString() })\n'
const PLANTS: ReadonlyArray<Plant> = [
  { id: "B1", what: "writes before the guard", effect: [E_GUARD + E_WRITE, E_WRITE + E_GUARD], twin: [T_GUARD + T_WRITE, T_WRITE + T_GUARD] },
  {
    id: "B2",
    what: "the guard inverted",
    effect: ["if (refused) return yield* Effect.fail(new StopRefused({ message: refused }))", "if (!refused) return yield* Effect.fail(new StopRefused({ message: 'no' }))"],
    twin: ["if (refused) throw new StopRefused(refused)", 'if (!refused) throw new StopRefused("no")'],
  },
  { id: "B3", what: "writes the wrong kind", effect: ["kind: 'stop-requested'", "kind: 'closed'"], twin: ['kind: "stop-requested"', 'kind: "closed"'] },
  { id: "B4", what: "writes to another task", effect: ["journal.append(taskId,", "journal.append('*',"], twin: ["journal.append(taskId,", 'journal.append("*",'] },
  { id: "B5", what: "writes twice", effect: [E_WRITE, E_WRITE + E_WRITE], twin: [T_WRITE, T_WRITE + T_WRITE] },
  { id: "B6", what: "refuses only an empty task id", effect: ["if (refused) return", "if (refused && taskId === '') return"], twin: ["if (refused) throw", 'if (refused && taskId === "") throw'] },
  { id: "B7", what: "reads another task", effect: ["journal.read(taskId)", "journal.read('*')"], twin: ["journal.read(taskId)", 'journal.read("*")'] },
]

/** `text` with `[find, replace]` applied inside the function `requestStop`, where `find` must occur exactly once. */
const plant = (text: string, [find, replace]: readonly [string, string], id: string): string => {
  const start = text.search(/export const requestStop = /)
  const end = text.indexOf("\n});", start) >= 0 && text.slice(start).startsWith("export const requestStop = Effect") ? text.indexOf("\n});", start) + 4 : text.indexOf("\n}\n", start) + 3
  const body = text.slice(start, end)
  assert.equal(body.split(find).length - 1, 1, `${id}: \`${find}\` must occur once in requestStop`)
  return text.slice(0, start) + body.replace(find, replace) + text.slice(end)
}

describe("planted bugs", () => {
  for (const p of PLANTS) {
    it(`${p.id}, ${p.what}: caught in Nemia's verb`, async () => {
      const planted = loadProject([spec], tsconfig, new Map([[filing, plant(readFileSync(filing, "utf8"), p.effect, p.id)]]))
      const v = await verify(z3, planted, spec, "effectStop")
      assert.equal(v.unsupported, undefined)
      assert.ok(v.laws.some((l) => l.status === "counterexample"), JSON.stringify(statuses(v)))
    })

    it(`${p.id}, ${p.what}: caught in the twin, and the planted twin breaks a law when run`, async () => {
      const text = plant(readFileSync(twinFile, "utf8"), p.twin, p.id)
      const planted = loadProject([spec], tsconfig, new Map([[twinFile, text]]))
      const v = await verify(z3, planted, spec, "asyncStop")
      assert.equal(v.unsupported, undefined)
      const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
      assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
      // Run it: some run breaks one of the laws the solver refuted.
      const file = path.join(root, `pilots/stop/stop.planted-${p.id}.ts`)
      writeFileSync(file, text)
      try {
        const program = ((await import(pathToFileURL(file).href)) as typeof twin).requestStop
        const seen = new Set<string>()
        for (const r of RUNS) for (const l of broken(r, await runAsync(program, r))) seen.add(l)
        assert.ok(refuted.some((l) => seen.has(l)), `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`)
      } finally {
        rmSync(file)
      }
    })
  }
})
