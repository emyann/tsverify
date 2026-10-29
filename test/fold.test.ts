// Nemia's `fold` (hkb-v2, agent-runtime/src/core/domain.ts), read through its
// loop's invariants: the copy in pilots/fold is hkb-v2's code word for word but
// for the `invariant(...)` lines, the two folds agree on random journals, the
// verifier proves the five laws of `fold.spec.ts` for every journal, five bugs
// planted in the copy are each caught with an input that breaks the planted
// code when it runs, and without its invariants nothing is proved.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import ts from "typescript"
import { init, killThreads } from "z3-solver"
import { type Event, fold as theirs } from "../../hkb-v2/packages/agent-runtime/src/core/domain.ts"
import { fold as ours } from "../pilots/fold/fold.ts"
import { folded } from "../pilots/fold/fold.spec.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "pilots/fold/fold.spec.ts")
const copy = path.join(root, "pilots/fold/fold.ts")
const domain = path.resolve(root, "../hkb-v2/packages/agent-runtime/src/core/domain.ts")
const FUNCTIONS = ["endAttempt", "foldInto", "fileInto", "fold"]

/** Each named function of `file`, printed after `drop` removed what it matches: the same printer for both sides. */
const printed = (file: string, drop: (n: ts.Node) => boolean): Map<string, string> => {
  const sf = ts.createSourceFile(file, ts.sys.readFile(file)!, ts.ScriptTarget.Latest, true)
  const strip = (ctx: ts.TransformationContext) => (node: ts.Node): ts.Node => {
    const visit = (n: ts.Node): ts.Node | undefined => (drop(n) ? undefined : ts.visitEachChild(n, visit, ctx))
    return ts.visitNode(node, visit) as ts.Node
  }
  const printer = ts.createPrinter({ removeComments: true })
  const out = new Map<string, string>()
  for (const st of sf.statements) {
    if (!ts.isFunctionDeclaration(st) || st.name === undefined || !FUNCTIONS.includes(st.name.text)) continue
    const [fn] = ts.transform(st, [strip]).transformed
    out.set(st.name.text, printer.printNode(ts.EmitHint.Unspecified, fn!, sf))
  }
  return out
}

const isInvariant = (n: ts.Node): boolean =>
  ts.isExpressionStatement(n) &&
  ts.isCallExpression(n.expression) &&
  ts.isIdentifier(n.expression.expression) &&
  n.expression.expression.text === "invariant"

/** A small, seeded generator of journals: every kind, attempts 1 to 3, so `find` both hits and misses. */
const journal = (seed: number): Event[] => {
  let x = seed
  const next = (k: number) => {
    x = (x * 1103515245 + 12345) % 2 ** 31
    return x % k
  }
  const at = "2026-10-29T12:00:00Z"
  const attempt = () => 1 + next(3)
  const outcome = () => (["succeeded", "failed", "stopped"] as const)[next(3)]!
  const make = (): Event => {
    switch (next(15)) {
      case 0:
        return { kind: "filed", at, brief: `b${next(9)}`, cwd: "/w", ...(next(2) ? { holdOpen: true } : {}), ...(next(2) ? { queued: false } : {}) }
      case 1:
        return { kind: "admitted", at }
      case 2:
        return { kind: "starting", at, attempt: attempt(), ...(next(2) ? { nudge: "n" } : {}) }
      case 3:
        return { kind: "spawned", at, attempt: attempt(), ...(next(2) ? { error: "e" } : {}) }
      case 4:
        return {
          kind: "ended",
          at,
          attempt: attempt(),
          sessionId: "s",
          observed: outcome(),
          reason: "harness",
          ...(next(2) ? { nativeId: `n${next(9)}` } : {}),
          ...(next(2) ? { denials: [] } : {}),
          ...(next(2) ? { skills: ["look"] } : {}),
          ...(next(2) ? { exitCode: next(3) } : {}),
        }
      case 5:
        return { kind: "measured", at, attempt: attempt(), usage: { responses: next(5) } }
      case 6:
        return { kind: "counted", at, attempt: attempt(), usage: { responses: next(5) } }
      case 7:
        return { kind: "denied", at, attempt: attempt(), tool: "Bash", ...(next(2) ? { what: "rm" } : {}) }
      case 8:
        return { kind: "gap", at, attempt: attempt() }
      case 9:
        return { kind: "process", at, attempt: attempt(), ...(next(2) ? { pid: next(99) } : {}) }
      case 10:
        return { kind: "stop-requested", at }
      case 11:
        return { kind: "said", at, attempt: attempt(), text: "t" }
      case 12:
        return { kind: "input", at, text: "i" }
      case 13:
        return { kind: "closed", at }
      default:
        return { kind: "settled", at, outcome: outcome(), ...(next(2) ? { nativeId: "z" } : {}) }
    }
  }
  return Array.from({ length: next(12) }, make)
}

describe("fold, read through its invariants", () => {
  it("the copy is hkb-v2's code but for the invariant lines", () => {
    const mine = printed(copy, isInvariant)
    const original = printed(domain, () => false)
    assert.deepEqual([...mine.keys()].sort(), [...FUNCTIONS].sort())
    for (const name of FUNCTIONS) assert.equal(mine.get(name), original.get(name), `${name} differs from hkb-v2's`)
    // And it carries invariants at all: the proof reads them.
    assert.equal(printed(copy, () => false).get("fold") === mine.get("fold"), false)
  })

  it("both folds agree on 2,000 random journals, and the five laws hold on each", () => {
    for (let seed = 1; seed <= 2000; seed++) {
      const events = journal(seed)
      const s = ours("t", events)
      assert.deepEqual(s, theirs("t", events), `seed ${seed}`)
      for (const [name, law] of Object.entries(folded.ensures)) assert.ok(law("t", events, s), `${name} broken on seed ${seed}`)
    }
  })
})

describe("fold, verified", () => {
  let api: Awaited<ReturnType<typeof init>>
  let z3: Ctx
  before(async () => {
    api = await init()
    z3 = api.Context("main")
  })
  after(() => killThreads(api.em))

  it("the spec type-checks against hkb-v2's types", () => {
    assert.deepEqual(diagnostics(loadProject([spec], path.join(root, "tsconfig.json")), spec), [])
  })

  it("proves the five laws and every invariant, for journals of every length", { timeout: 600_000 }, async () => {
    const v: Verification = await verify(z3, loadProject([spec], path.join(root, "tsconfig.json")), spec, "folded")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(
      Object.fromEntries(v.laws.map((l) => [l.name, l.status])),
      Object.fromEntries(Object.keys(folded.ensures).map((n) => [n, "proved"])),
    )
    assert.deepEqual(
      v.obligations.map((o) => `${o.kind} ${o.phase}: ${o.status}`),
      ["entry", "kept"].flatMap((phase) => Array.from({ length: 5 }, () => `invariant ${phase}: proved`)),
    )
  })
})

const tsconfig = path.join(root, "tsconfig.json")
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  /** The law the bug breaks. */
  readonly breaks: keyof typeof folded.ensures
}
const TWO_ATTEMPTS =
  "s.admitted = s.inputs.length;\n" +
  "        s.attempts.push({ n: 0, startedAt: e.at, spawnedAt: null, ended: null, endedAt: null, reason: null, nativeId: null, usage: null, exitCode: null });\n" +
  "        s.attempts.push({ n: 0, startedAt: e.at, spawnedAt: null, ended: null, endedAt: null, reason: null, nativeId: null, usage: null, exitCode: null });"
const PLANTS: ReadonlyArray<Plant> = [
  { id: "F1", what: "a second stop request takes the first back", change: ["s.stopRequested = true;", "s.stopRequested = !s.stopRequested;"], breaks: "stopRequestedExactlyWhenJournalled" },
  { id: "F2", what: "a close after an answer is lost", change: ["s.closed = true;", "s.closed = s.inputs.length === 0;"], breaks: "closedExactlyWhenJournalled" },
  { id: "F3", what: "an admission settles the task", change: ["s.admitted = s.inputs.length;", "s.admitted = s.inputs.length;\n        s.settled ??= 'stopped';"], breaks: "settledOnlyWhenJournalled" },
  { id: "F4", what: "an admission starts two attempts", change: ["s.admitted = s.inputs.length;", TWO_ATTEMPTS], breaks: "noMoreAttemptsThanEvents" },
  { id: "F5", what: "a filing renames the task", change: ["s.cwd = e.cwd;", "s.cwd = e.cwd;\n  s.taskId = e.cwd;"], breaks: "keepsItsTask" },
]

/** The copy with `find` (which must occur once) replaced. */
const plant = (text: string, [find, replace]: readonly [string, string], id: string): string => {
  assert.equal(text.split(find).length - 1, 1, `${id}: \`${find}\` must occur once in the copy`)
  return text.replace(find, replace)
}

describe("fold, with a bug planted", () => {
  let api: Awaited<ReturnType<typeof init>>
  let z3: Ctx
  before(async () => {
    api = await init()
    z3 = api.Context("main")
  })
  after(() => killThreads(api.em))

  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: ${p.breaks} refuted, and the planted fold breaks it when run`, async () => {
      const text = plant(readFileSync(copy, "utf8"), p.change, p.id)
      const v = await verify(z3, loadProject([spec], tsconfig, new Map([[copy, text]])), spec, "folded")
      assert.equal(v.unsupported, undefined)
      const law = v.laws.find((l) => l.name === p.breaks)!
      assert.equal(law.status, "counterexample", JSON.stringify(statuses(v)))
      // Run it on the counterexample: the planted fold breaks the law there.
      const file = path.join(root, `pilots/fold/fold.planted-${p.id}.ts`)
      writeFileSync(file, text)
      try {
        const planted = ((await import(pathToFileURL(file).href)) as { fold: typeof ours }).fold
        const [taskId, events] = law.args as [string, Event[]]
        assert.equal(folded.ensures[p.breaks]!(taskId, events, planted(taskId, events)), false, JSON.stringify(law.args))
      } finally {
        rmSync(file)
      }
    })

  it("a harmless change (`s.closed = s.closed || true`) is still proved", async () => {
    const text = plant(readFileSync(copy, "utf8"), ["s.closed = true;", "s.closed = s.closed || true;"], "C1")
    const v = await verify(z3, loadProject([spec], tsconfig, new Map([[copy, text]])), spec, "folded")
    assert.deepEqual(Object.values(statuses(v)), Object.keys(folded.ensures).map(() => "proved"))
  })

  it("without its invariants, no law is proved: each is bounded, unbroken on journals of up to four events", async () => {
    const text = readFileSync(copy, "utf8")
      .split("\n")
      .filter((l) => !/^\s*invariant\(/.test(l))
      .join("\n")
    const v = await verify(z3, loadProject([spec], tsconfig, new Map([[copy, text]])), spec, "folded")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(v.obligations, [])
    assert.deepEqual(Object.values(statuses(v)), Object.keys(folded.ensures).map(() => "bounded"))
  })
})
