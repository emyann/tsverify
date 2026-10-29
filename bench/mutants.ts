// The benchmark: one-line bugs planted in lifecycleOf and the two functions it
// calls, each hunted by the solver and by property testing over the same laws.
//
// A bug is caught when a law that holds on the original code fails on the
// planted copy (the original already fails `inFlight`, so it counts for
// neither). The solver reads the planted copy from source in memory and its
// counterexample is replayed on the planted code; property testing runs the
// planted code, extracted and transpiled, on seeded random states.
//
//   node bench/mutants.ts [--runs 100,1000,10000] [--json bench/results.json]
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import path from "node:path"
import { pathToFileURL } from "node:url"
import ts from "typescript"
import type { State } from "../../hkb-v2/packages/agent-runtime/src/core/domain.ts"
import { states } from "../pilots/lifecycle/generate.ts"
import { lifecycle } from "../pilots/lifecycle/lifecycle.spec.ts"
import { loadProject } from "../src/project.ts"
import { verify, withZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "pilots/lifecycle/lifecycle.spec.ts")
const domain = path.resolve(root, "../hkb-v2/packages/agent-runtime/src/core/domain.ts")
const original = readFileSync(domain, "utf8")

interface Mutant {
  readonly id: string
  readonly fn: "lifecycleOf" | "waitsForInput" | "turnOf"
  readonly find: string
  readonly replace: string
  readonly note: string
}

const MUTANTS: ReadonlyArray<Mutant> = [
  { id: "L1", fn: "lifecycleOf", find: "state.settled === 'succeeded' ? 'completed'", replace: "state.settled === 'failed' ? 'completed'", note: "the wrong outcome completes" },
  { id: "L2", fn: "lifecycleOf", find: "state.settled === 'stopped' ? 'canceled' : 'failed'", replace: "state.settled === 'stopped' ? 'failed' : 'canceled'", note: "stopped and failed swapped" },
  { id: "L3", fn: "lifecycleOf", find: "if (state.stopRequested) return 'stopping';", replace: "if (state.stopRequested && !state.closed) return 'stopping';", note: "a closed task ignores a stop" },
  { id: "L4", fn: "lifecycleOf", find: "if (state.stopRequested) return 'stopping';", replace: "if (state.stopRequested || state.closed) return 'stopping';", note: "a close reads as a stop" },
  { id: "L5", fn: "lifecycleOf", find: "if (last && last.ended === null)", replace: "if (last && last.ended !== 'succeeded')", note: "a failed attempt reads as in flight" },
  { id: "L6", fn: "lifecycleOf", find: "if (state.holdOpen && state.closed) return 'ending';", replace: "if (state.holdOpen || state.closed) return 'ending';", note: "closed without hold-open ends" },
  { id: "L7", fn: "lifecycleOf", find: "return turnOf(state).attempts.length > 0 ? 'ending' : 'submitted';", replace: "return turnOf(state).attempts.length > 1 ? 'ending' : 'submitted';", note: "one attempt reads as none" },
  { id: "L8", fn: "lifecycleOf", find: "return turnOf(state).attempts.length > 0 ? 'ending' : 'submitted';", replace: "return turnOf(state, 0).attempts.length > 0 ? 'ending' : 'submitted';", note: "always the first turn" },
  { id: "L9", fn: "lifecycleOf", find: "if (waitsForInput(state)) return 'input-required';", replace: "if (waitsForInput(state) || state.closed) return 'input-required';", note: "closed reads as waiting" },
  { id: "W1", fn: "waitsForInput", find: "!state.closed && last?.ended", replace: "last?.ended", note: "a closed task still waits" },
  { id: "W2", fn: "waitsForInput", find: "last?.ended === 'succeeded'", replace: "last?.ended === 'failed'", note: "waits after a failure, not a success" },
  { id: "W3", fn: "waitsForInput", find: "(last.turn ?? 0) === state.inputs.length", replace: "(last.turn ?? 1) === state.inputs.length", note: "an unnumbered turn is turn 1" },
  { id: "W4", fn: "waitsForInput", find: "(last.turn ?? 0) === state.inputs.length", replace: "(last.turn ?? 0) <= state.inputs.length", note: "an earlier turn's end waits" },
  { id: "W5", fn: "waitsForInput", find: "state.holdOpen === true && !state.settled && ", replace: "state.holdOpen === true && ", note: "a settled task waits" },
  { id: "T1", fn: "turnOf", find: "const attempts = state.attempts.filter((a) => (a.turn ?? 0) === n);", replace: "const attempts = state.attempts.filter((a) => (a.turn ?? 0) >= n);", note: "later turns count as this one" },
  { id: "T2", fn: "turnOf", find: "const attempts = state.attempts.filter((a) => (a.turn ?? 0) === n);", replace: "const attempts = state.attempts.filter((a) => a.turn === n);", note: "an unnumbered attempt is in no turn" },
  { id: "T3", fn: "turnOf", find: "export function turnOf(state: State, n = state.inputs.length)", replace: "export function turnOf(state: State, n = state.attempts.length)", note: "the turn counted by attempts" },
  { id: "E1", fn: "lifecycleOf", find: "if (last && last.ended === null)", replace: "if (last && !last.ended)", note: "equivalent: `ended` is an outcome or null (a control; nothing should catch it)" },
]

const arg = (flag: string): string | undefined => {
  const i = process.argv.indexOf(flag)
  return i < 0 ? undefined : process.argv[i + 1]
}
const budgets = (arg("--runs") ?? "100,1000,10000").split(",").map(Number)
const jsonOut = arg("--json")

/** The three functions, cut from a domain.ts text and transpiled to a module of their own. */
const tmp = path.join(root, "bench/.tmp")
mkdirSync(tmp, { recursive: true })
const load = async (id: string, text: string): Promise<(s: State) => string> => {
  const sf = ts.createSourceFile("domain.ts", text, ts.ScriptTarget.Latest, true)
  const pieces = sf.statements
    .filter((s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && ["lifecycleOf", "waitsForInput", "turnOf"].includes(s.name?.text ?? ""))
    .map((s) => s.getText(sf))
  if (pieces.length !== 3) throw new Error(`${id}: found ${pieces.length} of the 3 functions`)
  const js = ts.transpileModule(pieces.join("\n\n"), { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText
  const file = path.join(tmp, `${id}.mjs`)
  writeFileSync(file, js)
  return (await import(pathToFileURL(file).href)).lifecycleOf
}

/** domain.ts with `m` planted inside its function, where its text must occur exactly once. */
const plant = (m: Mutant): string => {
  const sf = ts.createSourceFile("domain.ts", original, ts.ScriptTarget.Latest, true)
  const decl = sf.statements.find((s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && s.name?.text === m.fn)
  if (decl === undefined) throw new Error(`${m.id}: no function ${m.fn}`)
  const [start, end] = [decl.getStart(sf), decl.getEnd()]
  const body = original.slice(start, end)
  const count = body.split(m.find).length - 1
  if (count !== 1) throw new Error(`${m.id}: \`${m.find}\` occurs ${count} times in ${m.fn}`)
  return original.slice(0, start) + body.replace(m.find, m.replace) + original.slice(end)
}

const LAWS = Object.entries(lifecycle.ensures)
const pool = states(20261028, Math.max(...budgets))

/** The laws a function breaks, by property testing on the first `n` states; and the run that first broke one. */
const sample = (fn: (s: State) => string, n: number, skip: ReadonlySet<string>) => {
  for (let k = 0; k < n; k++) {
    const s = pool[k]!
    let r: string
    try {
      r = fn(s)
    } catch {
      return { caught: true, run: k + 1, law: "(threw)" }
    }
    for (const [name, law] of LAWS) if (!skip.has(name) && !law(s, r as never)) return { caught: true, run: k + 1, law: name }
  }
  return { caught: false as const }
}

const fmt = (ms: number) => (ms < 1000 ? `${Math.round(ms)} ms` : `${(ms / 1000).toFixed(1)} s`)

await withZ3(async (z3) => {
  // The laws the original already fails count for nothing.
  const base = await verify(z3, loadProject([spec], path.join(root, "tsconfig.json")), spec, "lifecycle")
  const failing = new Set(base.laws.filter((l) => l.status !== "proved").map((l) => l.name))
  const originalFn = await load("original", original)
  const sampledOriginal = sample(originalFn, Math.max(...budgets), new Set())
  console.log(`original: the solver refutes ${[...failing].join(", ") || "nothing"}; property testing ${sampledOriginal.caught ? `refutes ${sampledOriginal.law} at run ${sampledOriginal.run}` : "refutes nothing"}`)
  console.log(`laws counted: ${LAWS.length - failing.size} of ${LAWS.length}\n`)

  const rows: Array<Record<string, unknown>> = []
  console.log(`| bug | what it does | solver | ${budgets.map((b) => `PBT ${b}`).join(" | ")} |`)
  console.log(`|---|---|---|${budgets.map(() => "---").join("|")}|`)
  for (const m of MUTANTS) {
    const text = plant(m)

    const started = performance.now()
    const project = loadProject([spec], path.join(root, "tsconfig.json"), new Map([[domain, text]]))
    const v = await verify(z3, project, spec, "lifecycle")
    const solverMs = performance.now() - started
    const fn = await load(m.id, text)
    const refuted = v.laws.filter((l) => l.status === "counterexample" && !failing.has(l.name))
    // Every counterexample is run on the planted code: a refutation the code does not confirm would be the verifier's bug.
    const confirmed = refuted.filter((l) => {
      const s = l.args![0] as State
      return !lifecycle.ensures[l.name]!(s, fn(s) as never)
    })
    if (confirmed.length !== refuted.length) throw new Error(`${m.id}: a counterexample the planted code does not confirm`)
    const open = v.laws.filter((l) => l.status !== "proved" && l.status !== "counterexample").map((l) => `${l.name}: ${l.status}`)

    const sampled = budgets.map((b) => {
      const t = performance.now()
      const r = sample(fn, b, failing)
      return { budget: b, ...r, ms: performance.now() - t }
    })
    // Missed: is the planted lifecycleOf the original's equal on every state, or does it change a result no law forbids?
    let gap = ""
    if (refuted.length === 0) {
      const planted = path.join(path.dirname(domain), "domain.planted.ts")
      const sameSpec = path.join(root, "bench/same.spec.ts")
      const sameText = [
        `import { contract } from "../src/contract.ts"`,
        `import { lifecycleOf } from "../../hkb-v2/packages/agent-runtime/src/core/domain.ts"`,
        `import { lifecycleOf as planted } from "../../hkb-v2/packages/agent-runtime/src/core/domain.planted.ts"`,
        `export const same = contract(lifecycleOf, { ensures: { same: (s, r) => r === planted(s) } })`,
      ].join("\n")
      const p = loadProject([sameSpec], path.join(root, "tsconfig.json"), new Map([[planted, text], [sameSpec, sameText]]))
      const eq = (await verify(z3, p, sameSpec, "same")).laws[0]!
      if (eq.status === "proved") gap = "equivalent in lifecycleOf (proved)"
      else if (eq.status === "counterexample") {
        const s = eq.args![0] as State
        gap = `changes a result no law forbids: ${originalFn(s)} becomes ${fn(s)} on ${JSON.stringify(s)}`
      } else gap = `equivalence ${eq.status}`
    }
    const solverCell = refuted.length > 0 ? `caught (${refuted.map((l) => l.name).join(", ")}), ${fmt(solverMs)}` : open.length > 0 ? `open: ${open.join("; ")}` : `missed: ${gap}`
    console.log(`| ${m.id} | ${m.note} | ${solverCell} | ${sampled.map((s) => (s.caught ? `caught at run ${s.run}` : "missed")).join(" | ")} |`)
    rows.push({ ...m, solver: { caught: refuted.map((l) => l.name), open, gap, ms: solverMs }, sampled })
  }
  if (jsonOut !== undefined) writeFileSync(jsonOut, `${JSON.stringify(rows, null, 2)}\n`)
})
