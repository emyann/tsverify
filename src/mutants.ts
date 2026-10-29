// Laws against planted bugs: one-line changes to the code under a contract,
// each hunted by the solver and by property testing over the same laws.
//
// A bug is caught when a law that holds on the original fails on the planted
// copy. The solver reads the planted copy from source, in memory, and every
// counterexample it gives is run on the planted code: one the code does not
// confirm is the verifier's bug, and stops the run. Property testing runs the
// planted code on the suite's seeded random inputs. A bug neither catches is
// either equivalent to the original (proved) or changes a result no law
// forbids, shown on an input.
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import path from "node:path"
import { pathToFileURL } from "node:url"
import ts from "typescript"
import { loadProject } from "./project.ts"
import type { Ctx } from "./value.ts"
import { verify } from "./verify.ts"

export interface Mutant {
  readonly id: string
  /** The function the change is made in; `find` occurs in it exactly once. */
  readonly fn: string
  readonly find: string
  readonly replace: string
  /** What the bug does, in a few words. */
  readonly note: string
}

/** A law of the contract, called with an input and the result: its parameters are the contract's, which differ per suite. */
type Law = (...args: any) => boolean

export interface MutantSuite {
  readonly tsconfig: string
  /** The spec, and the name of the contract it exports. */
  readonly spec: string
  readonly contract: string
  /** The contract's laws, imported: property testing runs them on the planted code. */
  readonly laws: Readonly<Record<string, Law>>
  /** The file of the code under the contract. */
  readonly source: string
  /**
   * The contract's function, then those it calls: cut from `source` and run as a module of their own, so they may import
   * nothing but each other. Whether a bug is equivalent is asked of the first, whose results are compared with `===`.
   */
  readonly functions: readonly [string, ...Array<string>]
  readonly mutants: ReadonlyArray<Mutant>
  /** Seeded random argument lists: property testing's inputs. */
  readonly inputs: (n: number) => ReadonlyArray<ReadonlyArray<unknown>>
  /** How many inputs property testing gets, one column each. */
  readonly budgets: ReadonlyArray<number>
  /** A folder the planted copies are written to, to run them. */
  readonly tmp: string
}

export interface Sampled {
  readonly budget: number
  readonly caught: boolean
  /** The first run that broke a law, counting from 1, and the law. */
  readonly run?: number
  readonly law?: string
  readonly ms: number
}

export interface MutantRow {
  readonly mutant: Mutant
  readonly solver: {
    /** The laws refuted, each counterexample confirmed by running the planted code. */
    readonly caught: ReadonlyArray<string>
    /** Laws neither proved nor refuted, with their status. */
    readonly open: ReadonlyArray<string>
    /** When nothing is refuted: equivalent, or the result that changed and where. */
    readonly gap: string
    readonly ms: number
  }
  readonly sampled: ReadonlyArray<Sampled>
}

export interface MutantReport {
  /** The laws the original already fails, which count for nothing. */
  readonly failing: ReadonlyArray<string>
  /** What property testing finds on the original, at the largest budget. */
  readonly sampledOriginal: Omit<Sampled, "budget" | "ms">
  readonly rows: ReadonlyArray<MutantRow>
}

type Fn = (...args: ReadonlyArray<unknown>) => unknown

const declarationOf = (sf: ts.SourceFile, name: string): ts.Statement | undefined =>
  sf.statements.find(
    (s) =>
      (ts.isFunctionDeclaration(s) && s.name?.text === name) ||
      (ts.isVariableStatement(s) && s.declarationList.declarations.some((d) => ts.isIdentifier(d.name) && d.name.text === name)),
  )

const arityOf = (sf: ts.SourceFile, name: string): number => {
  const s = declarationOf(sf, name)
  if (s !== undefined && ts.isFunctionDeclaration(s)) return s.parameters.length
  const init = s !== undefined && ts.isVariableStatement(s) ? s.declarationList.declarations[0]!.initializer : undefined
  if (init !== undefined && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) return init.parameters.length
  throw new Error(`no function \`${name}\` to compare with its planted copy`)
}

/** `text` with the change of `m` made inside its function, where its `find` must occur exactly once. */
export const plantIn = (text: string, m: Mutant): string => {
  const sf = ts.createSourceFile("source.ts", text, ts.ScriptTarget.Latest, true)
  const decl = declarationOf(sf, m.fn)
  if (decl === undefined) throw new Error(`${m.id}: no function \`${m.fn}\``)
  const [start, end] = [decl.getStart(sf), decl.getEnd()]
  const body = text.slice(start, end)
  const count = body.split(m.find).length - 1
  if (count !== 1) throw new Error(`${m.id}: \`${m.find}\` occurs ${count} times in \`${m.fn}\`; it must occur once`)
  return text.slice(0, start) + body.replace(m.find, m.replace) + text.slice(end)
}

const relative = (from: string, to: string): string => {
  const r = path.relative(path.dirname(from), to).replaceAll(path.sep, "/")
  return r.startsWith(".") ? r : `./${r}`
}

/** What to do as the run goes: once the original is judged, and after each bug. */
export interface MutantProgress {
  readonly onOriginal?: (original: Pick<MutantReport, "failing" | "sampledOriginal">) => void
  readonly onRow?: (row: MutantRow) => void
}

export const runMutants = async (z3: Ctx, suite: MutantSuite, progress: MutantProgress = {}): Promise<MutantReport> => {
  const original = readFileSync(suite.source, "utf8")
  const [main] = suite.functions
  mkdirSync(suite.tmp, { recursive: true })

  /** The suite's functions, cut from a text of the source and transpiled to a module of their own. */
  const load = async (id: string, text: string): Promise<Fn> => {
    const sf = ts.createSourceFile("source.ts", text, ts.ScriptTarget.Latest, true)
    const pieces = suite.functions.map((name) => {
      const s = declarationOf(sf, name)
      if (s === undefined) throw new Error(`${id}: no function \`${name}\` in ${suite.source}`)
      return s.getText(sf)
    })
    const js = ts.transpileModule(pieces.join("\n\n"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext },
    }).outputText
    const file = path.join(suite.tmp, `${id}.mjs`)
    writeFileSync(file, js)
    return (await import(pathToFileURL(file).href))[main] as Fn
  }

  const laws = Object.entries(suite.laws)
  const pool = suite.inputs(Math.max(...suite.budgets))
  const sample = (fn: Fn, n: number, skip: ReadonlySet<string>): Omit<Sampled, "budget" | "ms"> => {
    for (let k = 0; k < Math.min(n, pool.length); k++) {
      const input = pool[k]!
      let r: unknown
      try {
        r = fn(...input)
      } catch {
        return { caught: true, run: k + 1, law: "(threw)" }
      }
      for (const [name, law] of laws) if (!skip.has(name) && !law(...input, r)) return { caught: true, run: k + 1, law: name }
    }
    return { caught: false }
  }

  const base = await verify(z3, loadProject([suite.spec], suite.tsconfig), suite.spec, suite.contract)
  if (base.unsupported !== undefined) throw new Error(`the original is not read: ${base.unsupported}`)
  const failing = new Set(base.laws.filter((l) => l.status !== "proved").map((l) => l.name))
  const originalFn = await load("original", original)
  const sampledOriginal = sample(originalFn, Math.max(...suite.budgets), new Set())
  progress.onOriginal?.({ failing: [...failing], sampledOriginal })

  const rows: Array<MutantRow> = []
  for (const m of suite.mutants) {
    const text = plantIn(original, m)
    const started = performance.now()
    const v = await verify(z3, loadProject([suite.spec], suite.tsconfig, new Map([[suite.source, text]])), suite.spec, suite.contract)
    if (v.unsupported !== undefined) throw new Error(`${m.id}: the planted copy is not read: ${v.unsupported}`)
    const ms = performance.now() - started
    const fn = await load(m.id, text)
    const refuted = v.laws.filter((l) => l.status === "counterexample" && !failing.has(l.name))
    for (const l of refuted) {
      const input = l.args!
      if (suite.laws[l.name]!(...input, fn(...input)))
        throw new Error(`${m.id}: the counterexample to \`${l.name}\` holds when the planted code runs: the verifier is wrong`)
    }
    const open = v.laws.filter((l) => l.status !== "proved" && l.status !== "counterexample").map((l) => `${l.name}: ${l.status}`)
    const sampled = suite.budgets.map((budget) => {
      const t = performance.now()
      return { budget, ...sample(fn, budget, failing), ms: performance.now() - t }
    })

    // Missed: is the planted function the original's equal on every input, or does it change a result no law forbids?
    let gap = ""
    if (refuted.length === 0) {
      const planted = path.join(path.dirname(suite.source), `${path.basename(suite.source, ".ts")}.planted.ts`)
      const sameSpec = path.join(path.dirname(suite.spec), "same.contract.ts")
      const params = Array.from(
        { length: arityOf(ts.createSourceFile("source.ts", original, ts.ScriptTarget.Latest, true), main) },
        (_, i) => `a${i}`,
      )
      const sameText = [
        `import { contract } from "tsverify"`,
        `import { ${main} } from ${JSON.stringify(relative(sameSpec, suite.source))}`,
        `import { ${main} as planted } from ${JSON.stringify(relative(sameSpec, planted))}`,
        `export const same = contract(${main}, { ensures: { same: (${[...params, "r"].join(", ")}) => r === planted(${params.join(", ")}) } })`,
      ].join("\n")
      const p = loadProject(
        [sameSpec],
        suite.tsconfig,
        new Map([
          [planted, text],
          [sameSpec, sameText],
        ]),
      )
      const eq = (await verify(z3, p, sameSpec, "same")).laws[0]
      if (eq?.status === "proved") gap = `equivalent in ${main} (proved)`
      else if (eq?.status === "counterexample") {
        const input = eq.args!.slice(0, params.length)
        gap = `changes a result no law forbids: ${JSON.stringify(originalFn(...input))} becomes ${JSON.stringify(fn(...input))} on ${JSON.stringify(input.length === 1 ? input[0] : input)}`
      } else gap = `equivalence ${eq?.status ?? "not asked"}`
    }
    const row: MutantRow = { mutant: m, solver: { caught: refuted.map((l) => l.name), open, gap, ms }, sampled }
    rows.push(row)
    progress.onRow?.(row)
  }
  return { failing: [...failing], sampledOriginal, rows }
}

const fmt = (ms: number) => (ms < 1000 ? `${Math.round(ms)} ms` : `${(ms / 1000).toFixed(1)} s`)

/** The report's header lines and one Markdown table row per bug. */
export const header = (suite: MutantSuite, report: Pick<MutantReport, "failing" | "sampledOriginal">): Array<string> => [
  `original: the solver refutes ${report.failing.join(", ") || "nothing"}; property testing ${report.sampledOriginal.caught ? `refutes ${report.sampledOriginal.law} at run ${report.sampledOriginal.run}` : "refutes nothing"}`,
  `laws counted: ${Object.keys(suite.laws).length - report.failing.length} of ${Object.keys(suite.laws).length}`,
  "",
  `| bug | what it does | solver | ${suite.budgets.map((b) => `PBT ${b}`).join(" | ")} |`,
  `|---|---|---|${suite.budgets.map(() => "---").join("|")}|`,
]

export const tableRow = (row: MutantRow): string => {
  const s = row.solver
  const solver =
    s.caught.length > 0
      ? `caught (${s.caught.join(", ")}), ${fmt(s.ms)}`
      : s.open.length > 0
        ? `open: ${s.open.join("; ")}`
        : `missed: ${s.gap}`
  return `| ${row.mutant.id} | ${row.mutant.note} | ${solver} | ${row.sampled.map((x) => (x.caught ? `caught at run ${x.run}` : "missed")).join(" | ")} |`
}
