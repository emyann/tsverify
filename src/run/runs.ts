// The parent's half of running a contract's laws on generated inputs: the plan of a run, read from the checker in the
// verifier's process, and the child process it is handed to (`./child.ts`), which loads the code and the spec, runs
// them, and answers which laws broke on which input. The verifier's process never imports the user's code nor
// fast-check: the child does, with a throwaway HOME and TMPDIR, and is killed if it runs past `RUN_STUCK_MS`.
import { fork } from "node:child_process"
import { mkdtempSync, rmSync } from "node:fs"
import os from "node:os"
import path from "node:path"
import { fileURLToPath } from "node:url"
import ts from "typescript"
import { type Project, type ContractSource, implementationType } from "../project.ts"
import type { Trust } from "../lower.ts"
import { purityOf } from "../purity.ts"
import { symbolOf } from "../resolve.ts"
import type { Options } from "../verify.ts"
import type { Answer } from "./child.ts"
import { NotRunnable, type Shape, poolOf, shapeOf } from "./shape.ts"

/** Inputs run for each contract that meet `requires`: a count, never a time, so a run is the same on every machine. */
export const RUNS = 1_000

/** The clock that stops a child whose "pure" function never ends: the one stop that may differ between machines. */
export const RUN_STUCK_MS = 60_000

/** What the child is handed: what to load, what to generate, and the seed. Plain data, sent over ipc. */
export interface RunPlan {
  /** The contract's own module, absolute, and its exported name: a `contract(...)` object, or a spec's implementation. */
  readonly module: string
  readonly name: string
  /** For an implementation (`const f: Implementation<S>`): where the spec is declared, absolute, and its variable's name. */
  readonly spec?: { readonly module: string; readonly name: string }
  /** The laws, by name, in order, and for each the shape of the result a law reads (`output`), where it reads one. */
  readonly laws: ReadonlyArray<{ readonly name: string; readonly output?: Shape }>
  /** The shape of each parameter, in order. */
  readonly params: ReadonlyArray<Shape>
  /** The string literals of the program's own files: what generated strings are drawn from. */
  readonly pool: ReadonlyArray<string>
  readonly seed: number
  readonly runs: number
  /** The longest array, dictionary, `Map` or `Set` generated: `--bound`. */
  readonly bound: number
}

/** What a run did, or why there was none. */
export type Ran =
  | {
      readonly ran: true
      /** Inputs run that met `requires`. */
      readonly inputs: number
      /** Inputs `requires` refused. */
      readonly discarded: number
      /** Inputs on which the function or a law threw: skipped, never a counterexample. */
      readonly threw: number
      /** Every module the child loaded: the program's own files relative to the current folder, packages by name. */
      readonly modules: ReadonlyArray<string>
      /** The environment variables the child was given, by name. */
      readonly env: ReadonlyArray<string>
      readonly ms: number
    }
  | { readonly ran: false; readonly why: string; readonly stuck?: true }

export interface RunResult {
  /** Each law a run broke, with the input that breaks it, shrunk; a generated function shown as `{ "~calls": [[args, result], …] }`. */
  readonly broken: Readonly<Record<string, { readonly args: ReadonlyArray<unknown> }>>
  /** The laws a generated input meeting `requires`, with a generated free result, breaks: each says something. */
  readonly saysSomething: ReadonlyArray<string>
  readonly ran: Ran
}

/** The longest collection a run generates where `--bound` is not given: the search side's own default. */
const DEFAULT_BOUND = 4

/** The `const` a node is the value of, through parentheses and `satisfies`. */
const declarationOf = (n: ts.Node): ts.VariableDeclaration | undefined => {
  let at: ts.Node = n
  while (ts.isParenthesizedExpression(at.parent) || ts.isSatisfiesExpression(at.parent)) at = at.parent
  return ts.isVariableDeclaration(at.parent) && at.parent.initializer === at ? at.parent : undefined
}

const isExported = (d: ts.VariableDeclaration): boolean =>
  ts.isVariableStatement(d.parent.parent) && (d.parent.parent.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) ?? false)

/** Whether `inner` is written inside `outer`. */
const within = (inner: ts.Node, outer: ts.Node): boolean =>
  inner.getSourceFile() === outer.getSourceFile() && inner.pos >= outer.pos && inner.end <= outer.end

/**
 * The file that exports the contract `source` reads: the `export const <name>` of the program's own files whose value
 * holds its laws or its function, the first such otherwise.
 */
const contractFile = (project: Project, source: ContractSource): string | undefined => {
  const found: Array<ts.VariableDeclaration> = []
  for (const sf of project.program.getSourceFiles()) {
    if (sf.isDeclarationFile || /[\\/]node_modules[\\/]/.test(sf.fileName)) continue
    for (const stmt of sf.statements)
      if (ts.isVariableStatement(stmt) && stmt.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword))
        for (const d of stmt.declarationList.declarations)
          if (ts.isIdentifier(d.name) && d.name.text === source.name && d.initializer !== undefined) found.push(d)
  }
  const parts = [source.target, ...source.ensures.map((l) => l.law), ...(source.requires === undefined ? [] : [source.requires])]
  const holding = found.find((d) => parts.some((p) => within(p, d)))
  return (holding ?? found[0])?.getSourceFile().fileName
}

/** The spec an implementation (`const f: Implementation<S> = ...`) is typed by: where it is declared, and its name. */
const specOf = (checker: ts.TypeChecker, d: ts.VariableDeclaration): RunPlan["spec"] => {
  const arg = implementationType(checker, d)?.typeArguments?.[0]
  let query: ts.TypeNode | undefined = arg
  if (query !== undefined && ts.isTypeReferenceNode(query) && query.typeArguments === undefined) {
    const alias = symbolOf(checker, query.typeName)?.declarations?.find(ts.isTypeAliasDeclaration)
    query = alias?.type
  }
  if (query === undefined || !ts.isTypeQueryNode(query) || !ts.isIdentifier(query.exprName)) return undefined
  const decl = symbolOf(checker, query.exprName)?.valueDeclaration
  if (decl === undefined || !ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name)) return undefined
  return { module: decl.getSourceFile().fileName, name: decl.name.text }
}

/** The plan of a run of `source`, or why it is not run. */
export const planOf = (
  project: Project,
  source: ContractSource,
  trust: Trust,
  opts: Options,
  seed: number,
): RunPlan | { readonly why: string } => {
  if (source.kind === "computation") return { why: "a computation is not run" }
  if (source.kind === "lemma") return { why: "a lemma is not run" }
  if (opts.only !== undefined) return { why: "a law asked alone is not run" }
  const { checker } = project
  const fn = source.target
  if (!(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn) || ts.isFunctionDeclaration(fn)))
    return { why: "its function is not one written in the program" }
  const purity = purityOf(checker, fn, trust.assumptions.of)
  if (!purity.pure) return { why: purity.why }
  if (fn.parameters.some((p) => p.dotDotDotToken !== undefined)) return { why: "a rest parameter is not run" }
  const file = contractFile(project, source)
  if (file === undefined) return { why: `no \`export const ${source.name}\` found` }
  const declared = declarationOf(fn)
  const implemented = declared !== undefined && isExported(declared) && implementationType(checker, declared) !== undefined
  const spec = implemented ? specOf(checker, declared) : undefined
  if (implemented && spec === undefined) return { why: "its spec is not a `const` the program declares" }
  try {
    const sig = checker.getSignatureFromDeclaration(fn)
    const params = fn.parameters.map((p, i) => {
      const t = sig?.getParameters()[i] === undefined ? checker.getTypeAtLocation(p) : checker.getTypeOfSymbol(sig.getParameters()[i]!)
      // A parameter with a default may be left out: given as `undefined` too.
      const s = shapeOf(checker, t)
      return p.initializer !== undefined && !(s.kind === "union" && s.of.some((m) => m.kind === "undefined"))
        ? ({ kind: "union", of: [s, { kind: "undefined" }] } satisfies Shape)
        : s
    })
    const laws = source.ensures.map((l) => {
      const run = l.law.parameters[0]
      const output = run === undefined ? undefined : checker.getPropertyOfType(checker.getTypeAtLocation(run), "output")
      return output === undefined ? { name: l.name } : { name: l.name, output: shapeOf(checker, checker.getTypeOfSymbol(output)) }
    })
    return {
      module: file,
      name: source.name,
      ...(spec === undefined ? {} : { spec }),
      laws,
      params,
      pool: poolOf(project, file),
      seed,
      runs: RUNS,
      bound: opts.bound ?? DEFAULT_BOUND,
    }
  } catch (e) {
    if (e instanceof NotRunnable) return { why: e.message }
    throw e
  }
}

/** The child's module beside this one: `.ts` in a checkout, `.js` in the package built. */
const CHILD = fileURLToPath(new URL(`./child${path.extname(fileURLToPath(import.meta.url))}`, import.meta.url))

/**
 * The child's flags: the parent's, and where the verifier runs from its own source (a checkout), the condition that
 * resolves `@emyann/tsverify` to that source too, so a spec imports the same tsverify the verifier is.
 */
const EXEC_ARGV =
  CHILD.endsWith(".ts") && !process.execArgv.some((a) => a.includes("tsverify-source"))
    ? [...process.execArgv, "--conditions=tsverify-source"]
    : process.execArgv

const notRun = (why: string, stuck?: true): RunResult => ({
  broken: {},
  saysSomething: [],
  ran: stuck === undefined ? { ran: false, why } : { ran: false, why, stuck },
})

/**
 * Runs `plan` in a child process of its own, with a HOME and a TMPDIR of its own, removed after, and stops it past
 * `stuckMs` (`RUN_STUCK_MS`; a test sets less). Never rejects: a child that cannot load or run answers `ran: false`.
 */
export const runContract = (plan: RunPlan, opts: { readonly stuckMs?: number } = {}): Promise<RunResult> =>
  new Promise((resolve) => {
    const stuckMs = opts.stuckMs ?? RUN_STUCK_MS
    const started = performance.now()
    let home: string
    try {
      home = mkdtempSync(path.join(os.tmpdir(), "tsverify-run-"))
    } catch (e) {
      resolve(notRun(`no folder of its own: ${e instanceof Error ? e.message : String(e)}`))
      return
    }
    const env: Record<string, string> = {}
    if (process.env.PATH !== undefined) env.PATH = process.env.PATH
    env.HOME = home
    env.TMPDIR = home
    env.USERPROFILE = home
    if (process.env.NODE_OPTIONS !== undefined) env.NODE_OPTIONS = process.env.NODE_OPTIONS
    let answer: Answer | undefined
    let stuck = false
    let stderr = ""
    let over = false
    let timer: NodeJS.Timeout | undefined
    const finish = (stopped: string) => {
      if (over) return
      over = true
      clearTimeout(timer)
      rmSync(home, { recursive: true, force: true })
      if (stuck) return resolve(notRun(`stopped after ${stuckMs / 1000} s: it did not end`, true))
      if (answer === undefined) {
        const last = stderr
          .split("\n")
          .map((l) => l.trim())
          .filter((l) => l !== "")
          .at(-1)
        return resolve(notRun(last ?? `the run stopped (${stopped})`))
      }
      if (!answer.ran) return resolve(notRun(answer.why))
      resolve({
        broken: answer.broken,
        saysSomething: answer.saysSomething,
        ran: { ...answer.ran, env: Object.keys(env), ms: performance.now() - started },
      })
    }
    try {
      const child = fork(CHILD, [], {
        execArgv: EXEC_ARGV,
        env,
        stdio: ["ignore", "ignore", "pipe", "ipc"],
        serialization: "advanced",
      })
      child.stderr?.on("data", (d: Buffer) => {
        stderr = (stderr + d.toString()).slice(-8192)
      })
      child.on("message", (m: Answer) => {
        answer = m
      })
      child.on("error", (e) => {
        stderr += `\n${e.message}`
        child.kill("SIGKILL")
        finish("error")
      })
      child.on("close", (code, signal) => finish(signal ?? `exit ${code}`))
      timer = setTimeout(() => {
        stuck = true
        child.kill("SIGKILL")
      }, stuckMs)
      child.send(plan)
    } catch (e) {
      stderr += `\n${e instanceof Error ? e.message : String(e)}`
      finish("not started")
    }
  })
