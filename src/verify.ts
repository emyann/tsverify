// A contract's verification: each law of `ensures` proved, refuted with a
// counterexample, searched without a counterexample up to a bound, left
// unknown, or refused; and, for a result that is a union of string literals,
// which of them some allowed input reaches.
//
// Each contract is lowered twice. The proof side keeps arrays of any length and
// quantifiers as quantifiers: `unsat` there is a proof. The search side holds
// arrays to `bound` elements and writes quantifiers out: Z3 finds models there
// quickly, and every model it finds is a model of the proof side's formula too.
import { init, killThreads } from "z3-solver"
import type { Arith, Bool, Model } from "z3-solver"
import ts from "typescript"
import type { Adapter } from "./adapter.ts"
import { asyncAdapter } from "./adapters/async.ts"
import { effectAdapter } from "./adapters/effect/index.ts"
import { tsAdapter } from "./adapters/ts.ts"
import { emptyTrace, runBody } from "./computation.ts"
import { TooLong, fromModel, literal, pin } from "./concrete.ts"
import { emptyEnv, type Lowering, lowerCall, lowering, num } from "./lower.ts"
import { strictEq, truthy } from "./ops.ts"
import { type ContractSource, type Project, readContract } from "./project.ts"
import { symbolicOf } from "./symbolic.ts"
import { Universe } from "./universe.ts"
import { type Ctx, type FunctionNode, Unsupported, type Val } from "./value.ts"

/** The adapters every verification reads with, in the order they are asked. */
export const ADAPTERS: ReadonlyArray<Adapter> = [effectAdapter, asyncAdapter, tsAdapter]

export type LawStatus =
  /** No allowed input breaks it: `unsat` on the proof side. */
  | "proved"
  /** An allowed input breaks it; `args` holds one. */
  | "counterexample"
  /** Not proved in time, and no counterexample with arrays of at most `bound` elements. */
  | "bounded"
  | "unknown"
  | "unsupported"

export interface LawResult {
  readonly name: string
  readonly status: LawStatus
  /** On a counterexample: the arguments, as JavaScript values. */
  readonly args?: ReadonlyArray<unknown>
  /** On a counterexample of a computation: how each operation call it made ended, by call. */
  readonly world?: Readonly<Record<string, unknown>>
  /**
   * Set when the counterexample leans on functions read as unknown (their bodies refused): it holds of the code with
   * them unknown, and may not of the real ones. It names them.
   */
  readonly abstract?: ReadonlyArray<string>
  readonly reason?: string
  readonly ms: number
}

export interface CoverResult {
  readonly value: string
  readonly status: "reachable" | "unreachable" | "bounded" | "unknown"
  readonly args?: ReadonlyArray<unknown>
}

export interface Verification {
  readonly contract: string
  readonly laws: ReadonlyArray<LawResult>
  readonly cover: ReadonlyArray<CoverResult>
  /** What the model of JavaScript assumed on the way, each kind once. */
  readonly notes: ReadonlyArray<string>
  /** Set when the function or `requires` could not be lowered: no law is checked then. */
  readonly unsupported?: string
}

export interface Options {
  /** Per query, on each side. */
  readonly timeoutMs?: number
  /** The search side's longest array. */
  readonly bound?: number
  /** Called as each law and each cover query is decided: progress for a long run. */
  readonly progress?: (line: string) => void
}

/** One side's lowering: the universe, the arguments and result, the precondition. */
export interface Lowered {
  readonly u: Universe
  readonly L: Lowering
  readonly source: ContractSource
  /** The function read: the contract's, or a computation's body. */
  readonly fn: FunctionNode
  readonly params: ReadonlyArray<string>
  readonly args: ReadonlyArray<Val>
  /** A function's result, or a computation's outcome. */
  readonly result: Val
  /** A computation's calls, in order; undefined for a function. */
  readonly trace: Val | undefined
  readonly pre: Bool<"main">
}

const ALWAYS = [
  "The code under verification throws nothing: a binding it never reads is not evaluated.",
  "Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.",
]

/** Lowers the contract's function and precondition on one side (`bound` set: the search side). */
export const lowerSide = (z3: Ctx, project: Project, source: ContractSource, bound?: number, adapters = ADAPTERS): Lowered => {
  const u = new Universe(z3, bound)
  const L = lowering({ u, checker: project.checker }, adapters)
  const symbolicArgs = (fn: FunctionNode) => {
    const params = fn.parameters.map((p, i) => (ts.isIdentifier(p.name) ? p.name.text : `arg${i}`))
    return { params, args: fn.parameters.map((p, i) => symbolicOf(L, project.checker.getTypeAtLocation(p), [params[i]!], [], p)) }
  }
  const preOf = (args: ReadonlyArray<Val>) =>
    source.requires === undefined ? z3.Bool.val(true) : truthy(u, lowerCall(L, source.requires, emptyEnv, args, source.requires))
  if (source.kind === "function") {
    const t = source.target
    if (!(ts.isArrowFunction(t) || ts.isFunctionExpression(t) || ts.isFunctionDeclaration(t)))
      throw new Unsupported("a `contract` is about a function; a computation takes `computation<...>()`", t)
    const { params, args } = symbolicArgs(t)
    return { u, L, source, fn: t, params, args, result: lowerCall(L, t, emptyEnv, args, t), trace: undefined, pre: preOf(args) }
  }
  const c = adapters.map((a) => a.computation?.(L, source.target)).find((x) => x !== undefined)
  if (c === undefined) throw new Unsupported("no adapter reads this as a computation (an async function, `Effect.fn(...)(function* ...)`)", source.target)
  const { params, args } = symbolicArgs(c.node)
  const r = runBody(L, c.node, c.style, emptyEnv, args, emptyTrace(L), c.node)
  return { u, L, source, fn: c.node, params, args, result: r.outcome, trace: r.trace, pre: preOf(args) }
}

const lawOn = (side: Lowered, law: ContractSource["ensures"][number]): Bool<"main"> =>
  truthy(side.u, lowerCall(side.L, law.law, emptyEnv, side.trace === undefined ? [...side.args, side.result] : [...side.args, side.result, side.trace], law.law))

export const verify = async (z3: Ctx, project: Project, file: string, name: string, opts: Options = {}): Promise<Verification> => {
  const source = readContract(project, file, name)
  const bound = opts.bound ?? 4
  let proof: Lowered
  let search: Lowered
  try {
    proof = lowerSide(z3, project, source)
    search = lowerSide(z3, project, source, bound)
  } catch (e) {
    if (!(e instanceof Unsupported)) throw e
    return { contract: name, laws: [], cover: [], notes: ALWAYS, unsupported: e.message }
  }

  const laws: Array<LawResult> = []
  for (const law of source.ensures) {
    const started = performance.now()
    let onProof: Bool<"main">
    let onSearch: Bool<"main">
    try {
      onProof = lawOn(proof, law)
      onSearch = lawOn(search, law)
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e
      laws.push({ name: law.name, status: "unsupported", reason: e.message, ms: performance.now() - started })
      opts.progress?.(`law ${law.name}: unsupported`)
      continue
    }
    const proved = await solve(proof, [proof.pre, z3.Not(onProof)], opts)
    let r: Omit<LawResult, "name" | "ms">
    if (proved.status === "unsat") r = { status: "proved" }
    else if (proved.status === "sat" && !proof.u.abstracted) r = { status: "counterexample", ...proved.witness }
    else {
      const found = await solve(search, [search.pre, z3.Not(onSearch)], opts)
      r =
        found.status === "sat"
          ? { status: "counterexample", ...found.witness }
          : found.status === "unsat"
            ? { status: "bounded", reason: `not proved (${why(proved)}); no counterexample with arrays of at most ${bound} elements` }
            : { status: "unknown", reason: `proof: ${why(proved)}; search: ${found.reason}` }
    }
    laws.push({ name: law.name, ...r, ms: performance.now() - started })
    opts.progress?.(`law ${law.name}: ${r.status} (${Math.round(performance.now() - started)} ms)`)
  }

  const cover: Array<CoverResult> = []
  const returns = project.checker.getReturnTypeOfSignature(project.checker.getSignatureFromDeclaration(proof.fn)!)
  const literals = (returns.isUnion() ? returns.types : [returns]).filter((t) => t.isStringLiteral())
  if (source.kind === "function" && proof.result.kind === "str" && literals.length > 0)
    for (const t of literals) {
      const value = (t as ts.StringLiteralType).value
      const is = (side: Lowered) => strictEq(side.u, side.result, { kind: "str", term: z3.String.val(value) }, side.fn)
      const found = await solve(search, [search.pre, is(search)], opts)
      let c: CoverResult
      if (found.status === "sat") c = { value, status: "reachable", ...found.witness }
      else {
        const any = await solve(proof, [proof.pre, is(proof)], opts)
        c =
          any.status === "unsat"
            ? { value, status: "unreachable" }
            : any.status === "sat" && !proof.u.abstracted
              ? { value, status: "reachable", ...any.witness }
              : { value, status: found.status === "unsat" ? "bounded" : "unknown" }
      }
      cover.push(c)
      opts.progress?.(`cover ${value}: ${c.status}`)
    }
  if (source.kind === "computation")
    for (const [value, goal] of outcomesOf(project, proof)) {
      const found = await solve(search, [search.pre, goal(search)], opts)
      let c: CoverResult
      if (found.status === "sat") c = { value, status: "reachable", ...found.witness }
      else {
        const any = await solve(proof, [proof.pre, goal(proof)], opts)
        c =
          any.status === "unsat"
            ? { value, status: "unreachable" }
            : any.status === "sat" && !proof.u.abstracted
              ? { value, status: "reachable", ...any.witness }
              : { value, status: found.status === "unsat" ? "bounded" : "unknown" }
      }
      cover.push(c)
      opts.progress?.(`cover ${value}: ${c.status}`)
    }
  return { contract: name, laws, cover, notes: [...ALWAYS, ...proof.u.notes] }
}

/**
 * The ends a computation can come to, as cover goals: success, and a failure for each `_tag` its declared failure
 * type names (one undistinguished failure when it declares none).
 */
const outcomesOf = (project: Project, side: Lowered): Array<readonly [string, (s: Lowered) => Bool<"main">]> => {
  const field = (v: Val, n: string): Val | undefined => (v.kind === "record" ? v.field(n) : undefined)
  const tagIs = (v: Val | undefined, t: string, z3: Ctx): Bool<"main"> =>
    v?.kind === "str" ? v.term.eq(z3.String.val(t)) : z3.Bool.val(false)
  const sig = project.checker.getTypeAtLocation(side.source.target).getCallSignatures()[0]
  const returns = sig?.getReturnType()
  const op = returns === undefined ? undefined : side.L.adapters.map((a) => a.operation?.(side.L, returns)).find((x) => x !== undefined)
  const failures = op?.failure === undefined ? [] : op.failure.isUnion() ? op.failure.types : [op.failure]
  const tags = failures.flatMap((f) => {
    const t = project.checker.getPropertyOfType(f, "_tag")
    const tt = t === undefined ? undefined : project.checker.getTypeOfSymbol(t)
    return tt?.isStringLiteral() ? [tt.value] : []
  })
  const goals: Array<readonly [string, (s: Lowered) => Bool<"main">]> = [["Success", (s) => tagIs(field(s.result, "_tag"), "Success", s.u.z3)]]
  if (tags.length === 0) goals.push(["Failure", (s) => tagIs(field(s.result, "_tag"), "Failure", s.u.z3)])
  for (const t of tags)
    goals.push([
      `Failure ${t}`,
      (s) => s.u.z3.And(tagIs(field(s.result, "_tag"), "Failure", s.u.z3), tagIs(field(field(s.result, "error") ?? { kind: "nullish", which: "undefined" }, "_tag"), t, s.u.z3)),
    ])
  return goals
}

const why = (o: Outcome): string =>
  o.status === "unknown" ? o.reason : o.status === "sat" ? "the proof side's model rests on an approximation" : "proved"

type Witness = {
  readonly args?: ReadonlyArray<unknown>
  readonly world?: Readonly<Record<string, unknown>>
  readonly abstract?: ReadonlyArray<string>
  readonly reason?: string
}

type Outcome =
  | { readonly status: "sat"; readonly witness: Witness }
  | { readonly status: "unsat" }
  | { readonly status: "unknown"; readonly reason: string }

/** Checks a side's assumptions with `goals`; on `sat`, reads the arguments back, preferring short arrays. */
export const solve = async (side: Lowered, goals: ReadonlyArray<Bool<"main">>, opts: Options = {}): Promise<Outcome> => {
  const { u } = side
  const z3 = u.z3
  const run = async (extra: ReadonlyArray<Bool<"main">>) => {
    const solver = new z3.Solver()
    solver.set("timeout", opts.timeoutMs ?? 10_000)
    for (const a of [...u.assumptions, ...goals, ...extra]) solver.add(a)
    const status = await solver.check()
    return { status, solver }
  }
  const first = await run([])
  if (first.status === "unsat") return { status: "unsat" }
  if (first.status === "unknown") return { status: "unknown", reason: first.solver.reasonUnknown() }
  // A model may pick a huge array; ask again with short ones, which narrows the same formula.
  const short = [...u.leaves.values()]
    .filter((l) => l.arity === 0 && l.segments.at(-1) === "#len")
    .map((l) => (l.constant as Arith<"main">).le(8))
  const small = short.length > 0 && u.bound === undefined ? await run(short) : undefined
  const model = small?.status === "sat" ? small.solver.model() : first.solver.model()
  return { status: "sat", witness: witness(side, model) }
}

const witness = (side: Lowered, model: Model<"main">): Witness => {
  try {
    const roots = new Set([...side.u.leaves.values()].map((l) => l.segments[0]!))
    for (const p of side.params) roots.delete(p)
    const world = Object.fromEntries([...roots].sort().map((r) => [r, fromModel(side.u, model, r)]))
    return {
      args: side.params.map((p) => fromModel(side.u, model, p)),
      ...(roots.size > 0 ? { world } : {}),
      ...(side.u.opaqueCalls.size > 0 ? { abstract: [...side.u.opaqueCalls] } : {}),
    }
  } catch (e) {
    if (e instanceof TooLong) return { reason: `the counterexample holds ${e.message}; too long to replay` }
    throw e
  }
}

/**
 * Whether a side's lowering computes what the code does on `inputs`: with each
 * input's values pinned on the leaves, can the symbolic result differ from what
 * running the code gave? Returns the inputs on which it can.
 */
export const disagreements = async (
  side: Lowered,
  inputs: ReadonlyArray<ReadonlyArray<unknown>>,
  expected: (args: ReadonlyArray<unknown>) => unknown,
): Promise<Array<{ readonly args: ReadonlyArray<unknown>; readonly expected: unknown; readonly status: string }>> => {
  const { u, params, result } = side
  const z3 = u.z3
  const out: Array<{ args: ReadonlyArray<unknown>; expected: unknown; status: string }> = []
  for (const args of inputs) {
    const want = expected(args)
    const pins = params.flatMap((p, i) => pin(u, p, args[i]))
    const solver = new z3.Solver()
    solver.set("timeout", 20_000)
    for (const a of [...u.assumptions, ...pins, z3.Not(strictEq(u, result, valueOf(u, want), side.fn))]) solver.add(a)
    const status = await solver.check()
    if (status !== "unsat") out.push({ args, expected: want, status })
  }
  return out
}

const valueOf = (u: Universe, want: unknown): Val => {
  if (want === null || want === undefined) return { kind: "nullish", which: want === null ? "null" : "undefined" }
  const term = literal(u, want) as never
  if (typeof want === "string") return { kind: "str", term }
  if (typeof want === "boolean") return { kind: "bool", term }
  if (typeof want === "bigint") return { kind: "int", origin: "bigint", term }
  if (typeof want === "number") return num(u.z3, want)
  throw new Error(`cannot compare a result of type ${typeof want}`)
}

/** Runs `f` with a fresh Z3 context and frees Z3's worker threads after, so the process can exit. */
export const withZ3 = async <A>(f: (z3: Ctx) => Promise<A>): Promise<A> => {
  const api = await init()
  try {
    return await f(api.Context("main"))
  } finally {
    await killThreads(api.em)
  }
}
