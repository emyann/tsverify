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
import type { Obligation } from "./exec.ts"
import { emptyEnv, inSpec, type Lowering, lowerCall, lowering, num, type Trust, trustOf } from "./lower.ts"
import { strictEq, truthy } from "./ops.ts"
import { type ContractSource, type Project, readContract } from "./project.ts"
import { symbolicOf } from "./symbolic.ts"
import { PURITY_TRUSTS, readAssumptions, type Trusted } from "./trust.ts"
import { Universe } from "./universe.ts"
import { type Ctx, type FunctionNode, Unsupported, type Val } from "./value.ts"

/** The adapters every verification reads with, in the order they are asked. */
export const ADAPTERS: ReadonlyArray<Adapter> = [effectAdapter, asyncAdapter, tsAdapter]

export type LawStatus =
  /** No allowed input breaks it: `unsat` on the proof side. */
  | "proved"
  /** An allowed input breaks it; `args` holds one. */
  | "counterexample"
  /**
   * The two sides disagree: the proof side proved it, and the search side found an input that breaks it (`args`). One
   * of them is wrong, which is a bug of the verifier, never a verdict on the code.
   */
  | "inconsistent"
  /**
   * Proved, and no result of the law's type would break it either: it says nothing of the function. A law over the
   * inputs alone, or one whose condition no allowed input meets (`!A || B` with `A` never true).
   */
  | "vacuous"
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
  /** Set when the witness leans on declared functions, as a law's counterexample may. */
  readonly abstract?: ReadonlyArray<string>
}

/** An obligation of the proof code (an invariant, an assert, a lemma's precondition or the lemma itself), as decided. */
export interface ObligationResult {
  readonly kind: Obligation["kind"] | "lemma"
  readonly text: string
  readonly at: string
  readonly phase: Obligation["phase"]
  readonly status: "proved" | "counterexample" | "bounded" | "unknown" | "inconsistent"
  /** On a counterexample, or when the sides disagree: arguments on which it fails. */
  readonly args?: ReadonlyArray<unknown>
  readonly reason?: string
}

export interface Verification {
  readonly contract: string
  readonly laws: ReadonlyArray<LawResult>
  readonly cover: ReadonlyArray<CoverResult>
  /** What the model of JavaScript assumed on the way, each kind once. */
  readonly notes: ReadonlyArray<string>
  /**
   * The declarations the verification leaned on (`assume(...)`): what it took without proof. A proof holds of the
   * program only if each of these holds of the function it names.
   */
  readonly trusted: ReadonlyArray<Trusted>
  /**
   * What the proof code asked proved. A law proved on the proof side leans on every one of these; while one is not
   * proved, such a law is reported `bounded`.
   */
  readonly obligations: ReadonlyArray<ObligationResult>
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
  /** The lemmas being verified, outermost first: a lemma that leans on itself is refused. */
  readonly within?: ReadonlyArray<string>
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
export const lowerSide = (
  z3: Ctx,
  project: Project,
  source: ContractSource,
  bound?: number,
  adapters = ADAPTERS,
  trust: Trust = trustOf(readAssumptions(project)),
): Lowered => {
  const u = new Universe(z3, bound)
  const L = lowering({ u, checker: project.checker }, adapters, trust)
  const symbolicArgs = (fn: FunctionNode) => {
    const params = fn.parameters.map((p, i) => (ts.isIdentifier(p.name) ? p.name.text : `arg${i}`))
    return { params, args: fn.parameters.map((p, i) => symbolicOf(L, project.checker.getTypeAtLocation(p), [params[i]!], [], p)) }
  }
  const preOf = (args: ReadonlyArray<Val>) =>
    source.requires === undefined ? z3.Bool.val(true) : inSpec(L, () => truthy(u, lowerCall(L, source.requires!, emptyEnv, args, source.requires!)))
  if (source.kind === "lemma") {
    const t = source.target as FunctionNode
    const { params, args } = symbolicArgs(t)
    const result = inSpec(L, () => lowerCall(L, t, emptyEnv, args, t))
    return { u, L, source, fn: t, params, args, result, trace: undefined, pre: preOf(args) }
  }
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
  side.source.kind === "lemma" ? truthy(side.u, side.result) : inSpec(side.L, () =>
    truthy(side.u, lowerCall(side.L, law.law, emptyEnv, side.trace === undefined ? [...side.args, side.result] : [...side.args, side.result, side.trace], law.law)),
  )

/**
 * The law with the function's result, and a computation's calls, replaced by any value of the law's own parameter types;
 * `undefined` when such a value cannot be built.
 */
const lawOnAnyResult = (side: Lowered, law: ContractSource["ensures"][number]): Bool<"main"> | undefined => {
  const params = law.law.parameters
  const k = side.args.length
  try {
    const any = (i: number): Val => {
      const p = params[i]
      // A law that does not name it cannot read it: any value will do.
      if (p === undefined) return i === k ? side.result : side.trace!
      return symbolicOf(side.L, side.L.checker.getTypeAtLocation(p), [side.u.fresh("any-result")], side.u.openBounds(), p)
    }
    const replaced = side.trace === undefined ? [any(k)] : [any(k), any(k + 1)]
    return inSpec(side.L, () => truthy(side.u, lowerCall(side.L, law.law, emptyEnv, [...side.args, ...replaced], law.law)))
  } catch (e) {
    if (e instanceof Unsupported) return undefined
    throw e
  }
}

export const verify = async (z3: Ctx, project: Project, file: string, name: string, opts: Options = {}): Promise<Verification> => {
  const source = readContract(project, file, name)
  const bound = opts.bound ?? 4
  let proof: Lowered
  let search: Lowered
  let trust: Trust
  try {
    trust = trustOf(readAssumptions(project))
    proof = lowerSide(z3, project, source, undefined, ADAPTERS, trust)
    search = lowerSide(z3, project, source, bound, ADAPTERS, trust)
  } catch (e) {
    if (!(e instanceof Unsupported)) throw e
    return { contract: name, laws: [], cover: [], notes: ALWAYS, trusted: [], obligations: [], unsupported: e.message }
  }
  if (source.kind === "lemma" && opts.within?.includes(`${file}#${name}`))
    return { contract: name, laws: [], cover: [], notes: ALWAYS, trusted: [], obligations: [], unsupported: `the lemma \`${name}\` leans on itself` }
  return judge(z3, project, file, proof, search, trust, opts)
}

/**
 * Which of `items` the search side breaks, each with the input that does: one query for all of them, then one for each
 * only when that finds something. A proved item broken there means one side is wrong.
 */
const contradicted = async (
  search: Lowered,
  items: ReadonlyArray<{ readonly key: string; readonly broken: Bool<"main"> }>,
  opts: Options,
  hints?: ReadonlyArray<Bool<"main">>,
): Promise<Map<string, ReadonlyArray<unknown> | undefined>> => {
  const z3 = search.u.z3
  const out = new Map<string, ReadonlyArray<unknown> | undefined>()
  if (items.length === 0) return out
  const any = await solve(search, [search.pre, z3.Or(...items.map((i) => i.broken))], opts, hints)
  if (any.status !== "sat") return out
  for (const i of items) {
    const one = await solve(search, [search.pre, i.broken], opts, hints)
    if (one.status === "sat") out.set(i.key, one.witness.args)
  }
  return out
}

/** What it says when the two sides disagree: what to do with the input. */
const DISAGREE =
  "the proof side proved it, and the search side found this input breaking it: one side is wrong, a bug of tsverify. Run the code on the input: if it breaks the law, the proof is wrong; if not, the search side is. Report it with the input"

/** Decides a contract both sides have lowered: its obligations, its laws, what its result reaches. */
export const judge = async (z3: Ctx, project: Project, file: string, proof: Lowered, search: Lowered, trust: Trust, opts: Options = {}): Promise<Verification> => {
  const source = proof.source
  const name = source.name
  const bound = opts.bound ?? 4
  // The proof code's obligations first: a law the proof side proves leans on them, and stands only if they do.
  const obligations = await obligationsOf(z3, project, proof, search, bound, { ...opts, within: [...(opts.within ?? []), `${file}#${name}`] })
  const open = obligations.filter((o) => o.status !== "proved")
  const leaning =
    open.length === 0
      ? undefined
      : `proved only if the proof code's obligations hold, and ${open.length} of them ${open.length === 1 ? "is" : "are"} not proved (${open[0]!.kind} ${open[0]!.text} at ${open[0]!.at}: ${open[0]!.status}); no counterexample with arrays of at most ${bound} elements`

  const laws: Array<LawResult> = []
  const searchable = new Map<string, Bool<"main">>()
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
    // A proof that holds only of the inputs a truncated loop keeps to is no proof; read after the law, which may run it.
    const untrusted = leaning ?? (proof.u.truncated === undefined ? undefined : `proved only of the inputs that run no loop longer: ${proof.u.truncated}; no counterexample with arrays of at most ${bound} elements`)
    let r: Omit<LawResult, "name" | "ms">
    if (proved.status === "unsat" && untrusted === undefined) {
      // A proof of a law no result could break is a proof of nothing about the function.
      const onAny = source.kind === "lemma" ? undefined : lawOnAnyResult(proof, law)
      const breakable = onAny === undefined ? undefined : await solve(proof, [proof.pre, z3.Not(onAny)], opts)
      r =
        breakable?.status === "unsat"
          ? { status: "vacuous", reason: "no result breaks it, whatever the function returns: it says nothing of the function" }
          : { status: "proved" }
    }
    else if (proved.status === "sat" && !proof.u.abstracted) r = { status: "counterexample", ...proved.witness }
    else {
      const found = await solve(search, [search.pre, z3.Not(onSearch)], opts)
      r =
        found.status === "sat"
          ? { status: "counterexample", ...found.witness }
          : found.status === "unsat"
            ? { status: "bounded", reason: proved.status === "unsat" ? untrusted! : `not proved (${why(proved)}); no counterexample with arrays of at most ${bound} elements` }
            : { status: "unknown", reason: `proof: ${why(proved)}; search: ${found.reason}` }
    }
    laws.push({ name: law.name, ...r, ms: performance.now() - started })
    searchable.set(law.name, onSearch)
    opts.progress?.(`law ${law.name}: ${r.status} (${Math.round(performance.now() - started)} ms)`)
  }

  // Every law proved is checked against the search side, all in one query. One proved through an obligation the sides
  // disagree on is no proof: it is broken on the search side, or bounded.
  const provedLaws = laws.flatMap((l, k) => (l.status === "proved" || l.status === "vacuous" ? [k] : []))
  const failing = await contradicted(
    search,
    provedLaws.map((k) => ({ key: String(k), broken: z3.Not(searchable.get(laws[k]!.name)!) })),
    opts,
  )
  const shaken = obligations.some((o) => o.status === "inconsistent")
  for (const k of provedLaws) {
    const l = laws[k]!
    const found = failing.get(String(k))
    if (failing.has(String(k)))
      laws[k] = shaken
        ? { ...l, status: "counterexample", ...(found === undefined ? {} : { args: found }), reason: "proved only through an obligation the two sides disagree on" }
        : { ...l, status: "inconsistent", ...(found === undefined ? {} : { args: found }), reason: DISAGREE }
    else if (shaken) laws[k] = { ...l, status: "bounded", reason: `proved only through an obligation the two sides disagree on; no counterexample with arrays of at most ${bound} elements` }
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
  const coverOut = leaning === undefined && proof.u.truncated === undefined ? cover : cover.map((c) => (c.status === "unreachable" ? { ...c, status: "bounded" as const } : c))
  const trusted = trustedOf(trust)
  const notes = [...ALWAYS, ...new Set([...proof.u.notes, ...search.u.notes])]
  if (trusted.some((t) => t.purity === "checked")) notes.push(`A purity check takes on trust that ${PURITY_TRUSTS.join("; that ")}.`)
  return { contract: name, laws, cover: coverOut, notes, trusted, obligations }
}

/**
 * Decides the proof code's obligations: each proved on the proof side, or broken on the search side by a real input.
 * The same obligation met twice (a loop inlined in two calls) is one: broken if either instance is. Every lemma called
 * is verified, and is an obligation too.
 */
const obligationsOf = async (
  z3: Ctx,
  project: Project,
  proof: Lowered,
  search: Lowered,
  bound: number,
  opts: Options,
): Promise<Array<ObligationResult>> => {
  const keys = [...new Set([...proof.L.obligations, ...search.L.obligations].map((o) => o.key))]
  const broken = (side: Lowered, key: string): Bool<"main"> | undefined => {
    const os = side.L.obligations.filter((o) => o.key === key)
    return os.length === 0 ? undefined : z3.Or(...os.map((o) => z3.And(o.cond, z3.Not(o.goal), ...side.L.hints.slice(0, o.hints))))
  }
  /**
   * The obligation `key` failing on the search side as the first of the proof code to fail on that run: every obligation
   * met before it held. A loop's `kept` is proved from any state its invariants allow; a run on which they all held up to
   * here, and this one fails, breaks that step, where a run that failed an earlier one need not.
   */
  const firstToFail = (key: string): Bool<"main"> | undefined => {
    const os = search.L.obligations
    const each = os.flatMap((o, k) => (o.key !== key ? [] : [z3.And(o.cond, z3.Not(o.goal), ...os.slice(0, k).map((p) => z3.Implies(p.cond, p.goal)))]))
    return each.length === 0 ? undefined : z3.Or(...each)
  }
  const out: Array<ObligationResult> = []
  for (const key of keys) {
    const o = [...proof.L.obligations, ...search.L.obligations].find((x) => x.key === key)!
    const head = { kind: o.kind, text: o.text, at: o.at, phase: o.phase }
    const onProof = broken(proof, key)
    const proved = onProof === undefined ? undefined : await solve(proof, [proof.pre, onProof], opts, [])
    if (proved?.status === "unsat" && proof.u.truncated === undefined) {
      out.push({ ...head, status: "proved" })
      continue
    }
    if (proved?.status === "sat" && !proof.u.abstracted) {
      out.push({ ...head, status: "counterexample", ...(proved.witness.args === undefined ? {} : { args: proved.witness.args }) })
      continue
    }
    const onSearch = broken(search, key)
    const found = onSearch === undefined ? undefined : await solve(search, [search.pre, onSearch], opts, [])
    if (found?.status === "sat") out.push({ ...head, status: "counterexample", ...(found.witness.args === undefined ? {} : { args: found.witness.args }) })
    else if (found?.status === "unsat")
      out.push({
        ...head,
        status: "bounded",
        reason:
          o.phase === "kept"
            ? `true of every input with arrays of at most ${bound} elements, and not proved kept by an iteration from any state it allows: strengthen it with what else the loop keeps`
            : `not proved (${proved === undefined ? "the proof side does not meet it" : proved.status === "unsat" ? proof.u.truncated : why(proved)}); no counterexample with arrays of at most ${bound} elements`,
      })
    else out.push({ ...head, status: "unknown", reason: found?.status === "unknown" ? found.reason : "not met on either side" })
    opts.progress?.(`${o.kind} ${o.at}: ${out.at(-1)!.status}`)
  }
  // Every proof is checked against the search side, all in one query: a run on which one of them is the first to fail.
  const provedKeys = keys.filter((_, k) => out[k]?.status === "proved")
  const disagreements = await contradicted(
    search,
    provedKeys.flatMap((key) => {
      const f = firstToFail(key)
      return f === undefined ? [] : [{ key, broken: f }]
    }),
    opts,
    [],
  )
  for (const [key, args] of disagreements) {
    const k = keys.indexOf(key)
    out[k] = { ...out[k]!, status: "inconsistent", reason: DISAGREE, ...(args === undefined ? {} : { args }) }
  }
  const lemmas = new Map([...proof.L.lemmas, ...search.L.lemmas])
  for (const [key, lem] of lemmas) {
    const v = await verify(z3, project, lem.file, lem.name, opts)
    const status: ObligationResult["status"] =
      v.unsupported !== undefined
        ? "unknown"
        : v.laws.every((l) => l.status === "proved") && v.obligations.every((x) => x.status === "proved")
          ? "proved"
          : [...v.laws, ...v.obligations].some((l) => l.status === "inconsistent")
            ? "inconsistent"
              : v.laws.some((l) => l.status === "counterexample")
              ? "counterexample"
              : "bounded"
    const failed = v.laws.find((l) => l.status === "counterexample")
    out.push({
      kind: "lemma",
      text: lem.name,
      at: key,
      phase: "here",
      status,
      ...(failed?.args === undefined ? {} : { args: failed.args }),
      ...(v.unsupported === undefined ? {} : { reason: v.unsupported }),
    })
  }
  return out
}

/** The trusted base of a verification: each declaration it leaned on, with how far its purity was checked. */
const trustedOf = (trust: Trust): Array<Trusted> =>
  [...trust.used].map((a) => {
    const p = trust.purity.get(a)
    return {
      name: a.name,
      declared: a.views.map((v) => v.where),
      purity: !a.pure ? "impure" : p?.pure === true ? "checked" : "unchecked",
      laws: [...new Set(a.views.flatMap((v) => v.ensures.map((l) => l.name)))],
      ...(p?.pure === true ? { read: p.read } : {}),
    }
  })

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
export const solve = async (side: Lowered, goals: ReadonlyArray<Bool<"main">>, opts: Options = {}, hints: ReadonlyArray<Bool<"main">> = side.L.hints): Promise<Outcome> => {
  const { u } = side
  const z3 = u.z3
  const run = async (extra: ReadonlyArray<Bool<"main">>) => {
    const solver = new z3.Solver()
    solver.set("timeout", opts.timeoutMs ?? 10_000)
    for (const a of [...u.assumptions, ...hints, ...goals, ...extra]) solver.add(a)
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
    // A declared function's result inside a quantifier is one per element: a function of the index, not a value to show.
    for (const l of side.u.leaves.values()) if (l.arity > l.segments.filter((s) => s === "[]").length) roots.delete(l.segments[0]!)
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
/** A Z3 context to verify many contracts with, and how to let it go: a test opens one before its cases and closes it after. */
export const openZ3 = async (): Promise<{ readonly z3: Ctx; readonly close: () => Promise<void> }> => {
  const api = await init()
  return { z3: api.Context("main"), close: async () => void (await killThreads(api.em)) }
}

export const withZ3 = async <A>(f: (z3: Ctx) => Promise<A>): Promise<A> => {
  const { z3, close } = await openZ3()
  try {
    return await f(z3)
  } finally {
    await close()
  }
}
