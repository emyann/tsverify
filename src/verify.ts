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
import {
  type Asked,
  type End,
  type Engine,
  Ledger,
  type Question,
  type SidesEnd,
  STUCK_MS,
  type Side,
  type Unanswered,
  endOf,
  endWords,
  saysAnything,
  unansweredOf,
} from "./asked.ts"
import { type Cache, contractKey, runSeed } from "./cache.ts"
import { asyncAdapter } from "./adapters/async.ts"
import { effectAdapter } from "./adapters/effect/index.ts"
import { tsAdapter } from "./adapters/ts.ts"
import { emptyTrace, runBody } from "./computation.ts"
import { TooLong, fromModel, literal, pin } from "./concrete.ts"
import { MODELS, type Obligation } from "./exec.ts"
import {
  emptyEnv,
  type GuessedInvariant,
  inSpec,
  type Lowering,
  definedSpec,
  lowerCall,
  lowerExpr,
  lowering,
  member,
  num,
  type Trust,
  trustOf,
} from "./lower.ts"
import { slice } from "./lower/arrays.ts"
import { type Ran, type RunResult, planOf, runContract } from "./run/runs.ts"
import { runOf, strictEq, truthy } from "./ops.ts"
import { type ContractSource, type Project, readContract } from "./project.ts"
import { unwrap } from "./resolve.ts"
import { symbolicOf } from "./symbolic.ts"
import { PURITY_TRUSTS, readAssumptions, type Trusted } from "./trust.ts"
import { Universe } from "./universe.ts"
import { type Ctx, type FunctionNode, UNDEFINED as UNDEFINED_VAL, Unsupported, type Val, fromZ3String, jsString, locate } from "./value.ts"

/** The adapters every verification reads with, in the order they are asked. */
export const ADAPTERS: ReadonlyArray<Adapter> = [effectAdapter, asyncAdapter, tsAdapter]

export type LawStatus =
  /** No allowed input breaks it: `unsat` on the proof side. */
  | "proved"
  /** An allowed input breaks it; `args` holds one. */
  | "counterexample"
  /**
   * An allowed input breaks it (`args`), and no result keeps every law there at once: the laws in `conflicts` together,
   * or with `requires`, leave none. The spec, not the code, has to change: no code could keep the law.
   */
  | "unmeetable"
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
  /** What the law means, in words, where it is written `{ description, condition }`. */
  readonly description?: string
  readonly status: LawStatus
  /**
   * Which engine decided it: `run`, a counterexample found by running the function and the law on a generated input, real
   * by construction; `z3`, every other verdict. Set on every law decided.
   */
  readonly by?: Engine
  /** On a counterexample: the arguments, as JavaScript values. */
  readonly args?: ReadonlyArray<unknown>
  /** On a counterexample of a computation: how each operation call it made ended, by call. */
  readonly world?: Readonly<Record<string, unknown>>
  /** On an unmeetable law: the laws that together leave no result at `args`, itself among them. */
  readonly conflicts?: ReadonlyArray<string>
  /**
   * Set when the counterexample leans on functions read as unknown (their bodies refused): it holds of the code with
   * them unknown, and may not of the real ones. It names them.
   */
  readonly abstract?: ReadonlyArray<string>
  readonly reason?: string
  readonly ms: number
  /** The time of each question asked of the law, by side and by how its queries ended. */
  readonly asked?: ReadonlyArray<Asked>
  /** The questions of the law that ended without an answer, and what its verdict took of each instead. */
  readonly unanswered?: ReadonlyArray<Unanswered>
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
  /** For a loop invariant the verifier guessed (none was written), the law it restates. */
  readonly guessed?: string
  /** On a counterexample, or when the sides disagree: arguments on which it fails. */
  readonly args?: ReadonlyArray<unknown>
  /** On a computation's counterexample: what the world gave the code on that run, as a law's `world`. */
  readonly world?: Readonly<Record<string, unknown>>
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
  /** Set when the laws leave a result open between two kinds at some input: code could answer either. */
  readonly undecided?: Undecided
  /** Set when the function or `requires` could not be lowered: no law is checked then. */
  readonly unsupported?: string
  /**
   * The time of the contract's own questions, by side and by how its queries ended: the cross-check, what the result
   * reaches, whether the laws decide every input, and the obligations, the rounds that guess a loop's invariants among them.
   */
  readonly asked?: ReadonlyArray<Asked>
  /** The contract's own questions that ended without an answer. */
  readonly unanswered?: ReadonlyArray<Unanswered>
  /** How long its verification took, every question and the reading of its code; that of the run that decided it, when kept. */
  readonly ms?: number
  /** Where the laws were run on generated inputs (`Options.run`): what the run did, or why there was none. */
  readonly ran?: Ran
}

/**
 * An input `requires` allows where two results of different kinds each keep every law: code could answer either, and
 * a proof of the laws says nothing of which. Two results differ in kind where a closed part of them differs, a value of a
 * few literal cases (a union of strings, a boolean) or whether it is `undefined` or `null`; never a free string or
 * number, such as a message.
 */
export interface Undecided {
  /** The closed part they differ in: `output`, a field of it (`output.status`), or whether it is `undefined`. */
  readonly differ: string
  /** The input, as a call's arguments; unset where it is too long to show (`reason`). */
  readonly args?: ReadonlyArray<unknown>
  /** The two results, each keeping every law at `args`. */
  readonly results?: readonly [unknown, unknown]
  /** Why the input is not shown. */
  readonly reason?: string
}

export interface Options {
  /**
   * The work each query may do, on each side, in the solver's own units (Z3's resource limit, `rlimit`): a count of
   * its steps, not of seconds, so a verdict is the same on a fast machine and a slow one, idle or busy, as the context
   * of its own each contract is verified in keeps the order of the solver's search (`ownContext`), but for a query
   * that never counts its work, which `STUCK_MS`, a clock, stops. `WORK` by default.
   */
  readonly work?: number
  /** The search side's longest array. */
  readonly bound?: number
  /** Called as each law and each cover query is decided: progress for a long run. */
  readonly progress?: (line: string) => void
  /** The lemmas being verified, outermost first: a lemma that leans on itself is refused. */
  readonly within?: ReadonlyArray<string>
  /** Decide these laws alone, and ask no cover: the check of one law, as a test of a planted bug asks it. */
  readonly only?: ReadonlyArray<string>
  /**
   * Whether to ask what the result reaches (`cover`), true by default: false leaves it empty, and saves a query or two
   * for each end, most of a run's time when every law is proved. The command asks for it only where its report shows it.
   */
  readonly cover?: boolean
  /**
   * Where the verdicts of contracts verified before are kept (`verdictsIn` of `./cache.ts`): a contract whose program
   * reads the same text under the same settings is answered from it, and not verified again. None by default.
   */
  readonly cache?: Cache
  /**
   * Whether to run the laws of a pure function's contract on generated inputs first, in a child process, before any is
   * asked of Z3: a law a run breaks comes back as that run's counterexample. False by default; the command sets it.
   */
  readonly run?: boolean
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
  readonly pre: Bool
  /** The laws whose guessed invariant could not be read in the loop's state: guesses to drop. */
  readonly unguessable: ReadonlySet<string>
}

const ALWAYS = [
  "The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.",
  "Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.",
]

/** Lowers the contract's function and precondition on one side (`bound` set: the search side). */
export const lowerSide = (
  z3: Ctx,
  project: Project,
  source: ContractSource,
  bound?: number,
  adapters = ADAPTERS,
  trust: Trust = trustOf(readAssumptions(project).forTarget(source.target)),
  guessFrom?: ReadonlySet<string>,
  guessBeside = false,
  opaqueKeyed = false,
  specAlone = false,
): Lowered => {
  const u = new Universe(z3, bound)
  const L = lowering(
    { u, checker: project.checker, unchecked: project.program.getCompilerOptions().noUncheckedIndexedAccess === true },
    adapters,
    trust,
  )
  if (opaqueKeyed) L.opaqueKeyed = true
  const unguessable = new Set<string>()
  const symbolicArgs = (fn: FunctionNode) => {
    const params = fn.parameters.map((p, i) => (ts.isIdentifier(p.name) ? p.name.text : `arg${i}`))
    // A parameter with a default is one a caller may leave out, or give as `undefined`: drawn as maybe `undefined`.
    const drawn = (p: ts.ParameterDeclaration, i: number) =>
      symbolicOf(L, project.checker.getTypeAtLocation(p), [params[i]!], [], p, p.initializer !== undefined)
    return { params, args: fn.parameters.map(drawn) }
  }
  const preOf = (args: ReadonlyArray<Val>) =>
    source.requires === undefined
      ? z3.Bool.val(true)
      : definedSpec(
          L,
          () =>
            inSpec(L, () =>
              truthy(
                u,
                // A lemma's `requires` reads its statement's variables; a contract's, the arguments of a run.
                lowerCall(
                  L,
                  source.requires!,
                  emptyEnv,
                  source.kind === "lemma" ? args : [runOf(u, source.requires!, args)],
                  source.requires!,
                ),
              ),
            ),
          "requires",
        )
  if (source.kind === "lemma") {
    const t = source.target as FunctionNode
    const { params, args } = symbolicArgs(t)
    const result = inSpec(L, () => lowerCall(L, t, emptyEnv, args, t))
    return { u, L, source, fn: t, params, args, result, trace: undefined, pre: preOf(args), unguessable }
  }
  // Of the spec alone: the arguments and `requires`, and no call of the function, so none of what the code does rides
  // along. A law read on it is read on a free result (`lawOnAnyResult`).
  const alone = (fn: FunctionNode): Lowered => {
    const { params, args } = symbolicArgs(fn)
    return {
      u,
      L,
      source,
      fn,
      params,
      args,
      result: UNDEFINED_VAL,
      trace: source.kind === "computation" ? UNDEFINED_VAL : undefined,
      pre: preOf(args),
      unguessable,
    }
  }
  if (source.kind === "function") {
    const t = source.target
    if (!(ts.isArrowFunction(t) || ts.isFunctionExpression(t) || ts.isFunctionDeclaration(t)))
      throw new Unsupported("a `contract` is about a function; a computation takes `computation<...>()`", t)
    if (specAlone) return alone(t)
    const { params, args } = symbolicArgs(t)
    if (guessFrom !== undefined) {
      L.guess = guesser(L, source, t, args, guessFrom, unguessable)
      L.guessBeside = guessBeside
    }
    return {
      u,
      L,
      source,
      fn: t,
      params,
      args,
      result: lowerCall(L, t, emptyEnv, args, t),
      trace: undefined,
      pre: preOf(args),
      unguessable,
    }
  }
  const c = adapters.map((a) => a.computation?.(L, source.target)).find((x) => x !== undefined)
  if (c === undefined)
    throw new Unsupported("no adapter reads this as a computation (an async function, `Effect.fn(...)(function* ...)`)", source.target)
  if (specAlone) return alone(c.node)
  const { params, args } = symbolicArgs(c.node)
  const r = runBody(L, c.node, c.style, emptyEnv, args, emptyTrace(L), c.node)
  return { u, L, source, fn: c.node, params, args, result: r.outcome, trace: r.trace, pre: preOf(args), unguessable }
}

/**
 * The contract's spec alone on the proof side: its arguments and `requires`, with no call of the function. Whether a law
 * says anything is asked of it, so the answer is the spec's, whatever the code does. Undefined where it cannot be read.
 */
export const lowerSpecSide = (z3: Ctx, project: Project, source: ContractSource, trust: Trust): Lowered | undefined => {
  try {
    return lowerSide(z3, project, source, undefined, ADAPTERS, trust, undefined, false, false, true)
  } catch (e) {
    if (e instanceof Unsupported) return undefined
    throw e
  }
}

/**
 * The verifier's guesses for a loop of the contract's own function over one of its parameters, when the loop has none
 * written: each law, restated for the elements gone through so far, of what the function returns after the loop. A
 * fold's laws are often just that. A guess is only a candidate: `verify` keeps the ones proved on entry and kept by
 * each iteration, all together, and drops the rest.
 */
const guesser =
  (L: Lowering, source: ContractSource, fn: FunctionNode, args: ReadonlyArray<Val>, laws: ReadonlySet<string>, unguessable: Set<string>) =>
  (loop: ts.ForOfStatement): ReadonlyArray<GuessedInvariant> => {
    let host: ts.Node | undefined = loop.parent
    while (host !== undefined && !ts.isFunctionLike(host)) host = host.parent
    if (host !== fn || fn.body === undefined || !ts.isBlock(fn.body)) return []
    const iterated = unwrap(loop.expression)
    const sym = ts.isIdentifier(iterated) ? L.checker.getSymbolAtLocation(iterated) : undefined
    const p = sym === undefined ? -1 : fn.parameters.findIndex((q) => L.checker.getSymbolAtLocation(q.name) === sym)
    const xs = args[p]
    // What the function returns, by name, after the loop: `return a`.
    const returned = fn.body.statements.find(
      (st): st is ts.ReturnStatement =>
        ts.isReturnStatement(st) && st.pos >= loop.end && st.expression !== undefined && ts.isIdentifier(unwrap(st.expression)),
    )
    if (xs?.kind !== "array" || returned === undefined) return []
    const result = unwrap(returned.expression!) as ts.Identifier
    const count = (term: Arith): Val => ({ kind: "int", origin: "count", term })
    return source.ensures
      .filter((law) => laws.has(law.name) && law.law.parameters.length <= 1)
      .map((law) => ({
        law: law.name,
        key: `invariant@${locate(loop)}:${law.name}`,
        at: locate(loop),
        text: `${law.name}, of the elements gone through`,
        claim: (env, i) => {
          try {
            return inSpec(L, () => {
              const seen = slice(L, xs, [count(L.u.z3.Int.val(0)), count(i)], loop)
              return truthy(
                L.u,
                lowerCall(
                  L,
                  law.law,
                  emptyEnv,
                  [runOf(L.u, loop, [...args.slice(0, p), seen, ...args.slice(p + 1)], lowerExpr(L, result, env))],
                  law.law,
                ),
              )
            })
          } catch (e) {
            // Not readable in the loop's state: no candidate. It claims nothing, and is dropped.
            if (!(e instanceof Unsupported)) throw e
            unguessable.add(law.name)
            return L.u.z3.Bool.val(true)
          }
        },
      }))
  }

/** A law's `description`, for its result, when it has one. */
const described = (law: ContractSource["ensures"][number]): { readonly description?: string } =>
  law.description === undefined ? {} : { description: law.description }

const lawOn = (side: Lowered, law: ContractSource["ensures"][number]): Bool =>
  side.source.kind === "lemma"
    ? truthy(side.u, side.result)
    : definedSpec(side.L, () =>
        inSpec(side.L, () =>
          truthy(side.u, lowerCall(side.L, law.law, emptyEnv, [runOf(side.u, law.law, side.args, side.result, side.trace)], law.law)),
        ),
      )

type Law = ContractSource["ensures"][number]

/** Any value of the type `law`'s run gives `field`, or `given` where the law takes none: a law that does not take it cannot read it. */
const anyOf = (side: Lowered, law: Law, field: "output" | "calls", given: Val): Val => {
  const run = law.law.parameters[0]
  const checker = side.L.checker
  const p = run === undefined ? undefined : checker.getPropertyOfType(checker.getTypeAtLocation(run), field)
  if (run === undefined || p === undefined) return given
  return symbolicOf(side.L, checker.getTypeOfSymbol(p), [side.u.fresh("any-result")], side.u.openBounds(), run)
}

/** The law on a run of the function's input whose result, and a computation's calls, are `output` and `calls`. */
const lawWith = (side: Lowered, law: Law, output: Val, calls: Val | undefined): Bool =>
  definedSpec(side.L, () =>
    inSpec(side.L, () => truthy(side.u, lowerCall(side.L, law.law, emptyEnv, [runOf(side.u, law.law, side.args, output, calls)], law.law))),
  )

/**
 * The law with the function's result, and a computation's calls, replaced by any value of the law's own parameter types;
 * `undefined` when such a value cannot be built.
 */
const lawOnAnyResult = (side: Lowered, law: Law): Bool | undefined => {
  try {
    return lawWith(
      side,
      law,
      anyOf(side, law, "output", side.result),
      side.trace === undefined ? undefined : anyOf(side, law, "calls", side.trace),
    )
  } catch (e) {
    if (e instanceof Unsupported) return undefined
    throw e
  }
}

/**
 * Each of `laws` on one result they all share, any value of their run's type, and a computation's calls likewise: what
 * some result would have to keep at once. `undefined` when no law takes a result, or one cannot be read on it.
 */
const lawsOnOneResult = (
  side: Lowered,
  laws: ReadonlyArray<Law>,
): ReadonlyArray<{ readonly name: string; readonly holds: Bool }> | undefined => {
  const checker = side.L.checker
  const takes = laws.find((l) => {
    const run = l.law.parameters[0]
    return run !== undefined && checker.getPropertyOfType(checker.getTypeAtLocation(run), "output") !== undefined
  })
  if (takes === undefined) return undefined
  try {
    const output = anyOf(side, takes, "output", side.result)
    const calls = side.trace === undefined ? undefined : anyOf(side, takes, "calls", side.trace)
    return laws.map((law) => ({ name: law.name, holds: lawWith(side, law, output, calls) }))
  } catch (e) {
    if (e instanceof Unsupported) return undefined
    throw e
  }
}

/**
 * The laws that together leave no result at the input `args`, `requires` holding there (one law alone, where it refuses
 * every result): each law read on one result they share, the input pinned, and the set cut down until dropping any one
 * of them leaves a result that keeps the rest. Empty when some result keeps every law, or when that cannot be asked. A law broken there is broken by the spec:
 * no code could keep it.
 */
const conflictsAt = async (
  side: Lowered,
  laws: ReadonlyArray<Law>,
  args: ReadonlyArray<unknown>,
  opts: Options,
  ask?: Ask,
): Promise<{ readonly conflicts: ReadonlyArray<string>; readonly end?: End }> => {
  const { u } = side
  const z3 = u.z3
  const none = { conflicts: [] }
  const each = lawsOnOneResult(side, laws)
  if (each === undefined || each.length === 0) return none
  let pins: Array<Bool>
  try {
    pins = side.params.flatMap((p, i) => pin(u, p, args[i]))
  } catch {
    return none
  }
  const solver = new z3.Solver()
  // A tenth of a query's work: the question is asked of every counterexample, and one it cannot settle leaves it one.
  limited(solver, tenthOf(opts.work ?? WORK))
  vectorsBy(u, solver)
  for (const a of [...u.assumptions, ...side.L.hints, side.pre, ...pins]) solver.add(a)
  try {
    // The input itself must be one the model keeps, or every set of laws would read as conflicting.
    const input = await checked(solver, ask)
    if (input.status !== "sat") return input.status === "unknown" ? { conflicts: [], end: input.end } : none
    const marks = each.map(({ name, holds }, k) => {
      const mark = z3.Bool.const(`meets#${k}`)
      solver.add(z3.Implies(mark, holds))
      return { name, mark }
    })
    const all = await checked(solver, ask, ...marks.map((m) => m.mark))
    if (all.status !== "unsat") return all.status === "unknown" ? { conflicts: [], end: all.end } : none
    const core = new Set([...solver.unsatCore().values()].map((b) => b.id()))
    let kept = marks.filter((m) => core.has(m.mark.id()))
    for (const m of kept) {
      const without = kept.filter((k) => k !== m)
      if (without.length > 0 && (await checked(solver, ask, ...without.map((k) => k.mark))).status === "unsat") kept = without
    }
    return { conflicts: kept.map((m) => m.name) }
  } finally {
    solver.release()
  }
}

/** A closed part of a result: a value of a few literal cases, or whether the result is `undefined` or `null`, read where `present`. */
interface Part {
  readonly path: string
  readonly value: Val
  readonly present: Bool
}

const UNDEFINED = ts.TypeFlags.Undefined | ts.TypeFlags.Void
const NULLISH = UNDEFINED | ts.TypeFlags.Null
const literalCase = (t: ts.Type): boolean => t.isLiteral() || (t.flags & (ts.TypeFlags.BooleanLiteral | NULLISH)) !== 0

/**
 * The closed parts of `v`, a value of `type`: itself where every case of its type is a literal; whether it is `undefined`
 * or `null`, and the closed parts of its value, where it may be either; and the closed parts of each field of a record, two
 * levels down. Free strings and numbers have none: two results that differ only there are of one kind.
 */
const closedParts = (L: Lowering, type: ts.Type, v: Val, at: ts.Node, path: string, present: Bool, depth: number): ReadonlyArray<Part> => {
  const z3 = L.u.z3
  const cases = type.isUnion() ? type.types : [type]
  if (cases.length > 1 && cases.every(literalCase)) return [{ path, value: v, present }]
  if (v.kind === "maybe") {
    if (v.value === undefined) return []
    const there = z3.And(present, z3.Not(v.isNull), z3.Not(v.isUndefined))
    return [
      ...(cases.some((t) => (t.flags & UNDEFINED) !== 0)
        ? [{ path: `${path} === undefined`, value: { kind: "bool", term: v.isUndefined } as Val, present }]
        : []),
      ...(cases.some((t) => (t.flags & ts.TypeFlags.Null) !== 0)
        ? [{ path: `${path} === null`, value: { kind: "bool", term: v.isNull } as Val, present }]
        : []),
      ...closedParts(L, L.checker.getNonNullableType(type), v.value, at, path, there, depth),
    ]
  }
  if (v.kind !== "record" || v.entries !== undefined || depth >= 2) return []
  return L.checker.getPropertiesOfType(type).flatMap((p) => {
    const t = L.checker.getTypeOfSymbol(p)
    try {
      return closedParts(L, t, member(L, v, p.name, at, type, t), at, `${path}.${p.name}`, present, depth + 1)
    } catch (e) {
      if (e instanceof Unsupported) return []
      throw e
    }
  })
}

/**
 * An input `requires` allows where two results of different kinds each keep every law (`Undecided`), asked on the search
 * side: what it looks for is an example, and every model the search side finds is a real input, found quickly where the
 * proof side's unbounded records leave the solver without an answer. It reads no code: two results free of it, each with
 * every law asserted on it, required to differ in a closed part. Undefined where none is found within the search side's
 * bound, the laws take no result, or the result has no closed part.
 */
const undecidedOf = async (
  side: Lowered,
  laws: ReadonlyArray<Law>,
  open: ReadonlyArray<string>,
  opts: Options,
  ask?: Ask,
): Promise<Undecided | End | undefined> => {
  const { u, L } = side
  const z3 = u.z3
  const checker = L.checker
  const takes = laws.find((l) => {
    const run = l.law.parameters[0]
    return run !== undefined && checker.getPropertyOfType(checker.getTypeAtLocation(run), "output") !== undefined
  })
  if (takes === undefined) return undefined
  const run = takes.law.parameters[0]!
  const type = checker.getTypeOfSymbol(checker.getPropertyOfType(checker.getTypeAtLocation(run), "output")!)
  try {
    const answer = () => {
      const root = u.fresh("answer")
      const value = symbolicOf(L, type, [root], u.openBounds(), run)
      // A part the spec leaves open, or one under it, is not asked: `output.error` leaves `output.error._tag` open too.
      const asked = (p: Part) => !open.some((o) => p.path === o || p.path.startsWith(`${o}.`) || p.path.startsWith(`${o} `))
      return { root, value, parts: closedParts(L, type, value, run, "output", z3.Bool.val(true), 0).filter(asked) }
    }
    const a = answer()
    const b = answer()
    if (a.parts.length === 0 || a.parts.length !== b.parts.length) return undefined
    const differs = a.parts.map((p, i) => z3.And(p.present, b.parts[i]!.present, z3.Not(strictEq(u, p.value, b.parts[i]!.value, run))))
    const keeps = [a, b].flatMap((x) => laws.map((l) => lawWith(side, l, x.value, undefined)))
    // A query's whole work, not unmeetable's tenth: the input is free here, and a run's records are large.
    const solver = new z3.Solver()
    limited(solver, opts.work ?? WORK)
    vectorsBy(u, solver)
    for (const f of [...u.assumptions, ...L.hints, side.pre, ...keeps, z3.Or(...differs)]) solver.add(f)
    try {
      const asked = await checked(solver, ask)
      if (asked.status !== "sat") return asked.status === "unknown" ? asked.end : undefined
      const model = solver.model()
      const at = differs.findIndex((d) => z3.isTrue(model.eval(d, true)))
      const differ = a.parts[at]?.path ?? "output"
      try {
        return {
          differ,
          args: side.params.map((p) => fromModel(u, model, p)),
          results: [ended(fromModel(u, model, a.root)), ended(fromModel(u, model, b.root))],
        }
      } catch (e) {
        // Found, and too long to show: still undecided.
        if (e instanceof TooLong) return { differ, reason: `the input holds ${e.message}; too long to show` }
        throw e
      }
    } finally {
      solver.release()
    }
  } catch (e) {
    if (e instanceof Unsupported || e instanceof TooLong) return undefined
    throw e
  }
}

/**
 * The verdicts of contract `name` of `file`, each the same on every run but where `STUCK_MS` stops a query: the
 * contract is verified in a Z3 context of its own (`ownContext`), deleted once its verdicts are read, so no contract
 * verified before it changes them.
 */
export const verify = async (z3: Ctx, project: Project, file: string, name: string, opts: Options = {}): Promise<Verification> =>
  (await verifyOrKept(z3, project, file, name, opts)).v

/** `verify`, and whether its verdict was kept from an earlier run (`kept`): its times are then that run's, not this one's. */
const verifyOrKept = async (
  z3: Ctx,
  project: Project,
  file: string,
  name: string,
  opts: Options,
): Promise<{ readonly v: Verification; readonly kept: boolean }> => {
  const timed = async (): Promise<Verification> => {
    const started = performance.now()
    const v = await ownContext(z3, (own) => verified(own, project, file, name, opts))
    return { ...v, ms: performance.now() - started }
  }
  if (opts.cache === undefined) return { v: await timed(), kept: false }
  const key = contractKey(project, file, name, opts)
  const kept = opts.cache.get(key)
  if (kept !== undefined) return { v: kept, kept: true }
  const v = await timed()
  opts.cache.set(key, v)
  return { v, kept: false }
}

const verified = async (z3: Ctx, project: Project, file: string, name: string, opts: Options): Promise<Verification> => {
  // Without it a type leaves out `null` and `undefined`, and so would every proof read from it. TypeScript 6 has it on by default.
  const options = project.program.getCompilerOptions()
  if (!(options.strictNullChecks ?? options.strict ?? true))
    return {
      contract: name,
      laws: [],
      cover: [],
      notes: ALWAYS,
      trusted: [],
      obligations: [],
      unsupported:
        '`strictNullChecks` is off in the tsconfig.json that reads this file, so its types leave out `null` and `undefined`, and a proof would too: set `"strict": true` (or `"strictNullChecks": true`)',
    }
  let source: ContractSource
  try {
    source = readContract(project, file, name)
  } catch (e) {
    if (!(e instanceof Unsupported)) throw e
    return { contract: name, laws: [], cover: [], notes: ALWAYS, trusted: [], obligations: [], unsupported: e.message }
  }
  const bound = opts.bound ?? 4
  // The contract's own questions, over every round: the guessing, and each judge.
  const ledger = new Ledger()
  let trust: Trust
  // A loop with no invariant written gets the laws, restated for what it has gone through, as candidates. Round after
  // round, the candidates not proved on entry and kept by each iteration (all of them assumed at its start) are
  // dropped, until those left are proved together: Houdini's way (Flanagan and Leino, ESC/Java, 2001). When what is
  // written leaves a law unproved, the guesses are made again beside it, so writing an invariant never loses a guess.
  const guessed = async (beside: boolean) => {
    let guessing = source.kind === "function" ? new Set(source.ensures.map((l) => l.name)) : undefined
    const dropped: Array<string> = []
    let proof = lowerSide(z3, project, source, undefined, ADAPTERS, trust, guessing, beside)
    let search = lowerSide(z3, project, source, bound, ADAPTERS, trust, guessing, beside)
    for (;;) {
      if (guessing === undefined || !proof.L.obligations.some((o) => o.guessed !== undefined)) break
      const within = { ...opts, within: [...(opts.within ?? []), `${file}#${name}`] }
      const failed = new Set([...proof.unguessable, ...search.unguessable])
      for (const o of (await obligationsOf(z3, project, proof, search, bound, within, ledger)).obligations)
        if (o.guessed !== undefined && o.status !== "proved") failed.add(o.guessed)
      if (failed.size === 0) break
      dropped.push(...failed)
      guessing = new Set([...guessing].filter((l) => !failed.has(l)))
      proof = lowerSide(z3, project, source, undefined, ADAPTERS, trust, guessing, beside)
      search = lowerSide(z3, project, source, bound, ADAPTERS, trust, guessing, beside)
    }
    // Where a loop is read key by key, each law is asked first with what it writes at each key unknown (`opaqueWrites`):
    // what the law needs of it is often nothing, and the loop's body read at every key the law reads is costly.
    const g = guessing
    const opaque = proof.L.keyed === true ? () => lowerSide(z3, project, source, undefined, ADAPTERS, trust, g, beside, true) : undefined
    const kept = [...new Set(proof.L.obligations.flatMap((o) => (o.guessed === undefined ? [] : [o.guessed])))]
    if (kept.length > 0 || dropped.length > 0)
      proof.u.notes.add(
        `For a loop${beside ? " with invariants written" : " with no invariant written"}, the verifier guessed each law as an invariant, restated for the elements gone through, and kept ${kept.join(", ") || "none"}${dropped.length > 0 ? `; it dropped ${dropped.join(", ")}, not proved on entry and kept` : ""}.`,
      )
    return { proof, search, opaque }
  }
  let sides: { readonly proof: Lowered; readonly search: Lowered; readonly opaque: (() => Lowered) | undefined }
  try {
    trust = trustOf(readAssumptions(project).forTarget(source.target))
    sides = await guessed(false)
  } catch (e) {
    if (!(e instanceof Unsupported)) throw e
    return { contract: name, laws: [], cover: [], notes: ALWAYS, trusted: [], obligations: [], unsupported: e.message }
  }
  if (source.kind === "lemma" && opts.within?.includes(`${file}#${name}`))
    return {
      contract: name,
      laws: [],
      cover: [],
      notes: ALWAYS,
      trusted: [],
      obligations: [],
      unsupported: `the lemma \`${name}\` leans on itself`,
    }
  // A pure function's laws are run first, on generated inputs: what a run settles, Z3 is not asked.
  let ran: RunResult | undefined
  if (opts.run === true) {
    const plan = planOf(project, source, trust, opts, runSeed(project, name, opts))
    ran = "why" in plan ? { broken: {}, saysSomething: [], ran: { ran: false, why: plan.why } } : await runContract(plan)
    opts.progress?.(ran.ran.ran ? `ran ${ran.ran.inputs} inputs` : `not run: ${ran.ran.why}`)
  }
  const first = await judge(z3, project, file, sides.proof, sides.search, trust, opts, sides.opaque, ledger, ran)
  // Only where it can help: a law left bounded while what is written all holds. A broken invariant keeps its law bounded
  // whatever else is guessed.
  if (
    source.kind !== "function" ||
    sides.proof.L.wrote !== true ||
    !first.laws.some((l) => l.status === "bounded") ||
    !first.obligations.every((o) => o.status === "proved")
  )
    return first
  // Asked again beside what is written: whichever judge's verdicts are kept, every query of both is counted.
  const keptOf = (v: Verification, other: Verification): Verification => ({
    ...v,
    laws: v.laws.map((l) => {
      const before = other.laws.find((o) => o.name === l.name)?.asked ?? []
      const all = new Ledger()
      all.addAll([...before, ...(l.asked ?? [])])
      return { ...l, asked: all.asked }
    }),
    asked: ledger.asked,
  })
  let beside: { readonly proof: Lowered; readonly search: Lowered; readonly opaque: (() => Lowered) | undefined }
  try {
    beside = await guessed(true)
  } catch (e) {
    if (!(e instanceof Unsupported)) throw e
    return { ...first, asked: ledger.asked }
  }
  // Kept only where it proves more: a guess beside an invariant that fails proves nothing the report should carry.
  const second = await judge(z3, project, file, beside.proof, beside.search, trust, opts, beside.opaque, ledger, ran)
  const proved = (v: Verification) => v.laws.filter((l) => l.status === "proved").length
  return proved(second) > proved(first) ? keptOf(second, first) : keptOf(first, second)
}

/**
 * Which of `items` the search side breaks, each with the input that does: one query for all of them, then one for each
 * only when that finds something. A proved item broken there means one side is wrong.
 */
const contradicted = async (
  search: Lowered,
  items: ReadonlyArray<{ readonly key: string; readonly broken: Bool }>,
  opts: Options,
  hints?: ReadonlyArray<Bool>,
  ledger?: Ledger,
): Promise<{ readonly found: Map<string, ReadonlyArray<unknown> | undefined>; readonly unsettled: Map<string, End> }> => {
  const z3 = search.u.z3
  const found = new Map<string, ReadonlyArray<unknown> | undefined>()
  const unsettled = new Map<string, End>()
  if (items.length === 0) return { found, unsettled }
  const ask = ledger === undefined ? undefined : ({ ledger, question: "cross-check", side: "search" } as const)
  const any = await solve(search, [search.pre, z3.Or(...items.map((i) => i.broken))], opts, hints, ask)
  if (any.status === "unknown") for (const i of items) unsettled.set(i.key, any.end)
  if (any.status !== "sat") return { found, unsettled }
  for (const i of items) {
    const one = await solve(search, [search.pre, i.broken], opts, hints, ask)
    if (one.status === "sat") found.set(i.key, one.witness.args)
    else if (one.status === "unknown") unsettled.set(i.key, one.end)
  }
  return { found, unsettled }
}

/** A counterexample's input, and what the world gave the code on that run. */
const shown = (w: Witness): { readonly args?: ReadonlyArray<unknown>; readonly world?: Readonly<Record<string, unknown>> } => ({
  ...(w.args === undefined ? {} : { args: w.args }),
  ...(w.world === undefined ? {} : { world: w.world }),
})

/**
 * The runs of a side the model reads exactly: no division throws, every element write lands inside its array, and
 * every `number` operation is exact. A law speaks of what the code returns, so it is judged on these runs, and each
 * condition is reported as its own obligation. A run that breaks a write or arithmetic goes on, so a law leans on those
 * too (`judge`); a division by 0n throws, and its run returns nothing a law could speak of. Nor does a computation's
 * run that dies: a defect is outside its types, as Effect keeps it, and its ends say whether one can.
 */
const returning = (side: Lowered, dying: "judged" | "kept" = "judged"): Bool => {
  const z3 = side.u.z3
  const each = side.L.obligations.filter((o) => MODELS.has(o.kind)).map((o) => z3.Implies(o.cond, o.goal))
  const tag = dying === "judged" && side.u.dies && side.result.kind === "record" ? side.result.field("_tag") : undefined
  if (tag?.kind === "str") each.push(z3.Not(tag.term.eq(jsString(z3, "Die"))))
  return each.length === 0 ? z3.Bool.val(true) : z3.And(...each)
}

/** What a law proved with a loop's writes unknown says of how it was proved. */
const OPAQUE =
  "proved with what a loop read key by key writes at each key unknown, whether it sets the key and with which value: the law holds whatever that loop writes"

/**
 * The side asked first, lowered for one law, and the law read on it; undefined where either cannot be read: the law is
 * then asked of the loop as it is.
 */
const opaqueLaw = (opaque: () => Lowered, law: Law): { readonly side: Lowered; readonly law: Bool } | undefined => {
  try {
    const side = opaque()
    return { side, law: lawOn(side, law) }
  } catch (e) {
    if (e instanceof Unsupported) return undefined
    throw e
  }
}

/** What it says when the two sides disagree: what to do with the input. */
const DISAGREE =
  "the proof side proved it, and the search side found this input breaking it: one side is wrong, a bug of tsverify. Run the code on the input: if it breaks the law, the proof is wrong; if not, the search side is. Report it with the input"

/**
 * Decides a contract both sides have lowered: its obligations, its laws, what its result reaches. The time of the
 * contract's own questions goes to `ledger`, and is the contract's `asked`.
 */
export const judge = async (
  z3: Ctx,
  project: Project,
  file: string,
  proof: Lowered,
  search: Lowered,
  trust: Trust,
  opts: Options = {},
  opaque?: () => Lowered,
  ledger: Ledger = new Ledger(),
  ran?: RunResult,
): Promise<Verification> => {
  const source = proof.source
  const name = source.name
  const bound = opts.bound ?? 4
  // Every law, and every end the result may reach, is read on both sides before the obligations are decided: reading
  // them runs code (a division in a field a law reads) whose obligation exists only once it has run.
  const read = source.ensures.map((law) => {
    try {
      return { law, onProof: lawOn(proof, law), onSearch: lawOn(search, law) }
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e
      return { law, unsupported: e.message }
    }
  })
  const ends = endsOf(project, source, proof, search)
  const proofRuns = returning(proof)
  const searchRuns = returning(search)
  // The obligations next: a law the proof side proves leans on them, and stands only if they do.
  const { obligations, unanswered: unchecked } = await obligationsOf(
    z3,
    project,
    proof,
    search,
    bound,
    { ...opts, within: [...(opts.within ?? []), `${file}#${name}`] },
    ledger,
  )
  // A law leans on what the proof code proved; a division only says which runs return, and is reported on its own.
  const open = obligations.filter((o) => o.status !== "proved" && o.kind !== "division")
  const leaning =
    open.length === 0
      ? undefined
      : `proved only if its obligations hold, and ${open.length} of them ${open.length === 1 ? "is" : "are"} not proved (${open[0]!.kind} ${open[0]!.text} at ${open[0]!.at}: ${open[0]!.status}); no counterexample with arrays of at most ${bound} elements`

  const laws: Array<LawResult> = []
  /** Each law's ledger, and what its questions left without an answer, by its place in `laws`. */
  const ledgers: Array<Ledger> = []
  const notes: Array<Array<Unanswered>> = []
  // Whether a law says something is asked at a tenth of a query's work, as whether a counterexample's input leaves any
  // result is (`conflictsAt`): it is asked of every proved law. One it cannot settle in that keeps the law proved, said.
  const tenth = { ...opts, work: tenthOf(opts.work ?? WORK) }
  const searchable = new Map<string, Bool>()
  // The spec alone, read once, where a law's says-anything is not settled by a run.
  let specSide: Lowered | undefined | null = null
  const spec = (): Lowered | undefined => (specSide === null ? (specSide = lowerSpecSide(z3, project, source, trust)) : specSide)
  const inputs = ran?.ran.ran === true ? ran.ran.inputs : 0
  for (const r0 of read) {
    const { law } = r0
    if (opts.only !== undefined && !opts.only.includes(law.name)) continue
    const started = performance.now()
    const own = new Ledger()
    const unsettled: Array<Unanswered> = []
    const ask = (question: Question, side: Side): Ask => ({ ledger: own, question, side })
    if (r0.unsupported !== undefined) {
      laws.push({ name: law.name, ...described(law), status: "unsupported", reason: r0.unsupported, ms: 0 })
      ledgers.push(own)
      notes.push(unsettled)
      opts.progress?.(`law ${law.name}: unsupported`)
      continue
    }
    const { onProof, onSearch } = r0
    const broken = ran?.broken[law.name]
    if (broken !== undefined) {
      // A run broke it: the real function on a real input, the real law on its result. Z3 is asked once, the input
      // pinned, whether the law holds there: where it says so, the run and Z3 disagree.
      const r = await crossChecked(proof, proofRuns, onProof, broken.args, trust, tenth, ask("cross-check", "proof"))
      laws.push({ name: law.name, ...described(law), ...r, ms: performance.now() - started })
      ledgers.push(own)
      notes.push(unsettled)
      searchable.set(law.name, onSearch)
      opts.progress?.(`law ${law.name}: ${r.status}, found by running (${Math.round(performance.now() - started)} ms)`)
      continue
    }
    // Asked first with what a loop read key by key writes unknown, on a side of its own that reads this law alone; a law
    // that does not hold there is asked of the loop as it is.
    const alone = opaque === undefined ? undefined : opaqueLaw(opaque, law)
    const first =
      alone === undefined
        ? undefined
        : await solve(alone.side, [alone.side.pre, returning(alone.side), z3.Not(alone.law)], opts, undefined, ask("proof", "proof"))
    const byOpaque = first?.status === "unsat"
    const proved = byOpaque ? first : await solve(proof, [proof.pre, proofRuns, z3.Not(onProof)], opts, undefined, ask("proof", "proof"))
    // A proof that holds only of the inputs a truncated loop keeps to is no proof; read after the law, which may run it.
    const truncated = byOpaque ? alone!.side.u.truncated : proof.u.truncated
    const untrusted =
      leaning ??
      (truncated === undefined
        ? undefined
        : `proved only of the inputs that run no loop longer: ${truncated}; no counterexample with arrays of at most ${bound} elements`)
    let r: Omit<LawResult, "name" | "ms">
    if (proved.status === "unsat" && untrusted === undefined) {
      // A proof of a law no result could break is a proof of nothing about the function. It is a question of the spec
      // alone: a run that found a free result breaking it settles it; else the proof side is asked, of the spec alone.
      const byRun = source.kind !== "lemma" && ran?.saysSomething.includes(law.name) === true
      if (byRun) own.add("says-anything", undefined, "answered", 0, inputs, "run")
      const side = source.kind === "lemma" || byRun ? undefined : spec()
      const onAny = side === undefined ? undefined : lawOnAnyResult(side, law)
      const breakable =
        side === undefined || onAny === undefined
          ? undefined
          : await solve(side, [side.pre, z3.Not(onAny)], tenth, undefined, ask("says-anything", "proof"))
      const says = saysAnything(byRun, endedAs(breakable))
      if (says.unanswered !== undefined) unsettled.push(says.unanswered)
      r = says.vacuous
        ? { status: "vacuous", reason: "no result breaks it, whatever the function returns: it says nothing of the function" }
        : byOpaque
          ? { status: "proved", reason: OPAQUE }
          : { status: "proved" }
    } else if (proved.status === "sat" && !proof.u.abstracted) r = { status: "counterexample", ...proved.witness }
    else {
      const found = await solve(search, [search.pre, searchRuns, z3.Not(onSearch)], opts, undefined, ask("search", "search"))
      r =
        found.status === "sat"
          ? { status: "counterexample", ...found.witness }
          : found.status === "unsat"
            ? {
                status: "bounded",
                reason:
                  proved.status === "unsat"
                    ? untrusted!
                    : `not proved: ${why(proved, proof.u)}; no counterexample with arrays of at most ${bound} elements`,
              }
            : { status: "unknown", reason: `proof: ${why(proved, proof.u)}; search: ${found.reason}` }
    }
    laws.push({ name: law.name, ...described(law), ...r, ms: performance.now() - started })
    ledgers.push(own)
    notes.push(unsettled)
    searchable.set(law.name, onSearch)
    opts.progress?.(`law ${law.name}: ${r.status} (${Math.round(performance.now() - started)} ms)`)
  }

  // A law broken at an input where no result keeps every law is broken by the spec, not the code: asked on the proof side,
  // whose reading of the code over-approximates and of a law is exact, so a law it finds no result for has none.
  if (source.kind !== "lemma") {
    const readable = read.flatMap((r) => (r.unsupported === undefined ? [r.law] : []))
    for (const [k, l] of laws.entries()) {
      if (l.status !== "counterexample" || l.args === undefined) continue
      const { conflicts, end } = await conflictsAt(proof, readable, l.args, opts, {
        ledger: ledgers[k]!,
        question: "unmeetable",
        side: "proof",
      })
      if (end !== undefined) notes[k]!.push(unansweredOf("unmeetable", end, "proof"))
      if (conflicts.length === 0) continue
      laws[k] = {
        ...l,
        status: "unmeetable",
        conflicts,
        reason:
          conflicts.length === 1
            ? `no result keeps ${l.name} at this input, whatever the code returns: change the spec, by loosening the law or narrowing \`requires\` to rule the input out`
            : `no result keeps ${conflicts.join(" and ")} together at this input, so no code could keep ${l.name} here: change the spec, by loosening one of them or narrowing \`requires\` to rule the input out`,
      }
      opts.progress?.(`law ${l.name}: unmeetable`)
    }
  }

  // Every law proved is checked against the search side, all in one query. One proved through an obligation the sides
  // disagree on is no proof: it is broken on the search side, or bounded.
  const provedLaws = laws.flatMap((l, k) => (l.status === "proved" || l.status === "vacuous" ? [k] : []))
  const { found: failing, unsettled: crossUnchecked } = await contradicted(
    search,
    provedLaws.map((k) => ({ key: String(k), broken: z3.And(searchRuns, z3.Not(searchable.get(laws[k]!.name)!)) })),
    opts,
    undefined,
    ledger,
  )
  for (const [key, end] of crossUnchecked) notes[Number(key)]!.push(unansweredOf("cross-check", end, "search"))
  const shaken = obligations.some((o) => o.status === "inconsistent")
  for (const k of provedLaws) {
    const l = laws[k]!
    const found = failing.get(String(k))
    if (failing.has(String(k)))
      laws[k] = shaken
        ? {
            ...l,
            status: "counterexample",
            ...(found === undefined ? {} : { args: found }),
            reason: "proved only through an obligation the two sides disagree on",
          }
        : { ...l, status: "inconsistent", ...(found === undefined ? {} : { args: found }), reason: DISAGREE }
    else if (shaken)
      laws[k] = {
        ...l,
        status: "bounded",
        reason: `proved only through an obligation the two sides disagree on; no counterexample with arrays of at most ${bound} elements`,
      }
  }

  // An end is any run's, one that dies among them.
  const [proofEnds, searchEnds] = [returning(proof, "kept"), returning(search, "kept")]
  const cover: Array<CoverResult> = []
  for (const { value, onProof, onSearch } of opts.only === undefined && opts.cover !== false ? ends : []) {
    const found = await solve(search, [search.pre, searchEnds, onSearch], opts, undefined, { ledger, question: "cover", side: "search" })
    let c: CoverResult
    if (found.status === "sat") c = { value, status: "reachable", ...found.witness }
    else {
      const any = await solve(proof, [proof.pre, proofEnds, onProof], opts, undefined, { ledger, question: "cover", side: "proof" })
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
  const coverOut =
    leaning === undefined && proof.u.truncated === undefined
      ? cover
      : cover.map((c) => (c.status === "unreachable" ? { ...c, status: "bounded" as const } : c))
  // Last, as it adds roots of its own to the search side: whether the laws decide every input, asked of the spec alone. A
  // law not read could be the one that decides, so it is asked only where every law is.
  const asked =
    // A pure function's alone: a computation's laws read its calls, and two runs that share calls no code of it could make
    // would be undecided wherever its laws pin no trace, which is most of them.
    source.kind !== "function" || source.open === true || opts.only !== undefined || read.some((r) => r.unsupported !== undefined)
      ? undefined
      : await undecidedOf(search, source.ensures, source.open ?? [], opts, { ledger, question: "undecided", side: "search" })
  const undecided = typeof asked === "string" ? undefined : asked
  const unanswered = [...unchecked, ...(typeof asked === "string" ? [unansweredOf("undecided", asked, "search")] : [])]
  if (undecided !== undefined) opts.progress?.(`undecided: ${undecided.differ}`)
  const trusted = trustedOf(trust)
  const assumed = [...ALWAYS, ...new Set([...proof.u.notes, ...search.u.notes])]
  if (trusted.some((t) => t.purity === "checked")) assumed.push(`A purity check takes on trust that ${PURITY_TRUSTS.join("; that ")}.`)
  return {
    contract: name,
    laws: laws.map((l, k) => ({
      ...l,
      ...(l.status === "unsupported" ? {} : { by: l.by ?? "z3" }),
      asked: ledgers[k]!.asked,
      ...(notes[k]!.length === 0 ? {} : { unanswered: notes[k]! }),
    })),
    cover: coverOut,
    notes: assumed,
    trusted,
    obligations,
    ...(undecided === undefined ? {} : { undecided }),
    asked: ledger.asked,
    ...(unanswered.length === 0 ? {} : { unanswered }),
    ...(ran === undefined ? {} : { ran: ran.ran }),
  }
}

/**
 * A law a run broke at `args`, checked against Z3: the proof side asked, the input pinned, whether the law can break
 * there. Where it answers that it cannot, the real code and Z3's reading of it disagree: a declaration the reading leaned
 * on is wrong about its function, or, where it leaned on none, tsverify is. The run is the real code, so the law stays
 * broken. An input Z3 cannot pin (a generated function) is not asked.
 */
const crossChecked = async (
  proof: Lowered,
  runs: Bool,
  law: Bool,
  args: ReadonlyArray<unknown>,
  trust: Trust,
  opts: Options,
  ask: Ask,
): Promise<Omit<LawResult, "name" | "ms">> => {
  const found = { status: "counterexample", by: "run", args } as const
  let pins: Array<Bool>
  try {
    pins = proof.params.flatMap((p, i) => pin(proof.u, p, args[i]))
  } catch {
    return found
  }
  const z3 = proof.u.z3
  const there = await solve(proof, [proof.pre, runs, z3.Not(law), ...pins], opts, undefined, ask)
  if (there.status !== "unsat") return found
  const leaned = [...trust.used].map((a) => a.name)
  return leaned.length > 0
    ? {
        ...found,
        reason: `the code breaks it on this input when run, where Z3, leaning on what is declared of ${leaned.map((n) => `\`${n}\``).join(", ")}, proves it holds: a declaration (\`assume\`) is wrong about its function. Run it on this input, and correct the declaration`,
      }
    : { status: "inconsistent", by: "run", args, reason: RUN_DISAGREES }
}

/** What it says when a run breaks a law Z3 proves at the same input, leaning on no declaration. */
const RUN_DISAGREES =
  "the code breaks it on this input when run, and the proof side proves it holds there: Z3's reading of the code is wrong, a bug of tsverify. Report it with the input"

/** How a says-anything query ended, as `saysAnything` reads it; unset where it was not asked. */
const endedAs = (o: Outcome | undefined): SidesEnd | undefined =>
  o === undefined ? undefined : o.status === "unknown" ? { status: "unknown", end: o.end } : { status: o.status }

/**
 * The ends a contract's result may come to, each as a goal on both sides: every string of a result that is a union of
 * them, and for a computation its success and each failure its type allows.
 */
const endsOf = (
  project: Project,
  source: ContractSource,
  proof: Lowered,
  search: Lowered,
): Array<{ readonly value: string; readonly onProof: Bool; readonly onSearch: Bool }> => {
  if (source.kind === "computation")
    return outcomesOf(project, proof).map(([value, goal]) => ({ value, onProof: goal(proof), onSearch: goal(search) }))
  const checker = project.checker
  const returns = checker.getReturnTypeOfSignature(checker.getSignatureFromDeclaration(proof.fn)!)
  const members = returns.isUnion() ? returns.types : [returns]
  if (source.kind !== "function") return []
  const str = (side: Lowered, value: string): Val => ({ kind: "str", term: jsString(side.u.z3, value) })
  if (proof.result.kind === "str") {
    const is = (side: Lowered, value: string) => strictEq(side.u, side.result, str(side, value), side.fn)
    return members
      .filter((t) => t.isStringLiteral())
      .map((t) => ({ value: t.value, onProof: is(proof, t.value), onSearch: is(search, t.value) }))
  }
  // A union of records told apart by a field of string literals (`type`, `kind`, `do`): each of its values.
  if (proof.result.kind !== "record" || members.length < 2) return []
  const literalOf = (m: ts.Type, name: string): string | undefined => {
    const p = checker.getPropertyOfType(m, name)
    const t = p === undefined ? undefined : checker.getTypeOfSymbol(p)
    return t?.isStringLiteral() ? t.value : undefined
  }
  const tag = checker.getPropertiesOfType(members[0]!).find((p) => members.every((m) => literalOf(m, p.name) !== undefined))?.name
  if (tag === undefined) return []
  const values = [...new Set(members.map((m) => literalOf(m, tag)!))]
  const is = (side: Lowered, value: string) => strictEq(side.u, member(side.L, side.result, tag, side.fn), str(side, value), side.fn)
  return values.map((value) => ({ value: `${tag}: ${JSON.stringify(value)}`, onProof: is(proof, value), onSearch: is(search, value) }))
}

/**
 * Decides the obligations, the proof code's and each division's: each proved on the proof side, or broken on the search
 * side by a real input.
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
  ledger?: Ledger,
): Promise<{ readonly obligations: Array<ObligationResult>; readonly unanswered: ReadonlyArray<Unanswered> }> => {
  const on = (side: Side): Ask | undefined => (ledger === undefined ? undefined : { ledger, question: "obligation", side })
  const keys = [...new Set([...proof.L.obligations, ...search.L.obligations].map((o) => o.key))]
  const broken = (side: Lowered, key: string): Bool | undefined => {
    const os = side.L.obligations.filter((o) => o.key === key)
    return os.length === 0 ? undefined : z3.Or(...os.map((o) => z3.And(o.cond, z3.Not(o.goal), ...side.L.hints.slice(0, o.hints))))
  }
  /**
   * The obligation `key` failing on the search side as the first of the proof code to fail on that run: every obligation
   * met before it held. A loop's `kept` is proved from any state its invariants allow; a run on which they all held up to
   * here, and this one fails, breaks that step, where a run that failed an earlier one need not.
   */
  const firstToFail = (key: string): Bool | undefined => {
    const os = search.L.obligations
    const each = os.flatMap((o, k) =>
      o.key !== key ? [] : [z3.And(o.cond, z3.Not(o.goal), ...os.slice(0, k).map((p) => z3.Implies(p.cond, p.goal)))],
    )
    return each.length === 0 ? undefined : z3.Or(...each)
  }
  const out: Array<ObligationResult> = []
  for (const key of keys) {
    const o = [...proof.L.obligations, ...search.L.obligations].find((x) => x.key === key)!
    const head = { kind: o.kind, text: o.text, at: o.at, phase: o.phase, ...(o.guessed === undefined ? {} : { guessed: o.guessed }) }
    const onProof = broken(proof, key)
    const proved = onProof === undefined ? undefined : await solve(proof, [proof.pre, onProof], opts, [], on("proof"))
    if (proved?.status === "unsat" && proof.u.truncated === undefined) {
      out.push({ ...head, status: "proved" })
      continue
    }
    if (proved?.status === "sat" && !proof.u.abstracted) {
      out.push({ ...head, status: "counterexample", ...shown(proved.witness) })
      continue
    }
    const onSearch = broken(search, key)
    const found = onSearch === undefined ? undefined : await solve(search, [search.pre, onSearch], opts, [], on("search"))
    if (found?.status === "sat") out.push({ ...head, status: "counterexample", ...shown(found.witness) })
    else if (found?.status === "unsat")
      out.push({
        ...head,
        status: "bounded",
        reason:
          o.phase === "kept"
            ? `true of every input with arrays of at most ${bound} elements, and not proved kept by an iteration from any state it allows: strengthen it with what else the loop keeps`
            : `not proved (${proved === undefined ? "the proof side does not meet it" : proved.status === "unsat" ? proof.u.truncated : why(proved, proof.u)}); no counterexample with arrays of at most ${bound} elements`,
      })
    else out.push({ ...head, status: "unknown", reason: found?.status === "unknown" ? found.reason : "not met on either side" })
    opts.progress?.(`${o.kind} ${o.at}: ${out.at(-1)!.status}`)
  }
  // Every proof is checked against the search side, all in one query: a run on which one of them is the first to fail.
  const provedKeys = keys.filter((_, k) => out[k]?.status === "proved")
  const { found: disagreements, unsettled } = await contradicted(
    search,
    provedKeys.flatMap((key) => {
      const f = firstToFail(key)
      return f === undefined ? [] : [{ key, broken: f }]
    }),
    opts,
    [],
    ledger,
  )
  for (const [key, args] of disagreements) {
    const k = keys.indexOf(key)
    out[k] = { ...out[k]!, status: "inconsistent", reason: DISAGREE, ...(args === undefined ? {} : { args }) }
  }
  // One query asks of them all: where it ends without an answer, every proof it was asked of is unchecked alike.
  const ends = [...new Set(unsettled.values())]
  const unanswered: Array<Unanswered> = ends.map((end) =>
    unansweredOf("cross-check", end, "search", `the proofs of ${[...unsettled].filter(([, e]) => e === end).length} of the obligations`),
  )
  const lemmas = new Map([...proof.L.lemmas, ...search.L.lemmas])
  for (const [key, lem] of lemmas) {
    const { v, kept } = await verifyOrKept(z3, project, lem.file, lem.name, opts)
    // A lemma's own queries are this contract's, as an obligation, and so is what it left without an answer; a verdict
    // kept from an earlier run asked nothing now, and its times are not this run's.
    if (!kept) ledger?.addAll([...(v.asked ?? []), ...v.laws.flatMap((l) => l.asked ?? [])], "obligation")
    for (const n of [...(v.unanswered ?? []), ...v.laws.flatMap((l) => l.unanswered ?? [])])
      unanswered.push({ ...n, reason: `lemma ${lem.name}: ${n.reason}` })
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
  return { obligations: out, unanswered }
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
      ...(a.spec === undefined ? {} : { spec: a.spec }),
    }
  })

/**
 * The ends a computation can come to, as cover goals: success, and a failure for each `_tag` its declared failure
 * type names (one undistinguished failure when it declares none).
 */
const outcomesOf = (project: Project, side: Lowered): Array<readonly [string, (s: Lowered) => Bool]> => {
  const field = (v: Val, n: string): Val | undefined => (v.kind === "record" ? v.field(n) : undefined)
  const tagIs = (v: Val | undefined, t: string, z3: Ctx): Bool => (v?.kind === "str" ? v.term.eq(jsString(z3, t)) : z3.Bool.val(false))
  const sig = project.checker.getTypeAtLocation(side.source.target).getCallSignatures()[0]
  const returns = sig?.getReturnType()
  const op = returns === undefined ? undefined : side.L.adapters.map((a) => a.operation?.(side.L, returns)).find((x) => x !== undefined)
  const failures = op?.failure === undefined ? [] : op.failure.isUnion() ? op.failure.types : [op.failure]
  const tags = failures.flatMap((f) => {
    const t = project.checker.getPropertyOfType(f, "_tag")
    const tt = t === undefined ? undefined : project.checker.getTypeOfSymbol(t)
    return tt?.isStringLiteral() ? [tt.value] : []
  })
  const goals: Array<readonly [string, (s: Lowered) => Bool]> = [["Success", (s) => tagIs(field(s.result, "_tag"), "Success", s.u.z3)]]
  if (tags.length === 0) goals.push(["Failure", (s) => tagIs(field(s.result, "_tag"), "Failure", s.u.z3)])
  for (const t of tags)
    goals.push([
      `Failure ${t}`,
      (s) =>
        s.u.z3.And(
          tagIs(field(s.result, "_tag"), "Failure", s.u.z3),
          tagIs(field(field(s.result, "error") ?? { kind: "nullish", which: "undefined" }, "_tag"), t, s.u.z3),
        ),
    ])
  if (side.u.dies) goals.push(["Die", (s) => tagIs(field(s.result, "_tag"), "Die", s.u.z3)])
  return goals
}

const why = (o: Outcome, u: Universe): string =>
  o.status === "unknown"
    ? o.reason
    : o.status === "sat"
      ? u.approximations.size > 0
        ? [...u.approximations].join("; ")
        : "the proof side's model rests on an approximation"
      : "proved"

type Witness = {
  readonly args?: ReadonlyArray<unknown>
  readonly world?: Readonly<Record<string, unknown>>
  readonly abstract?: ReadonlyArray<string>
  readonly reason?: string
}

type Outcome =
  | { readonly status: "sat"; readonly witness: Witness }
  | { readonly status: "unsat" }
  | { readonly status: "unknown"; readonly reason: string; readonly end: End }

/** Where a query's time is recorded: the ledger of the law or contract it serves, the question and the side. */
export interface Ask {
  readonly ledger: Ledger
  readonly question: Question
  readonly side: Side
}

/**
 * `solver.check`, timed, and recorded in `ask`'s ledger by how it ended. The time is only recorded: no verdict reads it,
 * but for an end told apart by it (`endOf`).
 */
const checked = async (
  solver: { check(...assumptions: Array<Bool>): Promise<"sat" | "unsat" | "unknown">; reasonUnknown(): string },
  ask: Ask | undefined,
  ...assumptions: Array<Bool>
): Promise<{ readonly status: "sat" | "unsat" | "unknown"; readonly end: End; readonly reason: string }> => {
  const started = performance.now()
  const status = await solver.check(...assumptions)
  const ms = performance.now() - started
  const reason = status === "unknown" ? solver.reasonUnknown() : ""
  const end = endOf(status, reason, ms)
  ask?.ledger.add(ask.question, ask.side, end, ms)
  return { status, end, reason }
}

/**
 * The work a query may do by default: above the most any query of the suite and of the case study needs to end, 9.7
 * million, by half again. Measured on 5,672 queries; one that does not end, and counts its work, stops at the same
 * step on every run.
 */
export const WORK = 15_000_000

/** A tenth of `work`, a whole number of steps and at least one: Z3 takes no other as a limit. */
const tenthOf = (work: number): number => Math.max(1, Math.floor(work / 10))

const limited = (solver: { set(key: string, value: number): void }, work: number): void => {
  solver.set("rlimit", work)
  solver.set("timeout", STUCK_MS)
}

/**
 * Checks a side's assumptions with `goals`; on `sat`, reads the arguments back, preferring short arrays. Each query's
 * time goes to `ask`'s ledger.
 */
export const solve = async (
  side: Lowered,
  goals: ReadonlyArray<Bool>,
  opts: Options = {},
  hints: ReadonlyArray<Bool> = side.L.hints,
  ask?: Ask,
): Promise<Outcome> => {
  const { u } = side
  const z3 = u.z3
  const run = async (extra: ReadonlyArray<Bool>) => {
    const solver = new z3.Solver()
    limited(solver, opts.work ?? WORK)
    vectorsBy(u, solver)
    for (const a of [...u.assumptions, ...hints, ...goals, ...extra]) solver.add(a)
    const { status, end, reason } = await checked(solver, ask)
    return { status, end, reason, solver }
  }
  // Each solver is let go once read: one that ran out of work holds much of the memory Z3 may use, until collected.
  const first = await run([])
  if (first.status === "unsat") {
    first.solver.release()
    return { status: "unsat" }
  }
  if (first.status === "unknown") {
    const reason = endWords(first.end, first.reason)
    first.solver.release()
    return { status: "unknown", reason, end: first.end }
  }
  // A model may pick a huge array or dictionary; ask again with short ones, which narrows the same formula. A `Map`'s
  // or a `Set`'s count is left as it is: bounding it can cost the query its time, and its model is read back whole.
  const counts = new Set(["#len", "#own"])
  const short = [...u.leaves.values()]
    .filter((l) => l.arity === 0 && counts.has(l.segments.at(-1) ?? ""))
    .map((l) => (l.constant as Arith).le(8))
  const small = short.length > 0 && u.bound === undefined ? await run(short) : undefined
  const model = small?.status === "sat" ? small.solver.model() : first.solver.model()
  const found = witness(side, model)
  first.solver.release()
  small?.solver.release()
  return { status: "sat", witness: found }
}

/** An outcome as it ended: its value on a success, its error on a failure, not both (the model holds both). */
const ended = (x: unknown): unknown => {
  if (x === null || typeof x !== "object" || !("_tag" in x)) return x
  const { value, error, ...rest } = x as { readonly _tag: unknown; readonly value?: unknown; readonly error?: unknown }
  if (rest._tag === "Success") return "value" in x ? { ...rest, value } : rest
  if (rest._tag === "Failure") return "error" in x ? { ...rest, error } : rest
  return x
}

/** The operation calls a computation's run made, by root: the calls its trace holds in `model`. Undefined for a function. */
const madeCalls = (side: Lowered, model: Model): ReadonlySet<string> | undefined => {
  const { trace, u } = side
  if (trace === undefined || trace.kind !== "array") return undefined
  const length = model.eval(trace.length, true)
  if (!u.z3.isIntVal(length)) return undefined
  const made = new Set<string>()
  for (let i = 0; i < Number(length.value()); i++) {
    const call = trace.elem(u.z3.Int.val(i))
    const root = call.kind === "record" ? call.field("~root") : undefined
    if (root?.kind !== "str") continue
    const name = model.eval(root.term, true)
    if (u.z3.isString(name)) made.add(fromZ3String(name.asString()))
  }
  return made
}

/** Whether a run read root `r`: on the branch it was read on, when one was kept. */
const reached = (side: Lowered, model: Model, r: string): boolean => {
  const on = side.u.reached.get(r)
  return on === undefined || side.u.z3.isTrue(model.eval(on, true))
}

const witness = (side: Lowered, model: Model): Witness => {
  try {
    const made = madeCalls(side, model)
    const roots = new Set(
      [...side.u.leaves.values()]
        .map((l) => l.segments[0]!)
        .filter((r) => side.u.shown.has(r) && (made === undefined || !side.u.calls.has(r) || made.has(r)) && reached(side, model, r)),
    )
    // A declared function's result inside a quantifier is one per element: a function of the index, not a value to show.
    for (const l of side.u.leaves.values()) if (l.arity > l.segments.filter((s) => s === "[]").length) roots.delete(l.segments[0]!)
    const world = Object.fromEntries([...roots].sort().map((r) => [r, ended(fromModel(side.u, model, r))]))
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
    limited(solver, 2 * WORK)
    vectorsBy(u, solver)
    for (const a of [...u.assumptions, ...pins, z3.Not(strictEq(u, result, valueOf(u, want), side.fn))]) solver.add(a)
    const status = await solver.check()
    solver.release()
    if (status !== "unsat") out.push({ args, expected: want, status })
  }
  return out
}

const valueOf = (u: Universe, want: unknown): Val => {
  if (want === null || want === undefined) return { kind: "nullish", which: want === null ? "null" : "undefined" }
  if (typeof want === "number") return num(u.z3, want)
  const term = literal(u, want) as never
  if (typeof want === "string") return { kind: "str", term }
  if (typeof want === "boolean") return { kind: "bool", term }
  if (typeof want === "bigint") return { kind: "int", origin: "bigint", term }
  throw new Error(`cannot compare a result of type ${typeof want}`)
}

/**
 * A query that holds 32-bit vectors made from integers (`|`, `&`, `^` on numbers) is solved by integer blasting, which
 * decides `x & (x - 1)` in milliseconds where bit-blasting beside the integers runs out of time.
 */
const vectorsBy = (u: Universe, solver: { set(key: string, value: number): void }): void => {
  if (u.vectors) solver.set("smt.bv.solver", 2)
}

/**
 * The contexts a verification runs in (`ownContext`): no finalizer frees what they hold, which goes with the context,
 * all at once, when the verification ends. z3-solver frees each term when JavaScript collects the object that holds
 * it, and that moment is not the same on every run, nor always between two queries (a collection's finalizers run as
 * soon as the main thread waits, and it waits while Z3 solves on a thread of its own). A term freed hands its number to
 * the next one made, and those numbers order the solver's search: a law decided near its work limit was proved on one
 * run and not on the next (`docs/design-2026-11-03-maps.md`, *Verdicts*).
 */
const owned = new WeakSet()
/** Set while `openZ3`'s contexts make one for a verification: what is made then, the context first, is its own. */
let making = false
const Registry = globalThis.FinalizationRegistry
/** How many `openZ3` are starting z3-solver: the last to finish puts JavaScript's registry back. */
let starting = 0

/** z3-solver's finalizers, but for an object of a context a verification owns, which that context frees. */
class Finalizers<T> {
  readonly #registry: FinalizationRegistry<T>
  constructor(free: (held: T) => void) {
    this.#registry = new Registry<T>(free)
  }
  register(target: WeakKey, held: T, token?: WeakKey): void {
    if (making || owned.has((target as { readonly ctx?: object }).ctx ?? target)) return
    this.#registry.register(target, held, token)
  }
  unregister(token: WeakKey): boolean {
    return this.#registry.unregister(token)
  }
}

/** For a context `openZ3` opened, how to make one beside it that a verification owns, and how to delete it. */
const owning = new WeakMap<Ctx, () => { readonly ctx: Ctx; readonly free: () => void }>()

/** Runs `f` in a context of its own, made beside `z3` and deleted after; a context `openZ3` did not open, as it is. */
const ownContext = async <A>(z3: Ctx, f: (own: Ctx) => Promise<A>): Promise<A> => {
  const make = owning.get(z3)
  if (make === undefined) return f(z3)
  const { ctx, free } = make()
  try {
    return await f(ctx)
  } finally {
    free()
  }
}

/**
 * A Z3 context to verify many contracts with, and how to let it go: a test opens one before its cases and closes it
 * after. `verify` runs each contract in a context of its own beside it (`ownContext`); `lowerSide` and what reads its
 * side use this one, whose terms are freed as z3-solver frees them.
 */
export const openZ3 = async (): Promise<{ readonly z3: Ctx; readonly close: () => Promise<void> }> => {
  // z3-solver makes its finalizers once, as it starts: these.
  if (starting++ === 0) (globalThis as { FinalizationRegistry: unknown }).FinalizationRegistry = Finalizers
  const api = await init().finally(() => {
    if (--starting === 0) (globalThis as { FinalizationRegistry: unknown }).FinalizationRegistry = Registry
  })
  // A character of Z3's strings is 16 bits, a UTF-16 code unit, so a string is JavaScript's (`jsString`).
  api.setParam("encoding", "bmp")
  const z3 = api.Context("main")
  owning.set(z3, () => {
    making = true
    let ctx: Ctx
    try {
      ctx = api.Context("main")
    } finally {
      making = false
    }
    owned.add(ctx)
    return { ctx, free: () => api.Z3.del_context(ctx.ptr) }
  })
  return { z3, close: async () => await killThreads(api.em) }
}

/** Runs `f` with a fresh Z3 context and frees Z3's worker threads after, so the process can exit. */
export const withZ3 = async <A>(f: (z3: Ctx) => Promise<A>): Promise<A> => {
  const { z3, close } = await openZ3()
  try {
    return await f(z3)
  } finally {
    await close()
  }
}
