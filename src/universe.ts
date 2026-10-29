// One verification's Z3 context: its leaves (the unknowns), the assumptions the
// model of JavaScript adds about them, and the quantifier scopes they live in.
//
// A leaf is named by its path, `state.attempts[].turn!$` for "the value of the
// `turn` of an element of `state.attempts`". A leaf under N array elements is an
// N-ary function of the element indices, so one name stands for every element.
import type { Arith, Bool, Expr, FuncDecl } from "z3-solver"
import type { Ctx } from "./value.ts"

/** `num` is a `number`'s real value; its class is an `int` leaf beside it, at `~cls`. */
export type LeafSort = "int" | "num" | "bool" | "str"

export interface Leaf {
  readonly key: string
  readonly segments: ReadonlyArray<string>
  readonly sort: LeafSort
  readonly origin: "bigint" | "count" | undefined
  readonly arity: number
  readonly decl: FuncDecl<"main"> | undefined
  readonly constant: Expr<"main"> | undefined
}

interface Scope {
  /** The quantified index this scope binds, or none for the global scope. */
  readonly bound: Arith<"main"> | undefined
  readonly items: Array<Bool<"main">>
}

/** The largest length a JavaScript array can have. */
export const MAX_LENGTH = 4294967295n

export class Universe {
  readonly leaves = new Map<string, Leaf>()
  /** What the model assumes and why, for a report: each kind of assumption once. */
  readonly notes = new Set<string>()
  /**
   * Set when the lowering over-approximated: the formula admits every real run
   * and some that are not. Its `unsat` is still a proof; its models are not
   * evidence. Never set on the search side, which is exact.
   */
  abstracted = false
  /**
   * The declared functions whose results are unknowns, constrained only by their declared laws. A model that leans on
   * one is a counterexample of the code with those functions so, not necessarily of the real code: it is reported as
   * abstract.
   */
  readonly opaqueCalls = new Set<string>()
  private readonly scopes: Array<Scope> = [{ bound: undefined, items: [] }]
  private counter = 0

  readonly z3: Ctx
  /**
   * For a search, not a proof: every array holds at most this many elements, and
   * a quantifier over one is written out element by element. A model found so is
   * a model of the unbounded formula too; finding none proves nothing past it.
   */
  readonly bound: number | undefined

  constructor(z3: Ctx, bound?: number) {
    this.z3 = z3
    this.bound = bound
  }

  /** The assumptions of the global scope: true of every leaf, wherever it was first read. */
  get assumptions(): ReadonlyArray<Bool<"main">> {
    return this.scopes[0]!.items
  }

  /** How many quantifier scopes are open. */
  get depth(): number {
    return this.scopes.length - 1
  }

  fresh(prefix: string): string {
    return `${prefix}!${this.counter++}`
  }

  /**
   * Adds a fact about leaves at `indices`. It lands in the innermost scope that
   * binds one of them (a fact about element `i` of a quantifier is that
   * quantifier's), else in the global scope.
   */
  assume(fact: Bool<"main">, indices: ReadonlyArray<Arith<"main">> = []): void {
    const tokens = new Set(indices.flatMap((i) => i.sexpr().split(/[\s()]+/)))
    for (let s = this.scopes.length - 1; s > 0; s--) {
      if (tokens.has(this.scopes[s]!.bound!.sexpr())) {
        this.scopes[s]!.items.push(fact)
        return
      }
    }
    this.scopes[0]!.items.push(fact)
  }

  /** The indices the open quantifier scopes bind, outermost first. */
  openBounds(): Array<Arith<"main">> {
    return this.scopes.slice(1).map((s) => s.bound!)
  }

  /** Runs `f` in a scope binding `bound`; returns its result and the facts that scope collected. */
  within<A>(bound: Arith<"main">, f: () => A): { readonly result: A; readonly facts: ReadonlyArray<Bool<"main">> } {
    const scope: Scope = { bound, items: [] }
    this.scopes.push(scope)
    try {
      return { result: f(), facts: scope.items }
    } finally {
      this.scopes.pop()
    }
  }

  /** The term of the leaf at `segments`, applied to `indices`; declared on first use. */
  leaf(
    segments: ReadonlyArray<string>,
    sort: LeafSort,
    indices: ReadonlyArray<Arith<"main">>,
    origin?: "bigint" | "count",
  ): Expr<"main"> {
    const key = segments.join("")
    let leaf = this.leaves.get(key)
    if (leaf === undefined) {
      const z3 = this.z3
      const s =
        sort === "int" ? z3.Int.sort() : sort === "num" ? z3.Real.sort() : sort === "bool" ? z3.Bool.sort() : z3.String.sort()
      const arity = indices.length
      leaf = {
        key,
        segments,
        sort,
        origin,
        arity,
        decl: arity === 0 ? undefined : z3.Function.declare(key, ...Array.from({ length: arity }, () => z3.Int.sort()), s),
        constant: arity === 0 ? z3.Const(key, s) : undefined,
      }
      this.leaves.set(key, leaf)
    }
    if (leaf.arity !== indices.length) throw new Error(`leaf ${key} read with ${indices.length} indices, declared with ${leaf.arity}`)
    return leaf.constant ?? leaf.decl!.call(...indices)
  }
}
