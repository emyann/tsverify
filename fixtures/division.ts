// Bigint `/` and `%` as JavaScript computes them: the quotient truncated toward
// zero, the remainder with the dividend's sign. A division by 0n throws, so each
// one's divisor is proved other than 0n on the branch where it runs (`?:`, `&&`,
// `||`, `??`, `if`, a field read later, a loop, a step that succeeded), or the
// input that makes it 0n is shown; a law is judged on the runs that return.
// `test/division.test.ts` asks each.
import { computation, contract, type Rejects } from "../src/contract.ts"

/** JavaScript's own, for the lowering to be checked against: 0n where it would throw. */
export const quotient = contract((a: bigint, b: bigint): bigint => (b === 0n ? 0n : a / b), {
  ensures: { towardZero: (a, b, q) => b === 0n || ((a >= 0n) === (b > 0n) ? q >= 0n : q <= 0n) },
})
export const remainder = contract((a: bigint, b: bigint): bigint => (b === 0n ? 0n : a % b), {
  ensures: { dividendsSign: (a, _b, r) => (a >= 0n ? r >= 0n : r <= 0n) },
})

/** Not more than `a`, for an `a` that is not negative: a quotient's size is at most the dividend's. */
const atMostA = (a: bigint, _b: bigint, q: bigint) => a < 0n || q <= a

export const unguarded = contract((a: bigint, b: bigint): bigint => a / b, { ensures: { atMostA } })
export const byConditional = contract((a: bigint, b: bigint): bigint => (b === 0n ? 0n : a / b), { ensures: { atMostA } })
export const byAnd = contract((a: bigint, b: bigint): boolean => b !== 0n && a / b > 1n, {
  ensures: { onlyWithADivisor: (_a, b, big) => !big || b !== 0n },
})
export const byOr = contract((a: bigint, b: bigint): boolean => b === 0n || a / b > 1n, {
  ensures: { trueWithoutADivisor: (_a, b, big) => b !== 0n || big },
})
export const byNullish = contract((cached: bigint | undefined, b: bigint): bigint => cached ?? 10n / b, {
  requires: (cached, b) => cached !== undefined || b !== 0n,
  ensures: { cachedFirst: (cached, _b, out) => cached === undefined || out === cached },
})
export function perShare(a: bigint, b: bigint): bigint {
  if (b === 0n) return 0n
  return a / b
}
export const byIf = contract(perShare, { ensures: { atMostA } })
export const byField = contract((a: bigint, b: bigint) => ({ q: b === 0n ? 0n : a / b, b }), {
  ensures: { atMostA: (a, _b, out) => a < 0n || out.q <= a },
})
export function shares(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) if (x !== 0n) total += 100n / x
  return total
}
export const byLoop = contract(shares, { ensures: { zeroWhenEmpty: (xs, total) => xs.length > 0 || total === 0n } })
export function dividedIfAble(a: bigint, b: bigint): bigint {
  let q = a
  if (b !== 0n) q /= b
  return q
}
export const byCompound = contract(dividedIfAble, { ensures: { sameWithoutADivisor: (a, b, q) => b !== 0n || q === a } })

export const lawGuarded = contract((a: bigint, _b: bigint): bigint => a, { ensures: { same: (a, b, out) => b === 0n || out / b === a / b } })
export const lawUnguarded = contract((a: bigint, _b: bigint): bigint => a, { ensures: { same: (a, b, out) => out / b === a / b } })

export const inEvery = contract((xs: ReadonlyArray<bigint>): boolean => xs.every((x) => 10n / x > 0n), { ensures: { holds: () => true } })

export interface Counter {
  readonly count: () => Rejects<bigint, Error>
}
type Ops = { counter: Counter }
export const perItemUnguarded = computation<Ops, Error>()(
  async (counter: Counter, total: bigint): Promise<bigint> => total / (await counter.count()),
  { ensures: { readsOnce: (_c, _t, _out, calls) => calls.length === 1 } },
)
export const perItemGuarded = computation<Ops, Error>()(
  async (counter: Counter, total: bigint): Promise<bigint> => {
    const n = await counter.count()
    return n === 0n ? 0n : total / n
  },
  { ensures: { readsOnce: (_c, _t, _out, calls) => calls.length === 1 } },
)
