// Two wrong verdicts the verifier once gave, kept so it never gives them
// again; `test/soundness.test.ts` asks each.
import { computation, contract } from "../src/contract.ts"

/** An operation that returns a plain promise, which may reject with anything. */
interface Counter {
  readonly next: () => Promise<bigint>
}
export const readNext = async (counter: Counter): Promise<bigint> => await counter.next()
/** Once proved: a plain `Promise` was read as one that never rejects. */
export const alwaysSucceeds = computation<{ counter: Counter }>()(readNext, {
  ensures: { succeeds: (_counter, out) => out._tag === "Success" },
})

/** The number itself. */
export const same = (x: number): number => x
/**
 * True of every double: none lies between 1 and the next double up. Once refuted with `1`, a model of the proof side,
 * where a number is any real, taken for an input.
 */
export const noneBetween = contract(same, {
  ensures: { notBetweenTwoDoubles: (_x, r) => !(1 < r && r < 1.0000000000000002) },
})

/** A copy of `a` with 1n set at index 3. */
export function grow(a: ReadonlyArray<bigint>): Array<bigint> {
  const b = [...a]
  b[3] = 1n
  return b
}
/** Once proved: a write past the end was read as keeping the length, where JavaScript grows the array. */
export const growKeepsLength = contract(grow, { ensures: { sameLength: (a, out) => out.length === a.length } })

/** The second element's `v`, when there is one. */
export function second(a: ReadonlyArray<{ readonly v: bigint }>): bigint | undefined {
  const x = a[1]
  return x === undefined ? undefined : x.v
}
/** Once proved: an element borrowed at a literal index was read as there, past the end too. */
export const secondAlwaysThere = contract(second, { ensures: { always: (_a, out) => out !== undefined } })
