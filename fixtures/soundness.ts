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
