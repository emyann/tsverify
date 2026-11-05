// Identity on arrays, and a law over the result's length: kept at a bound of 2, broken at 3.
import { contract } from "@emyann/tsverify"

export function same(xs: ReadonlyArray<number>): ReadonlyArray<number> {
  return xs
}

export const short = contract(same, { ensures: { underThree: ({ output }) => output.length < 3 } })
