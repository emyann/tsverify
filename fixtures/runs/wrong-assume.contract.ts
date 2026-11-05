// A declaration whose law the real function breaks: a proof leans on it, a run calls the real function.
import { assume, contract } from "@emyann/tsverify"

/** Declared never negative; it counts each "a" down. */
export function score(word: string): number {
  let n = 0
  for (const c of word) if (c === "a") n--
  return n
}
export const scoreIsPure = assume(score, {
  pure: true,
  ensures: { nonNegative: ({ output }) => output >= 0 },
})

export const scored = contract((word: string) => score(word), { ensures: { nonNegative: ({ output }) => output >= 0 } })
