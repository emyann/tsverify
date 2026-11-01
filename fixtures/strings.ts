// Strings as JavaScript has them, a sequence of UTF-16 code units: an emoji is
// two, an accented letter one. `test/strings.test.ts` asks each.
import { contract } from "../src/contract.ts"

export const units = (s: string): number => s.length

export const unitsAsJavaScriptCounts = contract(units, {
  ensures: {
    emojiIsTwo: ({ input: [s], output }) => s !== "😀" || output === 2,
    accentIsOne: ({ input: [s], output }) => s !== "é" || output === 1,
    neverNegative: ({ output }) => output >= 0,
  },
})

export const unitsMiscounted = contract(units, { ensures: { emojiIsOne: ({ input: [s], output }) => s !== "😀" || output === 1 } })
