// Strings as JavaScript has them, a sequence of UTF-16 code units: an emoji is
// two, an accented letter one. `test/strings.test.ts` asks each.
import { contract } from "../src/contract.ts"

export const units = (s: string): number => s.length

export const unitsAsJavaScriptCounts = contract(units, {
  ensures: {
    emojiIsTwo: (s, n) => s !== "😀" || n === 2,
    accentIsOne: (s, n) => s !== "é" || n === 1,
    neverNegative: (_s, n) => n >= 0,
  },
})

export const unitsMiscounted = contract(units, { ensures: { emojiIsOne: (s, n) => s !== "😀" || n === 1 } })
