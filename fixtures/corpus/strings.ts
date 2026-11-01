// Strings: JavaScript's are UTF-16 code units, SMT-LIB's are code points; and the two answer differently out of range.
import { contract } from "../../src/contract.ts"
import type { Case } from "./cases.ts"

// str-prefix-suffix: a prefix and a suffix whose lengths add up are the whole string (a control).
export function splits(a: string, b: string, c: string): boolean {
  return a.startsWith(b) && a.endsWith(c) && a.length === b.length + c.length
}
export const prefixSuffix = contract(splits, {
  ensures: { whole: ({ input: [a, b, c], output }) => !output || a === b + c },
})
export function splitsAnyLength(a: string, b: string, c: string): boolean {
  return a.startsWith(b) && a.endsWith(c)
}
export const prefixSuffixAnyLength = contract(splitsAnyLength, {
  ensures: { whole: ({ input: [a, b, c], output }) => !output || a === b + c },
})

// str-length-code-units: `.length` counts UTF-16 code units; `[...s]` counts code points.
export function units(s: string): number {
  return s.length
}
export const lengthInUnits = contract(units, {
  ensures: {
    emojiIsTwo: ({ input: [s], output }) => s !== "😀" || output === 2,
    loneSurrogateIsOne: ({ input: [s], output }) => s !== "\uD83D" || output === 1,
  },
})
export const lengthAgainstCodePoints = contract(units, {
  ensures: {
    countsCodePoints: ({ input: [s], output }) => output === [...s].length,
    atMostTwiceTheCodePoints: ({ input: [s], output }) => output >= [...s].length && output <= 2 * [...s].length,
  },
})

// str-reverse: reversing by code units twice is the identity; by code points, it is not on a string not well formed.
const rev = (s: string): string => s.split("").reverse().join("")
const cprev = (s: string): string => [...s].reverse().join("")
export function revTwice(s: string): string {
  return rev(rev(s))
}
export const reversedByUnitsTwice = contract(revTwice, { ensures: { identity: ({ input: [s], output }) => output === s } })
export function cprevTwice(s: string): string {
  return cprev(cprev(s))
}
export const reversedByCodePointsTwice = contract(cprevTwice, { ensures: { identity: ({ input: [s], output }) => output === s } })

// zg-str-at-indexof: SMT-LIB's `str.at` is "" out of range, negative indices included; JavaScript's `at` counts from the end.
export function smtAt(s: string, i: number): string {
  return i >= 0 && i < s.length ? s.charAt(i) : ""
}
export const atAgainstSmt = contract(smtAt, {
  requires: ({ input: [, i] }) => Number.isInteger(i),
  ensures: {
    likeAt: ({ input: [s, i], output }) => output === (s.at(i) ?? ""),
    likeCharAt: ({ input: [s, i], output }) => output === s.charAt(i),
  },
})

const units1 = ["", "a", "ab", "abcd", "😀", "\uD83D", "\uDE00\uD83D", "a😀b", "😀😀"]
export const cases: Readonly<Record<string, Case>> = {
  prefixSuffix: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Strings#strprefixof-a-b-strsuffixof-a-b---prefix-and-suffix-checks",
    laws: { whole: "valid" },
    samples: [["ab", "a", "b"], ["aa", "a", "a"], ["😀", "\uD83D", "\uDE00"], ["abc", "", "abc"], ["a", "a", "a"]],
  },
  prefixSuffixAnyLength: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Strings#strprefixof-a-b-strsuffixof-a-b---prefix-and-suffix-checks",
    laws: { whole: "invalid" },
    samples: [],
    witnesses: { whole: ["a", "a", "a"] },
  },
  lengthInUnits: {
    source: "https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String/length",
    laws: { emojiIsTwo: "valid", loneSurrogateIsOne: "valid" },
    samples: units1.map((s) => [s]),
  },
  lengthAgainstCodePoints: {
    source: "https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String/length",
    laws: { countsCodePoints: ["invalid", "refused"], atMostTwiceTheCodePoints: ["valid", "refused"] },
    samples: units1.map((s) => [s]),
    witnesses: { countsCodePoints: ["😀"] },
  },
  reversedByUnitsTwice: {
    source: "https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String#utf-16_characters_unicode_code_points_and_grapheme_clusters",
    laws: { identity: ["valid", "refused"] },
    samples: units1.map((s) => [s]),
  },
  reversedByCodePointsTwice: {
    source: "https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String#utf-16_characters_unicode_code_points_and_grapheme_clusters",
    laws: { identity: ["invalid", "refused"] },
    samples: [],
    witnesses: { identity: ["\uDE00\uD83D"] },
  },
  atAgainstSmt: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Strings#strat-s-offset---character-substring-at-offset",
    laws: { likeAt: "invalid", likeCharAt: "valid" },
    samples: units1.flatMap((s) => [-2, -1, 0, 1, 3, 4, 10].map((i) => [s, i])),
    witnesses: { likeAt: ["abcd", -1] },
  },
}
