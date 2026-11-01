// A string's own methods, on its UTF-16 code units: `startsWith`, `endsWith`, `includes`, `indexOf`, `charAt`, `at`, an
// element `s[i]` and `slice`, each as JavaScript gives it out of range. `test/methods.test.ts` asks each, runs each, and
// plants a bug in each.
import { contract } from "../src/contract.ts"

/** `s` without the prefix `p`, where it starts with it. */
export function stripped(s: string, p: string): string {
  return s.startsWith(p) ? s.slice(p.length) : s
}
export const strippedOfPrefix = contract(stripped, {
  ensures: {
    rebuilt: ({ input: [s, p], output }) => !s.startsWith(p) || p + output === s,
    keptOtherwise: ({ input: [s, p], output }) => s.startsWith(p) || output === s,
    noLonger: ({ input: [s], output }) => output.length <= s.length,
  },
})

/** A name's first code unit, `""` for an empty name. */
export function initial(name: string): string {
  return name.charAt(0)
}
export const firstUnit = contract(initial, {
  ensures: {
    oneUnit: ({ input: [name], output }) => (name === "" ? output === "" : output.length === 1),
    itsFirst: ({ input: [name], output }) => name.startsWith(output),
    likeIndexing: ({ input: [name], output }) => output === (name[0] ?? ""),
  },
})

/** The last code unit, `undefined` for `""`. */
export function last(s: string): string | undefined {
  return s.at(-1)
}
export const lastUnit = contract(last, {
  ensures: {
    missingWhenEmpty: ({ input: [s], output }) => (output === undefined) === (s === ""),
    endsWithIt: ({ input: [s], output }) => output === undefined || s.endsWith(output),
    oneUnit: ({ output }) => output === undefined || output.length === 1,
  },
})

/** Whether `email` has an `@` with something on each side of it. */
export function plausible(email: string): boolean {
  return email.includes("@") && !email.startsWith("@") && !email.endsWith("@")
}
export const plausibleEmail = contract(plausible, {
  ensures: { threeAtLeast: ({ input: [email], output }) => !output || email.length >= 3 },
})

/** Where `t` first is in `s`, -1 where it is not. */
export function position(s: string, t: string): number {
  return s.indexOf(t)
}
export const firstPosition = contract(position, {
  ensures: {
    foundIffIncluded: ({ input: [s, t], output }) => output >= 0 === s.includes(t),
    emptyAtStart: ({ input: [, t], output }) => t !== "" || output === 0,
    inside: ({ input: [s], output }) => output <= s.length,
  },
})
