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
    rebuilt: (s, p, out) => !s.startsWith(p) || p + out === s,
    keptOtherwise: (s, p, out) => s.startsWith(p) || out === s,
    noLonger: (s, _p, out) => out.length <= s.length,
  },
})

/** A name's first code unit, `""` for an empty name. */
export function initial(name: string): string {
  return name.charAt(0)
}
export const firstUnit = contract(initial, {
  ensures: {
    oneUnit: (name, out) => (name === "" ? out === "" : out.length === 1),
    itsFirst: (name, out) => name.startsWith(out),
    likeIndexing: (name, out) => out === (name[0] ?? ""),
  },
})

/** The last code unit, `undefined` for `""`. */
export function last(s: string): string | undefined {
  return s.at(-1)
}
export const lastUnit = contract(last, {
  ensures: {
    missingWhenEmpty: (s, out) => (out === undefined) === (s === ""),
    endsWithIt: (s, out) => out === undefined || s.endsWith(out),
    oneUnit: (_s, out) => out === undefined || out.length === 1,
  },
})

/** Whether `email` has an `@` with something on each side of it. */
export function plausible(email: string): boolean {
  return email.includes("@") && !email.startsWith("@") && !email.endsWith("@")
}
export const plausibleEmail = contract(plausible, {
  ensures: { threeAtLeast: (email, out) => !out || email.length >= 3 },
})

/** Where `t` first is in `s`, -1 where it is not. */
export function position(s: string, t: string): number {
  return s.indexOf(t)
}
export const firstPosition = contract(position, {
  ensures: {
    foundIffIncluded: (s, t, out) => out >= 0 === s.includes(t),
    emptyAtStart: (_s, t, out) => t !== "" || out === 0,
    inside: (s, _t, out) => out <= s.length,
  },
})
