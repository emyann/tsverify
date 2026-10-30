// A string's methods (fixtures/methods.ts): every law proved; the laws hold when the functions run, on strings with an
// emoji, a lone surrogate and nothing at all; and a bug planted in each is caught.
import * as fixture from "../fixtures/methods.ts"
import { checkFixture } from "./fixture-plants.ts"

const pairs = [
  ["", ""],
  ["ab", "a"],
  ["ab", "b"],
  ["abc", "abc"],
  ["a", "ab"],
  ["😀x", "\uD83D"],
  ["abc", ""],
  ["aa", "a"],
]
checkFixture(
  "methods.ts",
  fixture,
  {
    strippedOfPrefix: pairs,
    firstUnit: ["", "a", "ab", "😀"].map((s) => [s]),
    lastUnit: ["", "a", "ab", "a😀"].map((s) => [s]),
    plausibleEmail: ["", "@", "a@", "@a", "a@b", "ab", "a@@"].map((s) => [s]),
    firstPosition: pairs,
  },
  [
    { id: "S1", what: "one unit too many cut", change: ["s.slice(p.length)", "s.slice(p.length + 1)"], contract: "strippedOfPrefix" },
    { id: "S2", what: "the second unit taken", change: ["name.charAt(0)", "name.charAt(1)"], contract: "firstUnit" },
    { id: "S3", what: "`.at` counted from the start", change: ["s.at(-1)", "s.at(0)"], contract: "lastUnit" },
    { id: "S4", what: "the end left unchecked", change: [' && !email.endsWith("@")', ""], contract: "plausibleEmail" },
    { id: "S5", what: "the position one short", change: ["return s.indexOf(t)", "return s.indexOf(t) - 1"], contract: "firstPosition" },
  ],
)
