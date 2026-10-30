// `Math.max`, `min`, `abs`, `trunc`, `Object.is` and the sign of zero (fixtures/signs.ts): every law proved; the laws
// hold when the functions run, on `-0`, `NaN` and the infinities; and a bug planted in each is caught, two of them seen
// only by telling `-0` from `0`.
import { grid } from "../fixtures/corpus/cases.ts"
import * as fixture from "../fixtures/signs.ts"
import { checkFixture } from "./fixture-plants.ts"

const edges = [-2, -0, 0, 0.5, 3, Infinity, -Infinity, Number.NaN]
checkFixture(
  "signs.ts",
  fixture,
  {
    clamped: grid(edges, edges, edges),
    distanceApart: grid([-3, -0, 0, 2, 5], [-3, -0, 0, 2, 5]),
    sameValue: grid([0, -0, Number.NaN, 1, -1, Infinity], [0, -0, Number.NaN, 1, -1, Infinity]),
    signFlipped: [0, -0, 1, -2.5, Number.NaN, Infinity].map((x) => [x]),
    towardZero: [-0.5, -1, -1.5, 0, -0, 0.5, 2.7, Number.NaN, -Infinity].map((x) => [x]),
  },
  [
    {
      id: "M1",
      what: "the two bounds taken the wrong way",
      change: ["Math.min(Math.max(x, lo), hi)", "Math.max(Math.min(x, lo), hi)"],
      contract: "clamped",
    },
    { id: "M2", what: "the difference left signed", change: ["Math.abs(a - b)", "a - b"], contract: "distanceApart" },
    {
      id: "M3",
      what: "an absolute value by hand, which keeps -0",
      change: ["Math.abs(a - b)", "a - b < 0 ? b - a : a - b"],
      contract: "distanceApart",
    },
    { id: "M4", what: "`===` in place of `Object.is`", change: ["Object.is(a, b)", "a === b"], contract: "sameValue" },
    { id: "M5", what: "`0 - x` in place of `-x`, which gives 0 of 0", change: ["return -x", "return 0 - x"], contract: "signFlipped" },
    { id: "M6", what: "rounded down, not toward 0", change: ["Math.trunc(x)", "Math.floor(x)"], contract: "towardZero" },
  ],
)
