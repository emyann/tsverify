// Arrays transformed and taken apart (fixtures/lists.ts): every law proved; the laws hold when the functions run, on
// empty arrays, one element and several; and a bug planted in each is caught.
import * as fixture from "../fixtures/lists.ts"
import { checkFixture } from "./fixture-plants.ts"

const strings = [[], ["a"], ["a", "b"], ["ab", "", "c"]]
const pairs = [
  [],
  [[1n, 2n]],
  [
    [1n, 2n],
    [3n, 4n],
  ],
  [
    [-1n, 0n],
    [5n, -5n],
    [0n, 0n],
  ],
]
checkFixture(
  "lists.ts",
  fixture,
  {
    labelsOf: [[[]], [[{ label: "a" }]], [[{ label: "ab" }, { label: "" }]]],
    secondsOf: pairs.map((p) => [p]),
    csvLine: strings.map((s) => [s]),
    flattened: pairs.map((p) => [p]),
    tailOf: strings.map((s) => [s]),
    firstOrFallback: strings.map((s) => [s, "none"]),
    swapOf: [[[1n, 2n]], [[0n, 0n]], [[-3n, 7n]]],
    creditedNonNegative: [
      [[]],
      [[["a", 5n]]],
      [[["a", -5n]]],
      [
        [
          ["a", 3n],
          ["b", -1n],
          ["c", 2n],
        ],
      ],
    ],
  },
  [
    { id: "A1", what: "a label cut short", change: ["item.label)", "item.label.slice(1))"], contract: "labelsOf" },
    { id: "A2", what: "the first of each pair taken", change: ["([, b]) => b", "([b]) => b"], contract: "secondsOf" },
    { id: "A3", what: "a comma after the last cell", change: ['cells.join(",")', 'cells.join(",") + ","'], contract: "csvLine" },
    {
      id: "A4",
      what: "a zero put in front",
      change: ["return pairs.flatMap(([a, b]) => [a, b])", "return [0n, ...pairs.flatMap(([a, b]) => [a, b])]"],
      contract: "flattened",
    },
    { id: "A5", what: "two skipped", change: ["const [, ...rest] = xs", "const [, , ...rest] = xs"], contract: "tailOf" },
    {
      id: "A6",
      what: "the default taken always",
      change: ["const [first = fallback] = xs", "const [, first = fallback] = xs"],
      contract: "firstOrFallback",
    },
    { id: "A7", what: "the pair kept as it was", change: ["return [b, a]", "return [a, b]"], contract: "swapOf" },
    {
      id: "A8",
      what: "every amount added",
      change: ["if (amount > 0n) total += amount", "total += amount"],
      contract: "creditedNonNegative",
    },
  ],
)
