// Bitwise operators on `number` (fixtures/bitwise.ts): every law proved; the laws hold when the functions run, on
// fractions, `NaN`, the infinities and values past 32 bits; and a bug planted in each is caught, the classic midpoint
// overflow among them.
import { grid } from "../fixtures/corpus/cases.ts"
import * as fixture from "../fixtures/bitwise.ts"
import { checkFixture } from "./fixture-plants.ts"

const wide = [0, -0, 1, -1, 1.5, -1.5, 2 ** 31, -(2 ** 31), 2 ** 32, Number.NaN, Infinity, 2147483647, 4294967295]
checkFixture(
  "bitwise.ts",
  fixture,
  {
    midBetween: [
      [0, 0],
      [1, 3],
      [0, 2 ** 31 - 1],
      [2 ** 30, 2 ** 31 - 1],
      [2 ** 31 - 1, 2 ** 31 - 1],
      [5, 9],
    ],
    evenByLowBit: [0, 1, 2, -1, -2, -3, 2147483647, -2147483648].map((n) => [n]),
    aByte: grid([0, 255, 256, -1, 0x12345678, 4294967295, 1.5, Number.NaN], [0, 1, 2, 3]),
    aFlag: [0, 1, 5, 30].map((n) => [n]),
    int32: wide.map((x) => [x]),
    branchless: [1, -1, 0, 2147483647, -2147483647, 5, -5].map((v) => [v]),
    mixedEven: grid(wide, [0, 1, -1, 7, Number.NaN]),
  },
  [
    { id: "B1", what: "a signed shift, which overflows past 2^31", change: ["(lo + hi) >>> 1", "(lo + hi) >> 1"], contract: "midBetween" },
    { id: "B2", what: "the second bit read for the first", change: ["(n & 1)", "(n & 2)"], contract: "evenByLowBit" },
    { id: "B3", what: "a mask one bit too wide", change: ["& 0xff", "& 0x1ff"], contract: "aByte" },
    { id: "B4", what: "the flag one bit too high", change: ["1 << n", "1 << (n + 1)"], contract: "aFlag" },
    { id: "B5", what: "an unsigned conversion for a signed one", change: ["return x | 0", "return x >>> 0"], contract: "int32" },
    { id: "B6", what: "the sign mask added back", change: ["(v ^ sign) - sign", "(v ^ sign) + sign"], contract: "branchless" },
    { id: "B7", what: "the shift left out", change: ["  h <<= 1\n", ""], contract: "mixedEven" },
  ],
)
