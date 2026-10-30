// Time and rounding (fixtures/times.ts): every law proved; the laws hold when the functions run, on real times; and a
// bug planted in each is caught. T4 is the regression of `Number.isInteger` of an optional number, which read as
// `false` and made the deadline's `requires` leave out every defined deadline, so that `pastIt` held of nothing.
import * as fixture from "../fixtures/times.ts"
import { checkFixture } from "./fixture-plants.ts"

const t = (s: string) => `2026-10-30T12:00:${s}Z`
checkFixture(
  "times.ts",
  fixture,
  {
    secondsShown: [
      [t("00.000"), new Date(t("01.500"))],
      [t("00.000"), new Date(t("00.000"))],
      [t("00.000"), new Date(t("01.000"))],
      [t("10.000"), new Date(t("00.000"))],
    ],
    overdueOnlyPastIt: [
      [5000, undefined],
      [5000, 4],
      [5000, 5],
      [0, 0],
    ],
    middleBetween: [
      [0, 0],
      [0, 1],
      [3, 9],
      [7, 8],
    ],
  },
  [
    { id: "T1", what: "rounded down", change: ["Math.round((now.getTime()", "Math.floor((now.getTime()"], contract: "secondsShown" },
    {
      id: "T2",
      what: "no deadline read as none",
      change: ["deadlineSeconds !== undefined && ranForMs > deadlineSeconds * 1000", "ranForMs > (deadlineSeconds ?? 0) * 1000"],
      contract: "overdueOnlyPastIt",
    },
    {
      id: "T3",
      what: "the middle one past",
      change: ["Math.floor((lo + hi) / 2)", "Math.floor((lo + hi + 2) / 2)"],
      contract: "middleBetween",
    },
    {
      id: "T4",
      what: "overdue at the deadline itself",
      change: ["ranForMs > deadlineSeconds * 1000", "ranForMs >= deadlineSeconds * 1000"],
      contract: "overdueOnlyPastIt",
    },
  ],
)
