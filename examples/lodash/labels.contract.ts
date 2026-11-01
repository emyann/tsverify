// The laws of a program that calls lodash. The pack is imported for what it
// declares: without it, every call to lodash is refused.
import "@emyann/tsverify/packs/lodash"
import { contract } from "@emyann/tsverify"
import { labelCount, progress } from "./labels.ts"

export const labels = contract(labelCount, {
  ensures: {
    noneExactlyWhenEmpty: (labels, out) => (out === "none") === (labels.length === 0),
    /**
     * True of lodash, and not provable from the pack: it says nothing of duplicates, so to the verifier `uniq(["a",
     * "a"])` may be `["a", "a"]`. The counterexample says it leans on `uniq`.
     */
    severalOnlyWithTwoDifferent: (labels, out) => out !== "several" || labels.some((a) => labels.some((b) => a !== b)),
  },
})

export const progressWithinTotal = contract(progress, {
  ensures: {
    withinTotal: (done, total, out) => !(total > 0 && done === done) || (0 <= out && out <= total),
    noneWithoutTotal: (done, total, out) => total > 0 || out === 0,
    allOfItWhenDone: (done, total, out) => !(total > 0 && done === total) || out === total,
  },
})
