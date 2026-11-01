// The laws of a program that calls lodash. The pack is imported for what it
// declares: without it, every call to lodash is refused.
import "@emyann/tsverify/packs/lodash"
import { contract } from "@emyann/tsverify"
import { labelCount, progress } from "./labels.ts"

export const labels = contract(labelCount, {
  ensures: {
    noneExactlyWhenEmpty: ({ input: [labels], output }) => (output === "none") === (labels.length === 0),
    /**
     * True of lodash, and not provable from the pack: it says nothing of duplicates, so to the verifier `uniq(["a",
     * "a"])` may be `["a", "a"]`. The counterexample says it leans on `uniq`.
     */
    severalOnlyWithTwoDifferent: ({ input: [labels], output }) => output !== "several" || labels.some((a) => labels.some((b) => a !== b)),
  },
})

export const progressWithinTotal = contract(progress, {
  ensures: {
    withinTotal: ({ input: [done, total], output }) => !(total > 0 && done === done) || (0 <= output && output <= total),
    noneWithoutTotal: ({ input: [, total], output }) => total > 0 || output === 0,
    allOfItWhenDone: ({ input: [done, total], output }) => !(total > 0 && done === total) || output === total,
  },
})
