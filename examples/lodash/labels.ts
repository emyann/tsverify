// A program that calls lodash, which the verifier does not read: it reads what
// the pack in force declares of `uniq` and `clamp` instead.
import { clamp, uniq } from "lodash-es"

/** How many different labels a card carries, in a word. */
export const labelCount = (labels: ReadonlyArray<string>): "none" | "one" | "several" => {
  const distinct = uniq(labels)
  return distinct.length === 0 ? "none" : distinct.length === 1 ? "one" : "several"
}

/** How far a run has come: between none of it and all of it, and none when there is nothing to do. */
export const progress = (done: number, total: number): number => (total > 0 ? clamp(done, 0, total) : 0)
