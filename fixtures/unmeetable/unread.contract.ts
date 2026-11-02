// A stub written to see its laws fail, shaped like the one that stopped a run for ten minutes (Nemia's raise of a cap): its
// input holds a number inside a field that may be null, which a counterexample read back may leave out (`tryRaise: {}`),
// while the side the counterexample is pinned back onto reads that number (`test/pin.test.ts`).
import { contract } from "@emyann/tsverify"

export interface Ask {
  readonly called: boolean
  readonly tryRaise: { readonly above: number } | null
  readonly loop: boolean
}

export interface Raise {
  readonly by: "retry" | "round"
  readonly above: number
}

/** Raises every run not called off and with no try's raise past 100, by retry or by round as it loops, above nothing. */
export function stub(a: Ask): Raise | null {
  if (a.called || (a.tryRaise !== null && a.tryRaise.above > 100)) return null
  return { by: a.loop ? "round" : "retry", above: -1 }
}

/** One law reads what a try's raise is above; the others read only whether there is one. */
export const raised = contract(stub, {
  ensures: {
    byRetryExactlyWhenTheTryCarriesOne: ({ input: [a], output }) =>
      (output !== null && output.by === "retry") === (!a.called && a.tryRaise !== null),
    retryAboveTheTrys: ({ input: [a], output }) =>
      output === null || output.by !== "retry" || (a.tryRaise !== null && output.above === a.tryRaise.above),
    neverBelowNothing: ({ output }) => output === null || output.above >= 0,
  },
})
