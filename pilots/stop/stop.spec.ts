// One stop request, two programs, the same five laws.
import { computation } from "../../src/contract.ts"
import { computation as effectComputation } from "../../src/adapters/effect/contract.ts"
import type { JournalShape } from "../../../hkb-v2/packages/agent-runtime/src/core/engine/journal.ts"
import { requestStop } from "../../../hkb-v2/packages/agent-runtime/src/core/engine/filing.ts"
import { requestStop as requestStopAsync, type JournalError, type JournalPort, type StopRefused } from "./stop.async.ts"
import { acceptedWritesOneStop, readFailurePassesThrough, readsFirst, refusedExactlyWhenTheGuardSays, refusedWritesNothing } from "./laws.ts"

/** Nemia's verb, read in place: `Effect.fn('requestStop')(function* (taskId) { ... })`. */
export const effectStop = effectComputation<{ journal: Pick<JournalShape, "read" | "append"> }>()(requestStop, {
  ensures: { readsFirst, readFailurePassesThrough, refusedWritesNothing, acceptedWritesOneStop, refusedExactlyWhenTheGuardSays },
})

/** Its async twin, whose journal is its first argument. */
export const asyncStop = computation<{ journal: JournalPort }, StopRefused | JournalError>()(requestStopAsync, {
  ensures: {
    readsFirst: (_, taskId, out, calls) => readsFirst(taskId, out, calls),
    readFailurePassesThrough: (_, taskId, out, calls) => readFailurePassesThrough(taskId, out, calls),
    refusedWritesNothing: (_, taskId, out, calls) => refusedWritesNothing(taskId, out, calls),
    acceptedWritesOneStop: (_, taskId, out, calls) => acceptedWritesOneStop(taskId, out, calls),
    refusedExactlyWhenTheGuardSays: (_, taskId, out, calls) => refusedExactlyWhenTheGuardSays(taskId, out, calls),
  },
})
