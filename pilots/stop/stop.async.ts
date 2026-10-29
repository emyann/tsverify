// `requestStop` as plain TypeScript would write it: async, its journal given as
// an interface, its refusal thrown. No Effect anywhere; the same pure helpers.
import type { Rejects } from "../../src/contract.ts"
import { fold, type Event } from "../../../hkb-v2/packages/agent-runtime/src/core/domain.ts"
import { stopRefusalOf } from "../../../hkb-v2/packages/agent-runtime/src/core/engine/filing.ts"

export class StopRefused extends Error {
  readonly _tag = "StopRefused" as const
}

export class JournalError extends Error {
  readonly _tag = "JournalError" as const
}

export interface JournalPort {
  readonly read: (taskId: string) => Rejects<readonly Event[], JournalError>
  readonly append: (taskId: string, event: Event) => Rejects<void, JournalError>
}

export const requestStop = async (journal: JournalPort, taskId: string): Promise<void> => {
  const events = await journal.read(taskId)
  const refused = stopRefusalOf(taskId, events.length ? fold(taskId, events) : undefined)
  if (refused) throw new StopRefused(refused)
  await journal.append(taskId, { kind: "stop-requested", at: new Date().toISOString() })
}
