// What Nemia's `fold` makes of a journal: five laws, read from its code (the
// copy that carries its invariants) for every journal of every length.
import { contract } from '../../src/contract.ts';
import { fold } from './fold.ts';

export const folded = contract(fold, {
  ensures: {
    keepsItsTask: (taskId, _events, s) => s.taskId === taskId,
    stopRequestedExactlyWhenJournalled: (_taskId, events, s) => s.stopRequested === events.some((e) => e.kind === 'stop-requested'),
    closedExactlyWhenJournalled: (_taskId, events, s) => s.closed === events.some((e) => e.kind === 'closed'),
    noMoreAttemptsThanEvents: (_taskId, events, s) => s.attempts.length <= events.length,
    settledOnlyWhenJournalled: (_taskId, events, s) => s.settled === null || events.some((e) => e.kind === 'settled'),
  },
});
