// Nemia's `fold` (hkb-v2, agent-runtime/src/core/domain.ts) and the three
// helpers it changes its state through, copied as they are, with the loop's
// invariants added: the proof code the verifier reads `fold` by. hkb-v2 is not
// changed; `test/fold.test.ts` holds these functions equal to its own, but for
// the `invariant(...)` lines.
import type { Attempt, Event, State } from '../../../hkb-v2/packages/agent-runtime/src/core/domain.ts';
import { invariant } from '../../src/contract.ts';

/**
 * Ends the attempt `a` as the `ended` event `e` says: an empty list of skills or files kept, an empty one of denials not, and an end with
 * no usage keeping what was counted while it ran (`counted`).
 */
function endAttempt(a: Attempt, e: Extract<Event, { kind: 'ended' }>): void {
  a.ended = e.observed;
  a.endedAt = e.at;
  if (e.mono) a.endedMono = e.mono;
  a.reason = e.reason;
  a.nativeId = e.nativeId ?? a.nativeId;
  a.closeout = e.closeout;
  if (e.closedOut !== undefined) a.closedOut = e.closedOut;
  if (e.former !== undefined) a.former = e.former;
  a.usage = e.usage ?? a.usage;
  a.exitCode = e.exitCode ?? null;
  if (e.denials?.length) a.denials = e.denials;
  if (e.skills) a.skills = e.skills;
  if (e.files) a.files = e.files;
  if (e.ranOn) a.ranOn = e.ranOn;
  if (e.limit) a.limit = e.limit;
  a.error = e.error ?? a.error;
}

/** An event about one attempt, `e`, written into that attempt's fold `a`. */
function foldInto(
  a: Attempt,
  e: Extract<Event, { kind: 'spawned' | 'ended' | 'measured' | 'counted' | 'denied' | 'gap' | 'process' }>,
): void {
  switch (e.kind) {
    case 'spawned':
      a.spawnedAt = e.at;
      if (e.mono) a.spawnedMono = e.mono;
      a.error = e.error;
      return;
    case 'ended':
      return endAttempt(a, e);
    case 'measured':
      a.usage = { ...a.usage, ...e.usage };
      return;
    case 'counted':
      a.usage = e.usage;
      return;
    case 'denied':
      a.denials = [...(a.denials ?? []), e.what === undefined ? { tool: e.tool } : { tool: e.tool, what: e.what }];
      return;
    case 'gap':
      if (a.gapSince === undefined && e.mono) a.gapMono = e.mono;
      a.gapSince ??= e.at;
      return;
    case 'process':
      delete a.gapSince;
      delete a.gapMono;
      if (e.pid !== undefined) a.processes = [...(a.processes ?? []), e.pid];
  }
}

/** The task as the `filed` event `e` states it, written into the fold `s`. */
function fileInto(s: State, e: Extract<Event, { kind: 'filed' }>): void {
  s.filedAt = e.at;
  s.brief = e.brief;
  s.cwd = e.cwd;
  s.harness = e.harness;
  s.deadlineSeconds = e.deadlineSeconds;
  s.resumeFrom = e.resumeFrom;
  s.config = e.config;
  s.closeoutSchema = e.closeoutSchema;
  if (e.holdOpen) s.holdOpen = true;
  if (e.restartPolicy === 'Always') s.restartPolicy = 'Always';
  if (e.queued !== undefined) s.queued = e.queued;
  if (e.priority !== undefined) s.priority = e.priority;
  if (e.labels !== undefined) s.labels = e.labels;
  if (e.traceparent !== undefined) s.traceparent = e.traceparent;
}

/** Observed state, folded. A `State` is never stored — it is always re-derived from the journal. */
export function fold(taskId: string, events: readonly Event[]): State {
  const s: State = {
    taskId,
    brief: '',
    cwd: '',
    attempts: [],
    said: [],
    inputs: [],
    closed: false,
    stopRequested: false,
    settled: null,
  };
  for (const e of events) {
    invariant(() => s.taskId === taskId);
    invariant((i) => s.stopRequested === events.slice(0, i).some((x) => x.kind === 'stop-requested'));
    invariant((i) => s.closed === events.slice(0, i).some((x) => x.kind === 'closed'));
    invariant((i) => s.attempts.length <= i);
    invariant((i) => s.settled === null || events.slice(0, i).some((x) => x.kind === 'settled'));
    switch (e.kind) {
      case 'filed':
        fileInto(s, e);
        break;
      case 'admitted':
        s.admitted = s.inputs.length;
        break;
      case 'starting':
        s.attempts.push({
          n: e.attempt,
          startedAt: e.at,
          ...(e.mono ? { startedMono: e.mono } : {}),
          spawnedAt: null,
          ended: null,
          endedAt: null,
          reason: null,
          nativeId: null,
          resumeFrom: e.resumeFrom,
          ...(e.nudge ? { nudge: e.nudge } : {}),
          usage: null,
          exitCode: null,
          ...(s.inputs.length ? { turn: s.inputs.length } : {}),
        });
        break;
      case 'spawned':
      case 'ended':
      case 'measured':
      case 'counted':
      case 'denied':
      case 'gap':
      case 'process': {
        const a = s.attempts.find((x) => x.n === e.attempt);
        if (a) foldInto(a, e);
        break;
      }
      case 'stop-requested':
        s.stopRequested = true;
        break;
      case 'said':
        s.said.push({ at: e.at, attempt: e.attempt, text: e.text, after: e.after ?? null });
        break;
      case 'input':
        s.inputs.push({ at: e.at, text: e.text, ...(e.config ? { config: e.config } : {}) });
        break;
      case 'closed':
        s.closed = true;
        break;
      case 'settled': {
        s.settled = e.outcome;
        const open = s.attempts.at(-1);
        if (open && open.ended === null && e.nativeId) open.nativeId = e.nativeId;
        break;
      }
    }
  }
  return s;
}
