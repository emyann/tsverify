// What a spec author writes for an Effect program: the core's `computation`,
// typed from the Effect itself. It imports only Effect's types.
//
//   computation<{ ledger: LedgerShape }>()(withdraw, { ensures: { … } })
//
// A law takes the program's arguments, its outcome and the calls it made to the
// operations named in the type argument.
import type { Effect } from "effect"
import type { Call, Outcome } from "../../contract.ts"

/** Every call the operations of `Ops` can make, as a law reads it. */
export type EffectCallsOf<Ops> = {
  [T in keyof Ops]: {
    [M in keyof Ops[T] & string]: Ops[T][M] extends (...args: infer P) => Effect.Effect<infer A, infer E, infer _R> ? Call<M, P, A, E> : never
  }[keyof Ops[T] & string]
}[keyof Ops]

export interface EffectContract<Args extends ReadonlyArray<unknown>, A, E, Ops> {
  readonly fn: (...args: Args) => Effect.Effect<A, E, never> | Effect.Effect<A, E, any>
  readonly requires?: (...args: Args) => boolean
  readonly ensures: Readonly<Record<string, (...args: [...Args, Outcome<A, E>, ReadonlyArray<EffectCallsOf<Ops>>]) => boolean>>
}

export const computation =
  <Ops>() =>
  <Args extends ReadonlyArray<unknown>, A, E, R>(
    fn: (...args: Args) => Effect.Effect<A, E, R>,
    laws: Omit<EffectContract<Args, A, E, Ops>, "fn">,
  ): EffectContract<Args, A, E, Ops> => ({ fn, ...laws })
