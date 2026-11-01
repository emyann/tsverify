// What a spec author writes for an Effect program: `spec<F>(laws)`, written
// before the code, the calls its laws read typed from the services `F`
// requires; or `computation<Ops>()(fn, laws)`, pointing at code that exists.
// It imports only Effect's types.
//
//   computation<{ ledger: LedgerShape }>()(withdraw, { ensures: { … } })
//
// A law takes the program's arguments, its outcome and the calls it made to the
// operations named in the type argument.
import type { Effect } from "effect"
import type { Call, ComputationRun, Given, Law, Outcome } from "../../contract.ts"

/** Every call the operations of `Ops` can make, as a law reads it. */
export type EffectCallsOf<Ops> = {
  [T in keyof Ops]: {
    [M in keyof Ops[T] & string]: Ops[T][M] extends (...args: infer P) => Effect.Effect<infer A, infer E, infer _R>
      ? Call<M, P, A, E>
      : never
  }[keyof Ops[T] & string]
}[keyof Ops]

/** A law of an Effect program: over its arguments, how it ended and the calls it made to its services. */
type EffectContractLaw<Args extends ReadonlyArray<unknown>, A, E, Ops> = Law<
  (run: ComputationRun<Args, Outcome<A, E>, EffectCallsOf<Ops>>) => boolean
>

export interface EffectContract<Args extends ReadonlyArray<unknown>, A, E, Ops> {
  readonly fn: (...args: Args) => Effect.Effect<A, E> | Effect.Effect<A, E, any>
  readonly requires?: (given: Given<Args>) => boolean
  readonly ensures: Readonly<Record<string, EffectContractLaw<Args, A, E, Ops>>>
}

/** Every call an Effect can make to the services it requires, each method of a service that returns an Effect. */
type ServiceCallsOf<R> = R extends { readonly Service: infer S }
  ? {
      [M in keyof S & string]: S[M] extends (...args: infer P) => Effect.Effect<infer A, infer E, infer _R> ? Call<M, P, A, E> : never
    }[keyof S & string]
  : never

/** The laws of a spec over an Effect program of type `F`: over its arguments, how it ended and the calls it made. */
export type EffectLawOf<F> = F extends (...args: infer A) => Effect.Effect<infer V, infer E, infer R>
  ? (run: ComputationRun<A, Outcome<V, E>, ServiceCallsOf<R>>) => boolean
  : never

// `any`: any Effect program; a spec constrains it through its laws.
type AnyProgram = (...args: any) => Effect.Effect<any, any, any>

/** A spec of an Effect program: what it must do. `Implementation<S>` (from `@emyann/tsverify`) is its type. */
export interface EffectSpec<F extends AnyProgram> {
  readonly requires?: (given: Given<Parameters<F>>) => boolean
  readonly ensures: Readonly<Record<string, Law<EffectLawOf<F>>>>
  /** The program's type: only for `Implementation`, never a value. */
  readonly "~fn"?: F
}

/**
 * A spec of an Effect program of type `F`, written before the code: `spec<(accountId: string) =>
 * Effect.Effect<bigint, LedgerError, Ledger>>({ ensures: { law: ({ input: [accountId], output, calls }) => ... } })`. The calls a law
 * reads are those of the services `F` requires (`Ledger`'s methods), typed from them. Beside it, its type, `export
 * type BalanceSpec = typeof balanceSpec`; the code is `const balanceOf: Implementation<BalanceSpec> = ...`.
 */
export const spec = <F extends AnyProgram>(laws: Omit<EffectSpec<F>, "~fn">): EffectSpec<F> => laws

export const computation =
  <Ops>() =>
  <Args extends ReadonlyArray<unknown>, A, E, R, L extends Readonly<Record<string, EffectContractLaw<Args, A, E, Ops>>>>(
    fn: (...args: Args) => Effect.Effect<A, E, R>,
    laws: { readonly requires?: (given: Given<Args>) => boolean; readonly ensures: L },
  ): Omit<EffectContract<Args, A, E, Ops>, "ensures"> & { readonly ensures: L } => ({ fn, ...laws })
