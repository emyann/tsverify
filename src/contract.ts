// What a spec author writes. No dependencies: it runs as a test oracle and as a
// runtime guard, and the verifier reads it from source without running it.
//
// - `contract(fn, { requires?, ensures })`: laws over a pure function's
//   arguments and result.
// - `computation<Ops, E>()(fn, { requires?, ensures })`: laws over an async
//   function's arguments, its outcome and the calls it made to the operations
//   of `Ops` (an object of the interfaces it is given). `E` is what it may fail
//   with. An Effect program takes the Effect adapter's `computation` instead,
//   which reads both from the Effect's type.

export interface Contract<A extends ReadonlyArray<unknown>, R> {
  readonly fn: (...args: A) => R
  readonly requires?: (...args: A) => boolean
  readonly ensures: Readonly<Record<string, (...args: [...A, R]) => boolean>>
}

export const contract = <A extends ReadonlyArray<unknown>, R>(
  fn: (...args: A) => R,
  laws: Omit<Contract<A, R>, "fn">,
): Contract<A, R> => ({ fn, ...laws })

/** How a computation ended. */
export type Outcome<A, E> = { readonly _tag: "Success"; readonly value: A } | { readonly _tag: "Failure"; readonly error: E }

/** One call a computation made to an operation: what it is an operation of, which, with what, and how it ended. */
export interface Call<Op extends string, Args, A, E> {
  readonly target: string
  readonly op: Op
  readonly args: Args
  readonly outcome: Outcome<A, E>
}

/**
 * A promise that declares what it rejects with: a promise in every way, and the
 * verifier reads `E` as the operation's failure. A plain `Promise<A>` is
 * assignable to it.
 */
export type Rejects<A, E> = Promise<A> & { readonly "~rejects"?: E }

type RejectionOf<R> = R extends { readonly "~rejects"?: infer E } ? Exclude<E, undefined> : unknown

/** Every call the operations of `Ops` can make, as a law reads it. */
export type AsyncCallsOf<Ops> = {
  [T in keyof Ops]: {
    [M in keyof Ops[T] & string]: Ops[T][M] extends (...args: infer P) => infer R ? Call<M, P, Awaited<R>, RejectionOf<R>> : never
  }[keyof Ops[T] & string]
}[keyof Ops]

export interface ComputationContract<Args extends ReadonlyArray<unknown>, A, E, Ops> {
  readonly fn: (...args: Args) => Promise<A>
  readonly requires?: (...args: Args) => boolean
  readonly ensures: Readonly<Record<string, (...args: [...Args, Outcome<A, E>, ReadonlyArray<AsyncCallsOf<Ops>>]) => boolean>>
}

export const computation =
  <Ops, E = unknown>() =>
  <Args extends ReadonlyArray<unknown>, A>(
    fn: (...args: Args) => Promise<A>,
    laws: Omit<ComputationContract<Args, A, E, Ops>, "fn">,
  ): ComputationContract<Args, A, E, Ops> => ({ fn, ...laws })
