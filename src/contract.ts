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
// - `assume(fn, { pure, ensures? })`: what the verifier takes on trust about a
//   function it does not read — a package's, or one of the program's whose
//   body it cannot lower. Verus's `assume_specification`.
//
// Spec code — every `requires`, every law, and what they call — is pure and
// deterministic: it runs no computation, calls no operation and calls nothing
// declared `pure: false`. The verifier refuses the rest.
//
// Proof code is written in the program, as calls that do nothing when it runs:
// - `invariant(i => ...)`, first in a loop's body;
// - `assert(() => ...)`;
// - a lemma's call, `lemma(statement, { requires? })` declared in a spec.
// The verifier proves each, then uses it.

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

/**
 * What is assumed, without proof, of a function the verifier does not read.
 *
 * - `pure: true`: the same arguments give the same result, and a call changes nothing anyone can see. Where the
 *   program has the function's source, the verifier checks this; for a package's function it is trusted.
 * - `pure: false`: each call may give a different result (the clock, a random number), and still changes nothing the
 *   program reads. Spec code may not call it.
 * - `ensures`: laws over the arguments and the result, assumed at every call.
 *
 * The type arguments are the view the laws are written for: `assume<[xs: ReadonlyArray<string>], string[]>(uniq, …)`
 * says what `uniq` does on arrays of strings, and `tsc` checks that `uniq` can be called so. The verifier applies it
 * only at calls whose arguments the view's parameters accept.
 */
export interface Assumption<A extends ReadonlyArray<unknown>, R> {
  readonly fn: (...args: A) => R
  readonly pure: boolean
  readonly ensures?: Readonly<Record<string, (...args: [...A, R]) => boolean>>
}

export const assume = <A extends ReadonlyArray<unknown>, R>(
  fn: (...args: A) => R,
  spec: Omit<Assumption<A, R>, "fn">,
): Assumption<A, R> => ({ fn, ...spec })

/**
 * Runs the real function on each input and asks each law of the assumption: the laws broken, with the input that
 * broke them. An assumption is trusted by the verifier; this is how a pack of them is tested against the library.
 */
export const brokenOn = <A extends ReadonlyArray<unknown>, R>(
  a: Assumption<A, R>,
  inputs: ReadonlyArray<A>,
): Array<{ readonly law: string; readonly input: A; readonly result: R }> =>
  inputs.flatMap((input) => {
    const result = a.fn(...input)
    return Object.entries(a.ensures ?? {})
      .filter(([, law]) => !law(...input, result))
      .map(([law]) => ({ law, input, result }))
  })

export const computation =
  <Ops, E = unknown>() =>
  <Args extends ReadonlyArray<unknown>, A>(
    fn: (...args: Args) => Promise<A>,
    laws: Omit<ComputationContract<Args, A, E, Ops>, "fn">,
  ): ComputationContract<Args, A, E, Ops> => ({ fn, ...laws })

/**
 * What a loop keeps: true before its first iteration, true after each one, and so true when it ends. Written first in
 * the loop's body; the verifier proves it, and reads the loop through it. In a `for…of` loop, `i` is how many elements
 * the loop has already gone through (0 before the first; the array's length at the end), and the invariant may not name
 * the element; in a `for` or `while` loop, write `invariant(() => ...)` over the loop's own variables.
 */
export const invariant = (_holds: (i: number) => boolean): void => {}

/** True here: the verifier proves it, and then knows it. */
export const assert = (_holds: () => boolean): void => {}

/** A statement proved once for all arguments that meet `requires`, and known wherever the lemma is called. */
export type Lemma<A extends ReadonlyArray<unknown>> = ((...args: A) => void) & {
  readonly statement: (...args: A) => boolean
  readonly requires?: (...args: A) => boolean
}

/**
 * A lemma: `statement` holds of every argument `requires` admits. The verifier proves it as it proves a contract
 * (`npm run verify -- <file> <name>`); a call of it in the program proves `requires` there and then knows `statement`.
 * Its body may be proof code: asserts and other lemmas' calls, then `return` of what it states.
 */
export const lemma = <A extends ReadonlyArray<unknown>>(
  statement: (...args: A) => boolean,
  opts: { readonly requires?: (...args: A) => boolean } = {},
): Lemma<A> => Object.assign((..._args: A): void => {}, { statement, ...opts })
