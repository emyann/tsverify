// What a spec author writes: the function a contract is about, the inputs it
// promises nothing for (`requires`), and the laws its result keeps (`ensures`),
// each an ordinary TypeScript predicate.
//
// The verifier reads a contract from source and never runs this file. At run
// time a contract is a plain object, so the same predicates serve as a test
// oracle: `c.ensures.law(input, c.fn(input))`.

export interface Contract<A extends ReadonlyArray<unknown>, R> {
  readonly fn: (...args: A) => R
  readonly requires?: (...args: A) => boolean
  readonly ensures: Readonly<Record<string, (...args: [...A, R]) => boolean>>
}

export const contract = <A extends ReadonlyArray<unknown>, R>(
  fn: (...args: A) => R,
  laws: Omit<Contract<A, R>, "fn">,
): Contract<A, R> => ({ fn, ...laws })
