// Code beside an `enum`, which Node's type stripping refuses: a run cannot load the module, though the verifier reads
// the function, which does not use it.
// @ts-expect-error -- an enum is not erasable; the fixture is about a module a run cannot load
export enum Level {
  Low,
  High,
}

export function levelOf(n: number): 0 | 1 {
  return n > 10 ? 1 : 0
}
