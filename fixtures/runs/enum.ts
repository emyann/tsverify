// Code with an `enum`, which Node's type stripping refuses: a run cannot load it.
// @ts-expect-error -- an enum is not erasable; the fixture is about a module a run cannot load
export enum Level {
  Low,
  High,
}

export function levelOf(n: number): Level {
  return n > 10 ? Level.High : Level.Low
}
