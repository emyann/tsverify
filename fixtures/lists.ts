// Arrays transformed and taken apart: `.map`, `.join` and `.flatMap`, array patterns in a `const`, a parameter, a
// callback and a `for…of` head, with holes, defaults and a rest, over arrays and tuples. `test/lists.test.ts` asks
// each, runs each, and plants a bug in each.
import { contract } from "../src/contract.ts"

/** Each item's label, in order. */
export function labels(items: ReadonlyArray<{ readonly label: string }>): Array<string> {
  return items.map((item) => item.label)
}
export const labelsOf = contract(labels, {
  ensures: {
    sameLength: (items, out) => out.length === items.length,
    each: (items, out) => out.every((l, i) => l === items[i]?.label),
  },
})

/** The second of each pair, taken apart in the callback's parameter. */
export function seconds(pairs: ReadonlyArray<readonly [bigint, bigint]>): Array<bigint> {
  return pairs.map(([, b]) => b)
}
export const secondsOf = contract(seconds, {
  ensures: { each: (pairs, out) => out.length === pairs.length && out.every((b, i) => b === pairs[i]?.[1]) },
})

/** A line of cells, comma-separated. */
export function line(cells: ReadonlyArray<string>): string {
  return cells.join(",")
}
export const csvLine = contract(line, {
  ensures: {
    emptyIsEmpty: (cells, out) => cells.length > 0 || out === "",
    oneIsItself: (cells, out) => cells.length !== 1 || out === cells[0],
  },
})

/** Every pair laid end to end. */
export function flat(pairs: ReadonlyArray<readonly [bigint, bigint]>): Array<bigint> {
  return pairs.flatMap(([a, b]) => [a, b])
}
export const flattened = contract(flat, {
  ensures: { emptyIsEmpty: (pairs, out) => pairs.length > 0 || out.length === 0 },
})

/** Everything but the first. */
export function tail(xs: ReadonlyArray<string>): ReadonlyArray<string> {
  const [, ...rest] = xs
  return rest
}
export const tailOf = contract(tail, {
  ensures: {
    oneLess: (xs, out) => (xs.length === 0 ? out.length === 0 : out.length === xs.length - 1),
    shifted: (xs, out) => out.every((y, i) => y === xs[i + 1]),
  },
})

/** The first, or a default. */
export function firstOr(xs: ReadonlyArray<string>, fallback: string): string {
  const [first = fallback] = xs
  return first
}
export const firstOrFallback = contract(firstOr, {
  ensures: { theFirst: (xs, fallback, out) => out === (xs[0] ?? fallback) },
})

/** The two of a pair the other way round. */
export function swapped(pair: readonly [bigint, bigint]): readonly [bigint, bigint] {
  const [a, b] = pair
  return [b, a]
}
export const swapOf = contract(swapped, {
  ensures: { swapped: (pair, out) => out[0] === pair[1] && out[1] === pair[0] },
})

/** What the positive amounts add up to. */
export function credited(entries: ReadonlyArray<readonly [string, bigint]>): bigint {
  let total = 0n
  for (const [, amount] of entries) if (amount > 0n) total += amount
  return total
}
export const creditedNonNegative = contract(credited, {
  ensures: { nonNegative: (_entries, out) => out >= 0n },
})
