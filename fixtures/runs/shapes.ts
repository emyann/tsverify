// Types and the values a run generates for each (test/runs.test.ts reads each alias's shape).
export type Flag = boolean
export type Id = string & { readonly __brand: "Id" }
export type Ledger = Readonly<Record<string, number>>
export type Pair = readonly [string, ...Array<bigint>]
export type Lookup = (k: string) => "a" | "b"
export type Tree = { readonly value: number; readonly children?: Tree }
export type Order = { readonly id: Id; readonly lines: ReadonlyArray<{ qty: number }>; readonly tags: ReadonlySet<string>; readonly by: ReadonlyMap<string, null | undefined> }
export type When = Date
export type Anything = unknown
export class Account {
  readonly balance = 0
}
export type Held = Account
