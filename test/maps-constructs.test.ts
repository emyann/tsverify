// Each construct a map the code builds takes (fixtures/maps.ts), against JavaScript: writes and deletes at computed keys,
// keys listed in JavaScript's order, a `Set` spread and sorted, `.flatMap`, a `Map`'s and a `Set`'s changes, `has`,
// `get`, `size` and iteration, and a loop read key by key. Each computes what JavaScript computes on the search side, and
// on the proof side where it reads it exactly; each input pins the result, so a wrong one is told apart on every input.
// Apart from `maps.test.ts`: in one process with its verifications, Z3's memory would not hold both.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as fixture from "../fixtures/maps.ts"
import { loadProject, readContract } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { disagreements, lowerSide, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/maps.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("each construct, against JavaScript", () => {
  const keys: ReadonlyArray<ReadonlyArray<string>> = [
    [],
    ["a"],
    ["b", "1", "a", "0"],
    ["a", "a", "b"],
    ["10", "9", "x", "2"],
    ["z", "", "z"],
  ]
  type List = ReadonlyArray<string>
  /** One construct: its contract, the function run, a wrong result, its inputs, and those the proof side is asked of. */
  interface Case {
    readonly name: string
    readonly what: string
    readonly run: (args: ReadonlyArray<unknown>) => unknown
    readonly wrong: (x: unknown) => unknown
    readonly inputs: ReadonlyArray<ReadonlyArray<unknown>>
    readonly proof?: ReadonlyArray<ReadonlyArray<unknown>>
  }
  const of = <A extends ReadonlyArray<unknown>, R>(
    name: string,
    what: string,
    fn: (...a: A) => R,
    wrong: (r: R) => unknown,
    inputs: ReadonlyArray<A>,
    proof?: ReadonlyArray<A>,
  ): Case => ({ name, what, run: (a) => fn(...(a as A)), wrong: (x) => wrong(x as R), inputs, ...(proof === undefined ? {} : { proof }) })
  const each = <A extends ReadonlyArray<unknown>>(f: (k: List) => ReadonlyArray<A>): ReadonlyArray<A> => keys.flatMap(f)
  const str = (x: string) => `${x}!`
  const more = (x: number) => x + 1
  // The proof side is asked where it reads the construct exactly: a map's keys listed, and their count, it knows only as
  // a list of the keys it holds, in an order not known.
  const cases: ReadonlyArray<Case> = [
    of(
      "writtenRun",
      "writes at computed keys in a loop, a write and a delete after",
      fixture.written,
      str,
      each((k): Array<[List, string, string]> => [
        [k, "a", "a"],
        [k, "b", "a"],
        [k, "q", "b"],
      ]),
      each((k): Array<[List, string, string]> => [
        [k, "a", "a"],
        [k, "b", "a"],
        [k, "q", "b"],
      ]),
    ),
    of(
      "listedRun",
      "the keys listed: array positions first, by number, a key deleted and set again last",
      fixture.listed,
      str,
      each((k): Array<[List, string]> => [[k, "a"]]),
    ),
    of(
      "countedRun",
      "how many keys after writes and a delete",
      fixture.counted,
      more,
      each((k): Array<[List, string]> => [[k, "a"]]),
    ),
    of(
      "sortedOnceRun",
      "a `Set` of a list, spread and sorted",
      fixture.sortedOnce,
      str,
      each((k): Array<[List]> => [[k]]),
    ),
    of(
      "distinctRun",
      "how many strings a `Set` keeps",
      fixture.distinct,
      more,
      each((k): Array<[List]> => [[k]]),
    ),
    of(
      "doubledRun",
      "`.flatMap` of none or two",
      fixture.doubled,
      str,
      each((k): Array<[List]> => [[k]]),
    ),
    of(
      "mappedAtRun",
      "a `Map` filled in a loop, a delete after: `has` and `get`",
      fixture.mappedAt,
      str,
      each((k): Array<[List, string]> => [
        [k, "a"],
        [k, "z"],
      ]),
      each((k): Array<[List, string]> => [
        [k, "a"],
        [k, "z"],
      ]),
    ),
    of(
      "mappedSizeRun",
      "a `Map`'s `size`",
      fixture.mappedSize,
      more,
      each((k): Array<[List]> => [[k]]),
    ),
    of(
      "membersRun",
      "a `Set` filled in a loop, a delete after, iterated in insertion order",
      fixture.members,
      str,
      each((k): Array<[List, string]> => [[k, "a"]]),
    ),
    of(
      "holdsOfRun",
      "a `Set`'s `has` after `add` and `delete`",
      fixture.holdsOf,
      (x: boolean) => !x,
      each((k): Array<[List, string, string]> => [
        [k, "a", "a"],
        [k, "q", "a"],
      ]),
      each((k): Array<[List, string, string]> => [
        [k, "a", "a"],
        [k, "q", "a"],
      ]),
    ),
    of(
      "setSizeRun",
      "a `Set`'s `size` after `add` and `delete`",
      fixture.setSize,
      more,
      each((k): Array<[List, string]> => [[k, "a"]]),
    ),
    of(
      "keyedAtRun",
      "a loop over a `Set`'s strings that writes a map at each, read key by key on the proof side",
      fixture.keyedAt,
      str,
      each((k): Array<[List, string]> => [
        [k, "a"],
        [k, ""],
        [k, "z"],
      ]),
      // On the proof side, lists of none or one: a key written, one absent, the empty one skipped. Through a `Set` of two,
      // each pinned query costs tens of seconds alone, and some orders of them run Z3 out of memory.
      [
        [["a"], "a"],
        [["a"], "b"],
        [[""], ""],
        [[], "a"],
      ],
    ),
    of(
      "keyedCountRun",
      "how many keys that loop writes",
      fixture.keyedCount,
      more,
      each((k): Array<[List]> => [[k]]),
    ),
  ]
  for (const c of cases)
    it(`${c.what}: the search side computes what JavaScript computes${c.proof === undefined ? "" : ", and the proof side"}`, async () => {
      const run = c.run
      for (const [bound, inputs] of [[4, c.inputs] as const, ...(c.proof === undefined ? [] : [[undefined, c.proof] as const])]) {
        const side = () => lowerSide(z3, project, readContract(project, file, c.name), bound)
        assert.deepEqual(await disagreements(side(), inputs, run), [], `${c.name}, ${bound === undefined ? "proof" : "search"} side`)
        // Each input pins what the lowering computes: a wrong result is told apart on every one.
        const wrong = await disagreements(side(), inputs, (args) => c.wrong(run(args)))
        assert.equal(wrong.length, inputs.length, `${c.name}, ${bound === undefined ? "proof" : "search"} side, a wrong result`)
      }
    })

  it("`.flatMap` on the proof side, read exactly: no input gets a count JavaScript does not give", async () => {
    const side = lowerSide(z3, project, readContract(project, file, "doubledCountRun"))
    const inputs = keys.map((k) => [k])
    const bad = await disagreements(side, inputs, ([k]) => fixture.doubledCount(k as List))
    // None is a wrong count. Within a query's work, the longest lists, of six or eight elements, may be left undecided;
    // the short ones are decided.
    assert.ok(
      bad.every((d) => d.status === "unknown"),
      JSON.stringify(bad),
    )
    assert.ok(
      bad.every((d) => (d.args[0] as List).length >= 3),
      JSON.stringify(bad),
    )
  })
})
