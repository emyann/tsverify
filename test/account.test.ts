// A loop read through its invariants: an account folded from its ledger
// (examples/account/account.ts). The verifier proves the five laws of
// `account.contract.ts` for ledgers of every length; each planted bug is caught
// with a ledger that breaks the planted code when it runs; and with no
// invariant written, it finds the five itself, and still catches each bug.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import ts from "typescript"
import { accountOf, type Entry } from "../examples/account/account.ts"
import { folded } from "../examples/account/account.contract.ts"
import { random } from "../examples/order/generate.ts"
import { diagnostics, loadProject, sourceFile } from "../src/project.ts"
import { purityOf } from "../src/purity.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "examples/account/account.contract.ts")
const source = path.join(root, "examples/account/account.ts")
const tsconfig = path.join(root, "tsconfig.json")
const LAWS = Object.keys(folded.ensures)
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const verifyWith = (z3: Ctx, overrides: ReadonlyMap<string, string> = new Map()) =>
  verify(z3, loadProject([spec], tsconfig, overrides), spec, "folded")

/** Seeded random ledgers, every kind, amounts positive (as the contract requires), ids that both match and miss. */
const ledger = (r: () => number): Entry[] => {
  const n = (k: number) => Math.floor(r() * k)
  const at = "2026-10-29T12:00:00Z"
  const make = (): Entry => {
    switch (n(7)) {
      case 0:
        return { kind: "opened", at, owner: `o${n(3)}` }
      case 1:
        return { kind: "deposited", at, id: `t${n(3)}`, amount: BigInt(1 + n(50)) }
      case 2:
        return { kind: "withdrawn", at, id: `t${n(3)}`, amount: BigInt(1 + n(50)) }
      case 3:
        return { kind: "disputed", at, id: `t${n(3)}` }
      case 4:
        return { kind: "resolved", at, id: `t${n(3)}`, upheld: r() < 0.5 }
      case 5:
        return { kind: "frozen", at, reason: n(2) ? "" : "audit" }
      default:
        return { kind: "closed", at }
    }
  }
  return Array.from({ length: n(10) }, make)
}

describe("the account fold, verified", () => {
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())

  it("the spec type-checks", () => {
    assert.deepEqual(diagnostics(loadProject([spec], tsconfig), spec), [])
  })

  it("proves the five laws and every invariant, for ledgers of every length", async () => {
    const v = await verifyWith(z3)
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), Object.fromEntries(LAWS.map((n) => [n, "proved"])))
    assert.deepEqual(
      v.obligations.map((o) => `${o.kind} ${o.phase}: ${o.status}`),
      ["entry", "kept"].flatMap((phase) => Array.from({ length: 5 }, () => `invariant ${phase}: proved`)),
    )
  })

  it("leans on `requires`: with negative deposits allowed, a deposit-only ledger can end in debt", async () => {
    const text = readFileSync(spec, "utf8").replace("  requires: positive,\n", "")
    const v = await verifyWith(z3, new Map([[spec, text]]))
    const law = v.laws.find((l) => l.name === "noDebtWithoutWithdrawals")!
    assert.equal(law.status, "counterexample", JSON.stringify(statuses(v)))
    const [entries] = law.args as [Entry[]]
    assert.equal(folded.ensures.noDebtWithoutWithdrawals({ input: [entries], output: accountOf(entries) }), false)
  })

  it("the laws hold on 2,000 random ledgers, run for real", () => {
    const r = random(29)
    for (let k = 0; k < 2000; k++) {
      const entries = ledger(r)
      const a = accountOf(entries)
      for (const [name, law] of Object.entries(folded.ensures))
        assert.ok(
          law({ input: [entries], output: a }),
          `${name} broken on ${JSON.stringify(entries, (_, x) => (typeof x === "bigint" ? `${x}n` : x))}`,
        )
    }
  })
})

interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  /** The law the bug breaks. */
  readonly breaks: keyof typeof folded.ensures
}
const DEPOSIT = "a.transactions.push({ id: e.id, amount: e.amount, disputed: false })"
const PLANTS: ReadonlyArray<Plant> = [
  {
    id: "A1",
    what: "a second close reopens the account",
    change: ["a.closed = true", "a.closed = !a.closed"],
    breaks: "closedExactlyWhenRecorded",
  },
  {
    id: "A2",
    what: "an opening after a freeze is lost",
    change: ["a.opened = true", "a.opened = a.frozen === null"],
    breaks: "openedExactlyWhenRecorded",
  },
  {
    id: "A3",
    what: "a dispute freezes the account",
    change: ["if (t) t.disputed = true", 'if (t) t.disputed = true\n        a.frozen ??= "disputed"'],
    breaks: "frozenOnlyWhenRecorded",
  },
  {
    id: "A4",
    what: "a deposit is recorded twice",
    change: [DEPOSIT, `${DEPOSIT}\n        ${DEPOSIT}`],
    breaks: "noMoreTransactionsThanEntries",
  },
  {
    id: "A5",
    what: "a deposit is taken out",
    change: ["a.balance += e.amount", "a.balance -= e.amount"],
    breaks: "noDebtWithoutWithdrawals",
  },
]

/** The example with `find` (which must occur once) replaced. */
const plant = (text: string, [find, replace]: readonly [string, string], id: string): string => {
  assert.equal(text.split(find).length - 1, 1, `${id}: \`${find}\` must occur once in the example`)
  return text.replace(find, replace)
}

describe("the account fold, with a bug planted", () => {
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())

  for (const p of PLANTS)
    it(`${p.id}, ${p.what}: ${p.breaks} refuted, and the planted fold breaks it when run`, async () => {
      const text = plant(readFileSync(source, "utf8"), p.change, p.id)
      const v = await verifyWith(z3, new Map([[source, text]]))
      assert.equal(v.unsupported, undefined)
      const law = v.laws.find((l) => l.name === p.breaks)!
      assert.equal(law.status, "counterexample", JSON.stringify(statuses(v)))
      const file = path.join(root, `examples/account/account.planted-${p.id}.ts`)
      writeFileSync(file, text)
      try {
        const planted = ((await import(pathToFileURL(file).href)) as { accountOf: typeof accountOf }).accountOf
        const [entries] = law.args as [Entry[]]
        assert.equal(
          folded.ensures[p.breaks]({ input: [entries], output: planted(entries) }),
          false,
          JSON.stringify(law.args, (_, x) => (typeof x === "bigint" ? `${x}n` : x)),
        )
      } finally {
        rmSync(file)
      }
    })

  it("a harmless change (`a.closed = a.closed || true`) is still proved", async () => {
    const v = await verifyWith(
      z3,
      new Map([[source, plant(readFileSync(source, "utf8"), ["a.closed = true", "a.closed = a.closed || true"], "C1")]]),
    )
    assert.deepEqual(
      Object.values(statuses(v)),
      LAWS.map(() => "proved"),
    )
  })

  it("with no invariant written, the verifier finds them: each law, restated for the entries gone through, proved on entry and kept", async () => {
    const v = await verifyWith(z3, new Map([[source, unwritten(readFileSync(source, "utf8"))]]))
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), Object.fromEntries(LAWS.map((n) => [n, "proved"])))
    assert.deepEqual(
      v.obligations.map((o) => `${o.guessed} ${o.phase}: ${o.status}`).sort(),
      LAWS.flatMap((n) => [`${n} entry: proved`, `${n} kept: proved`]).sort(),
    )
  })

  for (const p of PLANTS)
    it(`${p.id} with no invariant written: ${p.breaks}'s guess is dropped, and the law refuted`, async () => {
      const v = await verifyWith(z3, new Map([[source, plant(unwritten(readFileSync(source, "utf8")), p.change, p.id)]]))
      assert.equal(v.laws.find((l) => l.name === p.breaks)!.status, "counterexample", JSON.stringify(statuses(v)))
      assert.ok(!v.obligations.some((o) => o.guessed === p.breaks), "the broken law's guess is not kept")
    })
})

/** The fold with its written invariants taken out. */
const unwritten = (text: string): string =>
  text
    .split("\n")
    .filter((l) => !/^\s*invariant\(/.test(l))
    .join("\n")

it("the purity check reads the fold as pure, with the helper it changes its state through", () => {
  const project = loadProject([source], tsconfig)
  const fn = sourceFile(project, source).statements.find(
    (s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && s.name?.text === "accountOf",
  )!
  const p = purityOf(project.checker, fn, () => undefined)
  assert.ok(p.pure, p.pure ? "" : p.why)
  assert.deepEqual([...p.read].sort(), ["accountOf", "openInto"])
})
