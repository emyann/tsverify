// The laws of the programs that take text written elsewhere, over their outcome
// and the calls they made. What `Effect.try` ran is not a call: a law sees it
// only through the outcome.
import { assume, computation as plainComputation } from "tsverify"
import { computation } from "tsverify/effect"
import { accountOf } from "./account.ts"
import { depositTyped, importDeposits, openWith } from "./imports.ts"
import { balanceOf, copyDeposits } from "./imports.async.ts"
import type { LedgerShape } from "./withdraw.ts"
import type { LedgerError, LedgerPort } from "./withdraw.async.ts"

/** The ledger's fold, pure (checked from its source); its own laws are proved apart (`account.spec.ts`). */
export const accountOfIsPure = assume(accountOf, { pure: true })

type Ops = { ledger: LedgerShape }

export const typed = computation<Ops>()(depositTyped, {
  ensures: {
    unreadableNamesTheText: (_accountId, _id, text, out) =>
      !(out._tag === "Failure" && out.error._tag === "AmountUnreadable") || out.error.text === text,
    nothingCalledExactlyWhenUnreadable: (_accountId, _id, _text, out, calls) =>
      (calls.length === 0) === (out._tag === "Failure" && out.error._tag === "AmountUnreadable"),
    readsFirst: (accountId, _id, _text, _out, calls) => calls.length === 0 || (calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId),
    refusedOnlyAfterReading: (_accountId, _id, _text, out, calls) =>
      !(out._tag === "Failure" && out.error._tag === "DepositRefused") || (calls.length === 1 && calls.at(0)?.op === "read"),
    paidWritesOneDeposit: (accountId, id, _text, out, calls) => {
      if (out._tag !== "Success") return true
      const last = calls.at(-1)
      return (
        calls.filter((c) => c.op === "append").length === 1 &&
        last !== undefined &&
        last.op === "append" &&
        last.args[0] === accountId &&
        last.args[1].kind === "deposited" &&
        last.args[1].id === id
      )
    },
  },
})

export const imported = computation<Ops>()(importDeposits, {
  ensures: {
    writesOnlyDepositsHere: (accountId, _json, _out, calls) =>
      calls.every((c) => c.op === "append" && c.args[0] === accountId && c.args[1].kind === "deposited"),
    countsWhatItWrote: (_accountId, _json, out, calls) => out._tag !== "Success" || out.value === calls.length,
    stopsAtAFailedWrite: (_accountId, _json, _out, calls) =>
      calls.filter((c) => c.outcome._tag === "Failure").length === 0 ||
      (calls.filter((c) => c.outcome._tag === "Failure").length === 1 && calls.at(-1)?.outcome._tag === "Failure"),
    // Its error is `unknown` (what `JSON.parse` threw, or the ledger's): a law can say where it failed, not with what.
    failsOnlyWhereItStopped: (_accountId, _json, out, calls) => out._tag !== "Failure" || calls.length === 0 || calls.at(-1)?.outcome._tag === "Failure",
  },
})

export const opened = computation<Ops>()(openWith, {
  ensures: {
    opensThenDeposits: (accountId, owner, id, amount, out, calls) => {
      if (out._tag !== "Success") return true
      const first = calls.at(0)
      const second = calls.at(1)
      return (
        calls.length === 2 &&
        first !== undefined &&
        first.op === "append" &&
        first.args[0] === accountId &&
        first.args[1].kind === "opened" &&
        first.args[1].owner === owner &&
        second !== undefined &&
        second.op === "append" &&
        second.args[0] === accountId &&
        second.args[1].kind === "deposited" &&
        second.args[1].id === id &&
        second.args[1].amount === amount
      )
    },
    stopsAtAFailedWrite: (_accountId, _owner, _id, _amount, out, calls) =>
      out._tag !== "Failure" || calls.length === 0 || (calls.at(-1)?.outcome._tag === "Failure" && calls.length <= 2),
    refusedWritesNothing: (_accountId, _owner, _id, amount, out, calls) => (amount <= 0n) === (out._tag === "Failure" && calls.length === 0),
  },
})

// The async programs, whose ledger is their first argument.
type Port = { ledger: LedgerPort }

export const balanced = plainComputation<Port, LedgerError>()(balanceOf, {
  ensures: {
    readsOnce: (_, accountId, _out, calls) => calls.length === 1 && calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId,
    theFoldsBalance: (_, _accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      return out._tag === "Success" && out.value === accountOf(read.outcome.value).balance
    },
    failsAsTheReadFails: (_, _accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.outcome._tag !== "Failure") return true
      return out._tag === "Failure" && out.error._tag === read.outcome.error._tag
    },
  },
})

export const copied = plainComputation<Port, LedgerError>()(copyDeposits, {
  ensures: {
    readsTheSourceFirst: (_, from, _to, _out, calls) => calls.at(0)?.op === "read" && calls.at(0)?.args[0] === from,
    writesOnlyDepositsToTheTarget: (_, _from, to, _out, calls) =>
      calls.slice(1).every((c) => c.op === "append" && c.args[0] === to && c.args[1].kind === "deposited"),
    countsWhatItWrote: (_, _from, _to, out, calls) => out._tag !== "Success" || out.value === calls.slice(1).length,
    stopsAtAFailure: (_, _from, _to, _out, calls) =>
      calls.filter((c) => c.outcome._tag === "Failure").length === 0 ||
      (calls.filter((c) => c.outcome._tag === "Failure").length === 1 && calls.at(-1)?.outcome._tag === "Failure"),
  },
})
