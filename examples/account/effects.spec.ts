// The laws of the account's other programs, over their outcome and the calls
// they made.
import { assume } from "tsverify"
import { computation } from "tsverify/effect"
import { accountOf } from "./account.ts"
import { balanceOf, balanceOrZero, deposit, depositRefusalOf, doubledBalance } from "./effects.ts"
import type { LedgerShape } from "./withdraw.ts"

/** The ledger's fold, pure (checked from its source); its own laws are proved apart (`account.spec.ts`). */
export const accountOfIsPure = assume(accountOf, { pure: true })

type Ops = { ledger: LedgerShape }

export const balance = computation<Ops>()(balanceOf, {
  ensures: {
    readsOnce: (accountId, _out, calls) => calls.length === 1 && calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId,
    theFoldsBalance: (_accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      return out._tag === "Success" && out.value === accountOf(read.outcome.value).balance
    },
    failsAsTheReadFails: (_accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.outcome._tag !== "Failure") return true
      return out._tag === "Failure" && out.error._tag === read.outcome.error._tag
    },
  },
})

export const balanceOrNothing = computation<Ops>()(balanceOrZero, {
  ensures: {
    neverFails: (_accountId, out) => out._tag === "Success",
    zeroWhenUnreadable: (_accountId, out, calls) => {
      const read = calls.at(0)
      return read === undefined || read.outcome._tag !== "Failure" || (out._tag === "Success" && out.value === 0n)
    },
    theFoldsBalanceOtherwise: (_accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      return out._tag === "Success" && out.value === accountOf(read.outcome.value).balance
    },
  },
})

export const doubled = computation<Ops>()(doubledBalance, {
  ensures: {
    twiceTheFoldsBalance: (_accountId, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      const b = accountOf(read.outcome.value).balance
      return out._tag === "Success" && out.value === b + b
    },
  },
})

export const deposited = computation<Ops>()(deposit, {
  ensures: {
    readsFirst: (accountId, _id, _amount, _out, calls) => calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId,
    unreadableIsRefused: (_accountId, _id, _amount, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.outcome._tag !== "Failure") return true
      return out._tag === "Failure" && out.error._tag === "DepositRefused" && calls.length === 1
    },
    refusedWritesNothing: (_accountId, _id, _amount, out, calls) =>
      !(out._tag === "Failure" && out.error._tag === "DepositRefused") || !calls.some((c) => c.op === "append"),
    refusedExactlyWhenTheGuardSaysOrUnreadable: (_accountId, _id, amount, out, calls) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read") return true
      const refused = read.outcome._tag === "Failure" || depositRefusalOf(accountOf(read.outcome.value), amount) !== undefined
      return refused === (out._tag === "Failure" && out.error._tag === "DepositRefused")
    },
    paidWritesOneDeposit: (accountId, id, amount, out, calls) => {
      if (out._tag !== "Success") return true
      const last = calls.at(-1)
      return (
        calls.filter((c) => c.op === "append").length === 1 &&
        last !== undefined &&
        last.op === "append" &&
        last.args[0] === accountId &&
        last.args[1].kind === "deposited" &&
        last.args[1].id === id &&
        last.args[1].amount === amount
      )
    },
    writeFailureIsTheLedgers: (_accountId, _id, _amount, out, calls) => {
      const last = calls.at(-1)
      if (last === undefined || last.op !== "append" || last.outcome._tag !== "Failure") return true
      return out._tag === "Failure" && out.error._tag === "LedgerError"
    },
  },
})
