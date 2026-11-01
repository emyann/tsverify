// The laws of the account's other programs, over their outcome and the calls
// they made.
import { assume } from "@emyann/tsverify"
import { computation } from "@emyann/tsverify/effect"
import { accountOf } from "./account.ts"
import { balanceOf, balanceOrZero, deposit, depositRefusalOf, doubledBalance } from "./effects.ts"
import type { LedgerShape } from "./withdraw.ts"

/** The ledger's fold, pure (checked from its source); its own laws are proved apart (`account.contract.ts`). */
export const accountOfIsPure = assume(accountOf, { pure: true })

type Ops = { ledger: LedgerShape }

export const balance = computation<Ops>()(balanceOf, {
  ensures: {
    readsOnce: ({ input: [accountId], calls }) => calls.length === 1 && calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId,
    theFoldsBalance: ({ output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      return output._tag === "Success" && output.value === accountOf(read.outcome.value).balance
    },
    failsAsTheReadFails: ({ output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.outcome._tag !== "Failure") return true
      return output._tag === "Failure" && output.error._tag === read.outcome.error._tag
    },
  },
})

export const balanceOrNothing = computation<Ops>()(balanceOrZero, {
  ensures: {
    neverFails: ({ output }) => output._tag === "Success",
    zeroWhenUnreadable: ({ output, calls }) => {
      const read = calls.at(0)
      return read === undefined || read.outcome._tag !== "Failure" || (output._tag === "Success" && output.value === 0n)
    },
    theFoldsBalanceOtherwise: ({ output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      return output._tag === "Success" && output.value === accountOf(read.outcome.value).balance
    },
  },
})

export const doubled = computation<Ops>()(doubledBalance, {
  ensures: {
    twiceTheFoldsBalance: ({ output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read" || read.outcome._tag !== "Success") return true
      const b = accountOf(read.outcome.value).balance
      return output._tag === "Success" && output.value === b + b
    },
  },
})

export const deposited = computation<Ops>()(deposit, {
  ensures: {
    readsFirst: ({ input: [accountId], calls }) => calls.at(0)?.op === "read" && calls.at(0)?.args[0] === accountId,
    unreadableIsRefused: ({ output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.outcome._tag !== "Failure") return true
      return output._tag === "Failure" && output.error._tag === "DepositRefused" && calls.length === 1
    },
    refusedWritesNothing: ({ output, calls }) =>
      !(output._tag === "Failure" && output.error._tag === "DepositRefused") || !calls.some((c) => c.op === "append"),
    refusedExactlyWhenTheGuardSaysOrUnreadable: ({ input: [, , amount], output, calls }) => {
      const read = calls.at(0)
      if (read === undefined || read.op !== "read") return true
      const refused = read.outcome._tag === "Failure" || depositRefusalOf(accountOf(read.outcome.value), amount) !== undefined
      return refused === (output._tag === "Failure" && output.error._tag === "DepositRefused")
    },
    paidWritesOneDeposit: ({ input: [accountId, id, amount], output, calls }) => {
      if (output._tag !== "Success") return true
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
    writeFailureIsTheLedgers: ({ output, calls }) => {
      const last = calls.at(-1)
      if (last === undefined || last.op !== "append" || last.outcome._tag !== "Failure") return true
      return output._tag === "Failure" && output.error._tag === "LedgerError"
    },
  },
})
