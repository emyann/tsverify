// Steps inside an expression and a loop of steps, as plain TypeScript writes
// them: async, the ledger given as an interface, `await` where the Effect
// programs `yield*`. No Effect anywhere: the core reads both the same way.
import { accountOf } from "./account.ts"
import type { LedgerPort } from "./withdraw.async.ts"

/** The balance the account's ledger folds to. */
export const balanceOf = async (ledger: LedgerPort, accountId: string) => accountOf(await ledger.read(accountId)).balance

/** Copies every deposit of one account's ledger into another's, in order, and says how many it wrote; a failed read or write stops the copy there. */
export const copyDeposits = async (ledger: LedgerPort, from: string, to: string): Promise<number> => {
  const entries = await ledger.read(from)
  for (const e of entries) if (e.kind === "deposited") await ledger.append(to, e)
  return entries.filter((e) => e.kind === "deposited").length
}
