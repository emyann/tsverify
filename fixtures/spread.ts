// Object spreads: a key the spread value's type requires is read from it, and
// a key written after the spread overrides it; a key it may lack is refused, since what is spread
// may hold it or not whatever its type says. `test/spread.test.ts` asks each.
import { contract } from "../src/contract.ts"

interface User {
  readonly id: string
  readonly name: string
}

export const renamed = contract((user: User, name: string): User => ({ ...user, name }), {
  ensures: {
    keepsItsId: ({ input: [user], output }) => output.id === user.id,
    takesTheName: ({ input: [, name], output }) => output.name === name,
  },
})

interface Admin {
  readonly id: string
  readonly role: "admin"
}

/** A key every member of a union requires. */
export const eitherId = contract((who: User | Admin): string => ({ ...who }).id, {
  ensures: { sameId: ({ input: [who], output }) => output === who.id },
})

/** A key the spread may lack: what it holds depends on whether it is there. */
export const optionalKey = contract((options: { readonly retries?: bigint }): bigint => ({ retries: 3n, ...options }).retries ?? 0n, {
  ensures: { atMostThree: ({ output }) => output >= 0n },
})
