// A users API's domain: a user, the reply a handler gives, and the store an
// async handler is given. The Effect handlers' store is in users.effect.ts.
import type { Rejects } from "tsverify"

export interface User {
  readonly id: string
  readonly name: string
}

/** What a handler answers: the status, and the body Hono sends as JSON. */
export type Reply =
  | { readonly status: 200; readonly body: User }
  | { readonly status: 400 | 404; readonly body: { readonly error: string } }

export const ok = (user: User): Reply => ({ status: 200, body: user })
export const notFound = (): Reply => ({ status: 404, body: { error: "no such user" } })
export const emptyName = (): Reply => ({ status: 400, body: { error: "a name is not empty" } })

export class StoreDown extends Error {
  readonly _tag = "StoreDown" as const
}

/** Where users are kept, for the async handlers: each method an operation the verifier records. */
export interface UsersPort {
  readonly get: (id: string) => Rejects<User | undefined, StoreDown>
  readonly put: (user: User) => Rejects<void, StoreDown>
}
