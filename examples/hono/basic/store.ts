// The store, as the basic build's handlers are given it: an interface whose
// methods are async, each an operation the verifier records.
import type { Rejects } from "@emyann/tsverify"
import type { User } from "../users.ts"

export class StoreDown extends Error {
  readonly _tag = "StoreDown" as const
}

/** Where users are kept. */
export interface UsersPort {
  readonly get: (id: string) => Rejects<User | undefined, StoreDown>
  readonly put: (user: User) => Rejects<void, StoreDown>
}
