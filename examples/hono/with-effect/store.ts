// The store, as the Effect build's handlers require it: a service whose
// methods are Effects, each an operation the verifier records.
import { Context, Data, type Effect } from "effect"
import type { User } from "../users.ts"

export class StoreDown extends Data.TaggedError("StoreDown")<{}> {}

/** Where users are kept. */
export class Users extends Context.Service<
  Users,
  {
    readonly get: (id: string) => Effect.Effect<User | undefined, StoreDown>
    readonly put: (user: User) => Effect.Effect<void, StoreDown>
  }
>()("examples/hono/with-effect/Users") {}
