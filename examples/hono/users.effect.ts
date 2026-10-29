// The same store, as an Effect service, for the Effect handlers.
import { Context, Data, type Effect } from "effect"
import type { User } from "./users.ts"

export class StoreDown extends Data.TaggedError("StoreDown")<{}> {}

export class Users extends Context.Service<
  Users,
  {
    readonly get: (id: string) => Effect.Effect<User | undefined, StoreDown>
    readonly put: (user: User) => Effect.Effect<void, StoreDown>
  }
>()("examples/hono/Users") {}
