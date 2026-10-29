// The users API in Hono, its handlers Effect programs: each route runs one,
// the store given as a layer, and turns the store's failure into a 503. As in
// the basic build, the routes are Hono's and run by the test; the programs are
// verified.
import { Effect, Layer } from "effect"
import { Hono } from "hono"
import { nameIn, type Reply } from "../users.ts"
import { getUser, renameUser } from "./handlers.ts"
import { type StoreDown, Users } from "./store.ts"

const down = { status: 503, body: { error: "the store is down" } } as const

export const appOf = (users: Users["Service"]) => {
  const layer = Layer.succeed(Users)(Users.of(users))
  const run = (program: Effect.Effect<Reply, StoreDown, Users>) =>
    Effect.runPromise(
      program.pipe(
        Effect.catchTag("StoreDown", () => Effect.succeed(down)),
        Effect.provide(layer),
      ),
    )
  return new Hono()
    .get("/users/:id", async (c) => {
      const reply = await run(getUser(c.req.param("id")))
      return c.json(reply.body, reply.status)
    })
    .patch("/users/:id", async (c) => {
      const name = nameIn(await c.req.json().catch(() => undefined))
      if (name === undefined) return c.json({ error: 'the body is { "name": string }' }, 400)
      const reply = await run(renameUser(c.req.param("id"), name))
      return c.json(reply.body, reply.status)
    })
}
