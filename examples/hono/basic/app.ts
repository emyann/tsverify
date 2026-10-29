// The users API in Hono. A route reads the request and writes the reply; what
// to answer is the handler's, verified against its spec. The route itself is
// not verified: it is Hono's API (`c.req`, `c.json`), which the verifier does
// not read, so it is kept to reading and writing, and checked by running it
// (test/hono.test.ts).
import { Hono } from "hono"
import { nameIn } from "../users.ts"
import { getUser, renameUser } from "./handlers.ts"
import { StoreDown, type UsersPort } from "./store.ts"

export const appOf = (users: UsersPort) =>
  new Hono()
    .get("/users/:id", async (c) => {
      const reply = await getUser(users, c.req.param("id"))
      return c.json(reply.body, reply.status)
    })
    .patch("/users/:id", async (c) => {
      const name = nameIn(await c.req.json().catch(() => undefined))
      if (name === undefined) return c.json({ error: 'the body is { "name": string }' }, 400)
      const reply = await renameUser(users, c.req.param("id"), name)
      return c.json(reply.body, reply.status)
    })
    .onError((err, c) => (err instanceof StoreDown ? c.json({ error: "the store is down" }, 503) : c.json({ error: "internal" }, 500)))
