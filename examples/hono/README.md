# A users API in Hono, built twice from one set of laws

`GET /users/:id` answers a user; `PATCH /users/:id` with `{ "name": ... }` renames one.

```text
users.ts              shared: a user, the replies, the check of a request's body
laws.ts               shared: what each handler must do, written once
basic/                the handlers as async functions, handed the store
  store.ts              the store, an interface of async methods
  handlers.spec.ts      the laws, given an async handler's signature
  handlers.ts           the handlers, typed by their specs
  app.ts                the Hono app that calls them
with-effect/          the handlers as Effect programs, requiring the store
  store.ts              the store, an Effect service
  handlers.spec.ts      the laws, given an Effect program's signature
  handlers.ts           the handlers, typed by their specs
  app.ts                the Hono app that runs them
```

## The laws, and the specs

A spec is a signature and the laws it holds. The laws are what the API means, and are the same for every build:
`laws.ts` writes them once, each over the request's values, the handler's outcome (a reply, or the store's failure) and
the calls the handler made to the store. An empty name is a 400 that touches nothing; the user asked for is read first;
a user not found is a 404 and nothing is written; a 200 is the user read, renamed, written once and sent back as
written; a store that fails ends the handler with that failure.

The signature is each build's own. An async handler is handed the store as an argument, `(users, id) =>
Promise<Reply>`; an Effect program requires it as a service, `(id) => Effect<Reply, StoreDown, Users>`. So each folder's
`handlers.spec.ts` gives the shared laws its signature, and its `handlers.ts` takes its types from there
(`Implementation<typeof GetUserSpec>`). Nothing at the top imports either folder, nor `effect`, nor `hono`: a third
build, over another store or another library, would be a folder beside these two.

The routes are not verified. They are Hono's API (`c.req`, `c.json`), which the verifier does not read, so a route only
reads the request and writes the reply, and `test/hono.test.ts` runs both apps.

## Run it

From the repository's root:

```sh
npm run verify -- examples/hono                                   # 16 laws, proved in both builds
node --conditions=tsverify-source --test test/hono.test.ts        # also: planted bugs caught, both apps run through Hono
```
