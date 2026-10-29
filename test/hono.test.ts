// A users API in Hono (examples/hono), built twice from one set of laws: the
// basic build's handlers are async functions handed a store, the with-effect
// build's are Effect programs requiring it as a service. Each build's specs
// give the shared laws (laws.ts, imported through a namespace) its signature.
// Shown: every law proved in both builds; a bug planted in each handler caught
// in both; and the real apps, run through Hono against a store that keeps what
// it is asked, answer the same requests the same way, the laws holding of
// every run a handler made.
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { Effect } from "effect"
import { appOf as basicApp } from "../examples/hono/basic/app.ts"
import { StoreDown, type UsersPort } from "../examples/hono/basic/store.ts"
import * as laws from "../examples/hono/laws.ts"
import type { UsersCall } from "../examples/hono/laws.ts"
import type { User } from "../examples/hono/users.ts"
import { appOf as effectApp } from "../examples/hono/with-effect/app.ts"
import * as Fx from "../examples/hono/with-effect/store.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const dir = path.join(root, "examples/hono")
const tsconfig = path.join(root, "tsconfig.json")
const BUILDS = ["basic", "with-effect"] as const
const handlers = Object.fromEntries(BUILDS.map((b) => [b, path.join(dir, b, "handlers.ts")]))
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("the handlers, verified", () => {
  it("every file of the example type-checks", () => {
    const files = [
      "users.ts",
      "laws.ts",
      ...BUILDS.flatMap((b) => ["store.ts", "handlers.contract.ts", "handlers.ts", "app.ts"].map((f) => `${b}/${f}`)),
    ].map((f) => path.join(dir, f))
    const project = loadProject(files, tsconfig)
    for (const f of files) assert.deepEqual(diagnostics(project, f), [], f)
  })

  for (const [kind, file] of Object.entries(handlers))
    for (const name of ["getUser", "renameUser"])
      it(`${kind} ${name}: every law proved, and both a reply and the store's failure reachable`, async () => {
        const v = await verify(z3, loadProject([file], tsconfig), file, name)
        assert.equal(v.unsupported, undefined)
        assert.ok(v.laws.length >= 3 && v.laws.every((l) => l.status === "proved"), JSON.stringify(statuses(v)))
        const reached = v.cover.filter((c) => c.status === "reachable").map((c) => c.value)
        // An Effect program's failures are reached tag by tag; an async function's as one, `Failure`.
        assert.ok(
          reached.includes("Success") && reached.includes(kind === "with-effect" ? "Failure StoreDown" : "Failure"),
          JSON.stringify(v.cover),
        )
      })
})

/** Bugs planted in both builds' handlers, each the same text in either: what it breaks, and the law that says so. */
const PLANTS = [
  {
    id: "H1",
    what: "refuses the wrong name",
    fn: "renameUser",
    find: 'if (name === "") return emptyName()',
    replace: 'if (name === " ") return emptyName()',
    law: "emptyNameTouchesNothing",
  },
  {
    id: "H2",
    what: "keeps the old name",
    fn: "renameUser",
    find: "{ ...user, name }",
    replace: "{ ...user, name: user.name }",
    law: "renamedAsWritten",
  },
  {
    id: "H3",
    what: "answers 404 for a user it found",
    fn: "getUser",
    find: "notFound() : ok(user)",
    replace: "notFound() : notFound()",
    law: "answersWhatItFound",
  },
] as const

describe("bugs planted in the handlers", () => {
  for (const p of PLANTS)
    for (const [kind, file] of Object.entries(handlers))
      it(`${p.id}, ${p.what}: caught in the ${kind} build by ${p.law}`, async () => {
        const text = readFileSync(file, "utf8")
        assert.equal(text.split(p.find).length - 1, 1, `${p.id}: \`${p.find}\` must occur once in ${file}`)
        const project = loadProject([file], tsconfig, new Map([[file, text.replace(p.find, p.replace)]]))
        assert.deepEqual(diagnostics(project, file), [])
        const v = await verify(z3, project, file, p.fn)
        assert.equal(statuses(v)[p.law], "counterexample", JSON.stringify(statuses(v)))
      })
})

/** A store that holds `users` and keeps every call it is asked, down for its reads or its writes when told to be. */
const keeping = (users: ReadonlyArray<User>, down: "get" | "put" | undefined) => {
  const held = new Map(users.map((u) => [u.id, u]))
  const calls: Array<UsersCall> = []
  const failure = { _tag: "Failure", error: { _tag: "StoreDown" } } as const
  /** What the store holds under `id`, or `false` when it is down. */
  const read = (id: string): User | undefined | false => {
    if (down === "get") return (calls.push({ op: "get", args: [id], outcome: failure }), false)
    const found = held.get(id)
    calls.push({ op: "get", args: [id], outcome: { _tag: "Success", value: found } })
    return found
  }
  /** Whether the store kept `user`: `false` when it is down. */
  const write = (user: User): boolean => {
    if (down === "put") return (calls.push({ op: "put", args: [user], outcome: failure }), false)
    held.set(user.id, user)
    calls.push({ op: "put", args: [user], outcome: { _tag: "Success", value: undefined } })
    return true
  }
  const port: UsersPort = {
    get: async (id) => {
      const found = read(id)
      if (found === false) throw new StoreDown()
      return found
    },
    put: async (user) => {
      if (!write(user)) throw new StoreDown()
    },
  }
  const service = Fx.Users.of({
    get: (id) => Effect.suspend(() => ((found) => (found === false ? Effect.fail(new Fx.StoreDown()) : Effect.succeed(found)))(read(id))),
    put: (user) => Effect.suspend(() => (write(user) ? Effect.void : Effect.fail(new Fx.StoreDown()))),
  })
  return { port, service, calls, held }
}

const ANN: User = { id: "a", name: "Ann" }
type Ask = { readonly method: "GET" | "PATCH"; readonly id: string; readonly body?: string; readonly down?: "get" | "put" }
const ASKS: ReadonlyArray<readonly [string, Ask, number]> = [
  ["a user found", { method: "GET", id: "a" }, 200],
  ["a user missing", { method: "GET", id: "b" }, 404],
  ["a rename", { method: "PATCH", id: "a", body: '{"name":"Bea"}' }, 200],
  ["an empty name", { method: "PATCH", id: "a", body: '{"name":""}' }, 400],
  ["a rename of a user missing", { method: "PATCH", id: "b", body: '{"name":"Bea"}' }, 404],
  ["a body that is no name", { method: "PATCH", id: "a", body: "nope" }, 400],
  ["a store down on the read", { method: "GET", id: "a", down: "get" }, 503],
  ["a store down on the write", { method: "PATCH", id: "a", body: '{"name":"Bea"}', down: "put" }, 503],
]

describe("the apps, run through Hono", () => {
  for (const [what, ask, status] of ASKS)
    it(`${what}: ${status} from both apps, the store asked the same, the laws holding of the run`, async () => {
      const answers = []
      for (const make of [(s: ReturnType<typeof keeping>) => basicApp(s.port), (s: ReturnType<typeof keeping>) => effectApp(s.service)]) {
        const store = keeping([ANN], ask.down)
        const res = await make(store).request(`/users/${ask.id}`, {
          method: ask.method,
          ...(ask.body === undefined ? {} : { body: ask.body }),
        })
        const body = (await res.json()) as unknown
        answers.push({ status: res.status, body, calls: store.calls, held: [...store.held.values()] })
        assert.equal(res.status, status, JSON.stringify(body))
        // The handler's outcome, as its laws read it: a 503 is the store's failure passed through, any other reply its own.
        type Out = Parameters<typeof laws.readsTheUserOnce>[1]
        const out = (
          res.status === 503 ? { _tag: "Failure", error: { _tag: "StoreDown" } } : { _tag: "Success", value: { status: res.status, body } }
        ) as Out
        const name = ask.body === undefined ? undefined : (JSON.parse(ask.body.startsWith("{") ? ask.body : "{}") as { name?: string }).name
        if (ask.method === "GET")
          for (const law of [laws.readsTheUserOnce, laws.answersWhatItFound, laws.getFailsAsTheStoreFails])
            assert.ok(law(ask.id, out, store.calls), `${law.name} broken`)
        else if (name !== undefined)
          for (const law of [
            laws.emptyNameTouchesNothing,
            laws.readsTheUserFirst,
            laws.missingWritesNothing,
            laws.renamedAsWritten,
            laws.renameFailsAsTheStoreFails,
          ])
            assert.ok(law(ask.id, name, out, store.calls), `${law.name} broken`)
        else assert.deepEqual(store.calls, [], "a body that is no name reaches no handler")
      }
      assert.deepEqual(answers[0], answers[1])
    })
})
