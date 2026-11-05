// The release tool (`tools/release.ts`) and the workflows that run it. The pure rules are called directly: which tags are releases,
// the bump a set of labels gives, the next version, and the version written into the three files a release moves. Each verb is run
// as `node tools/release.ts <verb>` in a scratch repository whose `origin` is a local bare repository, so git is real and stubbed only
// at its remote, with a stub `gh` and a stub `npm` first on PATH: each logs its calls and answers from a state file. The stub
// `npm stage publish` keeps the staged versions in its state and answers as npm 11.21.2 does: `+ <name>@<v> (staged with id <id>)`,
// and E409 `Cannot stage previously published version` for a version staged already. What is asserted is the exit code, the calls
// made, the refs and files git holds, and facts (ids, commands, URLs) by `includes`, never a sentence.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, describe, it } from "node:test"
import { bump, LABELS, nextVersion, NPM_PIN, releaseTag, withVersion } from "../tools/release.ts"

const root = path.resolve(import.meta.dirname, "..")
const TOOL = path.join(root, "tools", "release.ts")
const read = (file: string) => readFileSync(path.join(root, file), "utf8")

describe("the release rules", () => {
  it("a release is a tag vX.Y.Z and nothing else", () => {
    assert.equal(releaseTag("v0.7.0"), "0.7.0")
    assert.equal(releaseTag("v1.2.3"), "1.2.3")
    for (const tag of ["v1", "v1.2", "1.2.3", "v1.2.3-rc.1", "legacy/v1.0.0", "xv1.2.3"]) assert.equal(releaseTag(tag), undefined, tag)
  })

  it("the bump is the highest a label gives, and nothing for internal, an unknown label or none", () => {
    assert.equal(bump(["breaking", "feature", "fix"]), "major")
    assert.equal(bump(["feature", "docs"]), "minor")
    assert.equal(bump(["fix"]), "patch")
    assert.equal(bump(["docs"]), "patch")
    assert.equal(bump(["internal", "dependencies"]), "none")
    assert.equal(bump([]), "none")
  })

  it("breaking is a minor while the major is 0, and a major from 1.0", () => {
    assert.equal(nextVersion("0.7.0", "major"), "0.8.0")
    assert.equal(nextVersion("1.4.2", "major"), "2.0.0")
    assert.equal(nextVersion("0.7.0", "minor"), "0.8.0")
    assert.equal(nextVersion("0.7.3", "minor"), "0.8.0")
    assert.equal(nextVersion("0.7.0", "patch"), "0.7.1")
    assert.equal(nextVersion("0.7.0", "none"), undefined)
  })

  it("the labels are five, in their order, each a colour GitHub takes and a description within its 100", () => {
    assert.deepEqual(
      LABELS.map((l) => [l.name, l.bump]),
      [
        ["breaking", "major"],
        ["feature", "minor"],
        ["fix", "patch"],
        ["docs", "patch"],
        ["internal", "none"],
      ],
    )
    for (const l of LABELS) {
      assert.match(l.color, /^[0-9a-f]{6}$/)
      assert.ok(l.description.length > 0 && l.description.length <= 100, l.name)
    }
  })

  it("the version moves in the four places Release 0.7.0 moved it, and nowhere else", () => {
    const files = { packageJson: read("package.json"), packageLock: read("package-lock.json"), readme: read("README.md") }
    const from = (JSON.parse(files.packageJson) as { version: string }).version
    const moved = withVersion(files, "9.8.7")
    const changed = (a: string, b: string) => {
      const [x, y] = [a.split("\n"), b.split("\n")]
      assert.equal(x.length, y.length)
      return x.flatMap((line, i): [string, string][] => (line === y[i] ? [] : [[line, y[i]!]]))
    }
    const lines = [
      ...changed(files.packageJson, moved.packageJson),
      ...changed(files.packageLock, moved.packageLock),
      ...changed(files.readme, moved.readme),
    ]
    assert.equal(lines.length, 4)
    for (const [was, now] of lines) assert.equal(now, was.replace(from, "9.8.7"))
  })

  it("REFUSED: a README whose version line is missing or repeated", () => {
    const files = { packageJson: read("package.json"), packageLock: read("package-lock.json"), readme: read("README.md") }
    const line = /A prototype: version \d+\.\d+\.\d+/.exec(files.readme)![0]
    assert.throws(() => withVersion({ ...files, readme: files.readme.replace(line, "A prototype") }, "0.8.0"))
    assert.throws(() => withVersion({ ...files, readme: `${files.readme}\n${line}\n` }, "0.8.0"))
  })

  it("REFUSED: a JSON file npm did not lay out as the tool writes it", () => {
    const files = { packageJson: read("package.json"), packageLock: read("package-lock.json"), readme: read("README.md") }
    const fourSpaces = `${JSON.stringify(JSON.parse(files.packageJson), null, 4)}\n`
    assert.throws(() => withVersion({ ...files, packageJson: fourSpaces }, "0.8.0"))
  })

  it("REFUSED: a lockfile with no root package to move", () => {
    const files = { packageJson: read("package.json"), packageLock: read("package-lock.json"), readme: read("README.md") }
    const lock = JSON.parse(files.packageLock) as { packages: Record<string, unknown> }
    delete lock.packages[""]
    assert.throws(() => withVersion({ ...files, packageLock: `${JSON.stringify(lock, null, 2)}\n` }, "0.8.0"))
  })
})

// The stubs, CommonJS (their folder's package.json says so). Each appends its argv to STUB_LOG and answers from STUB_STATE; a call it
// has no answer for exits 9, so the tool cannot make a call the tests do not see.
const STUB_GH = `
const fs = require("node:fs")
const { execFileSync } = require("node:child_process")
const args = process.argv.slice(2)
const stdin = args.includes("-") ? fs.readFileSync(0, "utf8") : undefined
fs.appendFileSync(process.env.STUB_LOG, JSON.stringify({ bin: "gh", args, stdin }) + "\\n")
const state = JSON.parse(fs.readFileSync(process.env.STUB_STATE, "utf8"))
const save = () => fs.writeFileSync(process.env.STUB_STATE, JSON.stringify(state))
const flag = (name) => { const i = args.indexOf(name); return i < 0 ? undefined : args[i + 1] }
const field = (key) => { for (let i = 0; i < args.length - 1; i++) if (args[i] === "-f" && args[i + 1].startsWith(key + "=")) return args[i + 1].slice(key.length + 1) }
const print = (value) => process.stdout.write(JSON.stringify(value))
const fail = (text, code = 1) => { process.stderr.write(text); process.exit(code) }
const releaseHead = () => execFileSync("git", ["ls-remote", "origin", "refs/heads/release"], { encoding: "utf8" }).split("\\t")[0]
if (args[0] === "api") {
  const method = flag("-X")
  const [route, query = ""] = args[args.indexOf("-X") + 2].split("?")
  const q = new URLSearchParams(query)
  let m
  if (method === "GET" && route === "repos/{owner}/{repo}/labels") print(Number(q.get("page")) === 1 ? state.labels : [])
  else if (method === "GET" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/pulls\\/(\\d+)$/.exec(route))) {
    const p = state.pulls.find((each) => each.number === Number(m[1]))
    if (!p) fail("gh: Not Found (HTTP 404)")
    print(p)
  } else if (method === "GET" && route === "repos/{owner}/{repo}/pulls") {
    const per = Number(q.get("per_page")), page = Number(q.get("page") || 1), head = q.get("head")
    const all = state.pulls.filter((p) => (q.get("state") === "open" ? !p.merged_at && !p.closed : p.merged_at || p.closed) && (!head || head === "{owner}:" + p.head.ref))
    print(all.slice((page - 1) * per, page * per))
  } else if (method === "PATCH" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/pulls\\/(\\d+)$/.exec(route))) {
    const p = state.pulls.find((each) => each.number === Number(m[1]))
    if (field("state") === "closed") p.closed = true
    if (field("title") !== undefined) p.title = field("title")
    if (field("body") !== undefined) p.body = field("body")
    save(); print(p)
  } else if (method === "POST" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/issues\\/(\\d+)\\/labels$/.exec(route))) {
    const p = state.pulls.find((each) => each.number === Number(m[1]))
    p.labels.push({ name: field("labels[]") }); save(); print(p.labels)
  } else if (method === "GET" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/actions\\/workflows\\/([^/]+)\\/runs$/.exec(route))) {
    const runs = (state.runs || []).filter((run) => run.file === m[1] && run.head === q.get("head_sha") && q.get("event") === "workflow_dispatch")
    print({ total_count: runs.length, workflow_runs: runs })
  } else if (method === "POST" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/statuses\\/([0-9a-f]{40})$/.exec(route))) print({})
  else if (method === "POST" && route === "repos/{owner}/{repo}/releases/generate-notes") print({ name: field("tag_name"), body: "## Features\\n* a feature" })
  else if (method === "GET" && (m = /^repos\\/\\{owner\\}\\/\\{repo\\}\\/releases\\/tags\\/(.+)$/.exec(route))) {
    if (!(state.releases || []).includes(m[1])) fail("gh: Not Found (HTTP 404)")
    print({ tag_name: m[1] })
  } else fail("stub gh: no answer for " + args.join(" "), 9)
  process.exit(0)
}
if (args[0] === "label" && args[1] === "create") {
  state.labels = state.labels.filter((l) => l.name !== args[2])
  state.labels.push({ name: args[2], color: flag("--color"), description: flag("--description") })
  save(); process.exit(0)
}
if (args[0] === "pr" && args[1] === "create") {
  if (state.createRefused) fail("pull request create failed: GraphQL: GitHub Actions is not permitted to create or approve pull requests (createPullRequest)")
  const number = state.next++
  state.pulls.push({ number, title: flag("--title"), body: stdin, labels: [], merged_at: null, head: { ref: flag("--head"), sha: releaseHead() } })
  save(); process.stdout.write("https://github.com/emyann/tsverify/pull/" + number + "\\n"); process.exit(0)
}
if (args[0] === "release" && args[1] === "create") { state.releases = [...(state.releases || []), args[2]]; save(); process.exit(0) }
if (args[0] === "workflow" && args[1] === "run") {
  const ref = flag("--ref")
  const head = ref === "release" ? releaseHead() : ref
  state.runs = [...(state.runs || []), { file: args[2], head, status: "queued", conclusion: null }]
  save(); process.exit(0)
}
fail("stub gh: no answer for " + args.join(" "), 9)
`

/** The stage id the stub npm answers, in the shape npm's API gives one. */
const STAGE_ID = "f8e7a45b-7a5f-4f31-8e6d-9dd1c6ef38c0"

const STUB_NPM = `
const STAGE_ID = "${STAGE_ID}"
const fs = require("node:fs")
const args = process.argv.slice(2)
fs.appendFileSync(process.env.STUB_LOG, JSON.stringify({ bin: "npm", args }) + "\\n")
const state = JSON.parse(fs.readFileSync(process.env.STUB_STATE, "utf8"))
const fail = (text, code = 1) => { process.stderr.write(text); process.exit(code) }
if (args[0] === "view") {
  const [, version] = args[1].split(/(?<=.)@/)
  if (!(state.npm || []).includes(version)) fail("npm error code E404\\nnpm error 404 No match found for version " + version + "\\n")
  process.stdout.write(version + "\\n"); process.exit(0)
}
if (args[0] === "--version") { process.stdout.write((state.npmVersion || process.env.STUB_NPM_PIN) + "\\n"); process.exit(0) }
if (args[0] === "stage" && args[1] === "publish") {
  if (state.stageFails) fail(state.stageFails)
  const pkg = JSON.parse(fs.readFileSync("package.json", "utf8"))
  state.staged = state.staged || []
  if (state.staged.includes(pkg.version) || (state.npm || []).includes(pkg.version))
    fail("npm error code E409\\nnpm error 409 Conflict - POST https://registry.npmjs.org/-/stage/package/@emyann%2ftsverify - Cannot stage previously published version \\"" + pkg.version + "\\"\\n")
  state.staged.push(pkg.version)
  fs.writeFileSync(process.env.STUB_STATE, JSON.stringify(state))
  process.stdout.write("+ " + pkg.name + "@" + pkg.version + " (staged with id " + STAGE_ID + ")\\n")
  process.exit(0)
}
fail("stub npm: no answer for " + args.join(" "), 9)
`

type Pull = {
  number: number
  title: string
  body?: string
  labels: { name: string }[]
  merged_at: string | null
  merge_commit_sha?: string | null
  closed?: boolean
  head: { ref: string; sha?: string }
}
type Run = { file: string; head: string; status: string; conclusion: string | null }
type State = {
  pulls: Pull[]
  labels: { name: string; color: string; description: string }[]
  next: number
  runs?: Run[]
  releases?: string[]
  createRefused?: boolean
  npm?: string[]
  staged?: string[]
  npmVersion?: string
  stageFails?: string
}
type Call = { bin: "gh" | "npm"; args: string[]; stdin?: string }

const scratches: string[] = []
after(() => {
  for (const dir of scratches) rmSync(dir, { recursive: true, force: true })
})

const README = (version: string) => `# tsverify\n\nSome words.\n\nA prototype: version ${version}, and its API may change.\n`

/**
 * A scratch world: `origin` (bare), `seed` (where main is written, as GitHub's merges would), `clone` (where the tool runs, as a
 * workflow's checkout), the stubs' state and log. The environment the tool gets is set here whole, so nothing a session or a runner
 * exports reaches it.
 */
const world = () => {
  mkdirSync(path.join(root, ".docs"), { recursive: true })
  const dir = mkdtempSync(path.join(root, ".docs", "release-"))
  scratches.push(dir)
  const [origin, seed, clone, bin] = ["origin.git", "seed", "clone", "bin"].map((name) => path.join(dir, name)) as [
    string,
    string,
    string,
    string,
  ]
  const env: Record<string, string> = {
    PATH: `${bin}${path.delimiter}${process.env.PATH ?? ""}`,
    HOME: dir,
    GIT_CONFIG_NOSYSTEM: "1",
    GIT_CONFIG_GLOBAL: path.join(dir, "gitconfig"),
    GIT_AUTHOR_NAME: "t",
    GIT_AUTHOR_EMAIL: "t@t",
    GIT_COMMITTER_NAME: "t",
    GIT_COMMITTER_EMAIL: "t@t",
    STUB_LOG: path.join(dir, "calls.log"),
    STUB_STATE: path.join(dir, "state.json"),
    STUB_NPM_PIN: NPM_PIN,
  }
  const git = (cwd: string, ...args: string[]): string => {
    const ran = spawnSync("git", args, { cwd, env, encoding: "utf8", timeout: 30_000 })
    assert.equal(ran.status, 0, `git ${args.join(" ")}: ${ran.stderr}`)
    return ran.stdout.trim()
  }
  mkdirSync(bin)
  writeFileSync(path.join(dir, "package.json"), '{ "type": "commonjs" }\n')
  writeFileSync(path.join(bin, "gh"), `#!${process.execPath}\n${STUB_GH}`, { mode: 0o755 })
  writeFileSync(path.join(bin, "npm"), `#!${process.execPath}\n${STUB_NPM}`, { mode: 0o755 })
  writeFileSync(env.GIT_CONFIG_GLOBAL!, "")
  git(dir, "init", "--quiet", "--bare", "-b", "main", origin)
  git(dir, "init", "--quiet", "-b", "main", seed)
  const json = (value: unknown) => `${JSON.stringify(value, null, 2)}\n`
  writeFileSync(path.join(seed, "package.json"), json({ name: "@emyann/tsverify", version: "0.7.0", type: "module" }))
  writeFileSync(
    path.join(seed, "package-lock.json"),
    json({
      name: "@emyann/tsverify",
      version: "0.7.0",
      lockfileVersion: 3,
      requires: true,
      packages: { "": { name: "@emyann/tsverify", version: "0.7.0" } },
    }),
  )
  writeFileSync(path.join(seed, "README.md"), README("0.7.0"))
  git(seed, "add", ".")
  git(seed, "commit", "--quiet", "-m", "Release 0.6.0")
  git(seed, "tag", "v0.6.0")
  git(seed, "commit", "--quiet", "--allow-empty", "-m", "Release 0.7.0")
  git(seed, "tag", "-a", "v0.7.0", "-m", "tsverify 0.7.0")
  git(seed, "tag", "legacy/v9.9.9")
  git(seed, "remote", "add", "origin", origin)
  git(seed, "push", "--quiet", "origin", "main", "--tags")
  git(dir, "clone", "--quiet", origin, clone)
  let n = 0
  /** A pull request merged into main: a commit on main, pushed. */
  const land = (): string => {
    n += 1
    writeFileSync(path.join(seed, `change-${n}.txt`), `${n}\n`)
    git(seed, "add", ".")
    git(seed, "commit", "--quiet", "-m", `change ${n}`)
    git(seed, "push", "--quiet", "origin", "main")
    return git(seed, "rev-parse", "HEAD")
  }
  /** The release branch merged into main with a merge commit, as GitHub's merge button makes it. */
  const mergeRelease = (): string => {
    git(seed, "fetch", "--quiet", "origin", "release")
    git(seed, "merge", "--quiet", "--no-ff", "-m", "Merge pull request #50 from emyann/release", "FETCH_HEAD")
    git(seed, "push", "--quiet", "origin", "main")
    return git(seed, "rev-parse", "HEAD")
  }
  const state = (value: State) => writeFileSync(env.STUB_STATE!, JSON.stringify(value))
  const now = (): State => JSON.parse(readFileSync(env.STUB_STATE!, "utf8")) as State
  const run = (verb: string, extra: Record<string, string> = {}, cwd = clone) => {
    rmSync(env.STUB_LOG!, { force: true })
    const ran = spawnSync(process.execPath, [TOOL, verb], { cwd, env: { ...env, ...extra }, encoding: "utf8", timeout: 60_000 })
    let calls: Call[] = []
    try {
      calls = readFileSync(env.STUB_LOG!, "utf8")
        .split("\n")
        .filter(Boolean)
        .map((line) => JSON.parse(line) as Call)
    } catch {
      calls = []
    }
    return { status: ran.status, out: `${ran.stdout}${ran.stderr}`, calls }
  }
  const remoteRef = (ref: string) => git(dir, "--git-dir", origin, "for-each-ref", "--format=%(objectname)", ref)
  return { dir, origin, seed, clone, git, land, mergeRelease, state, now, run, remoteRef }
}

const merged = (number: number, labels: string[], sha: string): Pull => ({
  number,
  title: `change ${number}`,
  labels: labels.map((name) => ({ name })),
  merged_at: "2026-11-01T00:00:00Z",
  merge_commit_sha: sha,
  head: { ref: `branch-${number}` },
})
const correctLabels = () => LABELS.map((l) => ({ name: l.name, color: l.color, description: l.description }))
const gh = (calls: Call[], ...prefix: string[]) =>
  calls.filter((c) => c.bin === "gh" && prefix.every((word, i) => c.args[i] === word)).map((c) => c.args)
const api = (calls: Call[], method: string, route: RegExp) =>
  calls.filter((c) => c.bin === "gh" && c.args[0] === "api" && c.args[2] === method && route.test(c.args[3] ?? ""))

describe("release.ts check", () => {
  const w = world()
  const pull = (labels: string[]): Pull => ({ ...merged(7, labels, ""), merged_at: null, head: { ref: "topic", sha: "a".repeat(40) } })

  it("REFUSED: no release label, or two, with the five named and the command that adds one", () => {
    for (const labels of [[], ["dependencies"], ["fix", "docs"]]) {
      w.state({ pulls: [pull(labels)], labels: [], next: 1 })
      const ran = w.run("check", { PR_NUMBER: "7" })
      assert.equal(ran.status, 1, JSON.stringify(labels))
      for (const l of LABELS) assert.ok(ran.out.includes(l.name), `names ${l.name}`)
      assert.ok(ran.out.includes("issues/7/labels"), "says how to add one")
    }
  })

  it("one release label passes, beside any other, and the check writes nothing", () => {
    w.state({ pulls: [pull(["feature", "dependencies"])], labels: [], next: 1 })
    const ran = w.run("check", { PR_NUMBER: "7" })
    assert.equal(ran.status, 0, ran.out)
    assert.ok(ran.calls.every((c) => c.args[0] === "api" && c.args[2] === "GET"))
  })

  it("REFUSED: a dispatched run whose commit is not the pull request's head", () => {
    w.state({ pulls: [pull(["fix"])], labels: [], next: 1 })
    assert.equal(w.run("check", { PR_NUMBER: "7", HEAD_SHA: "b".repeat(40) }).status, 1)
    assert.equal(w.run("check", { PR_NUMBER: "7", HEAD_SHA: "a".repeat(40) }).status, 0)
  })

  it("REFUSED: no pull request number", () => {
    assert.equal(w.run("check").status, 1)
  })
})

describe("release.ts labels", () => {
  it("makes the labels missing or drifted, and a rerun writes nothing", () => {
    const w = world()
    const labels = correctLabels().filter((l) => l.name !== "docs")
    labels[0] = { ...labels[0]!, color: "000000" }
    w.state({ pulls: [], labels: [...labels, { name: "bug", color: "d73a4a", description: "" }], next: 1 })
    const first = w.run("labels")
    assert.equal(first.status, 0, first.out)
    assert.deepEqual(
      gh(first.calls, "label", "create").map((args) => [args[2], args.includes("--force")]),
      [
        ["breaking", true],
        ["docs", true],
      ],
    )
    const second = w.run("labels")
    assert.equal(second.status, 0, second.out)
    assert.deepEqual(gh(second.calls, "label", "create"), [])
  })
})

describe("release.ts pr, tag and publish, one release from its first labelled merge to npm", () => {
  const w = world()
  let feature = ""
  let head = ""

  it("pr: a feature merged since v0.7.0 opens Release 0.8.0, from release, with its checks dispatched on its head", () => {
    feature = w.land()
    const internal = w.land()
    w.state({ pulls: [merged(1, ["feature"], feature), merged(2, ["internal"], internal)], labels: correctLabels(), next: 40 })
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    head = w.remoteRef("refs/heads/release")
    const main = w.remoteRef("refs/heads/main")
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "rev-parse", `${head}^`), main, "release is main plus one commit")
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "log", "-1", "--format=%s%n%an", head), "Release 0.8.0\ngithub-actions[bot]")
    assert.deepEqual(w.git(w.dir, "--git-dir", w.origin, "diff", "--name-only", main, head).split("\n"), [
      "README.md",
      "package-lock.json",
      "package.json",
    ])
    const pkg = JSON.parse(w.git(w.dir, "--git-dir", w.origin, "show", `${head}:package-lock.json`)) as {
      version: string
      packages: Record<string, { version: string }>
    }
    assert.equal(pkg.version, "0.8.0")
    assert.equal(pkg.packages[""]!.version, "0.8.0")
    assert.ok(w.git(w.dir, "--git-dir", w.origin, "show", `${head}:README.md`).includes("version 0.8.0"))

    const create = gh(ran.calls, "pr", "create")
    assert.equal(create.length, 1)
    const flag = (name: string) => create[0]![create[0]!.indexOf(name) + 1]
    assert.deepEqual([flag("--base"), flag("--head"), flag("--title")], ["main", "release", "Release 0.8.0"])
    const pr = w.now().pulls.find((p) => p.number === 40)!
    assert.deepEqual(
      pr.labels.map((l) => l.name),
      ["internal"],
    )
    const notes = api(ran.calls, "POST", /releases\/generate-notes$/)
    assert.equal(notes.length, 1)
    assert.ok(notes[0]!.args.includes("previous_tag_name=v0.7.0"))
    assert.ok(notes[0]!.args.includes("tag_name=v0.8.0"))
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [
      ["workflow", "run", "ci.yml", "--ref", "release"],
      ["workflow", "run", "release-label.yml", "--ref", "release", "-f", "pr=40"],
    ])
    const statuses = api(ran.calls, "POST", /statuses\//)
    assert.deepEqual(
      statuses.map((c) => [c.args[3], c.args.find((a) => a.startsWith("context=")), c.args.find((a) => a.startsWith("state="))]),
      [
        [`repos/{owner}/{repo}/statuses/${head}`, "context=ci", "state=pending"],
        [`repos/{owner}/{repo}/statuses/${head}`, "context=release-label", "state=pending"],
      ],
    )
  })

  it("pr, rerun with nothing new: no push, no new pull request, no dispatch while the dispatched runs stand", () => {
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    assert.equal(w.remoteRef("refs/heads/release"), head)
    assert.deepEqual(gh(ran.calls, "pr", "create"), [])
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [])
    assert.deepEqual(api(ran.calls, "POST", /statuses\//), [])
    assert.deepEqual(api(ran.calls, "POST", /issues\/\d+\/labels$/), [], "labelled internal already")
  })

  it("pr: a failed dispatched run is dispatched again", () => {
    const s = w.now()
    s.runs = s.runs!.map((r) => (r.file === "ci.yml" ? { ...r, status: "completed", conclusion: "failure" } : r))
    w.state(s)
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [["workflow", "run", "ci.yml", "--ref", "release"]])
  })

  it("pr: main moved, so release is rebuilt on it, and the open pull request updated, not opened again", () => {
    const fix = w.land()
    const s = w.now()
    s.pulls.push(merged(4, ["fix"], fix))
    w.state(s)
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    const moved = w.remoteRef("refs/heads/release")
    assert.notEqual(moved, head)
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "rev-parse", `${moved}^`), w.remoteRef("refs/heads/main"))
    assert.deepEqual(gh(ran.calls, "pr", "create"), [])
    assert.equal(gh(ran.calls, "workflow", "run").length, 2, "the new head gets its checks")
    head = moved
  })

  let tagged = ""
  it("tag: the release's merge gets the annotated tag v0.8.0, its release, and the publish dispatched on it", () => {
    tagged = w.mergeRelease()
    const ran = w.run("tag")
    assert.equal(ran.status, 0, ran.out)
    const tag = w.remoteRef("refs/tags/v0.8.0")
    assert.ok(tag, "the tag is on origin")
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "cat-file", "-t", tag), "tag", "annotated")
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "rev-parse", "v0.8.0^{commit}"), tagged, "on the merge commit")
    assert.equal(w.git(w.dir, "--git-dir", w.origin, "for-each-ref", "--format=%(contents:subject)", "refs/tags/v0.8.0"), "tsverify 0.8.0")
    const release = gh(ran.calls, "release", "create")
    assert.equal(release.length, 1)
    assert.equal(release[0]![2], "v0.8.0")
    assert.ok(release[0]!.includes("--verify-tag") && release[0]!.includes("--generate-notes"))
    assert.equal(release[0]![release[0]!.indexOf("--notes-start-tag") + 1], "v0.7.0")
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [["workflow", "run", "publish.yml", "--ref", "v0.8.0"]])
  })

  it("tag, rerun: no push, no release, no dispatch", () => {
    const ran = w.run("tag")
    assert.equal(ran.status, 0, ran.out)
    assert.deepEqual(gh(ran.calls, "release", "create"), [])
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [])
  })

  it("tag: a release missing for a tag this workflow made is made again, and the publish dispatched", () => {
    const s = w.now()
    s.releases = []
    w.state(s)
    const ran = w.run("tag")
    assert.equal(ran.status, 0, ran.out)
    assert.equal(gh(ran.calls, "release", "create").length, 1)
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [["workflow", "run", "publish.yml", "--ref", "v0.8.0"]])
  })

  it("tag: a tag a person made, with no GitHub release, is left alone", () => {
    const fresh = world()
    fresh.state({ pulls: [], labels: correctLabels(), next: 1, releases: [] })
    const ran = fresh.run("tag")
    assert.equal(ran.status, 0, ran.out)
    assert.deepEqual(gh(ran.calls, "release", "create"), [])
    assert.deepEqual(gh(ran.calls, "workflow", "run"), [])
  })

  it("pr, after the release: nothing labelled since v0.8.0, so the release pull request is closed and nothing pushed", () => {
    const s = w.now()
    s.pulls = s.pulls.map((p) => (p.number === 40 ? { ...p, merged_at: "2026-11-02T00:00:00Z", merge_commit_sha: tagged } : p))
    const internal = w.land()
    s.pulls.push(merged(5, ["internal"], internal), merged(6, [], w.land()), {
      ...merged(41, [], ""),
      merged_at: null,
      head: { ref: "release" },
    })
    w.state(s)
    const before = w.remoteRef("refs/heads/release")
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    assert.equal(w.remoteRef("refs/heads/release"), before, "nothing pushed")
    assert.equal(api(ran.calls, "PATCH", /pulls\/41$/).length, 1)
    assert.ok(api(ran.calls, "PATCH", /pulls\/41$/)[0]!.args.includes("state=closed"))
    assert.ok(w.now().pulls.find((p) => p.number === 41)!.closed)
  })

  const publishIn = (ref: string) => {
    const at = path.join(w.dir, `publish-${ref}`)
    w.git(w.dir, "clone", "--quiet", w.origin, at)
    w.git(at, "checkout", "--quiet", ref)
    return at
  }

  /** The npm calls a run made whose args start with `words`. */
  const npm = (calls: Call[], ...words: string[]) =>
    calls.filter((c) => c.bin === "npm" && words.every((word, i) => c.args[i] === word)).map((c) => c.args)
  /** A run of publish on `at`, with a scratch step summary: what it printed, and the summary GitHub would show. */
  let summaries = 0
  const publish = (at: string, ref = "refs/tags/v0.8.0") => {
    const file = path.join(w.dir, `summary-${(summaries += 1)}.md`)
    const ran = w.run("publish", { GITHUB_REF: ref, GITHUB_STEP_SUMMARY: file }, at)
    const summary = readFileSync(file, { encoding: "utf8", flag: "a+" })
    assert.deepEqual([...npm(ran.calls, "stage", "approve"), ...npm(ran.calls, "stage", "reject")], [], "approval is a maintainer's")
    return { ...ran, summary }
  }

  it("publish: a tag stages its version, and prints the stage id and the approve line, in the log and the run's summary", () => {
    const at = publishIn("v0.8.0")
    w.state({ ...w.now(), npm: ["0.7.0"], staged: [] })
    const ran = publish(at)
    assert.equal(ran.status, 0, ran.out)
    assert.equal(npm(ran.calls, "stage", "publish").length, 1)
    assert.deepEqual(npm(ran.calls, "publish"), [], "never a direct publish")
    assert.deepEqual(w.now().staged, ["0.8.0"])
    for (const text of [ran.out, ran.summary]) {
      assert.ok(text.includes(STAGE_ID), "names the stage id")
      assert.ok(text.includes(`npm stage approve ${STAGE_ID}`), "names the approve command")
      assert.ok(text.includes("https://www.npmjs.com/package/@emyann/tsverify"), "names the package's page on npmjs.com")
    }
  })

  it("publish: a version staged already stages nothing again, and says how to find and approve it", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    const ran = publish(at)
    assert.equal(ran.status, 0, ran.out)
    assert.deepEqual(w.now().staged, ["0.8.0"], "staged once")
    for (const text of [ran.out, ran.summary]) {
      assert.ok(text.includes("npm stage list @emyann/tsverify"), "says how to find the id")
      assert.ok(text.includes("npm stage approve"), "says how to approve it")
      assert.ok(!text.includes(STAGE_ID), "invents no id")
    }
  })

  it("publish: a version on npm already stages nothing, and the summary says nothing is left", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    w.state({ ...w.now(), npm: ["0.7.0", "0.8.0"] })
    const ran = publish(at)
    assert.equal(ran.status, 0, ran.out)
    assert.deepEqual(npm(ran.calls, "stage"), [])
    assert.ok(ran.summary.includes("0.8.0"), "the summary names the version")
    assert.ok(!ran.summary.includes("npm stage approve"), "nothing to approve")
  })

  it("REFUSED: an npm that is not the pin, before anything is read or staged", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    w.state({ ...w.now(), npm: ["0.7.0"], staged: [], npmVersion: "11.13.0" })
    const ran = publish(at)
    assert.equal(ran.status, 1)
    assert.deepEqual(npm(ran.calls, "stage"), [])
    assert.deepEqual(npm(ran.calls, "view"), [])
    assert.ok(ran.out.includes("11.13.0") && ran.out.includes(NPM_PIN), "names both versions")
    w.state({ ...w.now(), npmVersion: undefined })
  })

  it("REFUSED: publish of a ref that is no release tag, or a tag that disagrees with package.json", () => {
    w.state({ ...w.now(), npm: [], staged: [] })
    const at = publishIn("main")
    for (const ref of ["refs/heads/main", "refs/tags/v0.9.0"]) {
      const ran = publish(at, ref)
      assert.equal(ran.status, 1, ref)
      assert.deepEqual(npm(ran.calls, "stage"), [])
    }
    w.git(w.seed, "tag", "-a", "v0.9.0", "-m", "tsverify 0.9.0")
    w.git(w.seed, "push", "--quiet", "origin", "v0.9.0")
    const wrong = publishIn("v0.9.0")
    const ran = publish(wrong, "refs/tags/v0.9.0")
    assert.equal(ran.status, 1)
    assert.deepEqual(npm(ran.calls, "stage"), [])
  })

  it("REFUSED: publish of a tag whose commit is not on main", () => {
    const off = path.join(w.dir, "off")
    w.git(w.dir, "clone", "--quiet", w.origin, off)
    w.git(off, "checkout", "--quiet", "-b", "side", "v0.8.0")
    const pkg = JSON.parse(readFileSync(path.join(off, "package.json"), "utf8")) as { version: string }
    pkg.version = "0.8.1"
    writeFileSync(path.join(off, "package.json"), `${JSON.stringify(pkg, null, 2)}\n`)
    w.git(off, "commit", "--quiet", "-am", "0.8.1 off main")
    w.git(off, "tag", "-a", "v0.8.1", "-m", "tsverify 0.8.1")
    w.git(off, "push", "--quiet", "origin", "v0.8.1")
    const at = publishIn("v0.8.1")
    const ran = publish(at, "refs/tags/v0.8.1")
    assert.equal(ran.status, 1)
    assert.deepEqual(npm(ran.calls, "stage"), [])
  })

  it("REFUSED: a stage npm will not authenticate, naming where the trusted publisher is configured", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    for (const failure of [
      "npm error code ENEEDAUTH\nnpm error need auth\n",
      "npm error code E404\nnpm error 404 Not Found - POST https://registry.npmjs.org/-/stage/package/@emyann%2ftsverify\n",
    ]) {
      w.state({ ...w.now(), npm: [], staged: [], stageFails: failure })
      const ran = publish(at)
      assert.equal(ran.status, 1)
      for (const fact of ["https://www.npmjs.com/package/@emyann/tsverify/access", "publish.yml", "emyann", "tsverify", "v0.8.0"])
        assert.ok(ran.out.includes(fact), `names ${fact}`)
      assert.ok(/trusted publisher/i.test(ran.out))
    }
  })

  it("REFUSED: a stage the trusted publisher may not make, naming where to remake it and the box to leave unticked", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    w.state({
      ...w.now(),
      npm: [],
      staged: [],
      stageFails: "npm error code E403\nnpm error 403 Forbidden - POST https://registry.npmjs.org/-/stage/package/@emyann%2ftsverify\n",
    })
    const ran = publish(at)
    assert.equal(ran.status, 1)
    assert.ok(ran.out.includes("https://www.npmjs.com/package/@emyann/tsverify/access"), "names where it is configured")
    assert.ok(ran.out.includes("Allow npm publish"), "names the box")
  })

  it("REFUSED: a stage that fails for another reason, another 409 too, is read neither as staged nor as the trusted publisher", () => {
    const at = path.join(w.dir, "publish-v0.8.0")
    for (const failure of [
      "npm error code E500\nnpm error 500 Internal Server Error\n",
      "npm error code E409\nnpm error 409 Conflict - something else\n",
    ]) {
      w.state({ ...w.now(), npm: [], staged: [], stageFails: failure })
      const ran = publish(at)
      assert.equal(ran.status, 1, failure)
      assert.ok(!ran.out.includes("/access"))
    }
  })
})

describe("release.ts pr refusals", () => {
  it("REFUSED: GitHub's token may not open pull requests, and the setting is named", () => {
    const w = world()
    const sha = w.land()
    w.state({ pulls: [merged(1, ["fix"], sha)], labels: correctLabels(), next: 10, createRefused: true })
    const ran = w.run("pr")
    assert.equal(ran.status, 1)
    assert.ok(ran.out.includes("Allow GitHub Actions to create and approve pull requests"))
  })

  it("only internal or unlabelled merges since the tag: no release branch, whatever merged before the tag", () => {
    const w = world()
    const tagged = w.git(w.seed, "rev-parse", "v0.7.0^{commit}")
    w.state({
      pulls: [merged(1, ["internal"], w.land()), merged(2, [], w.land()), merged(3, ["feature"], tagged)],
      labels: correctLabels(),
      next: 10,
    })
    const ran = w.run("pr")
    assert.equal(ran.status, 0, ran.out)
    assert.equal(w.remoteRef("refs/heads/release"), "")
    assert.deepEqual(gh(ran.calls, "pr", "create"), [])
  })

  it("an unknown verb exits 2", () => {
    const w = world()
    w.state({ pulls: [], labels: [], next: 1 })
    assert.equal(w.run("proof").status, 2)
  })
})

describe("the release workflows", () => {
  const yml = (file: string) => read(path.join(".github", file))

  it("publish.yml: OIDC, the pinned Node and npm, and no token and no approval", () => {
    const publish = yml("workflows/publish.yml")
    assert.match(publish, /id-token: write/)
    assert.match(publish, /node-version: '24\.16\.0'/)
    assert.ok(publish.includes(`npm install --global npm@${NPM_PIN}\n`), "installs the npm the tool pins")
    assert.match(publish, /https:\/\/docs\.npmjs\.com\/trusted-publishers/)
    assert.match(publish, /https:\/\/docs\.npmjs\.com\/staged-publishing/)
    assert.match(publish, /node tools\/release\.ts publish/)
    const code = publish
      .split("\n")
      .filter((line) => !/^\s*#/.test(line))
      .join("\n")
    assert.match(code, /id-token: write/, "the permission is in the YAML, not only in the header")
    assert.doesNotMatch(code, /NPM_TOKEN|NODE_AUTH_TOKEN:|--provenance|secrets\.|stage approve|11\.13\.0/)
  })

  it("release.yml: labels, tag, pr, one group never cancelled", () => {
    const release = yml("workflows/release.yml")
    for (const verb of ["labels", "tag", "pr"]) assert.match(release, new RegExp(`node tools/release\\.ts ${verb}\\n`))
    assert.equal(release.match(/group: release\n\s+cancel-in-progress: false/g)?.length, 3)
  })

  it("release-label.yml: the check, on the base's code, with no concurrency group", () => {
    const check = yml("workflows/release-label.yml")
    assert.match(check, /node tools\/release\.ts check/)
    assert.match(check, /ref: \$\{\{ github\.event\.pull_request\.base\.sha \|\| 'main' \}\}/)
    assert.doesNotMatch(check, /concurrency:/)
  })

  it("ci.yml posts the ci status on a dispatched run only", () => {
    const ci = yml("workflows/ci.yml")
    const step = ci.slice(ci.indexOf("Post the ci status"))
    assert.match(step, /if: always\(\) && github\.event_name == 'workflow_dispatch'/)
    assert.match(step, /CONTEXT: ci\b/)
  })

  it(".github/release.yml has a category per label but internal, which it leaves out", () => {
    const notes = yml("release.yml")
    for (const l of LABELS.filter((each) => each.name !== "internal")) assert.match(notes, new RegExp(`- ${l.name}\\n`))
    assert.match(notes, /exclude:\s+labels:\s+- internal/)
  })
})
