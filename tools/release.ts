/**
 * tsverify's releases: a pull request a workflow keeps open, the tag and GitHub release its merge makes, and the publish to npm as a
 * trusted publisher (CONTRIBUTING.md, "Releasing"). The repository's own tool, never shipped (package.json `files`); it imports only
 * `node:` builtins and reaches git, GitHub and npm only through `git`, `gh` and `npm` on PATH, each call bounded.
 *
 * - `check`: the `release-label` check. Exactly one of `LABELS` on the pull request numbered `PR_NUMBER`, read live. Given a `HEAD_SHA`
 *   (a dispatched run's commit), it refuses a pull request whose head is another commit.
 * - `labels`: makes the five labels, and puts back the colour or description of one that drifted.
 * - `tag`: where main's package.json names a version above the last release and with no tag on origin, tags `vX.Y.Z` (annotated,
 *   `tsverify X.Y.Z`) on the first-parent commit of main that set it, makes its GitHub release, and dispatches `publish.yml` on it.
 * - `pr`: keeps the release pull request (`release` into `main`) open while a pull request merged since the last release carries a label
 *   that releases, rebuilt on main when main moves, and dispatches `ci.yml` and `release-label.yml` on its head. Closes it when nothing is
 *   to release.
 * - `publish`: on a checkout of `GITHUB_REF` = `refs/tags/vX.Y.Z`, publishes that commit to npm unless npm has the version already.
 *
 * Every verb decides from the repository as it is, so a rerun with nothing new writes nothing.
 * Exit codes: 0 done or nothing to do, 1 refused or failed (the line says what to do), 2 a verb it does not have.
 */
import { spawnSync } from "node:child_process"
import { readFileSync, writeFileSync } from "node:fs"
import path from "node:path"
import { fileURLToPath } from "node:url"

/** A version's bump: what a label releases. */
export type Bump = "major" | "minor" | "patch" | "none"

export type Label = { name: string; bump: Bump; color: string; description: string }

/** The release labels, in their order: every pull request into main carries exactly one. `.github/release.yml` holds a category each. */
export const LABELS: readonly Label[] = [
  { name: "breaking", bump: "major", color: "b60205", description: "Releases a major version (a minor while 0.x): breaks what a user had" },
  { name: "feature", bump: "minor", color: "0e8a16", description: "Releases a minor version: something a user can do that they could not" },
  { name: "fix", bump: "patch", color: "d93f0b", description: "Releases a patch: something that was wrong works" },
  { name: "docs", bump: "patch", color: "0075ca", description: "Releases a patch: the documentation a user reads changed" },
  { name: "internal", bump: "none", color: "cfd3d7", description: "Releases nothing: the repository changed, not what a user gets" },
]

/** The one package this tool publishes. */
export const PACKAGE = "@emyann/tsverify"

/** Where the package's trusted publisher is configured on npm, and what it names. */
export const TRUSTED_PUBLISHER = {
  url: `https://www.npmjs.com/package/${PACKAGE}/access`,
  owner: "emyann",
  repository: "tsverify",
  workflow: "publish.yml",
}

/** The setting GitHub refuses the token's pull request without. */
export const CREATE_SETTING = "Allow GitHub Actions to create and approve pull requests"

const BRANCH = "release"
const BASE = "main"

/** The workflows `pr` dispatches on the release head, each reporting the commit status of its name, and whether it takes `pr`. */
const DISPATCHED = [
  { file: "ci.yml", context: "ci", pr: false },
  { file: "release-label.yml", context: "release-label", pr: true },
] as const

/** A release tag, anchored: nothing before the `v`, nothing after the patch. */
const TAG = /^v(\d+)\.(\d+)\.(\d+)$/

/** The README's line that names the version. */
const README_LINE = /A prototype: version \d+\.\d+\.\d+/g

/** The bound on one `git`, `gh` or `npm` call: a stalled network fails the call, never the job's whole bound. */
const CALL_MS = 120_000

/**
 * Who commits and tags: the workflow, as GitHub names its own token's user. Set through the environment, which git reads before any
 * `user.name`, so nothing the runner or a person exported signs a release.
 */
const BOT_NAME = "github-actions[bot]"
const BOT_EMAIL = "41898282+github-actions[bot]@users.noreply.github.com"
const asBot = (env: Env): Env => ({
  ...env,
  GIT_AUTHOR_NAME: BOT_NAME,
  GIT_AUTHOR_EMAIL: BOT_EMAIL,
  GIT_COMMITTER_NAME: BOT_NAME,
  GIT_COMMITTER_EMAIL: BOT_EMAIL,
})

/** The pages of a list read at most: 100 each, far past the repository's count. */
const MAX_PAGES = 200

/** GitHub's bound on a pull request's body. */
const BODY_MAX = 65_000

/** The version a tag releases, or `undefined` for a tag that is no release. */
export const releaseTag = (tag: string): string | undefined => {
  const m = TAG.exec(tag)
  return m ? `${Number(m[1])}.${Number(m[2])}.${Number(m[3])}` : undefined
}

const ORDER: readonly Bump[] = ["none", "patch", "minor", "major"]

/** The bump of a set of labels: the highest any gives, `none` where none releases. */
export const bump = (labels: readonly string[]): Bump =>
  labels.reduce<Bump>((high, name) => {
    const given = LABELS.find((label) => label.name === name)?.bump ?? "none"
    return ORDER.indexOf(given) > ORDER.indexOf(high) ? given : high
  }, "none")

const parts = (version: string): [number, number, number] => {
  const [a = 0, b = 0, c = 0] = version.split(".").map(Number)
  return [a, b, c]
}

/** Whether version `a` is below `b`. */
const below = (a: string, b: string): boolean => {
  const [x, y] = [parts(a), parts(b)]
  for (let i = 0; i < 3; i++) if (x[i] !== y[i]) return x[i]! < y[i]!
  return false
}

/** The version after `last` for `by`, a breaking change a minor while the major is 0; `undefined` when `by` releases nothing. */
export const nextVersion = (last: string, by: Bump): string | undefined => {
  if (by === "none") return undefined
  const [major, minor, patch] = parts(last)
  if (by === "major" && major > 0) return `${major + 1}.0.0`
  if (by === "major" || by === "minor") return `${major}.${minor + 1}.0`
  return `${major}.${minor}.${patch + 1}`
}

/** A refusal: its message says what to do, and the verb exits 1 with it. */
export class Refusal extends Error {}

/** The three files a release moves, as text. */
export type VersionFiles = { packageJson: string; packageLock: string; readme: string }

const json = (value: unknown): string => `${JSON.stringify(value, null, 2)}\n`

/** A JSON file as an object, refused unless writing it back unchanged gives its own bytes: npm's layout is never disturbed. */
const parsed = (name: string, text: string): Record<string, unknown> => {
  const value = JSON.parse(text) as unknown
  if (typeof value !== "object" || value === null || Array.isArray(value)) throw new Refusal(`${name} is no JSON object`)
  if (json(value) !== text)
    throw new Refusal(`${name} is not laid out as JSON.stringify(x, null, 2) and a newline: run npm install once, commit it, and re-run`)
  return value as Record<string, unknown>
}

/**
 * The three files with `version` written in each of its four places: package.json's `version`, package-lock.json's root `version`
 * and `packages[""].version`, and the README's "A prototype: version x.y.z". Refused where a place is missing or the README names
 * its version more or less than once.
 */
export const withVersion = (files: VersionFiles, version: string): VersionFiles => {
  const pkg = parsed("package.json", files.packageJson)
  const lock = parsed("package-lock.json", files.packageLock)
  if (typeof pkg.version !== "string") throw new Refusal("package.json has no version")
  if (typeof lock.version !== "string") throw new Refusal("package-lock.json has no root version")
  const packages = lock.packages as Record<string, Record<string, unknown>> | undefined
  const rootPackage = packages?.[""]
  if (!rootPackage || typeof rootPackage.version !== "string")
    throw new Refusal('package-lock.json has no packages[""].version: run npm install once, commit it, and re-run')
  const found = files.readme.match(README_LINE) ?? []
  if (found.length !== 1)
    throw new Refusal(`README.md names "A prototype: version x.y.z" ${found.length} times, not once: put the one line back, and re-run`)
  return {
    packageJson: json({ ...pkg, version }),
    packageLock: json({ ...lock, version, packages: { ...packages, "": { ...rootPackage, version } } }),
    readme: files.readme.replace(README_LINE, `A prototype: version ${version}`),
  }
}

type Out = (line: string) => void
type Env = Record<string, string | undefined>
type Ran = { status: number | null; stdout: string; stderr: string }

const spawn = (command: string, args: string[], env: Env, cwd: string, input?: string): Ran => {
  const ran = spawnSync(command, args, { cwd, encoding: "utf8", timeout: CALL_MS, env, input, maxBuffer: 256 << 20 })
  if (ran.error) throw new Refusal(`${command} ${args[0]} did not finish (${ran.error.message}): re-run the job once ${command} answers`)
  return { status: ran.status, stdout: ran.stdout, stderr: ran.stderr }
}

/** The tool's reach into git, GitHub and npm, under one environment and working directory. */
const reach = (env: Env, cwd: string) => {
  const git = (...args: string[]): string => {
    const ran = spawn("git", args, env, cwd)
    if (ran.status !== 0) throw new Refusal(`git ${args.join(" ")} failed: ${ran.stderr.trim()}`)
    return ran.stdout.trim()
  }
  /** git as the workflow's bot, for what it signs: a commit, a tag. */
  const gitAsBot = (...args: string[]): string => {
    const ran = spawn("git", args, asBot(env), cwd)
    if (ran.status !== 0) throw new Refusal(`git ${args.join(" ")} failed: ${ran.stderr.trim()}`)
    return ran.stdout.trim()
  }
  const gitMaybe = (...args: string[]): string | undefined => {
    const ran = spawn("git", args, env, cwd)
    return ran.status === 0 ? ran.stdout.trim() : undefined
  }
  const gh = (args: string[], input?: string): string => {
    const ran = spawn("gh", args, env, cwd, input)
    if (ran.status !== 0)
      throw new Refusal(`gh ${args.slice(0, 4).join(" ")} failed: ${ran.stderr.trim()} (check GH_TOKEN and the job's permissions)`)
    return ran.stdout
  }
  const api = <T>(method: string, endpoint: string, fields: string[] = []): T => {
    const out = gh(["api", "-X", method, endpoint, ...fields.flatMap((field) => ["-f", field])])
    return (out.trim() === "" ? null : JSON.parse(out)) as T
  }
  /** A GET that answers `undefined` on GitHub's 404. */
  const apiMaybe = <T>(endpoint: string): T | undefined => {
    const ran = spawn("gh", ["api", "-X", "GET", endpoint], env, cwd)
    if (ran.status === 0) return JSON.parse(ran.stdout) as T
    if (/HTTP 404/.test(ran.stderr)) return undefined
    throw new Refusal(`gh api ${endpoint} failed: ${ran.stderr.trim()} (check GH_TOKEN and the job's permissions)`)
  }
  return { cwd, env, git, gitAsBot, gitMaybe, gh, api, apiMaybe }
}

type Reach = ReturnType<typeof reach>

type Pull = {
  number: number
  title: string
  body?: string | null
  labels: { name: string }[]
  merged_at?: string | null
  merge_commit_sha?: string | null
  head?: { ref: string; sha?: string }
}

const releaseLabels = (labels: readonly string[]): string[] => labels.filter((name) => LABELS.some((label) => label.name === name))
const labelsOf = (pull: Pull): string[] => pull.labels.map((label) => label.name)

/** `check`: exactly one release label on the pull request, read live, so a run reads the labels it has now. It only reads. */
const check = (env: Env, out: Out, r: Reach): number => {
  const number = env.PR_NUMBER ?? ""
  if (!/^\d+$/.test(number)) throw new Refusal("release-label: set PR_NUMBER to the pull request's number")
  const pull = r.api<Pull>("GET", `repos/{owner}/{repo}/pulls/${number}`)
  const head = env.HEAD_SHA ?? ""
  if (head !== "" && pull.head?.sha !== head)
    throw new Refusal(
      `release-label: pull request #${number}'s head is ${pull.head?.sha ?? "unknown"}, not ${head}, the commit this run checks. ` +
        `Check its head with gh workflow run release-label.yml --ref ${pull.head?.ref ?? "<its branch>"} -f pr=${number}`,
    )
  const given = releaseLabels(labelsOf(pull))
  if (given.length === 1) {
    out(`release-label: ${given[0]} (${bump(given)})`)
    return 0
  }
  const names = LABELS.map((label) => `${label.name} (${label.bump === "none" ? "no release" : label.bump})`).join(", ")
  const add = `gh api -X POST repos/{owner}/{repo}/issues/${number}/labels -f 'labels[]=<label>'`
  const remove =
    given.length > 1 ? `, and take the others off with gh api -X DELETE repos/{owner}/{repo}/issues/${number}/labels/<label>` : ""
  throw new Refusal(
    `release-label: pull request #${number} carries ${given.length === 0 ? "no release label" : `${given.length} release labels (${given.join(", ")})`}` +
      `, and needs exactly one of ${names}. Add one with ${add}${remove}.`,
  )
}

/** `labels`: the five labels exist, with their colour and description; only one missing or drifted is written. */
const labels = (out: Out, r: Reach): number => {
  const have: { name: string; color: string; description: string | null }[] = []
  for (let page = 1; page <= MAX_PAGES; page++) {
    const got = r.api<typeof have>("GET", `repos/{owner}/{repo}/labels?per_page=100&page=${page}`)
    have.push(...got)
    if (got.length < 100) break
  }
  for (const label of LABELS) {
    const found = have.find((each) => each.name === label.name)
    if (found && found.color.toLowerCase() === label.color && (found.description ?? "") === label.description) continue
    r.gh(["label", "create", label.name, "--color", label.color, "--description", label.description, "--force"])
    out(`labels: ${found ? "put back" : "made"} ${label.name}`)
  }
  return 0
}

/** Fetches main and the tags from origin: main's head. */
const fetchMain = (r: Reach): string => {
  r.git("fetch", "--quiet", "--tags", "--force", "origin", `+refs/heads/${BASE}:refs/remotes/origin/${BASE}`)
  return r.git("rev-parse", `origin/${BASE}`)
}

/** The releases among the tags merged into `ref`, highest first. */
const releasesIn = (r: Reach, ref: string): { tag: string; version: string }[] =>
  r
    .git("tag", "--merged", ref)
    .split("\n")
    .flatMap((each) => {
      const version = releaseTag(each.trim())
      return version ? [{ tag: each.trim(), version }] : []
    })
    .sort((a, b) => (below(a.version, b.version) ? 1 : below(b.version, a.version) ? -1 : 0))

/** The root package.json's version at `ref`, or `undefined`. */
const versionAt = (r: Reach, ref: string): string | undefined => {
  const text = r.gitMaybe("show", `${ref}:package.json`)
  if (text === undefined) return undefined
  const version = (JSON.parse(text) as { version?: unknown }).version
  return typeof version === "string" ? version : undefined
}

/**
 * `tag`: the release of the version main names. A version with no tag on origin and above the last release is tagged on the oldest
 * first-parent commit of main since that release that names it (the release pull request's merge), then released, then published. A
 * tag this workflow made whose GitHub release is missing (a run that failed between the two) gets its release and its publish again; a
 * tag a person made is theirs, and left alone.
 */
const tag = (out: Out, r: Reach): number => {
  fetchMain(r)
  const version = versionAt(r, `origin/${BASE}`)
  if (version === undefined) {
    out("tag: package.json on main names no version: nothing to release")
    return 0
  }
  const name = `v${version}`
  const previous = releasesIn(r, `origin/${BASE}`).find((each) => below(each.version, version))
  let made = false
  if (r.git("ls-remote", "--tags", "origin", `refs/tags/${name}`) === "") {
    const last = releasesIn(r, `origin/${BASE}`)[0]
    if (last && !below(last.version, version)) {
      out(`tag: main names ${version}, not above the last release ${last.tag}: nothing to release`)
      return 0
    }
    const commits = r
      .git("rev-list", "--first-parent", "--reverse", last ? `${last.tag}..origin/${BASE}` : `origin/${BASE}`)
      .split("\n")
      .filter(Boolean)
    const setter = commits.find((sha) => versionAt(r, sha) === version)
    if (!setter)
      throw new Refusal(`tag: no first-parent commit of ${BASE} names version ${version}: set it through the release pull request`)
    r.gitAsBot("tag", "-a", name, "-m", `tsverify ${version}`, setter)
    r.git("push", "--quiet", "origin", `refs/tags/${name}`)
    out(`tag: tagged ${name} on ${setter}`)
    made = true
  } else {
    const tagger = r.git("for-each-ref", "--format=%(taggername)", `refs/tags/${name}`)
    if (tagger !== BOT_NAME) {
      out(`tag: ${name} is tagged already, not by this workflow: nothing to do`)
      return 0
    }
  }
  if (r.apiMaybe(`repos/{owner}/{repo}/releases/tags/${name}`) !== undefined) {
    if (!made) {
      out(`tag: ${name} is released already`)
      return 0
    }
  } else {
    r.gh([
      "release",
      "create",
      name,
      "--verify-tag",
      "--title",
      name,
      "--generate-notes",
      ...(previous ? ["--notes-start-tag", previous.tag] : []),
    ])
    out(`tag: released ${name}`)
  }
  r.gh(["workflow", "run", "publish.yml", "--ref", name])
  out(`tag: dispatched publish.yml on ${name}`)
  return 0
}

/** The pull requests merged into main whose merge commit is in `commits`, read a page at a time. */
const mergedIn = (r: Reach, commits: Set<string>): Pull[] => {
  const found: Pull[] = []
  for (let page = 1; page <= MAX_PAGES; page++) {
    const got = r.api<Pull[]>("GET", `repos/{owner}/{repo}/pulls?state=closed&base=${BASE}&per_page=100&page=${page}`)
    found.push(...got.filter((pull) => pull.merged_at && pull.merge_commit_sha && commits.has(pull.merge_commit_sha)))
    if (got.length < 100) break
  }
  return found.sort((a, b) => a.number - b.number)
}

/** The release branch's head once it is main plus one commit writing `version`: rebuilt and force-pushed only where it is not. */
const rebuilt = (out: Out, r: Reach, main: string, version: string): string => {
  const remote = r.git("ls-remote", "origin", `refs/heads/${BRANCH}`)
  if (remote !== "") r.git("fetch", "--quiet", "origin", `+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}`)
  if (remote !== "" && r.gitMaybe("rev-parse", `origin/${BRANCH}^1`) === main && versionAt(r, `origin/${BRANCH}`) === version) {
    out(`pr: ${BRANCH} is ${BASE} plus ${version} already`)
    return r.git("rev-parse", `origin/${BRANCH}`)
  }
  r.git("checkout", "--quiet", "-B", BRANCH, `origin/${BASE}`)
  const top = r.git("rev-parse", "--show-toplevel")
  const file = (name: string) => path.join(top, name)
  const moved = withVersion(
    {
      packageJson: readFileSync(file("package.json"), "utf8"),
      packageLock: readFileSync(file("package-lock.json"), "utf8"),
      readme: readFileSync(file("README.md"), "utf8"),
    },
    version,
  )
  writeFileSync(file("package.json"), moved.packageJson)
  writeFileSync(file("package-lock.json"), moved.packageLock)
  writeFileSync(file("README.md"), moved.readme)
  r.git("add", "package.json", "package-lock.json", "README.md")
  r.gitAsBot("commit", "--quiet", "-m", `Release ${version}`)
  r.git("push", "--quiet", "--force", "origin", `HEAD:refs/heads/${BRANCH}`)
  out(`pr: rebuilt ${BRANCH} as ${BASE} plus ${version}`)
  return r.git("rev-parse", "HEAD")
}

/** What a person does with the release pull request, first in its body so `BODY_MAX`'s cut never reaches it. */
const TO_RELEASE = [
  "**To release:** merge this pull request once `ci` and `release-label` are green on its head. The release workflow dispatched both",
  "here, since a pull request its own token opens starts no workflow. Its merge tags `vX.Y.Z`, makes the GitHub release, and",
  "dispatches `publish.yml`, which publishes the tag's commit to npm. The `release` branch is rebuilt from main whenever main moves:",
  "push nothing to it by hand. A check missing or failed on the head: `gh workflow run release.yml`.",
].join("\n")

const bodyOf = (generated: string, unlabelled: Pull[]): string => {
  let body = `${TO_RELEASE}\n\n${generated}\n`
  if (unlabelled.length) body += `\n## Not labelled, counted for no bump\n\n${unlabelled.map((pull) => `#${pull.number}`).join(", ")}\n`
  return body.length > BODY_MAX
    ? `${body.slice(0, BODY_MAX)}\n\n… cut at GitHub's bound on a body; the release's own notes are whole.\n`
    : body
}

/** Opens the release pull request with `gh pr create`: its number, or the refusal naming the setting GitHub wants. */
const opened = (r: Reach, title: string, body: string): number => {
  const ran = spawn("gh", ["pr", "create", "--base", BASE, "--head", BRANCH, "--title", title, "--body-file", "-"], r.env, r.cwd, body)
  if (ran.status !== 0 && /not permitted to create or approve pull requests/i.test(ran.stderr))
    throw new Refusal(
      `pr: GitHub refused the workflow's token a pull request. Turn on "${CREATE_SETTING}" (Settings → Actions → General → Workflow ` +
        "permissions), then run gh workflow run release.yml",
    )
  if (ran.status !== 0) throw new Refusal(`pr: gh pr create failed: ${ran.stderr.trim()} (check GH_TOKEN and the pr job's permissions)`)
  const m = /\/pull\/(\d+)/.exec(ran.stdout)
  if (!m) throw new Refusal(`pr: gh pr create printed no pull request URL (${ran.stdout.trim()}): run gh workflow run release.yml again`)
  return Number(m[1])
}

type WorkflowRun = { status: string; conclusion: string | null }

/** Whether a dispatched run stands for its check on its head: still to finish, or green. A failed or cancelled one is tried again. */
const standing = (run: WorkflowRun): boolean => run.status !== "completed" || run.conclusion === "success"

/**
 * Dispatches each of `DISPATCHED` on the release branch where `head` has no dispatched run of it that stands, after posting its commit
 * status `pending` on the head, so the pull request shows the check from the start; the run posts its verdict over it.
 */
const dispatch = (out: Out, r: Reach, head: string, number: number): void => {
  for (const { file, context, pr } of DISPATCHED) {
    const { workflow_runs: runs } = r.api<{ workflow_runs: WorkflowRun[] }>(
      "GET",
      `repos/{owner}/{repo}/actions/workflows/${file}/runs?head_sha=${head}&event=workflow_dispatch&per_page=100`,
    )
    if (runs.some(standing)) continue
    r.api("POST", `repos/{owner}/{repo}/statuses/${head}`, ["state=pending", `context=${context}`, `description=dispatched on ${BRANCH}`])
    r.gh(["workflow", "run", file, "--ref", BRANCH, ...(pr ? ["-f", `pr=${number}`] : [])])
    out(`pr: dispatched ${file} on ${BRANCH} at ${head}`)
  }
}

/** `pr`: the release pull request, as main and the merged pull requests are now. */
const pr = (out: Out, r: Reach): number => {
  const main = fetchMain(r)
  const last = releasesIn(r, `origin/${BASE}`)[0]
  if (!last) throw new Refusal(`pr: no release tag vX.Y.Z is merged into ${BASE}: tag the last release by hand once, then re-run`)
  const range = new Set(r.git("rev-list", `${last.tag}..origin/${BASE}`).split("\n").filter(Boolean))
  const merged = mergedIn(r, range)
  const version = nextVersion(last.version, bump(merged.flatMap(labelsOf)))
  const open = r.api<Pull[]>("GET", `repos/{owner}/{repo}/pulls?state=open&base=${BASE}&head={owner}:${BRANCH}&per_page=100`)[0]
  if (version === undefined) {
    out(`pr: ${merged.length} pull request(s) merged since ${last.tag}, none released: nothing to release`)
    if (open) {
      r.api("PATCH", `repos/{owner}/{repo}/pulls/${open.number}`, ["state=closed"])
      out(`pr: closed #${open.number}, which nothing releases any more`)
    }
    return 0
  }
  const title = `Release ${version}`
  const head = rebuilt(out, r, main, version)
  const notes = r.api<{ body: string }>("POST", "repos/{owner}/{repo}/releases/generate-notes", [
    `tag_name=v${version}`,
    `target_commitish=${head}`,
    `previous_tag_name=${last.tag}`,
  ]).body
  const body = bodyOf(
    notes,
    merged.filter((pull) => releaseLabels(labelsOf(pull)).length === 0),
  )
  const number = open ? open.number : opened(r, title, body)
  if (open && (open.title !== title || (open.body ?? "") !== body))
    r.api("PATCH", `repos/{owner}/{repo}/pulls/${number}`, [`title=${title}`, `body=${body}`])
  out(`pr: #${number} is ${title}`)
  if (!open?.labels.some((label) => label.name === "internal"))
    r.api("POST", `repos/{owner}/{repo}/issues/${number}/labels`, ["labels[]=internal"])
  dispatch(out, r, head, number)
  return 0
}

/** Whether npm's answer to a publish says the trusted publisher is missing or wrong: no credential, or npm's 404 on the PUT. */
const unauthenticated = (text: string): boolean => /ENEEDAUTH|Unable to authenticate|\bE401\b|\bE404\b/.test(text)

/** `publish`: the tag `GITHUB_REF` names, checked out here, published to npm once. */
const publish = (env: Env, out: Out, r: Reach): number => {
  const ref = env.GITHUB_REF ?? ""
  const name = ref.startsWith("refs/tags/") ? ref.slice("refs/tags/".length) : ""
  const version = releaseTag(name)
  if (!version) throw new Refusal(`publish: ${ref || "GITHUB_REF unset"} is no release tag refs/tags/vX.Y.Z: run publish.yml on a tag`)
  const top = r.git("rev-parse", "--show-toplevel")
  const pkg = JSON.parse(readFileSync(path.join(top, "package.json"), "utf8")) as { name?: unknown; version?: unknown }
  if (pkg.name !== PACKAGE) throw new Refusal(`publish: package.json names ${String(pkg.name)}, and this publishes ${PACKAGE} alone`)
  if (pkg.version !== version)
    throw new Refusal(`publish: ${name} is not the version package.json names (${String(pkg.version)}): tag the commit that names it`)
  const sha = r.git("rev-parse", "HEAD")
  if (r.gitMaybe("rev-parse", `refs/tags/${name}^{commit}`) !== sha)
    throw new Refusal(`publish: the checkout is not ${name}'s commit: run publish.yml with --ref ${name}`)
  fetchMain(r)
  if (r.gitMaybe("merge-base", "--is-ancestor", sha, `origin/${BASE}`) === undefined)
    throw new Refusal(`publish: ${name} (${sha}) is not on ${BASE}: a release is a commit of ${BASE}`)
  const view = spawn("npm", ["view", `${PACKAGE}@${version}`, "version"], env, top)
  if (view.status === 0 && view.stdout.trim() === version) {
    out(`publish: ${PACKAGE}@${version} is on npm already: nothing to do`)
    return 0
  }
  if (view.status !== 0 && !/\bE404\b/.test(view.stderr))
    throw new Refusal(`publish: npm view ${PACKAGE}@${version} failed: ${view.stderr.trim()}; re-run publish.yml once npm answers`)
  const ran = spawn("npm", ["publish"], env, top)
  if (ran.stdout) out(ran.stdout.trimEnd())
  if (ran.stderr) out(ran.stderr.trimEnd())
  if (ran.status === 0) {
    out(`publish: published ${PACKAGE}@${version} from ${name}`)
    return 0
  }
  if (unauthenticated(`${ran.stdout}\n${ran.stderr}`))
    throw new Refusal(
      `publish: npm's trusted publisher for ${PACKAGE} is not configured yet, or does not match this workflow. Configure it at ` +
        `${TRUSTED_PUBLISHER.url} → Trusted Publisher → GitHub Actions: organization or user ${TRUSTED_PUBLISHER.owner}, repository ` +
        `${TRUSTED_PUBLISHER.repository}, workflow filename ${TRUSTED_PUBLISHER.workflow}, environment left empty. Then re-run ` +
        `${TRUSTED_PUBLISHER.workflow} on tag ${name}: gh workflow run ${TRUSTED_PUBLISHER.workflow} --ref ${name}`,
    )
  throw new Refusal(`publish: npm publish failed (exit ${String(ran.status)}): read its output above, then re-run publish.yml on ${name}`)
}

const USAGE = "usage: node tools/release.ts check | labels | tag | pr | publish"

/** Runs a verb in the repository at `cwd`: its exit code. */
export const main = (argv: readonly string[], env: Env = process.env, out: Out = console.log, cwd: string = process.cwd()): number => {
  const r = reach(env, cwd)
  try {
    switch (argv[0]) {
      case "check":
        return check(env, out, r)
      case "labels":
        return labels(out, r)
      case "tag":
        return tag(out, r)
      case "pr":
        return pr(out, r)
      case "publish":
        return publish(env, out, r)
      default:
        out(USAGE)
        return 2
    }
  } catch (error) {
    if (!(error instanceof Refusal)) throw error
    out(error.message)
    return 1
  }
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = main(process.argv.slice(2))
}
