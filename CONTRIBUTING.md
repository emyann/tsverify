# Contributing to tsverify

## Run it

```sh
npm test            # 641 tests, the documentation's examples among them; ~21 min one file at a time (--test-concurrency=1)
npm run verify      # every contract below here, a line each, the laws that need a look under it, then the totals
npm run verify -- examples/account                                   # one folder, or one file
npm run verify -- examples/account/withdraw.ts withdraw              # one contract, with all it knows
npm run verify -- examples/hono                                      # a Hono API built twice, basic and with Effect
npm run verify -- examples/charge --watch                            # again on every save
npm run verify -- examples --cache                                   # each contract's verdict kept, answered again while its files are the same
npm run bench       # planted bugs: the solver beside property testing (~15 s)
npm run coverage -- <tsconfig.json> [--modular]                      # how much of a code base it reads
npm run typecheck
npm run lint        # oxlint, then oxfmt --check; npm run format writes the layout
```

On this repository `npm run verify` exits 1, on purpose: two examples keep a law the solver refutes,
`examples/account/imports.contract.ts` keeps 8 laws bounded by a loop of steps, and `fixtures/vacuous` holds three vacuous
laws. CI's `verify` job runs the command on the examples meant to hold, and fails when one does not: an example added that
holds goes on its list (`.github/workflows/ci.yml`).

`test/docs.test.ts` runs every example of the documentation, the README and each page of `docs/`. It writes each page's
files into a project of their own, in the page's order, runs each command the page shows, and compares what it prints. A
page marks its blocks with comments the reader does not see: `<!-- file: src/charge.ts -->` before a block makes it that
file, and `<!-- run -->` (or `<!-- run, exits 1 -->`) before a block of `$ npx tsverify ...` and its output runs it.

Before you commit, run the typecheck, the lint and the tests. CI runs the same on every push and pull request
(`.github/workflows/ci.yml`), the tests on the Node floor `engines.node` claims and on the latest 24. The maps test files
(`test/maps*.test.ts`) run there in a job of their own, `maps`, so the `test` job stays clear of its 20 minutes on a slow
runner: `maps.test.ts` and `maps-constructs.test.ts` took about 3 minutes each beside the other files, and alone, one
file at a time, about 2 minutes together; `maps-steady.test.ts`, one contract verified five times, one process after
another, takes about 4 minutes. Locally `npm test` runs them with the rest. The `test` job's longest file is
`corpus-floats.test.ts`, about 12 minutes on a runner: two of its queries run until the 5-minute clock stops them.

A commit that only changes the layout (a new rule of `oxfmt`, say) goes in `.git-blame-ignore-revs`, so `git blame` looks
past it. GitHub reads the file by itself; locally, `git config blame.ignoreRevsFile .git-blame-ignore-revs` once.

## Building and packing

The repository runs its TypeScript source, with no build: Node 24 runs `.ts` files directly. An installed package
cannot, since Node does not run TypeScript from inside `node_modules`, so what a project installs is built JavaScript,
in `dist/`.

Each entry of `exports` names both. Its source sits under a condition of its own, `tsverify-source`: `tsconfig.json` sets
it in `customConditions`, and every script passes `--conditions=tsverify-source`, so a test that imports `@emyann/tsverify` gets
`src/contract.ts`. A project that installs the package sets no such condition and gets `dist/`: `npm run build` emits it
(JavaScript and declarations, through `tsconfig.build.json`), and `npm pack` runs the build first. The verifier knows its
own modules by package, the nearest `package.json` named `@emyann/tsverify`, and by their path in it, source or built
(`ownModule` in `src/project.ts`), so a spec reads the same whether it imports this checkout, a linked copy or an
installed one.

`test/install.test.ts` packs the package, installs the tarball into a new project with some of the examples copied in,
and asks the installed command what the source answers on the same files: the same verdicts. It also checks that the
tarball holds nothing but the build and the packs, and that a planted bug's counterexample breaks the installed code when
it runs. It needs `npm` and, when the npm cache lacks a dependency, the network.

## Releasing

Nobody cuts a release by hand. Three workflows do it, each running one verb of `tools/release.ts`, the repository's own
tool (never shipped, tested by `test/release.test.ts`):

- `release.yml` runs on every push to `main`. It makes the release labels, tags a release that has just merged, and keeps
  the release pull request open.
- `release-label.yml` checks every pull request into `main`.
- `publish.yml` publishes a release tag to npm.

### The labels

Every pull request into `main` carries exactly one release label, and `release-label` fails until it does. The labels are
made by `release.yml`, never by hand.

| Label      | Releases                                      |
| ---------- | --------------------------------------------- |
| `breaking` | a major version, but a minor while 0.x        |
| `feature`  | a minor version                               |
| `fix`      | a patch                                       |
| `docs`     | a patch                                       |
| `internal` | nothing, and it is left out of the notes      |

### The release pull request

Once a pull request labelled `breaking`, `feature`, `fix` or `docs` has merged since the newest `v*` tag, `release.yml`
opens a pull request titled `Release x.y.z`, from the branch `release` into `main`.

- Its version is the highest bump among the labels merged since that tag.
- It moves the version where a release always has: `package.json`, `package-lock.json` (twice), and the README's line "A
  prototype: version x.y.z".
- Its body is the notes GitHub will generate for the release, by the categories of `.github/release.yml`.
- It is rebuilt from `main` whenever `main` moves, and `release` is force-pushed: push nothing to it by hand.
- It is closed when nothing left to release remains.

A pull request opened with the workflow's token starts no workflow. So `release.yml` dispatches `ci.yml` and
`release-label.yml` on the release head, and each posts its verdict there as the commit status `main` requires. Merge the
pull request once `ci` and `release-label` are green. If one is missing or failed, run `gh workflow run release.yml`.

### What the merge does

The merge's push to `main` runs `release.yml` again. Its `tag` job:

1. tags the merge commit `vX.Y.Z`, annotated, with the message `tsverify X.Y.Z`;
2. makes the GitHub release with generated notes;
3. dispatches `publish.yml` on the tag.

`publish.yml` checks that the tag names the version `package.json` names and is a commit of `main`. It then runs `npm
publish`, which builds `dist/` through `prepack`. It authenticates as npm's trusted publisher, by GitHub's OIDC token, with
no npm token stored anywhere. A version already on npm is not sent again, so re-running the workflow on a tag is always
safe: `gh workflow run publish.yml --ref vX.Y.Z`. A `v*` tag a person pushes starts it too.

Every step decides from the repository as it is: a rerun with nothing new does nothing. The three jobs of `release.yml`
share one concurrency group, so two runs never write the labels, the tag or the release branch at once.

### One-time steps for the owner

- **npm's trusted publisher.** At <https://www.npmjs.com/package/@emyann/tsverify/access>, under Trusted Publisher, choose
  GitHub Actions and enter: user `emyann`, repository `tsverify`, workflow filename `publish.yml`, environment left empty.
  Until then, `publish.yml` fails saying so, and nothing else in the release fails with it: the tag and the GitHub release
  stand. Once it is set, re-run `publish.yml` on the tag. Afterwards, npm's package settings can require trusted
  publishing and disallow tokens.
- **GitHub: "Allow GitHub Actions to create and approve pull requests"**, under Settings → Actions → General → Workflow
  permissions. Without it, `release.yml`'s `pr` job fails naming that setting.
- **Optional: require `release-label` on `main`**, beside `ci`, in the branch protection. Unrequired, an unlabelled pull
  request shows a red check but can still merge, and counts for no release.
