# Contributing to tsverify

## Run it

```sh
npm test            # 274 tests, ~55 s, the documentation's examples among them
npm run verify      # every contract below here, a line per law, then a total
npm run verify -- examples/account                                   # one folder, or one file
npm run verify -- examples/account/withdraw.ts withdraw              # one contract, with all it knows
npm run verify -- examples/hono                                      # a Hono API built twice, basic and with Effect
npm run bench       # planted bugs: the solver beside property testing (~15 s)
npm run coverage -- <tsconfig.json> [--modular]                      # how much of a code base it reads
npm run typecheck
npm run lint        # oxlint, then oxfmt --check; npm run format writes the layout
```

On this repository `npm run verify` exits 1, on purpose: two examples keep a law the solver refutes,
`examples/account/imports.contract.ts` keeps 8 laws bounded by a loop of steps, and `fixtures/vacuous` holds three vacuous
laws.

`test/docs.test.ts` runs every example of the documentation, the README and each page of `docs/`. It writes each page's
files into a project of their own, in the page's order, runs each command the page shows, and compares what it prints. A
page marks its blocks with comments the reader does not see: `<!-- file: src/charge.ts -->` before a block makes it that
file, and `<!-- run -->` (or `<!-- run, exits 1 -->`) before a block of `$ npx tsverify ...` and its output runs it.

Before you commit, run the typecheck, the lint and the tests. CI runs the same on every push and pull request
(`.github/workflows/ci.yml`), the tests on the Node floor `engines.node` claims and on the latest 24.

A commit that only changes the layout (a new rule of `oxfmt`, say) goes in `.git-blame-ignore-revs`, so `git blame` looks
past it. GitHub reads the file by itself; locally, `git config blame.ignoreRevsFile .git-blame-ignore-revs` once.

## Building and packing

The repository runs its TypeScript source, with no build: Node 24 runs `.ts` files directly. An installed package
cannot, since Node does not run TypeScript from inside `node_modules`, so what a project installs is built JavaScript,
in `dist/`.

Each entry of `exports` names both. Its source sits under a condition of its own, `tsverify-source`: `tsconfig.json` sets
it in `customConditions`, and every script passes `--conditions=tsverify-source`, so a test that imports `tsverify` gets
`src/contract.ts`. A project that installs the package sets no such condition and gets `dist/`: `npm run build` emits it
(JavaScript and declarations, through `tsconfig.build.json`), and `npm pack` runs the build first. The verifier knows its
own modules by package, the nearest `package.json` named `tsverify`, and by their path in it, source or built
(`ownModule` in `src/project.ts`), so a spec reads the same whether it imports this checkout, a linked copy or an
installed one.

`test/install.test.ts` packs the package, installs the tarball into a new project with some of the examples copied in,
and asks the installed command what the source answers on the same files: the same verdicts. It also checks that the
tarball holds nothing but the build and the packs, and that a planted bug's counterexample breaks the installed code when
it runs. It needs `npm` and, when the npm cache lacks a dependency, the network.
