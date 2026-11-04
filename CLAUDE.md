# tsverify

tsverify proves laws of ordinary TypeScript for every input, or finds an input that breaks one: it reads the spec and the code from
source and hands them to Z3. How to use it as a coding agent is in the skill `tsverify` (`skills/tsverify/SKILL.md`).

## Checks a session runs

- `npm run lint` (oxlint, then `oxfmt --check`); `npm run format` writes the layout `oxfmt --check` reads.
- `npm run typecheck`.
- One test file alone:
  `node --predictable-gc-schedule --conditions=tsverify-source --test --test-concurrency=1 test/<file>.test.ts`
- `npm run verify <file>` on the file a change touched stays open to a session.

Run only the test files of what you changed, one at a time, at `--test-concurrency=1`. Never run `npm test`, `npm run coverage`,
`npm run bench`, nor every file of `test/`: the suite runs Z3 in WASM, up to about 2 GB a process for about 11 minutes, on a machine
other work shares, and the steps' fence refuses those commands.

`test/maps*.test.ts` are the slow Z3 files (`maps-steady` takes about 4 minutes): run them only when the change touches what they test.

CI's `ci` context runs the whole suite on every pull request, and it is the judge.
