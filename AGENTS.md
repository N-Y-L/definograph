# Agent guide

Definograph draws the logical structure of a Lean 4 statement so that a person
can check what it says. It reads statements, not proofs. It runs locally: a
Lean 4.28.0 worker, a TypeScript reader in the browser, and a VS Code
companion. Read [docs/principles.md](docs/principles.md) first; it is short.

Changes are accepted on machine checks, not on a person's review. A claim the
code makes needs a Lean proof, a kernel check, or a test that fails when the
claim breaks.

## Invariants

Breaking one of these is never the fix.

1. **Statements, not proofs.** A proof is shown as the statement it proves,
   with the kernel's verdict and its axioms where they were recorded. Do not
   draw a proof body. Proofs inside a selected data term are still drawn today
   ([status](docs/status.md#what-remains-unsolved)); do not add new cases.
2. **Never show what the term does not say.** Unread or uninterpreted parts
   stay visible and labelled. Never invent a witness, coordinates, a metric, a
   region, continuity or a proof.
3. **Keep identity and scope exact.** Preserve expression and binder identity,
   universe distinctions, argument roles, quantifier order and lexical scope.
   A field or law is available only where its owning object is. Keep the
   original expression beside any transformation of it.
4. **No new axioms.** Do not add `axiom`, `sorry`, `native_decide` or a looser
   kernel check to make something work. The exceptions are the negative
   control `scripts/fixtures/axiom-audit/AxiomAuditFixture.lean`, which
   nothing imports, and test inputs that check such a term is refused.
5. **The axiom policy only tightens.** In `scripts/axiom-policy.json`,
   `allowedAxioms`, `ratchetExceptions` and each certificate's `axioms` may
   lose entries, never gain them; `ratchetedAxiom` stays `Classical.choice`,
   and no certificate is deleted to make the audit pass. A theorem that newly
   needs an exception is the defect: if `Classical.choice` enters through its
   proof, fix the proof; if through its statement, fix the statement in the
   foundation. No test refuses a new entry yet.
6. **Vendored code is read-only.** `vendor/DefinographCapture/src/` is a
   byte-exact copy of a foundation repository that is not public, pinned by
   SHA-256 in `UPSTREAM.json`; `npm run test:source-dependency` fails on any
   change. It is refreshed only from that repository, as its
   [README](vendor/DefinographCapture/README.md) says. `vendor/LeanTeX/upstream/`
   is unchanged too; the native build verifies its checksums, and its
   compatibility changes are `vendor/LeanTeX/lean-4.28.patch`.
7. **Drawings read back.** Anything added to the drawing's grammar needs a test
   that reads the drawing back to the structure it was drawn from
   (`src/visual/skeleton-readback.ts` is the pattern). Never weaken a readback
   or an expectation to match new output.
8. **No name dispatch.** Do not key behaviour on a theorem name, corpus case
   id, record name or field spelling. The rules in `src/semantic/registry.ts`
   keyed on audited Lean and Mathlib constant names are a known gap
   ([principles](docs/principles.md#where-the-code-stands)), not a pattern to
   extend.
9. **Say where each check comes from.** Keep kernel checks, elaborator answers
   (`Meta.isDefEq`, `Meta.isProp`), tested-only code and unchecked vocabulary
   distinct, in code, on screen and in documents.
10. **Leave the user's project alone.** Never change a user's Lean source, Lake
    files, dependencies, toolchain or settings, and never log or commit a
    user's buffer. The editor sidecar runs trusted code; it is not a sandbox.
11. **Compatibility names stay.** `StatementLens` Lean namespaces, IPC
    identifiers and `statementLens.*` settings are kept on purpose.

## Where things are

| Path | Contents |
| --- | --- |
| `lean/StatementLens/` | Lean programs: browser worker (`Worker.lean`), editor context program (`Context.lean`, `SourceSnapshot.lean`), and the export both use (`Export.lean`) |
| `vendor/DefinographCapture/` | The proved core: the Lean modules with the theorems (read-only) |
| `src/` | The reader: `core/`, `semantic/`, `reading/`, `visual/` (skeleton and figures), `editor/`, `packets/` |
| `server/` | Local HTTP service and Lean process management |
| `extension/` | VS Code controller |
| `corpus/` | Expectations for the native suites |
| `scripts/` | Native suites, the axiom audit, setup |
| `website/` | The static site at definograph.com; its own package |
| `docs/` | Current contracts; `docs/history/` is a frozen record |

[Code entry points](docs/status.md#code-entry-points) maps each boundary to files.

## Checks

These need no Lean, and CI runs exactly these on every push. Install with the
two `npm ci` lines, then run the rest before every commit:

```sh
npm ci --ignore-scripts
npm ci --prefix extension --ignore-scripts
npm run build
npm run check:reader-drivers
npm test
npm run test:server
npm run test:source-dependency
npm run check:extension
cd website && npm ci --ignore-scripts && npm run check
```

Run them one at a time, never two together. The heavy ones, which take a large
share of a small machine's memory, are both `npm ci` lines, `npm run build`,
`npm test`, `npm run check:extension` and the website's `npm ci` and
`npm run check`.

Native checks need the built native engine. Without it they stop at once,
most of them on a missing `.local/config.json`. Build it once with
`npm run setup:lean -- --lean /absolute/path/to/lean-4.28.0/bin/lean --download`
(several GB into the ignored `.local/`); later, `npm run setup:lean` rebuilds
with the saved paths. Then:

- `npm run test:axioms`: the proved core's axioms, a negative control and a
  kernel replay. Run it after any change under `lean/`, `vendor/` or
  `scripts/axiom-*`.
- The focused native suite for what you changed, for example
  `npm run test:editor` or `npm run test:corpus`. The list is in `package.json`
  and in [status](docs/status.md#validation-and-evidence).
- `npm run check`: the build and the reader-driver, unit, server and
  source-dependency checks, then every native suite and the axiom audit.

Every native check is heavy. Run them one at a time, and never while
`setup:lean` is rebuilding: the corpus compares executable hashes. CI runs no
native check, so say in the commit message which ones you ran. Known failing
checks are listed in [status](docs/status.md#known-failing-checks); do not
spend time rediscovering them.

## Adding a test

- Unit or renderer: `src/<area>/<name>.test.ts` beside the module. Vitest runs
  `src/**/*.test.ts` with `npm test`.
- Server: `server/<name>.test.ts`, run by `npm run test:server`.
- Extension: `extension/src/<name>.test.ts`, run by `npm run check:extension`.
- Native: extend `scripts/<area>-integration.ts`, or add a script with an npm
  entry and add that entry to `check`.
- Expectations for native suites: `corpus/cases.ts`, `corpus/structures.ts`.
- Use real Lean exports for anything that depends on elaboration. Include a
  renamed or unfamiliar definition, and a boundary case that must stay unknown.
- A bug fix comes with a test that fails without the fix. Test what a reader
  sees, not the implementation's branches.

## Commits

- One logical change per commit, built and passing the checks above.
- Subject: imperative, at most 72 characters, saying what changes for a reader
  or a contributor.
- Body: why, what changed, and what did not. End the body, before any
  trailers, with `Checked:` and the commands actually run, with counts.
- Write only about this repository's code and documents. No personal names
  except in credit lines and `Co-Authored-By` trailers, no quotations from
  conversations, no local paths, no references to files outside the repository,
  and no project-management state (who approved what, what is awaited).
- Never force-push, rewrite history or delete branches. A passing check is not
  permission to push, publish, deploy or install; do what the task authorizes.

## Documents

When behaviour changes, update `docs/status.md` and the contract page in the
same commit. Do not add dated reports to `docs/`; the commit message is the
record. Generated output and native builds go in `.local/`.
