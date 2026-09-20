# Contributing to Definograph

Definograph is a research project, not a completed general mathematical visualizer.
Contributions should advance the [architecture](docs/architecture.md) toward
reusable decomposition and composition. Read [current status](docs/status.md)
and [the roadmap](docs/roadmap.md) before choosing work.

## Useful contributions

- Improve a general decomposition rule, its provenance, or its stopping boundary.
- Compose existing typed objects and logical relationships into clearer readings.
- Supply an unfamiliar definition that exposes a general failure, with expected
  identities, dependencies, and meaning boundaries.
- Evaluate whether a diagram helps a reader understand a statement, separately
  from whether extraction and rendering succeed.
- Improve editor integration, accessibility, or reproducible setup without
  changing a user's formal environment.

A presentation for one named theorem may be a useful illustration, but it is
not evidence of generality. A new optional mathematical lens should state the
checked structure it requires, which relationships it preserves, and what it
does not encode. Names and notation are labels, not evidence of meaning.

## Development setup

Use Node.js 22.12 or later and the committed npm lockfiles:

```sh
npm ci
npm ci --prefix extension --ignore-scripts
```

The TypeScript, browser, server, and extension checks below do not need Lean.
Native extraction requires Lean 4.28.0 and the pinned mathlib cache. Follow the
[README setup](README.md) and [Lean setup contract](docs/lean-contract.md)
explicitly; the default checks do not install a toolchain for you. Native
artifacts and machine paths belong in ignored `.local/`.

The editor adapter executes trusted Lean source in a separate process. It must
not modify the user's source, Lake configuration, dependencies, or global
toolchain. Do not add `sorry`, axioms, or looser kernel checks to make an example
render. See [the editor boundary](docs/editor-integration.md).

## Validation

The fast, toolchain-independent check set is:

```sh
npm run build
npm test
npm run test:server
npm run check:extension
```

GitHub CI runs those commands. Its result does **not** imply native Lean checks
or an installed VS Code extension passed. It installs npm dependencies; it does
not run `setup:lean`, Lake, Elan, or download mathlib.

For native or semantic changes, configure and build the native engine first,
then run the relevant integration suite. The complete local check set is:

```sh
npm run setup:lean
npm run check
npm run check:extension
```

`setup:lean` without arguments requires a previous local configuration and
rebuilds against it. Run it before the tests, not concurrently with native
integration tests: the corpus checks executable hashes to detect mixed builds.
Useful focused commands include `test:decomposition`, `test:structure-export`,
`test:semantic`, `test:reading`, `test:editor`, and `test:corpus`; see
[the status test map](docs/status.md#validation-and-evidence).

Use real exported expressions when a change depends on elaboration, coercions,
instances, or scope. Include negative cases as well as supported ones. For
general decomposition, rename records and fields, reuse shared projections, and
exercise opaque definitions and resource limits. Test the mathematical contract
rather than duplicating the implementation's branching logic.

Browser changes need a visual and interaction check of the production reader,
including one partially interpreted statement. Document any untested viewport
or host. A snapshot, an SSR render, and a mocked VS Code controller each test
different things; none establishes that a mathematical explanation is useful.

## Pull requests and reports

Explain the problem, resulting behavior, relevant validation, and remaining
limitations. Include the Lean statement or a minimal trusted fixture when it
helps reproduce a semantic issue. Remove private mathematical work, local
machine paths, credentials, and generated artifacts before sharing a report.

Update the corresponding contract and current status if the supported boundary
changes. Historical verification records should retain their original scope.
Credit reused sources and preserve their licenses; distinguish copied code,
runtime dependencies, and design inspiration in [NOTICE](NOTICE).

Project code uses [Apache-2.0](LICENSE). Contributions are provided under that
license; third-party files retain the notices and licenses recorded with them.
