# Definograph

**Read a Lean statement as a picture of its structure**: what is chosen before what, what is assumed, which maps connect which objects, and where interpretation stops. The reading is built from Lean's own types and definitions. Abstract objects get no invented coordinates, and numerical sample views are optional and kept apart from what the statement asserts.

A research prototype, built for CS 124 at UIUC. It is not a general mathematical visualizer yet; [status](docs/status.md) says exactly what works.

## What it does

Order matters, so the reader shows it. These two statements differ only in quantifier order:

```lean
∀ x : ℝ, ∃ y : ℝ, x < y      -- y is chosen after x, and may depend on it
∃ y : ℝ, ∀ x : ℝ, x < y      -- y is fixed before any x is chosen
```

The reader lays each one out as a sequence of choices, assumptions and conditions with its logical overview alongside, and the dependency of `y` on `x` appears in the first and not in the second.

Names you choose are labels, not meaning. A structure written today, never seen by Definograph:

```lean
structure Passage (A B : Type) where
  advance : A → B
  retreat : B → A
  roundTrip : ∀ x, retreat (advance x) = x

#check ∀ (A B : Type) (p : Passage A B), True
```

In the editor extension it is read through Lean's checked projections: two maps between `A` and `B`, and a law saying the round trip returns its input. Nothing is registered under the name `Passage`, and renaming a record and all its fields leaves the extracted fields, maps and law kinds unchanged (`npm run test:decomposition`).

Mathematics the reader cannot yet interpret is shown as typed structure marked as uninterpreted. Known gaps are listed in [status](docs/status.md).

## Two surfaces

- **Web reader.** A local app: pick or type a statement and step through it with **Next**. **Inspect** shows what was and was not interpreted.
- **Lean editor extension.** A VS Code command, **Definograph: Visualize Selection**, reads a selected proposition in its real project context, including unsaved text.

Both surfaces share one reader. Rocq is not implemented.

## Where it is going

The 0.7 code partly works by recognition: some relation kinds and figures are written per domain (sets, graphs, metric balls, restricted maps). The [architecture decision](docs/design/architecture-decision.md) proposes replacing this with a compositional design:

- **Fundamental objects** are eight logical building blocks (binders, and/or, equality, function application, records, atomic terms, types, and folded parts). On top of them sits a short, counted list of *readings*: name-free patterns such as containment, an order, or a symmetric relation, which Lean certifies each time one is used.
- **Decomposition** rewrites the Lean term into those blocks by checked steps. When several decompositions are valid, a fixed and inspectable order picks one.
- **Composition** is a small algebra. Pieces placed side by side mean "and", an output wired into an input means application, and nested frames carry quantifiers, implication and negation. The decision states which algebraic laws hold and which fail.
- **Meaning and presentation** meet only through facts Lean has certified. Names, coordinates and prose never reach the drawing code.

The claim to test is that pictures grow per theory, never per object or theorem. It rests on a hand-executed stress test over seven statements from seven areas; nothing in the new design is implemented yet. The first vertical slice, its acceptance criteria and human reading gates are in the decision, which amends the [TNF specification](docs/design/tnf-specification.md).

## Run it

Requirements: Node.js 22.12+, a Lean 4.28.0 toolchain, macOS or Linux (WSL on Windows). Mathlib is pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

```sh
git clone https://github.com/N-Y-L/definograph.git
cd definograph
npm ci
npm run setup:lean -- --lean /absolute/path/to/lean-4.28.0/bin/lean --download
npm run dev          # then open http://127.0.0.1:5173
```

Setup does not install Lean or change Elan defaults. `--download` puts the pinned mathlib dependencies (several GB) in this checkout's ignored `.local/`; `--packages /path/to/.lake/packages` reuses an existing matching build instead. The web reader accepts a statement term, not a file of declarations. For a production build: `npm run build`, `npm start`, then open http://127.0.0.1:4317. Details: [Lean contract](docs/lean-contract.md).

**Editor extension:** run `npm run build`, then `npm ci --prefix extension` and `npm run check:extension`. Install `.local/statement-lens-editor-0.7.1.vsix` with **Extensions: Install from VSIX…**, and set `statementLens.engineDirectory` to this checkout. The package is local, not on the Marketplace, and a full manual VS Code session is not yet verified. See the [editor guide](docs/editor-integration.md). The `statementLens` names are compatibility identifiers from an earlier project name.

## Checks

```sh
npm run build && npm test && npm run test:server   # portable
npm run check:extension                            # extension type checks and packaging
npm run check                                      # build, unit, server and all native Lean suites
```

CI runs the first two lines; the native suites need the Lean setup above. Tests check stated contracts and catch regressions. They do not measure whether a reader understands the mathematics; that needs people, and the decision's reading gates provide for it.

## Trust boundaries

Lean checks that a statement is well typed. It does not prove the statement, verify the diagrams, or certify that the picture explains anything. The editor path re-elaborates the whole trusted buffer in a separate process, and Lean commands can run code, so it is not a sandbox. Statements and project code are processed locally; nothing is sent to a cloud service or a model API. See [execution limits](docs/editor-integration.md#execution-and-isolation-limits).

## Documentation

Start with [status](docs/status.md), the [code map](docs/architecture.md), and the [architecture decision](docs/design/architecture-decision.md). The [documentation index](docs/README.md) separates current contracts from historical iteration reports. Contributors should read [AGENTS.md](AGENTS.md) and [CONTRIBUTING.md](CONTRIBUTING.md).

## Credits and license

The 0.7 prototype was developed by Codex. The architecture decision and further development are by Claude. Both worked under the supervision of Neil Yuanting Li.

[Apache License 2.0](LICENSE). [Lean](https://github.com/leanprover/lean4) and [mathlib](https://github.com/leanprover-community/mathlib4) provide the formal environment. [LeanTeX](https://github.com/kmill/LeanTeX) is vendored for optional notation, and KaTeX, CodeMirror and React support the interface. [3Blue1Brown/Manim](https://github.com/3b1b/manim) and [Penrose](https://penrose.cs.cmu.edu/) informed the visual approach, but none of their code is bundled. Reuse and attribution are recorded in [NOTICE](NOTICE) and [vendor/LeanTeX](vendor/LeanTeX); citation metadata is in [CITATION.cff](CITATION.cff).
