# Definograph

An experimental foundation for reading mathematical statements through diagrams, using Lean's actual types, definitions, and logical context.

The aim is general: a long statement should become a visual sequence of objects and relationships, with an overview alongside. Abstract spaces should not need invented coordinates. Understanding the statement comes first; playing with examples is secondary.

**This is a research prototype, not a general mathematical visualizer.** It contains a working Lean-backed reader and useful extraction machinery, but the central compositional engine is incomplete. The repository is being reorganized around that problem. [Current status](docs/status.md) describes what works; the [architecture proposal](docs/design/architecture-reset.md) describes what must change.

## The central problem

Adding one diagram per theorem cannot achieve this goal. The intended architecture is:

```text
Lean statement + actual context
         ↓
typed objects, definitions, scopes, and dependencies
         ↓
bounded, checked decomposition with named folds
         ↓
shared mathematical relations + compositional visual rules
         ↓
visual sequence and linked overview
```

The decomposition and composition stages above are **the research direction**, not a claim about a completed implementation. Fully unfolding a definition does not by itself produce an understandable explanation. The reader needs to preserve useful abstractions, choose which relationships to expose, and say where interpretation stops. A concrete numerical model is optional and must remain distinct from what the statement asserts.

The next milestone is one shared decomposition mechanism that works inside nested definitions and structure laws, preserves scope and object identity, and succeeds on previously unseen definitions without registering their names. The [proposal and acceptance criteria](docs/design/architecture-reset.md) make that milestone reviewable.

## What runs today

The local web reader elaborates accepted Lean terms or inspects imported declarations. It presents quantifiers, assumptions, conclusions, typed maps, sets, and selected geometric relationships in a guided sequence. It can reflect the direct fields and laws of an unfamiliar Lean record. A VS Code adapter reads selected propositions in a trusted project's actual environment, including the active buffer's unsaved text.

For example, a project can define:

```lean
structure Passage (A B : Type) where
  advance : A → B
  retreat : B → A
  roundTrip : ∀ x, retreat (advance x) = x

#check ∀ (A B : Type) (p : Passage A B), True
```

The record's maps and law are available through checked projections; `Passage` is not a registered mathematical name. This demonstrates a reusable part of the foundation. It does **not** establish recursive understanding: a law hidden behind another definition can still remain folded.

Existing adapters cover selected set, metric, graph, and restricted-map relations. These are bounded capabilities, not evidence that the hairy-ball, constant-rank, or four-color theorem has a complete visual explanation. Unsupported mathematics remains visible as typed or logical structure. Rocq support is not implemented.

Lean checks the submitted statement's type. It does **not** prove the statement, verify the diagrams, or certify that the reader understands its mathematics.

## Run locally

Requirements: Node.js **22.12+**, a Lean **4.28.0** toolchain, and macOS or Linux; use WSL on Windows. Mathlib is pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

```sh
git clone https://github.com/N-Y-L/definograph.git
cd definograph
npm ci
npm run setup:lean -- \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --download
npm run dev
```

Supply an existing Lean 4.28.0 executable or extract the [official release](https://github.com/leanprover/lean4/releases/tag/v4.28.0) into a dedicated directory. Setup does not install Lean or change Elan defaults. `--download` fetches the pinned mathlib dependencies into this checkout's ignored `.local/` directory and can use several GB. Alternatively, use `--packages /absolute/path/to/a/built/.lake/packages` to read an existing matching cache. See the [setup and extraction contract](docs/lean-contract.md).

Open [localhost:5173](http://127.0.0.1:5173), choose a statement, and follow **Next**. **Lean source** accepts a statement term, not a file of declarations. **Inspect** exposes interpretation gaps and available expansions. Optional LeanTeX notation provides a more familiar mathematical rendering.

For a production build, run `npm run build` followed by `npm start`, then open [localhost:4317](http://127.0.0.1:4317).

### Read from a Lean editor

After building the application and configuring Lean:

```sh
npm ci --prefix extension
npm run check:extension
```

Install `.local/statement-lens-editor-0.7.1.vsix` using **Extensions: Install from VSIX…**. Set `statementLens.engineDirectory` to this checkout and run **Definograph: Visualize Selection** in a trusted Lean 4.28.0 workspace with built imports. The VSIX is local; it is not published to the Marketplace. The real VS Code GUI workflow still needs validation beyond automated native and controller tests. See the [editor guide](docs/editor-integration.md).

The retained `StatementLens` Lean module names, `statementLens.*` settings, and extension package ID are compatibility identifiers from the prototype's previous name.

## Develop and evaluate

Start with [AGENTS.md](AGENTS.md), [current status](docs/status.md), the [current code map](docs/architecture.md), and the [architecture reset](docs/design/architecture-reset.md). The [roadmap](docs/roadmap.md) orders the work by acceptance gates. The [documentation index](docs/README.md) separates current contracts from historical iteration reports.

```sh
# Portable checks; no Lean setup or download
npm run build
npm test
npm run test:server

# With the pinned native worker configured
npm run check

# With extension dependencies installed
npm run check:extension
```

GitHub CI runs the portable and extension checks. Native Lean integration requires the separate pinned setup. Test results measure specific contracts and regressions; they do not measure how much mathematics the reader understands. Contribution guidance is in [CONTRIBUTING.md](CONTRIBUTING.md).

Standalone input uses fixed trusted imports and a restricted term syntax. Editor mode re-elaborates the **whole trusted active buffer** in a separate process; Lean commands and elaborators can execute code. It is not a security sandbox. The adapter does not rewrite formal project files, toolchains, or Lake configuration. There is no cloud analysis or model API. [Execution boundaries](docs/editor-integration.md#execution-and-isolation-limits) are part of the contract.

## License and credits

[Apache License 2.0](LICENSE). This permissive license includes an express patent grant and supports reuse in research and editor tooling while preserving applicable license and attribution notices. Third-party code keeps its own license.

Codex under the supervision of Neil Yuanting Li.

[Lean](https://github.com/leanprover/lean4) and [mathlib](https://github.com/leanprover-community/mathlib4) provide the formal environment. [LeanTeX](https://github.com/kmill/LeanTeX) is vendored for optional notation; KaTeX, CodeMirror, and React support the interface. [3Blue1Brown/Manim](https://github.com/3b1b/manim) and [Penrose](https://penrose.cs.cmu.edu/) informed the visual approach; their code and assets are not bundled. Exact reuse, revisions, and attribution are recorded in [NOTICE](NOTICE) and [vendor/LeanTeX](vendor/LeanTeX). Citation metadata is in [CITATION.cff](CITATION.cff).
