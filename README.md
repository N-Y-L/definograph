# StatementLens

Read a Lean mathematical statement as a visual sequence, with its logical overview alongside. StatementLens introduces the objects, distinguishes assumptions from conclusions, preserves quantifier order, and draws relationships using the resolved Lean types. Understanding the statement is the primary purpose; numerical experimentation is optional.

The goal is a general mathematical statement visualizer. Extensions describe reusable mathematical constructions, not named theorems. This release provides the semantic foundation and working visual vocabulary; it does not claim complete visual understanding of arbitrary mathematics.

## Read a statement

Choose a statement from the top bar to read it immediately. Use **Next** to follow its constructions in order, or jump through the overview. **Full visual statement** opens the complete static reading. To enter your own, open **Lean source**, enter a Lean expression, and select **Interpret statement**. Editing and inspection use focused panels so the mathematical sequence and overview have the main surface. The editor supports syntax highlighting, search, history, and Lean symbol abbreviations such as `\forall` followed by Tab. The **Structure** tab lets you focus on part of a long statement while retaining its enclosing context.

- **Connected objects:** sets, membership, inclusion, functions, applications, images, preimages, relations, and metric regions share object identities across fragments. Select an object to inspect its type and occurrences. **Inspect** also exposes coverage and definition expansion.
- **Graph constraints:** adjacency, proper colorings, colorability, graph homomorphisms, and embeddings have reusable diagrams. Named vertices and mapped values keep their identities across the guided steps. Available color labels are distinct from an assigned coloring; zero- and one-color cases keep their exact meaning. No complete graph instance or planar drawing is invented.
- **Compound sets:** union, intersection, difference, and complement compose inside membership, inclusion, and equality. Highlighted regions encode allowed membership combinations; hatching identifies combinations required to be empty. No sample element or nonempty intersection is invented.
- **Typed constructions:** abstract maps connect their domain and codomain from Lean type expressions. Curried maps retain their ordered inputs, and dependent families retain which earlier arguments their types use. No coordinate model or finite cardinality is invented.
- **A complete visual reading:** every logical node is retained; binders and connected logical regions are composed into a reading sequence with an overview. Negation, alternatives, equivalence directions, and implication roles stay visible. Selecting a fragment focuses it without removing the surrounding statement. Abstract objects and maps need no coordinates. Coverage distinguishes mathematical interpretation from faithful logical structure.
- **Quantifier dependencies:** `∀` introduces an arbitrary choice; `∃` asks for a candidate witness using earlier choices in its branch. Hypotheses and definition parameters are labeled separately. Numerical witness controls appear only in optional exploration; changing an earlier numerical choice clears dependent witnesses.
- **Symbolic geometry:** audited metrics distinguish intervals, circular balls, and maximum-metric square balls without choosing sample coordinates. Unknown radius signs retain their positive, zero, and negative cases. Higher-dimensional balls and spheres use their distance condition without selecting a projection. **Explore a sample** opens optional numerical slices and distance profiles.
- **Declarations and definitions:** look up a declaration such as `Metric.mem_ball` or `Function.comp`. Theorems expose their statements; definitions expose their bodies and typed signatures separately. The reader can automatically inspect one small, checked definition when it reduces uninterpreted structure. An on-screen notice identifies that change, and **Inspect** retains the original reading and a toggle. Larger or unhelpful definitions remain symbolic; explicit bounded expansion is also available.
- **Actionable coverage:** inspect the recognized vocabulary and remaining unknown definitions for the selected fragment, jump to their source context, or expand an eligible definition. Coverage describes interpretation by the installed rules, not mathematical truth or a percentage of all mathematics.
- **Readable notation:** optionally show a LeanTeX rendering of the elaborated statement alongside its visual sequence. Typesetting is local with KaTeX; unsupported notation falls back to Lean and never changes the expression used for diagrams.
- **Source provenance:** a selection in the editor exposes its type using exact Lean InfoTree source ranges. Export the typed analysis, semantic document, reading sequence, overview, optional view plan, and scenario as JSON.

For example, this statement generates connected set and membership views without any coordinates:

```lean
∀ (A B : Set ℝ) (x : ℝ),
  A ⊆ B → x ∈ A → x ∈ B
```

This one adds geometry under the standard Euclidean metric:

```lean
∀ (c : EuclideanSpace ℝ (Fin 2)) (ε : ℝ),
  0 < ε → ∀ P : EuclideanSpace ℝ (Fin 2),
  P ∈ Metric.ball c ε → dist P c < ε
```

A graph statement uses the same reading pipeline:

```lean
∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (u v : V),
  G.Adj u v → c u ≠ c v
```

This exposes the adjacency condition and its required color inequality. It neither chooses a coloring nor establishes the four-color theorem. See [the graph iteration](docs/graph-iteration.md) for the semantic boundary.

Lean checks the input's type. It does **not** prove arbitrary submitted propositions. Symbolic diagrams retain their logical context; numerical samples are approximations and do not establish quantified claims.

## Run locally

Requirements: Node.js 22.12 or later, Lean **4.28.0**, and a built mathlib cache at revision **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. Versioned setup instructions and the isolated dependency option are in [the Lean contract](docs/lean-contract.md).

```sh
npm ci
npm run setup:lean -- \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --packages /absolute/path/to/a/built/.lake/packages
npm run dev
```

Open [the local application](http://127.0.0.1:5173). After the initial configuration, `npm run setup:lean` rebuilds the worker without further arguments. To run the production build:

```sh
npm run build
npm start
```

The production application listens at [127.0.0.1:4317](http://127.0.0.1:4317). The first analysis loads mathlib; later analyses reuse the imported environment while starting a fresh elaboration context.

## Use your Lean editor

The optional VS Code extension reads a selected proposition from a **Lean 4.28.0** project, including unsaved changes in the active buffer and its built imported definitions. It keeps local parameters and assumptions attached and invalidates diagrams after edits.

```sh
npm ci --prefix extension
npm run check:extension
```

Install the resulting `.local/statement-lens-editor-0.6.0.vsix` with **Extensions: Install from VSIX…**, set `statementLens.engineDirectory` to this checkout, then run **Statement Lens: Visualize Selection** in a trusted Lean workspace. The package has not been published. Native extraction, mocked controller, and hosted-browser checks do not substitute for installing and exercising the extension in an actual VS Code GUI; that workflow remains unverified. [The editor guide](docs/editor-integration.md) explains exact selection, explicit definition expansion, project isolation, and the initial symbolic-only interpretation boundary.

## Product direction

The target is general mathematical statements, including abstract definitions and maps. Reusable rules recognize constructions rather than named theorems. The default is a visual sequence with a linked overview; examples and coordinates do not supply unstated assumptions. See [the atlas iteration](docs/atlas-iteration.md) for typed construction and reading-region boundaries, [the statement-first review](docs/statement-first-review.md) for concrete acceptance cases and [the reading contract](src/reading/types.ts) for the renderer-independent representation.

The [visual-method notes](docs/visual-method.md) document design references from [3Blue1Brown/Manim](https://github.com/3b1b/manim) and [Penrose](https://penrose.cs.cmu.edu/examples): persistent object identity, ordered constructions, and the [guided-reading layer](docs/guided-reading.md), which preserves the same logical scope as the static diagrams. The current graph figures use local SVG and add no layout or animation runtime.

The general goal remains unfinished. Planar graph structure, the four-color theorem, tangent fields and bundles, derivatives, and constant-rank normal forms do not yet have semantic grammars. Next shared foundations are restricted maps with local inverse laws, indexed fibers and sections, and linear-map structure. [The roadmap](docs/roadmap.md) and [coverage corpus](docs/coverage-corpus.md) keep those gaps explicit.

## Scope and isolation

This is a standalone local web application with a versioned Lean extraction contract and a renderer-independent semantic document. An optional VS Code extension reads a selected proposition from its actual Lean project context. See [the editor integration](docs/editor-integration.md) for installation, supported toolchains, and the separate trust boundary. A Rocq adapter is not implemented.

In standalone browser mode, only fixed, trusted modules are loaded. Input passes a closed declarative syntax allowlist, elaboration, unresolved-placeholder checks, and a kernel type check. Standalone input does not open existing formal projects. Editor mode reads the selected trusted project and its imported environment in a separate process; the adapter does not rewrite project files or configuration. Arbitrary imports, pasted proof scripts, and user command execution are outside the standalone input contract. Editor mode elaborates trusted Lean source, which can run project elaborators and commands; the process is not a security sandbox. The selected expression must elaborate without unresolved placeholders; this is not general recovery from incomplete mathematical syntax.

Custom metric and arithmetic instances remain symbolic unless their interpretation is audited. View rules use typed constructors and argument roles rather than matching theorem names or source spelling. Unsupported parts are retained with explicit coverage information. Numerical vectors have a resource bound of 256 coordinates; larger spaces retain typed structure rather than receiving a fabricated numerical model.

Build products and machine-specific paths stay in ignored `.local/`. Existing toolchains and caches are read-only inputs. There is no cloud analysis, model API, telemetry, or external font request. The server binds to loopback and checks request origins. Its separate worker is not a hardened sandbox for arbitrary uploaded Lean projects.

The optional notation provider is documented in [the LeanTeX integration record](docs/leantex-integration.md).

See [the architecture](docs/architecture.md) for the semantic registry, planner, upstream research, and remaining work. [The Lean contract](docs/lean-contract.md) documents declaration inspection, definition expansion, source ranges, and instance safeguards.

## Verification

```sh
npm run check
```

This builds the application and runs unit, server, native Lean, project-context, and end-to-end semantic checks. The reproducible vocabulary audit is also available as `node --import tsx scripts/corpus-audit.ts`; its JSON and Markdown reports stay in ignored `.local/`. `npm run check:extension` additionally checks and packages the optional editor extension after installing its dependencies. [The verification record](docs/verification.md) records tested behaviors and limits. Passing these tests is not a claim that the application has no bugs.

## Attribution

Codex under the supervision of Neil Yuanting Li.

Lean and mathlib supply the checked mathematical environment, including [the pinned graph-coloring definitions](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Coloring.lean). LeanTeX, KaTeX, CodeMirror, and React supply the documented printing and interface components. 3Blue1Brown/Manim and Penrose are credited design references; no code, scene assets, or styles from either were copied or bundled.

Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency attribution: [NOTICE](NOTICE).
