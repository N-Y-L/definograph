# StatementLens

Read a Lean mathematical statement as a visual sequence, with its logical overview alongside. StatementLens introduces the objects, distinguishes assumptions from conclusions, preserves quantifier order, and draws relationships using the resolved Lean types. Understanding the statement is the primary purpose; numerical experimentation is optional.

The goal is a general mathematical statement visualizer. Extensions describe reusable mathematical constructions, not named theorems. This release provides the semantic foundation and working visual vocabulary; it does not claim complete visual understanding of arbitrary mathematics.

## Read a statement

Choose a statement from the top bar to read it immediately. To enter your own, open **Lean source**, enter a Lean expression, and select **Interpret statement**. Editing and inspection use focused panels so the mathematical sequence and overview have the main surface. The editor supports syntax highlighting, search, history, and Lean symbol abbreviations such as `\forall` followed by Tab. The **Structure** tab lets you focus on part of a long statement while retaining its enclosing context.

- **Connected objects:** sets, membership, inclusion, functions, applications, images, preimages, relations, and metric regions share object identities across fragments. Select an object to inspect its type and occurrences. **Inspect** also exposes coverage and definition expansion.
- **Typed constructions:** abstract maps connect their domain and codomain from Lean type expressions. Curried maps retain their ordered inputs, and dependent families retain which earlier arguments their types use. No coordinate model or finite cardinality is invented.
- **A complete visual reading:** every logical node is retained; binders and connected logical regions are composed into a reading sequence with an overview. Negation, alternatives, equivalence directions, and implication roles stay visible. Selecting a fragment focuses it without removing the surrounding statement. Abstract objects and maps need no coordinates. Coverage distinguishes mathematical interpretation from faithful logical structure.
- **Quantifier dependencies:** `∀` introduces an arbitrary choice; `∃` asks for a candidate witness using earlier choices in its branch. Hypotheses and definition parameters are labeled separately. Numerical witness controls appear only in optional exploration; changing an earlier numerical choice clears dependent witnesses.
- **Symbolic geometry:** audited metrics distinguish intervals, circular balls, and maximum-metric square balls without choosing sample coordinates. Unknown radius signs retain their positive, zero, and negative cases. Higher-dimensional balls and spheres use their distance condition without selecting a projection. **Explore a sample** opens optional numerical slices and distance profiles.
- **Declarations and definitions:** look up a declaration such as `Metric.mem_ball` or `Function.comp`. Theorems expose their statements; definitions expose their bodies and typed signatures separately. Explicitly expand a trusted definition such as `Function.Injective` to reveal its logical structure.
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

## Product direction

The target is general mathematical statements, including abstract definitions and maps. Reusable rules recognize constructions rather than named theorems. The default is a visual sequence with a linked overview; examples and coordinates do not supply unstated assumptions. See [the atlas iteration](docs/atlas-iteration.md) for typed construction and reading-region boundaries, [the statement-first review](docs/statement-first-review.md) for concrete acceptance cases and [the reading contract](src/reading/types.ts) for the renderer-independent representation.

The [visual-method notes](docs/visual-method.md) document lessons from 3Blue1Brown and Manim: persistent object identity, ordered constructions, and a future guided-reading layer that preserves the same logical scope as the static diagrams.

## Scope and isolation

This is a standalone local web application with a versioned Lean extraction contract and a renderer-independent semantic document. The same boundary is designed for a future Lean editor panel. A Rocq adapter is not implemented.

Only fixed, trusted modules are loaded. Input passes a closed declarative syntax allowlist, elaboration, unresolved-placeholder checks, and a kernel type check. Existing formal projects are not opened or edited. Arbitrary imports, pasted proof scripts, and user command execution are outside the input contract. The full expression must elaborate before its parts can be inspected; incomplete-term recovery remains future work.

Custom metric and arithmetic instances remain symbolic unless their interpretation is audited. View rules use typed constructors and argument roles rather than matching theorem names or source spelling. Unsupported parts are retained with explicit coverage information. Numerical vectors have a resource bound of 256 coordinates; larger spaces retain typed structure rather than receiving a fabricated numerical model.

Build products and machine-specific paths stay in ignored `.local/`. Existing toolchains and caches are read-only inputs. There is no cloud analysis, model API, telemetry, or external font request. The server binds to loopback and checks request origins. Its separate worker is not a hardened sandbox for arbitrary uploaded Lean projects.

The optional notation provider is documented in [the LeanTeX integration record](docs/leantex-integration.md).

See [the architecture](docs/architecture.md) for the semantic registry, planner, upstream research, and remaining work. [The Lean contract](docs/lean-contract.md) documents declaration inspection, definition expansion, source ranges, and instance safeguards.

## Verification

```sh
npm run check
```

This builds the application and runs unit, server, native Lean, and end-to-end semantic checks. [The verification record](docs/verification.md) records tested behaviors and limits. Passing these tests is not a claim that the application has no bugs.

## Attribution

Codex under the supervision of Neil Yuanting Li.

Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency attribution: [NOTICE](NOTICE).
