# StatementLens

A local mathematical workbench that turns Lean statements into connected, inspectable views. Lean resolves types and scope; StatementLens identifies shared objects and relationships, then automatically composes geometry, mapping diagrams, and quantifier dependencies.

The goal is a general mathematical statement visualizer. Extensions describe reusable mathematical constructions, not named theorems. This release provides the semantic foundation and working visual vocabulary; it does not claim complete visual understanding of arbitrary mathematics.

## Explore a statement

Enter a Lean expression or choose an example, then select **Interpret statement**. The editor supports syntax highlighting, search, history, and Lean symbol abbreviations such as `\forall` followed by Tab. The **Structure** tab lets you focus on part of a long statement while retaining its enclosing context.

- **Connected objects:** sets, membership, inclusion, functions, applications, images, preimages, relations, and metric regions share object identities across fragments. Select an object to inspect its type and occurrences.
- **Automatic composition:** a planner chooses a primary view and supporting representations. Abstract mathematics remains structurally inspectable even when no numerical model is available. Coverage distinguishes interpreted, partially interpreted, and structural fragments.
- **Quantifier dependencies:** `∀` introduces an arbitrary choice; `∃` asks for a candidate witness using earlier choices in its branch. Hypotheses and definition parameters are labeled separately. Changing an earlier numerical choice clears dependent witnesses.
- **Geometry:** audited real and finite-dimensional Euclidean/max metrics receive interactive regions. The same ball notation can produce a disk or a square depending on its actual metric. High-dimensional numerical views offer labeled coordinate slices and distance profiles.
- **Declarations and definitions:** look up a declaration such as `Metric.mem_ball` or `Function.comp`. Theorems expose their statements; definitions expose their signatures. Explicitly expand a trusted definition such as `Function.Injective` to reveal its logical structure.
- **Source provenance:** a selection in the editor exposes its type using exact Lean InfoTree source ranges. Export the typed analysis, semantic document, plan, and current scenario as JSON.

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

## Scope and isolation

This is a standalone local web application with a versioned Lean extraction contract and a renderer-independent semantic document. The same boundary is designed for a future Lean editor panel. A Rocq adapter is not implemented.

Only fixed, trusted mathlib modules are loaded. Input passes a closed declarative syntax allowlist, elaboration, unresolved-placeholder checks, and a kernel type check. Existing formal projects are not opened or edited. Arbitrary imports, pasted proof scripts, and user command execution are outside the input contract. The full expression must elaborate before its parts can be inspected; incomplete-term recovery remains future work.

Custom metric and arithmetic instances remain symbolic unless their interpretation is audited. View rules use typed constructors and argument roles rather than matching theorem names or source spelling. Unsupported parts are retained with explicit coverage information. Numerical vectors have a resource bound of 256 coordinates; larger spaces retain typed structure rather than receiving a fabricated numerical model.

Build products and machine-specific paths stay in ignored `.local/`. Existing toolchains and caches are read-only inputs. There is no cloud analysis, model API, telemetry, or external font request. The server binds to loopback and checks request origins. Its separate worker is not a hardened sandbox for arbitrary uploaded Lean projects.

See [the architecture](docs/architecture.md) for the semantic registry, planner, upstream research, and remaining work. [The Lean contract](docs/lean-contract.md) documents declaration inspection, definition expansion, source ranges, and instance safeguards.

## Verification

```sh
npm run check
```

This builds the application and runs unit, server, native Lean, and end-to-end semantic checks. [The verification record](docs/verification.md) records tested behaviors and limits. Passing these tests is not a claim that the application has no bugs.

## Attribution

Codex under the supervision of Neil Yuanting Li.

Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency attribution: [NOTICE](NOTICE).
