# StatementLens

A local application for inspecting the geometry and logical structure of Lean 4 mathematical statements. Lean elaborates a proposition; StatementLens finds supported fragments, retains their quantifier context, and gives them interactive views.

For example,

```lean
∀ (c : EuclideanSpace ℝ (Fin 2)) (ε : ℝ),
  0 < ε → ∀ P : EuclideanSpace ℝ (Fin 2),
  P ∈ Metric.ball c ε → dist P c < ε
```

produces a disk and a movable representative point. Changing the ambient type to `ℝ × ℝ` produces a square, because mathlib's standard product metric is the maximum metric. The interpretation comes from elaborated expressions and checked instances, rather than matching the input text.

## Explore a statement

Choose an example or enter a proposition with its variable binders, then select **Analyze statement**. The logical tree lets you inspect a condition inside a larger statement. Select a marked fragment or a view tab to see its geometry; the scenario controls follow the variables in scope.

- **Quantifiers:** `∀` is an arbitrary representative, not an enumeration of every point. `∃` is a candidate witness that can depend only on earlier choices. Reversing their order changes which choices remain fixed.
- **Metrics:** real-line intervals, product/max-norm balls, and Euclidean balls have separate interpretations. Open boundaries, closed boundaries, spheres, and nonpositive radii are distinguished.
- **Dimensions:** recognized finite real vector spaces in dimensions 2–12 use labeled coordinate slices above two dimensions. Omitted coordinates and the displayed axes are adjustable. A 3-sphere has ambient dimension four; the view is an intersection with a coordinate plane.
- **Functions:** explicit supported real expressions can be sampled as graphs. Unknown functions can still have symbolic mapping diagrams.
- **Partial inspection:** supported fragments remain discoverable inside an otherwise unsupported, well-typed statement. The entire input must first elaborate; recovery from an invalid outer expression is not implemented.

Lean checks that the input is a well-formed proposition. It does **not** prove the proposition. The renderer and floating-point evaluator are not formally verified, and a finite numerical scan establishes neither a universal claim nor a certified counterexample.

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

This version is a standalone local web application, with a portable expression format for a future VS Code adapter. It accepts proposition terms, including the logical body of a definition or theorem statement. It does not open or edit formal projects, execute pasted proof scripts, add declarations, load arbitrary imports, or claim to visualize all of mathlib.

Only fixed, trusted mathlib modules are loaded. User input passes a closed syntax allowlist, elaboration, unresolved-placeholder checks, and a kernel type check. Local and custom operation instances are rejected by numerical recognizers unless they are definitionally equal to the imported standard instance. Unsupported objects remain symbolic.

Build products and machine-specific paths stay in ignored `.local/`. Existing Lean toolchains and mathlib caches are read-only inputs. There is no cloud analysis, model API, telemetry, or external font request. The server binds to loopback and checks request origins. These boundaries are intended for a local development application; they are not a hardened multi-user sandbox.

The current views do not include perspective 3D rendering, general manifold charts, Hopf fibrations, arbitrary projections, user-defined notation, or extraction from a running Lean language server. Those require explicit mathematical adapters. See [the architecture](docs/architecture.md).

## Check the implementation

```sh
npm run build
npm test
npm run test:server
npm run test:lean
npm run test:integration
```

[The verification record](docs/verification.md) describes the tested behaviors and remaining limits. Passing these tests is not a claim that the application has no bugs.

## Attribution

**Project lead and maintainer:** Neil Yuanting Li.

**Development:** Codex under the supervision of Neil Yuanting Li.

Citation: [CITATION.cff](CITATION.cff). License: [Apache 2.0](LICENSE). Dependency attribution: [NOTICE](NOTICE).
