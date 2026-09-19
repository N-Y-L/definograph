# Architecture and interpretation boundaries

StatementLens has three independently testable layers.

1. `lean/StatementLens/Worker.lean` imports a fixed mathlib environment, parses one proposition term, validates its syntax, elaborates it, checks for unresolved metavariables and placeholders, and calls Lean's kernel type checker. It exports the logical tree and typed expression data over JSON lines. Each request receives a fresh elaboration context.
2. `src/core/` recognizes supported mathematical objects, interprets audited numerical operations, preserves lexical scope, tracks witness dependencies, and computes coordinate intersections. Recognition relies on fully qualified constants and Lean's canonical-instance checks. Display names never identify binders.
3. `src/App.tsx` and `src/SceneView.tsx` render the tree and numerical scenarios. Source edits invalidate the displayed analysis. Requests carry generation checks so an old result cannot replace a newer source.

`server/` manages the local worker, enforces size and time limits, and exposes `/api/health` and `/api/analyze`. It does not accept executable paths, import lists, filesystem paths, or compiler options from HTTP requests. Production file serving stays inside `dist/`. Machine-local configuration is ignored by Git.

## What the checks establish

| Stage | Establishes | Does not establish |
|---|---|---|
| Lean elaboration and kernel type checking | The submitted expression is a proposition with resolved types | That the proposition is true |
| Instance-aware recognition | A supported constant uses a recognized standard mathematical interpretation | Correctness of the TypeScript implementation by proof |
| Numerical evaluation | An approximate result for the current finite scenario | A theorem, exhaustive search, or exact-real decision |
| Coordinate slice | Intersection with a specified coordinate plane under the recognized metric | A picture of every point of a higher-dimensional object |

## Quantifiers and scope

`∀ x, ∃ y, P x y` permits a candidate `y` to depend on `x`. Changing an earlier choice invalidates later dependent witness choices. In `∃ y, ∀ x, P x y`, changing `x` leaves `y` fixed. No automatic witness search or proof is implied.

Lean represents both universal binders and implications with `Expr.forallE`. Proposition-valued binders are displayed as assumptions, not geometric sliders. Existentials under a negation, implication antecedent, or disjunction retain that logical context. Two binders with the same printed name retain distinct internal IDs.

## Geometric views

For a Euclidean ball centered at `c`, a coordinate slice fixing omitted coordinates `z` has squared radius `r² − ‖z − c_omitted‖²`. Negative residual gives an empty intersection. An open ball excludes tangency; a closed ball and sphere can meet in a single point.

For the maximum metric, omitted coordinate displacements must satisfy the original radius bound. A max-norm sphere can intersect a plane in a **filled square** if an omitted coordinate already attains the radius. The scene identifies this case explicitly.

The plotted axes are coordinate directions. Changing them or the fixed coordinates changes the view, not the Lean statement. A point outside the slice is hidden and labeled as outside it. Dragging inside the plot places a representative in that slice.

## Extending the application

New recognizers should specify the exact Lean constants, type and instance checks, geometric interpretation, unsupported cases, and numerical limitations. Tests should contain a near-miss example that must remain unsupported. A specialized Hopf-fibration view would need its own map and chart semantics; substituting a generic projection would not be sufficient.

A future VS Code adapter should obtain elaborated expressions and local context from Lean's `InfoTree` or an RPC extension, then reuse this portable scene pipeline. It should preserve the source project and its toolchain. Source ranges, incomplete-term recovery, arbitrary declaration loading, and proof-status auditing are separate work and are not implemented here.

## Primary references

- [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean expression representation](https://lean-lang.org/doc/api/Lean/Expr.html)
- [Mathlib metric balls](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Defs.html)
- [Mathlib finite-dimensional Euclidean spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html)
- [Lean InfoTree data](https://lean-lang.org/doc/api/Lean/Elab/InfoTree/Types.html)

Online references may describe newer versions. The implementation and tests use the pinned Lean and mathlib versions in this repository.
