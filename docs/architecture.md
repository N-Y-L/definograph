# Architecture

StatementLens aims to make arbitrary mathematical statements inspectable through automatically composed representations. Its unit of extension is a mathematical construction—sets, maps, relations, spaces, quantifiers—not a theorem name. A regression example exercises reusable rules; it is never a dispatch key.

## The pipeline

```text
Lean term / imported declaration
        ↓
Lean elaboration, kernel type check, instance audit
        ↓
Versioned typed expression + scope + source provenance
        ↓
Semantic document: shared objects, relations, choices, unknown regions
        ↓
Capability registry and ranked view composition
        ↓
Linked diagrams, numerical scenarios, source/type inspection
```

`lean/StatementLens/Worker.lean` resolves mathematical meaning in a pinned environment. `src/semantic/` separates that meaning from presentation. `src/visual/` renders symbolic structure. `src/core/` and `src/SceneView.tsx` provide audited numerical interpretation. `src/editor/` provides CodeMirror input and exact UTF-8-to-UTF-16 source occurrence conversion. `server/` transports bounded requests to a persistent, isolated worker context.

## A semantic document rather than a diagram recipe

`compileSemanticDocument` creates the versioned document in `src/semantic/types.ts`. Objects carry typed expressions, identity, scope, and provenance. Relations connect named ports to object identities. Quantifier choices retain the information available at their introduction. Logical alternatives, implications, and negations remain separate contexts. Unrecognized expressions remain in `opaqueRegions`; recognized children can still contribute relations and scenes.

Binder names are display labels, not identities. Expression keys preserve types and instances, since different metrics or overloaded operations can change the mathematics. Implicit type, instance, and proof arguments stay in the exported expression but are filtered from ordinary visual roles. A definition signature uses parameter nodes, not universal proposition nodes.

`src/semantic/registry.ts` is a registry of reusable recognizers. Each rule declares its capabilities and limitations. Recognition uses elaborated constructors and typed argument roles. Generic typed relation applications remain visible even when their domain has no coordinate model. Arbitrary unknown predicates remain structural; the program does not infer their meaning from familiar-looking names.

## Automatic representation selection

`planViews` ranks geometric, relational, structural, and quantifier views using directness, recognized mathematical information, shared objects, and selected scope. It retains supporting views and a complete semantic document. Selecting a fragment changes the plan while carrying its enclosing assumptions. Selecting an object connects appearances across views.

Geometry receives a direct rendering when its metric and operations are understood. Abstract sets and maps receive schematic relationships; their drawing does not assign cardinalities or coordinates. Quantifier flow describes the permitted order of choices. For larger finite-dimensional spaces, a distance profile can show every coordinate's contribution while a coordinate slice provides an adjustable spatial intersection. Neither representation is described as the entire high-dimensional object.

The current planner is a tested heuristic, not a theorem that its representation is optimal. The extensible boundary matters: a future chart, fiber, graph embedding, commutative diagram, or projection rule can state what information it preserves and compete as a view without changing the prover extractor or inventing theorem-specific detection.

## Trust and meaning

| Stage | Establishes | Does not establish |
|---|---|---|
| Lean elaboration and kernel type checking | Resolved type of a statement or declaration signature | Truth of an arbitrary submitted proposition |
| Definition expansion | Kernel-checked definitional equality with the original fragment | A new mathematical theorem |
| Typed semantic extraction | Scope, object roles, recognized relationships | Geometric meaning for every unknown symbol |
| Symbolic diagram | Relationships and roles in a labeled logical context | That its pictured hypotheses hold |
| Numerical scenario | Approximate values for selected representatives | Universal truth or a certified counterexample |
| Coordinate slice | Intersection with a specified coordinate plane | A projection or complete picture of the ambient object |

Changing an earlier arbitrary choice clears dependent candidate witnesses. In `∃ y, ∀ x, P x y`, changing `x` leaves `y` fixed. No witness search or proof is implied. An implication's hypothesis is available only in its consequent. Disjoint branches never acquire each other's binders.

Custom typeclass instances cannot silently receive standard numerical meanings. The worker compares actual instances against trusted canonical instances. Parametric set operations have separate exact constructor checks; tests include locally overridden membership and inclusion.

## Prover and editor boundaries

`GET /api/capabilities` describes protocol version 2 and bounded input options. `POST /api/analyze` accepts only a source string, an optional term/declaration mode, and explicit bounded definition expansion. It accepts no filesystem paths, commands, import lists, or executable settings. The semantic document and view plan can be exported from the interface as JSON.

The current Lean adapter uses fixed imports. An editor adapter should extract from the active Lean document's `InfoTree` and local environment, through Lean RPC or ProofWidgets, then emit the same typed contract. Exact source occurrences are implemented; source links on transformed logical nodes are deliberately not guessed. Recovery from incomplete outer syntax and active-project environment access remain separate work.

The semantic document has a prover identifier and is independent of React and HTTP. A Rocq extractor would need its own handling of universes, coercions, modules, contexts, and kernel terms. Shared views are an architectural direction, not a claim of working Rocq support.

## Existing foundations and reuse

[Penrose](https://penrose.cs.cmu.edu/docs/ref) separates mathematical vocabulary and relationships from visual style and constraint-based layout. That separation informs the document/rule/view design here. Penrose does not supply a general Lean-to-mathematics extractor; no Penrose runtime or copied styles are bundled in this release. The present symbolic renderer uses bounded deterministic layout. A Penrose renderer can fit behind the same view boundary when optimization and reusable styles justify its runtime.

[ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) supplies Lean/React integration and a [Penrose component](https://github.com/leanprover-community/ProofWidgets4/blob/main/ProofWidgets/Component/PenroseDiagram.lean). It is a useful future editor host, not a replacement for the semantic recognizers. The existing mathlib dependency graph already pins ProofWidgets; the standalone application does not load its UI bundle.

[CodeMirror](https://github.com/codemirror/dev) supplies the editor, selection, history, bracket matching, and search infrastructure. The small Lean highlighter is lexical; only the Lean worker determines validity. Lean and mathlib provide the actual typed mathematical environment.

## Current boundaries

The application has generalized structure and a growing reusable visual vocabulary. It does not yet automatically discover a faithful geometric model for every mathematical construction. Fixed imports, limited supported input syntax, bounded semantic extraction, the numerical subset, incomplete-term recovery, richer layout planning, witness strategies, and active editor integration are engineering work still to do. High dimension is a representation-design problem, not grounds for rejecting a statement.

The renderer has regression tests, not a formal correctness proof. The local server and allowlisted input are not an operating-system sandbox for arbitrary third-party Lean projects. Full transport and extraction details are in [the Lean contract](lean-contract.md).
