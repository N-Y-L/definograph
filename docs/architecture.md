# Architecture

StatementLens aims to make arbitrary mathematical statements understandable through a small set of shared visual primitives. Its central mechanism is deterministic decomposition of actual Lean definitions, followed by composition of typed objects and logical conditions. A new library object should not require a new renderer. Named theorems are regression inputs, never dispatch keys.

The implemented foundation combines direct structure reflection, bounded type-head alias exposure, logical decomposition, and bounded definitional unfolding. Optional mathematical adapters provide concise views of known contracts. This remains incomplete: arbitrary recursive values and inductive definitions do not yet reduce into useful visual explanations automatically.

## The pipeline

```text
Standalone Lean term/declaration OR selected trusted project fragment
        ↓
Lean elaboration and kernel type check in the actual environment
        ↓
Typed expression + scope + source provenance
        ↓ (same elaboration context)
Direct structure fields/laws + bounded aliases and definition unfolding
        ↓
Shared primitives: typed objects, maps, sets, relations, quantifiers, conditions
        ↓
Semantic document: shared identities + dependencies + unknown frontier
        ↓
Composed reading: visual sequence + logical overview
        ↓
Optional concise mathematical views and optional numerical exploration
```

`lean/StatementLens/Worker.lean` handles the fixed imported environment. `lean/StatementLens/Context.lean` extracts a selected project fragment from Lean's `InfoTree` and local context; `server/editor-context.ts` and the optional VS Code controller provide its separate transport. Both native paths share the exporter. Assigned expression and universe metavariables in editor local declarations are instantiated before kernel checks so the checker and exporter use the same context.

`src/semantic/` separates interpretation from presentation; `src/reading/` preserves statement logic; `src/visual/` renders the composed reading. `src/core/` and `src/SceneView.tsx` provide optional audited numerical interpretation. The semantic contract is independent of React, HTTP, and a particular prover transport.

## Generic decomposition

A bound value's type is examined using Lean's structure metadata. Direct fields are read in declaration order; their exact projections and inferred types are kernel checked. Data fields retain typed projected expressions. Proposition-valued fields also receive ordinary scoped logical trees. Earlier exact field expressions appearing in a later field's type become dependencies. Field names remain labels: renaming a structure or its fields does not require a semantic rule change.

Maps, subsets, elements, and internal carrier types therefore become available from previously unseen user records. Their laws reuse the same expressions, so applications can feed membership conditions, comparisons, and subsequent applications. An unfamiliar predicate remains visible where decomposition stops. A field law is available because of its owning value, within that value's scope; it does not become a global assertion. Law-only records in `Prop` retain their hypothesis scope.

The native `Binder.structure` view is optional and bounded: at most 16 direct fields, at most 120 expression nodes and depth 24 per projected expression or field type, and at most 128 KiB per envelope. Direct inherited subobjects remain visible fields. Reflected law trees suppress further structure reflection of their own introduced binders. A separate heartbeat budget and saved meta state isolate optional work; omitted fields and failures have explicit status. Aggregate response overflow removes optional structure views before the checked statement is lost.

A safe type-head alias can expose an existing representation without a new adapter. Up to two small, kernel-checked, definitionally equal steps preserve the original type and name. The same optional type view can accompany data-field types. This supports user aliases of sets, functions, structures, or known mathematical bundles. It does not recursively normalize arbitrary computations or infer a structure from suggestive field names. [The reflection contract](structure-reflection.md) gives the exact export schema and limits.

## Shared identities and optional mathematical adapters

`compileSemanticDocument` creates the document in `src/semantic/types.ts`. Objects carry typed expressions, identity, scope, and provenance. Relations connect named ports to those identities. Quantifier choices retain the information available at their introduction. Alternatives, implications, and negations remain separate contexts. Unknown expressions stay in `opaqueRegions`, with recognized children available as expression parts rather than replacement assertions.

Binder names are display labels. Structural expression keys retain universe and instance distinctions. A definition signature uses parameter nodes rather than universal proposition nodes. Actual checked field projections make generic structure decomposition possible without treating every project constant as a known mathematical operation.

The plugin registry accepts expression rules and generic `matchBinder` hooks. Its existing vocabulary includes sets and Boolean operations, applications and function properties, equality and audited order, metric regions, graph constraints, and maps inverse on designated regions. These adapters are useful concise views over mathematical contracts; they are not the sole mechanism for handling new definitions. Declaring-module checks, exact saturation, and audited coercions prevent same-spelled project constants or replacement instances from receiving an established meaning.

The graph adapter describes adjacency, proper coloring, colorability, homomorphisms, and embeddings. Its figures do not enumerate an unknown graph or assign vertex colors. The restricted-map adapter normalizes exact `symm` and forgetful projections while preserving the original map identity. Stored functions are total, but their inverse laws apply only on the designated source and target. Openness and continuity come from the supplied type, without assumed coordinates or differentiability. See [graph semantics](graph-semantics.md) and [restricted-map semantics](restricted-semantics.md).

## Composed reading and optional exploration

`compileReading` retains source nodes in a nested logical tree and source-order sequence. Cues carry branch paths, assumptions, binder dependencies, and expression-local scopes. Shared-object composition stays within its clause and scope. Selecting a fragment changes focus without discarding the enclosing statement. Typed carriers, maps, dependent families, set constructions, and structure laws do not need a numerical model.

The cue plan in `src/reading/cues.ts` orders applications and constructions before their enclosing comparison. Object IDs connect introductions, intermediate values, and later conditions. Schematic slots never acquire invented source identities. The complete static reading remains available. See [guided reading](guided-reading.md) and [the visual method](visual-method.md).

`src/statement-geometry/` draws supported conditions without selecting examples. Radius signs follow exact syntax or an available audited assumption; otherwise the sign cases remain visible. High-dimensional conditions use distance without choosing a coordinate plane. A geometric figure replaces a clause only when it represents the complete membership relation.

Optional exploration uses `planViews` to rank detailed views using recognized information, shared relationships, and selected scope. Numerical geometry requires audited metrics and operations. Distance profiles and adjustable slices expose different information; neither is described as the entire ambient object. Changing an earlier arbitrary choice clears dependent candidate witnesses. Samples do not discharge quantified obligations, and the planner is a heuristic rather than a verified optimum.

## Bounded definition unfolding

Direct structure reflection complements the existing inspection of proposition definitions. Optional native previews use the already elaborated expression in the same context; they do not replay editor commands. The exporter considers at most three safe, nonpartial proposition definitions at logical heads, unfolds one step, and requires a small proposition without unresolved placeholders, a kernel check, and definitional equality. Preview work has its own budget, restores meta state, and is limited to 256 KiB in aggregate.

`src/semantic/inspection.ts` chooses at most one preview that reduces uninterpreted structure. The candidate must retain the root identity, carry checked expansion metadata, satisfy node and payload bounds, remove its selected unknown head, and introduce no traversal diagnostics or exporter truncation. The original analysis remains available and the UI identifies the opened definition. Explicit bounded expansion is also supported. This is implemented unfolding, not general simplification, arbitrary value decomposition, or theorem proving.

## Unknown frontier and trust

Coverage reports describe what the current primitives and adapters interpret and where understanding stops. `compileInterpretationReport` records vocabulary, clause status, exact unknown heads, source scopes, and eligible expansions. Reflected fields and laws retain their own unknown portions and export omissions. Hidden type operands may contain additional meaning, so a short gap list is not evidence of complete interpretation.

The [native corpus](coverage-corpus.md) and fresh user-structure fixtures exercise renaming, exact dependencies, scope, unfamiliar predicates, custom instances, limits, and source preservation. Successful extraction, faithful logical decomposition, specialized geometric interpretation, and human understanding are different outcomes. The fixtures do not estimate a percentage of all mathematics.

| Stage | Establishes | Does not establish |
|---|---|---|
| Lean elaboration and kernel checking | Resolved types in the selected environment | Truth of an arbitrary submitted proposition |
| Structure reflection | Exact projected data and laws carried by that value | A preferred geometry or a theorem inferred from field names |
| Definition unfolding | Checked definitional equality | A useful normal form for every mathematical definition |
| Semantic composition | Represented relationships, shared identities, and scope | Meaning for every symbol or missing mathematical property |
| Symbolic diagram | A condition in its logical context | That a chosen graph, point, or geometry exists |
| Numerical scenario | Approximate representative values | Universal truth or a certified counterexample |

## Prover and editor boundaries

The loopback browser API accepts bounded source/options and no client-selected filesystem paths, commands, imports, or executable settings. Standalone syntax is a closed declarative allowlist with fixed trusted imports. The project adapter separately reads a trusted Lean 4.28.0 buffer and built dependencies, preserving local parameters and assumptions without rewriting project configuration. Project source may execute elaborators or commands; the native process is not a security sandbox. Responses are tied to the exact document version and selection and invalidated after relevant edits.

Editor mode checks canonical modules and selected exact instances for specialized interpretation. Generic structure metadata comes directly from the elaborated environment, including project-defined structures. Broader numerical geometry remains disabled there. Exact source occurrences are implemented; transformed-node source links are not guessed. More toolchains, incremental extraction, incomplete-term recovery, and actual VS Code GUI installation/use remain separate validation work. See [editor integration](editor-integration.md) and [verification](verification.md).

The semantic document has a prover identifier. A Rocq adapter would need its own checked handling of contexts, universes, coercions, modules, structures, and kernel terms; none is implemented.

## Reuse and remaining foundations

Lean provides the actual structure metadata and projection-building APIs. Mathlib supplies checked mathematical definitions, including the pinned [graph coloring](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Coloring.lean), [partial equivalence](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Logic/Equiv/PartialEquiv.lean), and [open partial homeomorphism](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean) definitions. Lean and Mathlib are reused Apache-2.0 dependencies.

[LeanTeX](https://github.com/kmill/LeanTeX) supplies the isolated Expr-to-LaTeX printer with documented compatibility changes; [KaTeX](https://katex.org/) renders it locally. CodeMirror and React supply editor/interface infrastructure. Typesetting never feeds back into semantics. [The LeanTeX record](leantex-integration.md) and [NOTICE](../NOTICE) retain attribution.

[3Blue1Brown/Manim](https://github.com/3b1b/manim) informs ordered constructions and persistent visual identity. [Penrose](https://penrose.cs.cmu.edu/docs/ref) informs the separation of mathematical relationships and presentation. These are design references: no code, scenes, assets, or styles from either are copied, and neither runtime is included. ProofWidgets4 remains an integration reference in Mathlib's dependency graph; its UI bundle is not loaded.

Further generality requires bounded recursive definition/value decomposition, handling of inductive data and dependent structure, richer composition and abstraction choices, and evaluation on unfamiliar statements. Fibers, tangent fields, derivatives, rank conditions, and planar embeddings remain useful mathematical stress tests for those shared foundations. This release does not complete hairy-ball, constant-rank, or four-color theorem visualization. [The roadmap](roadmap.md) separates these future steps from implemented reflection.
