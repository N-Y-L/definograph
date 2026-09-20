# Architecture

StatementLens aims to make arbitrary mathematical statements inspectable through composed representations. Its unit of extension is a mathematical construction—sets, maps, relations, spaces, quantifiers—not a theorem name. A regression example exercises reusable rules; it is never a dispatch key. Release 0.6 is a working but incomplete vocabulary for that goal.

## The pipeline

```text
Standalone Lean term/declaration OR selected trusted project fragment
        ↓
Lean elaboration, kernel type check, constructor/instance audit
        ↓
Typed expression + local scope + source provenance
        ↓ (optional, same elaboration context)
Bounded, definitionally equal inspection previews
        ↓
Semantic document: shared objects, relations, choices, unknown regions
        ↓
Whole-statement reading: guided construction sequence + logical overview
        ↓
Symbolic diagrams + actionable coverage + source/type inspection
        ↓ (optional)
Ranked detailed views and numerical scenarios
```

`lean/StatementLens/Worker.lean` handles the fixed imported environment. `lean/StatementLens/Context.lean` extracts a selected project fragment from Lean's `InfoTree` and local context; `server/editor-context.ts` and the optional VS Code controller provide its separate transport. Both native paths share the typed exporter. `src/semantic/` separates interpretation from presentation; `src/reading/` preserves statement logic; `src/visual/` renders it. `src/core/` and `src/SceneView.tsx` provide optional audited numerical interpretation.

## Semantic identities and reusable vocabulary

`compileSemanticDocument` creates the document in `src/semantic/types.ts`. Objects carry typed expressions, identity, scope, and provenance. Relations connect named ports to those identities. Quantifier choices retain the information available at their introduction. Alternatives, implications, and negations remain separate contexts. Unknown expressions stay in `opaqueRegions`, with recognized children available as expression parts rather than replacement assertions.

Binder names are display labels. Structural expression keys retain types, universes, and instances. Ordinary visual ports omit implementation arguments; specialized rules can explicitly interpret typed operands. A definition signature uses parameter nodes rather than universal proposition nodes. Prover-exported provenance distinguishes audited constructors from same-spelled project constants.

The registry recognizes elaborated constructors and argument roles. Current families include sets and Boolean operations, application and function properties, equality and audited order, metric regions, and the simple-graph grammar in `src/graphs/semantics.ts`. Graph rules cover adjacency, colorings and colorability, homomorphisms, and embeddings. Exact constructor saturation and audited bundled-function coercions prevent a partial application or replacement instance from receiving those meanings. Graph binder relations originate at their actual introduction scope.

`src/graphs/model.ts` and `GraphConstraintFigure.tsx` draw constraints on named objects or explicitly arbitrary endpoint slots. They do not enumerate an unknown graph or assign vertex colors. Finite palette labels require an exact audited natural bound; at most eight labels are displayed with an exact remaining count. Zero colors require an empty vertex type; one color requires an edgeless graph, not a singleton vertex set. [The graph contract](graph-iteration.md) records the remaining distinctions.

## Guided reading and optional exploration

`compileReading` retains all source nodes in a nested logical tree and source-order sequence. Cues carry branch paths, assumptions, binder dependencies, and expression-local scopes. Shared-object composition is restricted to one clause and one expression scope. Selecting a fragment changes focus without discarding the enclosing statement. Typed carriers, maps, dependent families, set constructions, and graph constraints need no numerical model.

The source-linked cue plan in `src/reading/cues.ts` orders applications and constructions before their enclosing comparison. Object IDs and their shared visual colors connect introductions, applications, and later conditions; arbitrary schematic slots never acquire invented source identities. The complete static reading remains available. See [guided reading](guided-reading.md) and [the visual method](visual-method.md).

`src/statement-geometry/` draws conditions without selecting examples. Radius signs follow exact syntax or a directly available audited assumption; otherwise all sign cases remain visible. High-dimensional conditions use distance without choosing a coordinate plane. A geometric figure replaces a clause only when it represents the complete membership relation.

The separate exploration experience uses `planViews` to rank detailed views using recognized information, shared relationships, and selected scope. Numerical geometry requires audited metrics and operations. Distance profiles and adjustable slices expose different information; neither is described as the entire high-dimensional object. Changing an earlier arbitrary choice clears dependent candidate witnesses, whereas a witness introduced before a later universal choice stays fixed. Samples do not discharge quantified obligations.

## Bounded automatic definition inspection

Optional native previews are generated from the already elaborated expression in the same `MetaM` context. They do not replay editor commands or submit a second source-analysis request. The exporter considers at most three safe, nonpartial proposition definitions at logical heads, unfolds one step, and requires a small result that remains a proposition, no unresolved placeholders, a kernel check, and definitional equality. Native preview work has its own budget, restores its saved meta state, and is limited to 256 KiB in aggregate; failure leaves the mandatory analysis available.

`src/semantic/inspection.ts` chooses at most one preview whose definition was initially uninterpreted and eligible for expansion. A candidate must retain the root identity, contain checked expansion metadata, have at most 80 logical nodes and add at most 24, and remain within 262,144 serialized characters. It must reduce the number of opaque regions, remove the selected unknown head, and introduce neither traversal diagnostics nor opaque exporter truncation. A bounded heuristic favors the greatest reduction while penalizing growth. The original analysis is retained; the UI identifies the opened definition and offers an original-reading toggle. Explicit expansion remains a separate action. This is limited definition inspection, not unrestricted simplification or theorem proving.

## Coverage and trust

`compileInterpretationReport` in `src/semantic/coverage.ts` reports recognized vocabulary, clause status, exact unknown heads, source scopes, and eligible expansions. Selecting a clause restricts its report. The UI can focus a gap's source context or request explicit expansion. Coverage is relative to installed semantic rules, not a measure of truth or mathematical understanding. Hidden type operands can contain additional uninterpreted meaning, so a short gap list is not evidence of complete interpretation.

The [18-case native corpus](coverage-corpus.md) records supported, partial, and currently unsupported examples, with independent checks for renaming, quantifier dependence, scope, unknown wrappers, custom instances, and source preservation. Its reports identify concrete missing vocabulary; they do not estimate a percentage of all mathematics.

| Stage | Establishes | Does not establish |
|---|---|---|
| Lean elaboration and kernel type checking | Resolved type in the stated environment | Truth of an arbitrary submitted proposition |
| Definition inspection or expansion | Checked definitional equality with the original fragment | A new theorem or arbitrary semantic understanding |
| Semantic rules | Audited relationships, identities, and scopes | Meaning for every symbol or binder type |
| Symbolic diagram | A condition within its logical context | That the condition holds, or a chosen graph/geometry exists |
| Numerical scenario | Approximate values for representatives | Universal truth or a certified counterexample |
| Coordinate slice | Intersection with the stated plane | A projection or complete ambient object |

## Prover and editor boundaries

The loopback browser API accepts bounded source/options, including optional definition previews, and no client-selected filesystem paths, commands, imports, or executable settings. Standalone syntax is a closed declarative allowlist with fixed trusted imports. The project adapter is a separate boundary: it reads a trusted Lean 4.28.0 buffer and existing compiled dependencies, preserves local parameters and assumptions, and never rewrites the project configuration. Project source may execute elaborators or commands; the native process is not a security sandbox. Diagram responses are tied to the exact document version and selection and invalidated after relevant edits.

Editor mode checks canonical declaring modules and selected exact instances. Audited natural literals support finite color bounds; broader numerical geometry remains disabled there. Exact source occurrences are implemented, but transformed logical-node source links are not guessed. Incomplete-term recovery, more toolchain versions, and incremental extraction remain work. Native extraction, mocked controller, and hosted-browser checks are distinct from the still-unverified actual VS Code GUI installation workflow. See [editor integration](editor-integration.md) and [verification](verification.md).

The semantic document is independent of React and HTTP and has a prover identifier. Rocq would need its own tested treatment of contexts, universes, coercions, modules, and kernel terms; no Rocq adapter is implemented.

## Reused software and reviewed designs

Lean and mathlib provide the actual mathematical environment. Release 0.6 imports and interprets the pinned mathlib [simple-graph coloring definitions](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Coloring.lean) and [map definitions](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Maps.lean), under Apache 2.0. These are reused dependencies, not reimplemented coloring mathematics.

[LeanTeX](https://github.com/kmill/LeanTeX) supplies a pinned, isolated Expr-to-LaTeX printer with documented compatibility changes; [KaTeX](https://katex.org/) renders it locally. [CodeMirror](https://github.com/codemirror/dev) supplies editor infrastructure and React supplies the UI. Typesetting never feeds back into semantic recognition. [The LeanTeX record](leantex-integration.md) and [NOTICE](../NOTICE) retain attribution.

[3Blue1Brown/Manim](https://github.com/3b1b/manim) informs ordered constructions and persistent visual identity. [Penrose's examples](https://penrose.cs.cmu.edu/examples) and [Domain/Substance/Style separation](https://penrose.cs.cmu.edu/docs/ref) inform the separation of mathematical relationships from their presentation. These are reviewed design references: no Manim or Penrose code, scenes, assets, or styles are copied, and neither runtime is added. Current graph constraints use bounded deterministic SVG layout and need no new graph-layout dependency. [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) remains an upstream integration reference already present in mathlib's dependency graph; the app does not load its UI bundle.

## Remaining shared foundations

Restricted maps with source/target sets and local inverse laws can serve both charts and bundle trivializations. Indexed fibers, total spaces, projections, and sections can build on existing dependent signatures without inferring continuity or linearity. Linear-map image/kernel/rank and derivative semantics require further typed rules. These foundations, a planar graph grammar, and faithful models for tangent fields are not implemented. The four-color, hairy-ball, and constant-rank theorems are not completed visualization cases. The renderer has regression tests rather than a formal correctness proof; the planner is a heuristic rather than a verified optimum. See [the roadmap](roadmap.md).
