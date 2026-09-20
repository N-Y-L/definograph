# Release 0.6: graph constraints and inspectable definitions

This iteration extends reusable mathematical vocabulary and makes remaining gaps visible. It adds symbolic simple-graph constraints, carries their source identities through guided reading, and can inspect one small definition when a checked expansion exposes more understood structure. It does not complete the goal of general mathematical statement visualization.

## Implemented graph vocabulary

Recognition uses canonical, fully applied Lean constructors and typed ports in [`src/graphs/semantics.ts`](../src/graphs/semantics.ts). It never dispatches on a theorem name. The standalone worker now imports the pinned Mathlib coloring module; editor extraction audits declaring modules and the exact bundled-function coercion instance.

| Construction | Interpreted relationship | Important boundary |
|---|---|---|
| `G.Adj u v` | The named vertices satisfy adjacency in `G`, within the surrounding logical context | No other vertices or edges are inferred; an occurrence under negation is not a positive edge assertion |
| `c : G.Coloring C` and `c u` | A supplied coloring maps vertices to labels, with unequal labels required across every edge | The schematic does not choose the color of a vertex or assume every label is used |
| `G.Colorable n` | Existence of a proper coloring into `Fin n` | This is a condition, not a constructed witness or a solver result |
| `f : G →g H` and its application | Edges in `G` map to edges in `H` | Injectivity and the converse implication are not inferred |
| A `SimpleGraph.Embedding G H` and its application | Injectivity with adjacency preserved and reflected | This is an induced graph embedding, not a planar embedding or target-wide surjectivity |

The mathematical definitions come from mathlib's pinned [Coloring module](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Coloring.lean) and [Maps module](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Maps.lean). They are reused under Apache 2.0; the renderer and semantic adapters are implemented here.

A typical input is:

```lean
∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (u v : V),
  G.Adj u v → c u ≠ c v
```

Its guided reading keeps `G`, `c`, `u`, and `v` connected to their introductions and shows the color applications before the final inequality. The premise stays a premise. Reversing quantifiers or moving a condition into a negated alternative changes its logical context; the graph rule cannot flatten those changes away.

## Honest schematic choices

[`src/graphs/model.ts`](../src/graphs/model.ts) consumes recognized relations and validates exact object/scope references. Named objects keep their shared IDs and visual colors. Arbitrary endpoint slots used to explain an edge rule have separate schematic IDs and no invented source-object interaction. Repeated occurrences of the same named vertex retain one identity; the renderer does not turn a self-adjacency condition into two distinct vertices.

A palette is enumerated only from an exact exported natural literal or an audited standard natural numeral. At most eight labels are displayed, with the exact remaining count; symbolic or excessively large literal representations stay symbolic. These are available labels, never a vertex assignment.

- **Zero labels:** a coloring into an empty palette requires an empty vertex type. The figure shows no instantiated endpoint slots; the edge condition is vacuous there.
- **One label:** the graph must have no edges. It may have more than one vertex; no singleton cardinality is inferred.
- **An arbitrary bound or color type:** no finite palette size is guessed from display text.

Each figure remains inside its quantifier, assumption, conclusion, alternative, or negation. Related stages are joined only within the same source clause and expression scope. The model bounds related-stage discovery at 48 and reports omitted related relations. No graph instance, vertex set enumeration, coloring assignment, or planar layout is synthesized.

## Automatic small-definition inspection

Native optional previews reuse the already elaborated expression and local `MetaM` context. There is no second source execution, editor-command replay, network request, or generated program. At most three eligible safe, nonpartial proposition definitions at logical heads are considered. Each is unfolded by one step, checked for unresolved placeholders, kernel checked, and required to be definitionally equal to the original. Candidate bodies are bounded by depth 24 and expression size 80; the preview batch is bounded by 256 KiB and its own execution budget. Failure to generate a preview leaves the original analysis usable.

[`src/semantic/inspection.ts`](../src/semantic/inspection.ts) selects at most one candidate. It must target an initially unknown, expandable definition, retain the root identity, carry checked expansion metadata, reduce opaque-region count, and remove the selected unknown head. The resulting logical tree is limited to 80 nodes and growth of 24 nodes; a preview exceeding 262,144 serialized characters, traversal diagnostics, or opaque exporter truncation is rejected. A bounded quality score also penalizes growth. Definition-body inspection and explicit expansion retain their separate controls.

The reader identifies the definition it opened. **Inspect** exposes the original statement and the **Automatically inspect small definitions** toggle, so the original reading can be restored. A more legible definitional form does not prove the proposition and does not supply a missing semantic grammar for a large unknown construction.

## Coverage and evaluation

The coverage panel reports the installed vocabulary used in the selected fragment and the unknown heads that remain. Unknown entries retain source context, and eligible definitions can be expanded explicitly. A named type or generic application diagram is not presented as full interpretation of its mathematical meaning.

The [native corpus](coverage-corpus.md) deliberately includes interpreted, partial, and currently unsupported statements, including actual editor contexts. It compares binder renamings, quantifier order, branch scope, unknown wrappers, and custom instances. Reports list observed missing constructors rather than estimating a percentage of arbitrary mathematics. Type arguments omitted from ordinary relation traversal may hide further meaning, and optional previews are assessed separately from the corpus's primary unexpanded statement.

The current checks and browser observations are recorded in [verification](verification.md). Native sidecar, mocked extension-controller, and hosted-browser checks do not establish that installation and the full workflow in an actual VS Code GUI have been tested; that remains unverified.

## Reused software and reviewed designs

Mathlib's graph definitions are actual mathematical dependencies, alongside Lean, the pinned LeanTeX printer, KaTeX, CodeMirror, and React. Their notices remain in [NOTICE](../NOTICE) and the dependency sources.

[3Blue1Brown/Manim](https://github.com/3b1b/manim) is a design reference for following constructions while retaining object identity. [Penrose's examples](https://penrose.cs.cmu.edu/examples) and [language architecture](https://penrose.cs.cmu.edu/docs/ref) inform reusable vocabulary and separation of mathematical content from visual style. The application of those ideas here is our design inference. No Manim or Penrose code, scene assets, or styles were copied; neither runtime is bundled. The current constraint schematics use local SVG, so no additional graph-layout dependency was needed. These references are credited without implying that either project supplies the Lean semantic extraction.

## Remaining mathematical work

There is no planar graph grammar or complete visualization of the four-color theorem. Nor are tangent-bundle/vector-field semantics, derivatives, or constant-rank coordinate normal forms implemented. Existing typed maps, dependent signatures, and set relations can expose useful parts of such statements while the central concepts remain uninterpreted.

The next shared contracts are restricted maps with explicit source/target regions and local inverse laws; base/fiber/projection/section relationships; and linear-map image, kernel, and rank. They can support multiple areas without named-theorem rendering. See [the roadmap](roadmap.md) and [the corpus assessment](coverage-corpus.md).

Development and design assessment: Codex under the supervision of Neil Yuanting Li.
