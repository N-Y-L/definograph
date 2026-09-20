# Restricted-map lens and its audit

This optional mathematical lens gives a common visual meaning to a map that is invertible only between specified regions. It is one consumer of the shared decomposition and composition architecture described in [the generic decomposition iteration](decomposition-iteration.md). The primary output remains a visual sequence with the whole logical statement available alongside it.

## One grammar, several Lean representations

The new grammar decomposes a bundled object into two carriers, a source region, a target region, two directed maps, and conditional laws. The same renderer serves `PartialEquiv A B` and `OpenPartialHomeomorph A B`. The second adapter additionally supplies the audited facts that the regions are open and the maps are continuous on their respective regions. There is no renderer selected by the name of a theorem.

Lean adapters recognize exact canonical constructors, field projections, and function coercions. Their output is the shared semantic graph: typed object ports, source expression identity, relation kind, and logical scope. The general binder-plugin hook also lets a supported bundled type contribute its constraints when its value is introduced. The reader composes those constraints with the existing set-membership, equality, quantifier, and implication grammar.

For example:

```lean
∀ (A B : Type) (e : PartialEquiv A B) (x : A),
  x ∈ e.source → e.symm (e x) = x
```

The sequence introduces the carriers and bundled map, reads the source-membership premise, constructs `e x`, constructs the reverse image of that same result, and finally reads the equality with `x`. The intermediate point keeps one semantic identity across both applications. The premise remains attached to the conclusion. Renaming `A`, `B`, `e`, and `x` does not change this structure.

This extends the existing decomposition strategy. A small unfamiliar definition can already be opened through checked definitional equality when that reveals useful known structure. The resulting expression is then interpreted through the same primitive relations and composed according to its source dependencies. Unfolding alone cannot explain every structure: unfamiliar mathematical laws remain visible as unknown meanings until an audited contract connects them to the grammar.

This release also exports a checked view of small type aliases at binder introductions. Up to two safe, nonpartial type-head definitions can be unfolded, with each result kernel checked and definitionally equal to the original type. The original declared type remains visible. The optional expansion is limited to 80 expression nodes, depth 24, and a 64 KiB payload, with a separate heartbeat budget. Audited type constructors are kept intact. An alias such as `RegionCorrespondence A B := PartialEquiv A B` therefore reaches the existing grammar without a rule for the alias's name. A map obtained as `family i` similarly composes the ordinary function-application grammar with the restricted-map grammar.

## Region-limited mathematical meaning

The contract follows the pinned Mathlib [PartialEquiv definition](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Logic/Equiv/PartialEquiv.lean#L121). Its forward and reverse functions are defined on their entire carrier types, but their inverse laws hold on the stated source and target regions. A function application by itself is not evidence that its input belongs to the valid region.

| Component | Meaning represented | What is not inferred |
|---|---|---|
| Bundled map | Two carriers, two valid regions, forward/reverse maps, and laws restricted to those regions | A global inverse, nonempty regions, or chosen sample points |
| Source or target projection | The exact exported set expression and its role relative to the original map | An ellipse-shaped subset, dimension, coordinates, or a particular topology |
| Forward or reverse application | The actual input/output expressions and the direction used | Membership of either expression in a valid region |
| `symm` and `toPartialEquiv` | Direction and region changes resolved back to the original bundled value | A new unrelated map or replacement of an expression's source identity |
| `OpenPartialHomeomorph` | Open source/target sets and continuity of each map on its valid region | A manifold atlas, differentiability, tangent spaces, or a derivative |

The additional topological facts follow the pinned [OpenPartialHomeomorph definition](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean#L54). They are structure-level annotations; this release does not provide a general visual interpretation of an arbitrary continuity or openness predicate.

The diagram uses schematic region containers and arrows. It creates no geometric point positions. A projection receives an interactive source-object identity only when that exact expression occurs in the same source clause and scope. Otherwise the label is an explanatory slot for the bundled field. Two regions can share the same carrier type without becoming the same region. The diagram does not interpret displayed region area or shape as data.

## Scope, trust, and unknown expressions

The adapter requires canonical Lean provenance and the audited projection/coercion shape. A project function merely named `PartialEquiv.source`, or a different `CoeFun` instance supplied by the statement, receives no inferred restricted-map contract. The actual bundle can still be explained while the separate coercion remains unknown.

An expression such as `ReadingUnknown (e.symm (e x))`, with an uninterpreted project definition `ReadingUnknown`, retains that definition as the assertion. The inner applications are shown as contained expression structure, not as independent claims. An arbitrary supplied predicate `F : A → Prop` already has a general relation-application interpretation; it still remains the parent of its argument, and no additional property of `F` is inferred. An existential map inside one negated disjunction alternative cannot appear as an available witness in the other alternative.

An unguarded statement `e.symm (e x) = x` is also preserved as written. The reader does not manufacture a source-membership hypothesis to make the equality follow from the bundle. Its supplementary map diagram keeps the conditional bundled laws explicit, and it does not certify that the input statement is true.

## Evaluation

[`scripts/restricted-reading-integration.ts`](../scripts/restricted-reading-integration.ts) evaluates actual unsaved Lean editor buffers through the native context sidecar, semantic compiler, guide compiler, and production React renderer. The independent cases cover both bundled structures, nested inverse applications, `symm`, `toPartialEquiv`, a selected theorem fragment with a local hypothesis, separate existential alternatives, unknown wrappers, a custom coercion, fake familiar names, an unguarded equality, and equal carrier types.

The checks verify scope and port identity, ordered construction stages, exact input/output connections, source/target law labels, complete-clause preservation, and the absence of invented numerical scenes. They also verify that private saved source and configuration remain unchanged and that native executable hashes are stable throughout the run. The broader [coverage corpus](coverage-corpus.md) includes a renamed restricted-map statement and keeps the previous unsupported continuity and rank conditions.

See [verification](verification.md) for the recorded release results and remaining environment limitations. A passing rendering test checks the implementation's stated contract; it is not a proof of the original proposition or a measure of human comprehension.

## Upstream sources and remaining foundations

The mathematical structures are reused from Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` under Apache 2.0. The semantic adapters and SVG renderer are implemented here; this iteration adds no Manim or Penrose runtime, copied scene asset, or layout dependency. Earlier visual and architectural references remain credited in [NOTICE](../NOTICE) and [the visual method](visual-method.md).

This common grammar is useful groundwork for charts and local trivializations, whose additional conditions still require interpretation. Base/fiber/projection relationships, linear-map image/kernel/rank, derivatives, tangent fields, and planarity remain separate mathematical foundations to build. Hairy-ball, constant-rank, and four-color theorem visualization are not completed by this release.

Development and design assessment: Codex under the supervision of Neil Yuanting Li.
