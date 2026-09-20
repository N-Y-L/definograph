# Visual method: lessons from 3Blue1Brown

Reviewed on 2026-09-19, following the user's reference to [Grant Sanderson's GitHub profile](https://github.com/3b1b). The recommendations below are our design inferences from specific public examples. They do not claim that an animation library automatically explains arbitrary mathematics.

The useful direction is to make constructions and relationships perceptible while preserving the statement's logic. Motion should help the reader follow an object, an operation, or a correspondence. The complete static statement must remain understandable without playback.

## Transferable mechanisms

| Observed mechanism and primary source | Application to a general statement reader |
| --- | --- |
| Manim's formula example assigns consistent colors and matches corresponding expression parts between successive arrangements. Its examples also show explicit mappings when matching text is insufficient. [Formula transformations](https://3b1b.github.io/manim/getting_started/example_scenes.html#textransformexample) | Keep an object's identity stable across its introduction, applications, and conditions. Use Lean-derived object IDs, not identical names or glyph shapes. Highlight the same object across views; shadowed variables must remain distinct. |
| The matrix-composition lesson follows successive transformations and connects their order with the resulting composition. [Matrix multiplication as composition](https://www.3blue1brown.com/lessons/matrix-multiplication/) | For `g (f x) = h x`, first make the two typed paths visible, then guide attention through `x → f(x) → g(f(x))` and `x → h(x)`, ending at the required equality. The construction is general to application expressions; it needs no theorem-name recognition or numerical function. |
| The updater example keeps a brace and numerical label attached to a changing object; the graph example connects a parameter tracker to a point. [Updaters and graphs](https://3b1b.github.io/manim/getting_started/example_scenes.html#updatersexample) | Labels, source focus, and object emphasis should update together. In optional numerical exploration, show which displayed quantities depend on a changed choice. In the default reader, guide symbolic attention without silently choosing a value or asserting that a witness exists. |
| The three-dimensional transformation lesson follows basis vectors and retains the original axes as a reference instead of showing an overcrowded full grid. [Three-dimensional transformations](https://www.3blue1brown.com/lessons/3d-transformations/) | Choose a representation that exposes the relevant structure. Arbitrary types can use carrier-and-map diagrams; dependent types can use indexed families; high-dimensional metric conditions can use distance profiles or explicit slices. A basis-based view is justified only when the required linear structure and basis are actually available. |
| The abstract-vector-space lesson connects operations on arrows with operations on functions, then states the shared algebraic properties. [Abstract vector spaces](https://www.3blue1brown.com/lessons/abstract-vector-spaces/) | Prefer reusable visual grammars for operations and relations. A picture of a two-dimensional example can illustrate an abstract structure, but must not replace the abstract objects or imply that their dimension, topology, or cardinality has been determined. |

These observations support the current atlas: typed constructions, ordered map paths, persistent object identities, compact scalar constraints, and explicit logical regions. They also suggest that the next advance should be a coherent guided reading of one construction, rather than adding unrelated animated theorem demonstrations.

## Concrete next foundation: a semantic reading cue plan

Add a pure presentation compiler over the existing semantic document and reading presentation. It should emit a deterministic list of attention cues, independent of an animation engine. This is a proposed next component, not functionality supplied by Manim or already implemented here.

Each cue should contain:

- Exact source node, scope, and branch-path IDs.
- The objects and relations receiving attention, plus the object identities retained from the preceding cue.
- One intent: introduce objects, follow an application, compare expressions, or focus a logical condition.
- Its logical role: parameter, arbitrary choice, requested witness, assumption, required conclusion, alternative, negated condition, or contained expression part.
- A short explanation derived from that role and the recognized relation; no claim that the condition has been proved.

Generate cues from the same scope-preserving regions already used by the atlas. Within one atomic clause, ordered application dependencies can supply a construction sequence. Do not flatten a disjunction into successive required facts, move a witness before its permitted dependencies, or expose an inner predicate as an assertion of its unknown wrapper. An equality cue compares its two expressions; it does not certify their equality.

The first renderer can use the existing browser SVGs: a Next/Previous control focuses the relevant objects and paths while keeping the surrounding logic and overview visible. Unchanged objects keep their positions where practical. An optional short transition makes correspondence easier to follow; reduced-motion mode performs the identical change of focus instantly. The complete static atlas remains the default available view. No autoplay or chosen coordinates are required.

Acceptance checks should establish that:

1. Every cue refers to existing objects and relations in its declared scope.
2. Binder renaming preserves cue topology; same-spelled binders in separate scopes never merge.
3. Reversing `∀ x, ∃ y` to `∃ y, ∀ x` changes introduction order and permitted dependence.
4. OR, iff, negation, nested antecedents, and unknown wrappers retain their enclosing roles throughout playback.
5. Static, reduced-motion, and animated presentations expose the same mathematical content.

Coordinated highlighting inside the optional mathematical notation needs a further provenance contract: LaTeX fragments linked to expression IDs. LeanTeX currently returns a string, so matching letters in that string is not a reliable way to identify bound objects.

## What Manim contributes

Manim supplies mathematical drawing primitives, object transforms, animation composition, cameras, and scene output. Its documented architecture separates mathematical objects, animations, scenes, and rendering. These are useful reference boundaries for our own presentation layer. [Manim architecture](https://3b1b.github.io/manim/getting_started/structure.html)

The referenced `3b1b/manim` project is ManimGL, distinct from the community edition. Its current README describes a Python engine with OpenGL and FFmpeg requirements, and optional LaTeX support. Adopting it would add a separate runtime and rendering pipeline. It does not supply Lean elaboration, scoped quantifier semantics, automatic representation selection, or source-to-expression correspondence; those remain StatementLens responsibilities. The latter assessment follows from the documented engine's scope and our required architecture. [ManimGL repository](https://github.com/3b1b/manim)

For this iteration, use the mechanisms as design references and keep the browser renderer. If reliable video export becomes a concrete requirement, a future optional Manim backend could consume the same validated cue plan. It should receive data and a fixed trusted renderer, not arbitrary generated Python submitted by the client.

## Reuse and attribution

The Manim engine uses the MIT license; copied substantial portions would retain its copyright and permission notice. The separate `3b1b/videos` repository declares CC BY-NC-SA 4.0 for its contents and notes that older scenes may require older Manim versions. It is not licensed on the same terms as the engine. No scene code, artwork, video assets, or Manim dependency was copied for this review. [Manim license](https://github.com/3b1b/manim/blob/master/LICENSE.md), [video repository's license statement](https://github.com/3b1b/videos#readme)

Design research and recommendations: Codex under the supervision of Neil Yuanting Li. Inspiration credited to the linked 3Blue1Brown lessons and Manim examples.
