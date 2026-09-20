# Semantic coverage corpus

The corpus answers a narrow, reproducible question: **which mathematical relationships in these selected Lean statements are interpreted, which remain structural, and which previously supported relationships have regressed?** It does not estimate a percentage of arbitrary mathematics, certify any proposition, or establish that a reader understands a diagram.

Run from the repository root after the local native worker, context sidecar, and their pinned dependencies have been built:

```sh
node --import tsx scripts/corpus-audit.ts
```

Case IDs may be supplied for a focused run. A renaming case automatically includes its baseline. Full results are written to ignored `.local/corpus-audit.json` and `.local/corpus-audit.md`; focused results use `corpus-audit-focused` and cannot overwrite the full record. The process exits unsuccessfully if a selected expectation fails or a native executable changes during the run. Nothing updates expected results automatically.

## Fixtures and categories

[`corpus/cases.ts`](../corpus/cases.ts) contains 25 hand-reviewed cases. They cover set images and Boolean operations, quantifier dependence, negated alternatives, custom membership, continuity, supported fragments inside unknown predicates, imported project definitions, dependent functions, local inverse laws, local rank conditions, graph/color constraints, checked type aliases, and unaudited coercions. These are vocabulary probes, not bespoke implementations of named theorems.

- **Supported** means the chosen statement has no opaque predicate applications and its listed reusable relations are recognized. It does not imply all structure declared in binder types has a specialized interpretation. In particular, the section example tests a dependent function and equality, not a smooth vector bundle.
- **Partially supported** requires both interpreted relations and opaque expressions. An equality can be understood while a rank expression inside it remains uninterpreted; a restricted map can have an interpreted bundled contract while an independently supplied coercion remains unknown.
- **Currently unsupported** requires the chosen predicate to remain structural with no interpreted relation. Typed objects and their argument order are still available. Some negative cases must remain unsupported unless an explicit semantic contract is supplied, such as a custom membership instance or a project constant imitating a familiar name.

The graph cases express adjacency, a supplied proper coloring, and colorability constraints. They do not assert planarity, draw a complete arbitrary graph, construct a coloring, or establish the four-color theorem. The local rank fixture supplies a family of linear maps; it does not identify that family with a derivative or formalize the constant rank theorem. The local homeomorphism fixture now interprets the actual imported `OpenPartialHomeomorph`, its source projection, and its inverse applications. Its type supplies openness and continuity on the valid regions, without introducing a general continuity grammar or inferring a manifold atlas from a theorem name.

## Native execution and isolation

Standalone cases pass through the existing fixed-environment worker. Editor cases pass actual Lean source and an exact selected proposition through the native project-context sidecar. A private temporary project contains a compiled copy of [`ProjectDependency.lean`](../corpus/ProjectDependency.lean); one case imports that definition to exercise a genuine compiled dependency. The saved files deliberately differ from submitted unsaved buffers. The runner verifies that all private project source/configuration files remain unchanged and removes the temporary project afterward.

The runner never rebuilds the engine, fetches dependencies, changes the pinned toolchain, invokes Lake, or modifies a user project. It reads existing library paths from `.local/config.json`. A missing built dependency or unavailable native engine fails the audit explicitly. Project-context evaluation uses trusted fixture source and the existing adapter; its separate process is not a security sandbox.

The assessment compiles the primary exported statement before optional definition previews or explicit expansion. An opaque constructor can therefore still have a useful separately labelled preview; expandable-definition metadata is included in the interpretation report. The report records source hashes, native binary hashes, and exported prover provenance. It lists the local relation vocabulary, exact opaque application heads, typed-object and scoped-choice counts, native validation labels, and diagnostics. These counts describe this corpus only. The missing-head inventory includes projections and coercions, and its frequency is not a ranking of mathematical importance. `canonical: false` means the constructor has not passed the current built-in provenance audit; it does not by itself mean a project is malicious or the definition is invalid. Type arguments hidden by the current export policy are not counted as opaque applications; absence from the inventory therefore does not prove their mathematical meaning is understood.

## Independent semantic expectations

Every case checks source-node coverage, relation-port identities, scope references, permitted choice dependencies, and the agreement of guided cues with their logical branch and assumption context. Additional checks require:

- Renaming every user binder preserves constructor/port topology and dependency structure.
- `∀ c, ∃ p` and `∃ p, ∀ c` retain their distinct introduction order.
- Both branches inside a conditional negation retain the premise and enclosing logical roles.
- A known child of an unknown project predicate cannot replace the parent assertion; contained-expression cues must say they are not separate assertions.
- An indexed section keeps a genuinely dependent target in the typed construction model.
- Untrusted familiar names and unaudited instances cannot acquire canonical visual semantics.
- Restricted inverse applications share the original bundled value through `symm`, and user renaming preserves their port/dependency topology.
- A checked user type alias reaches the shared restricted-map grammar without a recognizer for the alias's name.
- The source restriction in a local inverse statement is retained as a premise, while project wrappers and arbitrary coercions stay unknown.

[`corpus/structures.ts`](../corpus/structures.ts) is a separate acceptance corpus for generic record reflection. Its fresh record and field names are not mathematical dispatch rules. It exercises maps, sets, an internal carrier, a binary operation, laws, unused fields, opaque types and predicates, type aliases, and size/depth boundaries. [The decomposition iteration](decomposition-iteration.md) describes this broader foundation; predicate-vocabulary counts below do not measure the completeness of reflected record meanings.

Expected missing constructors are asserted too. If a new plugin interprets one, the corpus fails until its case and explanation are deliberately reviewed. This prevents stale documentation from silently describing a new interpretation as unsupported.

## Recorded local result

The expanded corpus passes **25/25 case expectations**, with stable native executable hashes and unchanged private source/configuration during the run. It contains 15 supported, seven partially supported, and three currently unsupported cases. These categories describe the fixtures, not a completion percentage for mathematics. Each full execution records the exact results and exported provenance in `.local/corpus-audit.json`; focused runs cannot overwrite that record. The release's combined verified results are listed in [verification](verification.md).

The first complete graph iteration exposed two real gaps: graph color bounds retained an unaudited natural numeral, and a finite color carrier was misclassified as an opaque predicate. Exact native numeral auditing and carrier traversal were corrected; the original positive expectations then passed without weakening them. The restricted-map iteration deliberately upgrades the local-homeomorphism case only after its projections and applications receive audited semantics with no remaining opaque heads. The remaining inventory includes general continuity, finite rank, nonemptiness, project definitions, and deliberately unaudited instances. Real-valued numeral interpretation in editor contexts remains conservative.

## Next reusable foundations

Generic reflection now exposes declared fields and laws of unfamiliar records through common pieces. Optional lenses can further organize those pieces when their mathematical contract is audited. Inspection of the pinned Mathlib source suggests the following connected work:

1. **Restricted maps and local inverses.** The current shared lens now represents `PartialEquiv` and `OpenPartialHomeomorph` using carriers, valid regions, forward/reverse maps, and conditional inverse laws. It supplies groundwork for charts, but chart families and smooth compatibility are additional mathematics. Source: [the pinned OpenPartialHomeomorph definition](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean).
2. **Base, fibers, projection, and sections.** A dependent function `(x : B) → E x` already identifies a section-shaped signature. A bundle interpretation additionally needs a total space and projection, and must keep continuity, linear structure, and local triviality as explicit requirements. Mathlib's `Trivialization` extends a local homeomorphism from the total space to `B × F`, restricts its source to the preimage of a base region, and requires compatibility with the projection. Source: `Mathlib/Topology/FiberBundle/Trivialization.lean` at the pinned revision.

These contracts can be composed in future chart and bundle views. Derivatives, rank of linear maps, smooth charts, tangent fields, and topological obstruction arguments still require further mathematical representation. The corpus itself is an evaluation harness; it does not implement the visual grammar.
