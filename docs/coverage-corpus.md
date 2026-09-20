# Semantic coverage corpus

The corpus answers a narrow, reproducible question: **which mathematical relationships in these selected Lean statements are interpreted, which remain structural, and which previously supported relationships have regressed?** It does not estimate a percentage of arbitrary mathematics, certify any proposition, or establish that a reader understands a diagram.

Run from the repository root after the local native worker, context sidecar, and their pinned dependencies have been built:

```sh
node --import tsx scripts/corpus-audit.ts
```

Case IDs may be supplied for a focused run. A renaming case automatically includes its baseline. Full results are written to ignored `.local/corpus-audit.json` and `.local/corpus-audit.md`; focused results use `corpus-audit-focused` and cannot overwrite the full record. The process exits unsuccessfully if a selected expectation fails or a native executable changes during the run. Nothing updates expected results automatically.

## Fixtures and categories

[`corpus/cases.ts`](../corpus/cases.ts) contains 18 hand-reviewed cases. They cover set images and Boolean operations, quantifier dependence, negated alternatives, custom membership, continuity, supported fragments inside unknown predicates, imported project definitions, dependent functions, local inverse laws, local rank conditions, and graph/color constraints. These are vocabulary probes, not bespoke implementations of named theorems.

- **Supported** means the chosen statement has no opaque predicate applications and its listed reusable relations are recognized. It does not imply all structure declared in binder types has a specialized interpretation. In particular, the section example tests a dependent function and equality, not a smooth vector bundle.
- **Partially supported** requires both interpreted relations and opaque expressions. A source restriction or equality can be understood while the local homeomorphism or rank expression inside it remains uninterpreted.
- **Currently unsupported** requires the chosen predicate to remain structural with no interpreted relation. Typed objects and their argument order are still available. Some negative cases must remain unsupported unless an explicit semantic contract is supplied, such as a custom membership instance or a project constant imitating a familiar name.

The graph cases express adjacency, a supplied proper coloring, and colorability constraints. They do not assert planarity, draw a complete arbitrary graph, construct a coloring, or establish the four-color theorem. The local rank fixture supplies a family of linear maps; it does not identify that family with a derivative or formalize the constant rank theorem. The local homeomorphism fixture uses an actual imported `OpenPartialHomeomorph`; it does not infer a manifold atlas from a theorem name.

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

Expected missing constructors are asserted too. If a new plugin interprets one, the corpus fails until its case and explanation are deliberately reviewed. This prevents stale documentation from silently describing a new interpretation as unsupported.

## Recorded local result

The full corpus passes **18/18 case expectations** with unchanged native binary hashes during the run and unchanged private source/configuration files. The selected corpus contains 10 supported, five partially supported, and three currently unsupported cases. These categories describe the fixtures, not a completion percentage for mathematics. The runner and fixture definitions also pass a focused strict TypeScript check.

The first complete run exposed two real gaps: graph color bounds retained an unaudited natural numeral, and a finite color carrier was misclassified as an opaque predicate. Exact native numeral auditing and carrier traversal were corrected; the original positive expectations then passed without weakening them. The remaining inventory includes continuity, local-homeomorphism projections, finite rank, nonemptiness, project definitions, and deliberately unaudited instances. Real-valued numeral interpretation in editor contexts remains conservative.

## Next reusable foundations

Inspection of the pinned Mathlib source suggests two connected contracts, rather than theorem-specific diagrams:

1. **Restricted maps and local inverses.** `OpenPartialHomeomorph` extends `PartialEquiv` with open source/target sets and continuity on those sets. A faithful representation needs typed endpoints, forward/inverse maps, their explicit valid regions, and inverse laws limited to those regions. The current set/image/preimage grammar is useful groundwork, but displaying those sets is not yet an interpretation of the local map. Source: `Mathlib/Topology/OpenPartialHomeomorph/Defs.lean` at the project's pinned revision.
2. **Base, fibers, projection, and sections.** A dependent function `(x : B) → E x` already identifies a section-shaped signature. A bundle interpretation additionally needs a total space and projection, and must keep continuity, linear structure, and local triviality as explicit requirements. Mathlib's `Trivialization` extends a local homeomorphism from the total space to `B × F`, restricts its source to the preimage of a base region, and requires compatibility with the projection. Source: `Mathlib/Topology/FiberBundle/Trivialization.lean` at the pinned revision.

These contracts could be shared by future chart and bundle views. They are **not implemented by this corpus**. Derivatives, rank of linear maps, smooth charts, tangent fields, and topological obstruction arguments require further audited semantic rules and representation contracts.
