# Generic structure decomposition

The main foundation in this iteration is deterministic inspection of user and library definitions. A mathematical statement should become readable because its objects, maps, applications, and laws can be composed from common pieces, without requiring a dedicated renderer for every mathematical name.

## From a Lean record to common pieces

The native exporter inspects the actual Lean structure declaration of an introduced object. For each exported field it retains the exact projection, its instantiated type, and whether it is data or a proposition. A data field can be a carrier, an element, a set, a function, another structure, or an unfamiliar typed object. A proposition field supplies a law whose logical tree can be read using the existing quantifier, implication, relation, and application grammar.

For example, a previously unseen user record can contain two maps named `carry` and `recover`, two sets named `entrance` and `exit`, and a law stating that the maps undo each other on `entrance`. These names supply labels, not dispatch keys. The generic decomposition exposes the maps and sets and reads the actual quantified law. An unused field remains part of the record's structure. A second record containing a carrier, a binary operation, and associativity uses the same pipeline.

Dependent fields refer to the exact earlier projections. If an internal carrier is `algebra.Carrier`, the operation's inputs and output use that carrier expression. Applying a projected map retains the same field identity in the law. The decomposition must preserve these links through renaming; display labels are never object identities.

## Scope and fidelity

Reflected laws are supplementary information supplied by an introduced object. They do not replace the user's selected proposition or become global facts outside that object's scope. An existential object's fields remain conditional on that witness, and a record inside one alternative does not supply fields to its sibling alternative.

A field's declared type and an available checked expansion are both retained. Small aliases can therefore expose an existing structure or function signature while keeping the user's original name. A `Set` alias can be recognized as a set from its checked type without guessing from the alias's spelling.

An opaque field type remains a typed field with an unresolved meaning. An opaque proposition remains visible in its law. Generic decomposition reveals composition; it does not invent geometric interpretation, coordinates, nonemptiness, smoothness, or a proof of the selected statement.

The reflection work is bounded: at most 16 direct fields, 120 expression nodes per field type, expression depth 24, and a 128 KiB optional structure payload. Large records expose a limited field prefix with an explicit omitted-field count. Recursive inductive types are not expanded into an infinite object graph. Deep type-head aliases report a visible stopping boundary, and unavailable bodies retain their original names. Some early heartbeat or oversized-type exits retain only the original typed object without a specific omission reason; more complete boundary reporting remains work to do. No such fallback is treated as an interpreted definition. Direct inherited parent fields remain explicit subobjects; their complete nested structure is not recursively expanded in this release.

## Special mathematical lenses

An optional specialized lens can improve how a recognized collection of relations is arranged. The [restricted-map lens](restricted-iteration.md), for example, places two carriers and valid regions around forward and reverse arrows and keeps the inverse laws guarded by membership. `PartialEquiv` and `OpenPartialHomeomorph` share this grammar; they do not require separate theorem renderers.

These lenses supplement the generic foundation. Unknown user record names still expose their checked fields and laws. The existing bounded definition previews, typed constructions, application dependencies, set relations, graph constraints, and logical guide are reusable components of the same direction.

## Independent acceptance fixtures

[`corpus/structures.ts`](../corpus/structures.ts) contains fresh user definitions chosen to avoid known-constructor shortcuts:

- Two abstract maps, function and set aliases, an unused scalar field, and guarded laws.
- The same record with every structure, alias, and field name changed.
- An internal carrier, binary operation, distinguished element, and algebraic laws.
- A field with an opaque type and a law with an opaque predicate.
- A new alias for an unfamiliar record.
- A 23-field record that exceeds the reflection field budget.
- A chain of type aliases and a recursive inductive type.
- A record whose fields are all proofs, available only under its local hypothesis.
- Two same-named record witnesses under separate negated alternatives.

[`scripts/decomposition-integration.ts`](../scripts/decomposition-integration.ts) uses actual editor buffers and inspects the native reflection, semantic composition, production object renderer, and whole-statement reader. The ten fixtures require retained identities, scoped laws, bounded output, and explicit unknown or omitted structure. None of the fixture names is a built-in semantic rule. Native executable and private-source checks distinguish a stable test result from a concurrent rebuild.

The [coverage corpus](coverage-corpus.md) remains a separate regression inventory for interpreted and unknown predicate vocabulary. Its categories are not a percentage of mathematics understood. The release's recorded verification and environment limitations are in [verification](verification.md).

## Limits of this foundation

This implementation reflects direct record fields and laws and inspects bounded type-head aliases. It does not yet decompose arbitrary recursive inductives or all nested record fields. Reflection reads what the structure declares; it does not infer every mathematical consequence or automatically synthesize the best picture of every abstraction. Generic law diagrams also do not by themselves explain a topological obstruction, a rank theorem, or graph planarity. Additional common primitives and optional lenses can improve those readings without introducing a named-theorem catalogue.

The implementation uses Lean's checked expressions and structure metadata. Mathlib definitions used by optional lenses remain pinned and credited in [NOTICE](../NOTICE). Existing Manim and Penrose design references are inspiration; no corresponding runtime or scene asset is added by this iteration.

Development and design assessment: Codex under the supervision of Neil Yuanting Li.
