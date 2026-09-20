# Compositional set interpretation

The set grammar recognizes imported `Set.union`, `Set.inter`, `Set.diff`, and
`Set.compl`, plus overloaded `Union.union`, `Inter.inter`, `SDiff.sdiff`, and
`Compl.compl` only when the Lean exporter reports a canonical instance and a
`Set` result descriptor. Explicit value arity must be exact. Partial applications,
custom instances, non-set overloads, and unrecognized definitions retain their
structural representation. The constructor definitions are those in the pinned
Mathlib `Mathlib/Data/Set/Defs.lean`; no theorem names or source spelling trigger a
view.

Semantic relations use kind `set-construction`, a `setOperation`, ordered
`operand 1` / `operand 2` ports (one operand for complement), and a `result` port.
The expression and its original type/instance arguments remain intact. Object
identity uses elaborated expressions and binder identities, not display labels.
Expression identity keys serialize the structural expression once, avoiding exponential escaping in deeply nested applications. A membership, subset, or equality relation consumes that same result object.

`compileSetConstruction(document, relation, relations?)` creates an ordered set
expression graph. It accepts producers only from the root relation's exact
source node and expression scope. It never captures a local lambda body into
its enclosing statement. Image/preimage constructions can participate, but an
image is an atomic set in its result type when Boolean membership regions are
computed: membership of its source sets does not become membership in the
codomain. Input order is preserved, including the asymmetry of difference.

`SetConstructionFigure` accepts that document and root relation, the optional
scoped relation list, and shared object selection callbacks. For up to three
atomic sets it draws a schematic of Boolean membership combinations:

- Membership highlights all allowed combinations without choosing which one
  contains the named element.
- Subset highlights combinations that must be empty: in the left operand and
  outside the right.
- Equality highlights the symmetric difference, which must be empty.
- Inequality highlights combinations where a distinguishing witness is required;
  it chooses no witness.
- A set expression highlights its defining membership combinations.

These regions are not a sample population. No dots, inhabitedness, cardinalities,
relative sizes, or nonempty intersections are invented. Drawing the ambient type does not assert inhabitedness. The surrounding reader retains the statement's assumptions, quantifiers,
negation, and alternatives; this figure describes its clause condition and does
not assert that the condition is true. For more than three distinct atoms, the
renderer keeps ordered construction steps instead of assigning a planar Venn
shape. Construction steps reuse exact object identities and are progressively
revealed six at a time.

Model expansion is bounded at 18 construction levels and 80 producer visits.
Unexpanded subexpressions remain consistently named atomic objects; they are not
replaced by guessed sets. Boolean evaluation visits each shared construction
once per assignment and evaluates at most eight assignments. It requires an
explicit membership value for each atom. These are symbolic display calculations,
not Lean proof certificates; the original statement is still checked by Lean.

Validation: targeted semantic and renderer tests cover all operations, custom
and partial rejection, scope isolation, shadowed identities, repeated operands,
map codomains, and Boolean condition interpretation. Run the native export checks
with `node --import tsx scripts/set-construction-integration.ts`.
