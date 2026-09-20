# Maps inverse on designated regions

StatementLens uses one shared diagram contract for a map with two carriers, two designated regions, and inverse laws on those regions. The Lean adapter recognizes `PartialEquiv` and `OpenPartialHomeomorph`. It does not recognize a theorem by its name or build a particular coordinate model. New provers or checked constructions can target the same contract.

The audited definitions come from Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` with Lean 4.28.0:

- [`PartialEquiv`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Logic/Equiv/PartialEquiv.lean)
- [`OpenPartialHomeomorph`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean)

Their definitions are reused through the existing pinned Mathlib dependency, under Apache-2.0. No upstream diagram code or artwork is copied for this vocabulary.

## Shared meaning

A partial equivalence stores total forward and inverse functions. It also specifies a source subset of the first carrier and a target subset of the second. The forward function sends source into target, the inverse sends target into source, and the respective round trips are identities there. Their values outside those sets carry no inverse guarantee. The subsets can be empty or the whole carrier.

An open partial homeomorphism adds openness of those subsets and continuity of the two functions on their respective subsets in the supplied topologies. This does not imply differentiability, a manifold structure, coordinates, a dimension, or a global homeomorphism.

| Shared relation | Ports | Additional metadata |
| --- | --- | --- |
| `restricted-equivalence` | map, source carrier, target carrier | map kind, direction |
| `restricted-region` | map, source carrier, target carrier, region | map kind, direction, source/target side |
| `restricted-application` | map, source carrier, target carrier, input, output | map kind, direction |

The map kind is `partial-equivalence` or `open-partial-homeomorphism`. Direction is `forward` or `inverse`. The actual projected set and application expressions retain their native expression identities. The binder relation introduces no fabricated point, set expression, or membership witness. Its region slots describe structural obligations, not discovered nonempty geometric shapes.

Only exact audited `symm` and `toPartialEquiv` constructions normalize the map identity. Thus `e.symm.source` points to the target side of the original `e`, and `e.symm y` points in the inverse direction, while keeping each original set or application expression intact. An unfamiliar constructor returning a partial equivalence remains its own map object. No relationship to its arguments is guessed.

## Native provenance and coercions

Editor mode checks exact declaring modules for the interpreted structures, projections, and symmetry operations. The TypeScript adapter then requires canonical provenance, complete saturation, the exact argument classifications, and a set or type result where appropriate. A project declaration that merely shares a spelling is not recognized.

Lean's ordinary `CoeFun` instances for these structures elaborate to the stored `PartialEquiv.toFun` or `OpenPartialHomeomorph.toFun'` projection. The adapter recognizes those exact projections. It does not assign their meaning to a generic `CoeFun.coe`, a custom coercion, a partial application, or a printed type name. Arbitrary supplied topology instances remain legitimate parameters; the adapter does not assume a particular topology.

The fixed worker imports `Mathlib.Topology.OpenPartialHomeomorph.Defs`; setup requests its dependency closure in the repository's isolated cache. Editor mode continues using the selected project's built imports.

## Checked type-head exposure

Small type aliases share existing representations automatically. A binder `e : MyMap X Y`, with `MyMap X Y := PartialEquiv X Y`, retains its printed type and receives an optional checked view of the underlying type. The compiler first tries the original type and only then that view. This same mechanism works for graph/coloring aliases and aliases to function types; it is not a map-specific list of accepted alias names.

The native exporter attempts at most two safe type-head definition steps in the original elaboration context. Each result must have at most 80 expression nodes and depth 24, contain no metavariables or `sorry`, pass the kernel expression check, and be definitionally equal to the original type. Already audited constructors remain folded. Opaque, unsafe, partial, oversized, unchanged-head, or over-budget steps are not exposed. If a later step cannot proceed, an earlier checked view can still be returned; it does not gain unsupported semantics merely by being present.

The optional `Binder.typeExpansion` records the original and resulting displays, expanded constants, expression, a true definitional-equality marker, and depth limit 2. It has a separate 200,000-heartbeat budget, reserves the parent request's budget, restores meta state, and is capped at 64 KiB. This metadata is produced for both statement binders and editor context binders without executing the source buffer again. The consumer also validates these bounds before using it. This is a reusable decomposition step, not general structure-field synthesis or unlimited unfolding.

## Boundaries

The shared diagram supports scoped variables, hypotheses, negations, alternatives, and actual applications. An application alone does not establish source/target membership. A displayed conditional law does not prove a selected proposition.

This foundation does not yet interpret tangent bundles, vector fields, constant-rank factorizations, arbitrary smooth charts, arbitrary structures with inverse-like fields, or the hairy-ball theorem. Adding arbitrary names that resemble these concepts would not supply their checked meaning. Wider coverage requires further semantic decomposition and composition rules feeding shared visual primitives.
