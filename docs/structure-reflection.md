# Generic decomposition of Lean structures

The primary 0.7 foundation reads a structure's actual fields and laws from Lean. It needs no entry for the structure's name or its field names. A fresh user-defined record containing maps, subsets, elements, and quantified laws can feed the same typed-object and logical primitives used elsewhere in the reader.

This is deterministic reflection of the checked mathematical definition. It does not train a model, compare a theorem name against a catalogue, or infer a meaning from words such as “forward,” “chart,” or “inverse.” The specialized restricted-map adapter remains an optional concise view of a known contract; generic decomposition exposes unfamiliar records independently of that adapter.

## Native record view

For each bound value, the exporter asks Lean's `getStructureInfo?` for its type. If the type is a small safe alias, it follows at most two type-head definitions and checks definitional equality. It then uses Lean's ordered direct-field metadata and `mkProjection` to form each exact projected value. Both the projected expression and its inferred type are checked by the kernel before export.

A field's kind is determined by whether its type is a proposition. Data fields retain their projected value, type expression, and structural type descriptor. Law fields also receive the ordinary logical statement tree, in the owning value's lexical context. The projection itself is the evidence supplied by that structure value; its law is not a globally asserted theorem. This also applies to law-only records in `Prop`, whose proof fields remain scoped to the local hypothesis.

Each field records dependencies by occurrences of earlier exact projected expressions in its type. Printed names are labels only. The complete projected expression remains available to distinguish different records, shadowed binders, and unrelated fields with the same name. A data field with a small type alias may have the same optional checked `typeExpansion` view used for ordinary binders.

Direct inherited subobjects remain explicit fields and identify their parent structure. This release does not recursively flatten or synthesize all their fields. Likewise, law trees suppress recursive structure reflection of their own newly introduced binders, preventing an unbounded tree of supplementary explanations.

## Export contract and limits

`Binder.structure` contains:

- The actual structure name and reflected type expression.
- Ordered fields with projector name, projected expression, original type and type expression, descriptor, data/law kind, exact dependencies, and optional law tree, parent structure, or checked type view.
- A true kernel-check marker, field omission count, explicit export limits, and a stop reason when only a bounded prefix or subset could be read.

Reflection is limited to 16 direct fields. Projected expressions and field types each have at most 120 expression nodes and depth 24; the optional envelope is at most 128 KiB. Each binder has an independent two-million-heartbeat ceiling while preserving a reserve for its enclosing request. Unsafe, partial, opaque, oversized, unresolved, or placeholder-bearing reductions are not used to expose types. If a field cannot be exported safely within these bounds, its omission is recorded.

Optional reflection runs inside the existing elaboration and restores meta state. It neither replays the editor buffer nor changes a project declaration. If aggregate response size exceeds the transport budget, optional structure and type views are removed recursively and affected binder records receive `structureOmission`. The original checked statement remains the mandatory result.

## What this enables and what remains

The frontend can read a new record as typed data followed by its quantified, conditional, or relational laws. Its exact field expressions are shared objects in those laws, so a map application, an intermediate value, a subset membership condition, and a subsequent equality can compose rather than become separate pictures keyed by the record's name. Unknown predicates remain visible at the point where interpretation stops.

Reflection supplies checked structure, not a universal geometric interpretation. It does not decide that arbitrary inverse-like fields form a homeomorphism, deduce continuity from naming, prove a proposition, choose coordinates, or discover a useful normal form for every recursively defined object. General arbitrary-definition reduction, recursive algebraic data types, automatic theorem-level abstraction, and richer geometric primitives remain future work.

The implementation reuses Lean's public structure metadata and expression-building APIs, under the existing Lean dependency and Apache-2.0 license. It adds no new third-party visualization runtime or copied artwork.
