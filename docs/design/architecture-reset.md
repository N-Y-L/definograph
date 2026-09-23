# Architecture reset: from recognizers to compositional reading

**Status: design proposal, not an implemented replacement; superseded by the [architecture decision](architecture-decision.md) where the two differ.** Written against the 0.7 code after the generic-record iteration. The current code map is in [architecture.md](../architecture.md); delivery gates are in [roadmap.md](../roadmap.md).

## Objective and standard of success

Definograph should help a reader see the objects, relationships, assumptions, and quantifier dependencies in a mathematical statement. It should use the actual formal context and definitions, work without a coordinate system, and choose an informative representation automatically. The first view is a reading sequence with a folded overview alongside it. Examples and manipulation may help later; they are not substitutes for displaying the statement.

The user's central architectural observation is sound: a reusable visual vocabulary, a way to expose unfamiliar definitions, and composition rules can generalize beyond a catalogue of named objects. The present code only partially implements this pattern. More recognizers will not close its structural gaps.

The long-term objective remains **useful visualization of arbitrary mathematical statements**. A faithful, inspectable partial reading is an explicit fallback while mathematical meaning remains unsupported; it is not a redefinition of success. Reaching the objective requires increasingly useful abstractions, not just accepting arbitrary syntax. An opaque declaration has no body to expose. An abstract structure may have no distinguished concrete model. Recursive definitions cannot be exhaustively expanded into a finite picture. Even a fully exposed definition can obscure the mathematical idea. These are reasons to represent boundaries and select abstractions, not reasons to replace the goal with a gallery of examples or promise that every definition has a finite, uniquely best geometric picture.

## Findings from the current code

| Finding | Code evidence | Consequence |
|---|---|---|
| Several separate decomposition paths | `Export.lean` has `tree`, `reflectBinder`, `binderTypeExpansion`, and `definitionPreviews`; `semantic/inspection.ts` chooses a preview; `decomposition/compiler.ts` builds supplementary documents | Being understandable in one location does not imply being understandable in another |
| Nested law inspection is not closed under composition | `tree` calls `reflectBinder` with a callback using an empty expansion policy and `reflectStructures := false`; `compileStructuralObject` directly compiles the resulting law tree | The same `Function.LeftInverse` that opens at the root remains folded in an `Equiv` field law |
| Direct fields are exposed eagerly and shallowly | A binder may carry up to 16 direct fields; inherited records stay as subobjects; nested law binders do not reflect | The current result is often a field inventory, not a focused explanation of the selected condition |
| The shared schema still grows with domain adapters | `RelationKind` includes graph and restricted-map variants; `relationMetadata` and renderer dispatch know those variants | New mathematical lenses still require cross-layer changes; the generic substrate is not yet a small independent contract |
| Interpretation and sample discovery remain coupled | `compileSemanticDocument` calls `discoverScenes`; semantic types import core scene types | The intended statement/model separation is incomplete |
| Abstraction is selected by local heuristics | `inspectSmallDefinitions` favors a reduction in opaque-region count; `planViews` uses fixed representation scores | Opening one useful predicate into several new predicates can lose under a count metric; ranking does not measure comprehension |
| Existing checks validate a bounded success path | `corpus/structures.ts` tests fresh/renamed direct records, aliases, opaque boundaries, and scope; recursive/deep cases are allowed to stop | These are valuable safety and generality checks, but not evidence of recursive decomposition or broad mathematical usefulness |

Retain the real strengths: exact projected expressions; checked types and definitional equality; shared object identity; scope, branch, and witness-dependency handling; explicit unknown regions; bounded exports; actual project-context extraction; and independent notation. Preserve these through refactoring. Their value is as contracts and regression cases, not proof that the overall design is finished.

The public reader and the native exporter are trusted program components. A JSON `kernelChecked` marker records a result from that native component; it is not a proof independently verified by the browser. Any new documentation or evidence format must keep that distinction.

## Proposed separation of responsibilities

```text
Actual prover context
       │ typed terms + identities + source occurrences
       ▼
Checked decomposition service ── demand ──┐
       │                                 │
       ▼                                 │
Shared intensional graph ── abstraction planner
       │                         │
       │                 admissible view plan
       │                         │
       └─────────────────────────▼
                    Compositional renderer

Optional concrete/model providers ──► separate model views
```

This is a proposed organization, not a request to create empty packages. Implement it through the first vertical slice, then extract stable module boundaries. The browser should request decompositions by checked term/context handles, not send executable Lean fragments or filesystem choices. A prover adapter owns term elaboration, reduction, type checking, declaration access, and context lifetime. Shared code owns graph composition and representation contracts. Rendering owns layout and interaction.

### 1. Small intensional representation

Use a representation of **what the statement says**, rather than what a convenient sample looks like. Its initial grammar needs only:

- Typed objects and type/family expressions, including the identity of their actual prover terms.
- Binding and scope: parameters, universal variables, existential obligations, hypotheses, and local definitions.
- Applications with typed input/output ports, projections, and references to shared terms.
- Atomic conditions and equality, with logical composition: implication, conjunction, alternatives, equivalence, and negation.
- Available field/law declarations and their dependencies on an owning object and context.
- Folded expressions with an explicit reason that further interpretation is unavailable or deferred.

Sets and relations can have useful shared representations over this grammar. A typed predicate may be displayed as an abstract condition; a curve or shaded region needs additional justification. Keep mathematical names as annotations and navigable folds. Do not erase universes, instances, coercion provenance, dependent types, or binder identity merely because most views hide them.

This is a **candidate small vocabulary**, not a claim of mathematically proved minimality. Inductive alternatives, quotients, and elimination may require additional structure. The adapter may retain an opaque native term handle when the shared grammar cannot express a term faithfully. A future Rocq adapter must satisfy the same meaning contracts, not imitate Lean's serialized syntax.

Separate semantic identity from source occurrence. Repeated terms can share one graph node while keeping several occurrences. Only terms in compatible contexts can share identity. Definitionally equal expressions may be linked by evidence without collapsing their useful original names. Do not attempt arbitrary equivalence checking to deduplicate a whole library.

### 2. Demand-driven checked decomposition graph

Every inspection operation acts on the same kind of node, whether it originated in the selected statement, a nested data field, a law, or an alias. A request contains a context revision, a term handle, an operation, and a resource allowance. Initial operations are:

1. Expose one definition or local-definition step.
2. Inspect direct fields of a structure value.
3. Expose logical and dependent-function structure.
4. Inspect constructor alternatives when the later inductive milestone supports them.

The result contains the original node, derived nodes, typed edges, evidence, and an explicit stop reason when incomplete. Each accepted reduction is checked in the original context. Each field includes its exact projection and type. A law includes the projection or assumption that supplies it and the context in which it is available. Theorems used as abstractions require a checked application with its premises; definitional equality is not interchangeable with a theorem.

Use a DAG for finite decompositions with explicit folded reference nodes for recursive dependencies. Memoize requests by environment revision, local context, native term identity, and policy. Maintain an active expansion stack as well as a completed cache: a recursive reference is not permission to expand again. Invalidate results when relevant project context changes. Stable semantic IDs must not be regenerated merely because a nearby fold opens.

Budget each operation and the complete reading: native heartbeats/time, term nodes, graph nodes, depth, response bytes, and displayed complexity. A budget stop must retain the folded original and distinguish `opaque`, `recursive`, `unsupported operation`, `budget`, `cancelled`, and `stale context`. Do not hide these outcomes behind a generic successful extraction status. A failed optional inspection must not destroy the checked primary statement.

An implementation may start with requests resolved during one bounded native analysis. Persistent demand-driven requests require a context-lifetime design before they are exposed to the browser. They must reuse a valid elaborated context or clearly perform a new user analysis; automatic inspection must not silently replay source commands once per fold. The current preview path's single-execution test is an invariant to keep.

### 3. Composition rules and evidence contracts

A representation rule declares a typed input pattern, requirements, scope dependencies, output ports, preserved facts, omitted information, and required evidence. It matches exposed structure and available laws rather than theorem or field names. A specialized library adapter may supply a concise rule, but disabling it must leave a usable generic reading.

Start with a few reusable visual operations:

| Operation | Meaning that may be shown | What must not be inferred |
|---|---|---|
| Introduce object/type | A named object in its actual binder context | A chosen coordinate model or a finite cardinality |
| Apply map or relation | Typed arguments linked to the actual result or condition | Continuity, invertibility, or truth of the condition |
| Compose applications | Shared intermediate terms and ordered ports | Equality between different intermediate terms without evidence |
| Show dependent family | Fiber/type dependency on a base object | A geometric bundle, local triviality, or smoothness |
| Show law or constraint | Its inputs, premises, and conclusion | Global validity outside the owning object and scope |
| Frame logical context | Conjunction, alternatives, implication, negation, and quantifier order | Simultaneous availability of alternative branches or an existing witness |

Composition is primarily port connection and logical framing. Typed ports must agree in the actual context, not merely share labels. A field law retains its owner; an implication premise is available only in the consequent; a witness may depend only on earlier allowed choices. Negation surrounds the whole relevant assertion. Do not turn nested applications inside an unknown predicate into independently asserted clauses.

Each visual element should trace back to the represented graph nodes, source occurrences where available, and evidence edges. Use distinct evidence classes for typed structure, definitional equality, available assumptions/field proofs, theorem-derived facts, and model approximations. For the first slice, a typed schema and trace assertions are sufficient engineering gates; no formal proof of renderer correctness is claimed.

### 4. Deterministic abstraction selection

Unfolding is a means of exposing useful relationships, not the objective. First enforce admissibility: preserve scope, polarity, dependencies, identity, and the meaning of every encoded relation. Preserve access to omitted statements and folded originals. Reject a candidate that acquires meaning solely from a field name or an illustrative model.

Then generate a bounded set of candidates from shared rules. Select deterministically using an inspectable order:

1. Expose the objects and obligations needed to read the selected clause.
2. Preserve connections to its immediate logical context and shared terms.
3. Prefer useful established abstractions when opening them adds no relevant relationship.
4. Minimize visible complexity, duplicated objects, and expansion depth among candidates satisfying those needs.
5. Break remaining ties with stable rule and node identifiers.

The implementation should log the satisfied requirements, omitted details, and score components. Candidate enumeration and any numeric weights must be versioned and evaluated. Reducing the count of opaque nodes alone is not sufficient: one unknown wrapper may unfold into several meaningful obligations whose atomic predicates remain abstract. Conversely, a large expansion into basic logic may technically reduce opacity while becoming unreadable.

There is no established objective function for the universally “best” mathematical explanation. This proposal commits to deterministic, testable choices and measured reading usefulness. It does not claim that a heuristic score proves perceptual optimality. Local AI/ML is unnecessary for the initial architecture; any future learned ranking must not decide mathematical truth or replace evidence requirements.

### 5. Optional extensional models

Keep concrete realizations separate from the intensional statement. A model provider may supply finite graph data, coordinates, sampled function values, or a user-given witness. It must state which abstract objects it interprets, what assumptions it satisfies, which checks support that claim, and what is approximate.

No automatic sample should create an unasserted existence claim. A schematic drawing is not a finite enumeration. For a high-dimensional object, a slice, projection, distance profile, or incidence diagram preserves different information; the selected view must state its relationship to the ambient object. These providers enrich reading but cannot repair a missing understanding of quantifier structure.

## First vertical slice

Implement **a nested unfamiliar record whose quantified law unfolds through ordinary definitions into shared maps and a scoped equality**, alongside an existing library record. This closes a concrete composition failure without trying to solve every mathematical domain.

Use fixture names chosen after the rule implementation. One example shape is a user record containing another record with two maps; an outer field states a law through two ordinary definition wrappers. The law says that, for every input satisfying a predicate, a return application equals that input. Additional cases place the owner under an existential, negation, or alternative and place an existential result inside a universal law. No specific field spelling supplies its semantics.

### Acceptance criteria

1. **One mechanism across locations.** Root-level `Function.LeftInverse` and an `Equiv` field law both expose the same quantified return condition through the shared decomposition interface. No special `Equiv` or `LeftInverse` renderer is added.
2. **Previously unseen definitions.** A nested user record and its law wrappers reach ordinary objects, applications, premises, and equality without editing a recognizer table. Record, field, binder, and wrapper renaming preserves the normalized graph and visual topology.
3. **Actual dependencies.** Internal carrier projections remain the exact carrier used by field maps. Repeated intermediate applications share identity. Nested subobjects remain attached to their owner, and original names remain available at every fold.
4. **Quantified laws.** Changing `∀ x, ∃ y` to `∃ y, ∀ x` changes the witness dependency diagram. A law available from a hypothetical owner does not assert that the owner exists. No facts or fields cross sibling alternatives or escape negation.
5. **Ordinary abstraction.** With domain-specific lenses disabled, the first view gives a connected, typed map/condition reading and the overview retains its logical context. It is not only a list of field names or an expanded syntax tree.
6. **Honest boundaries.** Opaque predicates stay explicit. Recursive references, deep wrappers, large records, and cancellation produce bounded results with specific stop reasons. Increasing the allowance can expose additional nodes without changing already established meaning.
7. **Evidence and isolation.** Every derived edge has its typed/projection/equality evidence and context revision. Opening optional folds does not execute trusted source commands repeatedly, rewrite project files, or change toolchains. Stale handles are rejected.
8. **Regression and usability.** Native export, graph invariants, production rendering, and source/context preservation pass automated checks. A recorded reading review confirms that a reader can identify the objects, premise, return condition, and allowed witness dependencies. Automated tests alone do not satisfy this final criterion.

Pin the native inputs, expected semantic obligations, limits, and evaluation observations. Separate fixtures used during implementation from a small held-out set added after the contracts stabilize. A failed held-out case is evidence about a missing rule or abstraction boundary, not a reason to add its declaration name to a dispatch table.

## Migration and work boundaries

1. Add a failing native regression for the root-versus-field-law asymmetry. Define the smallest decomposition result that can satisfy it.
2. Wrap current native alias, field, and one-step definition operations behind that result, preserving their checks and bounds. Implement nested requests with identity and context reuse before adding more operations.
3. Adapt the existing semantic compiler to consume the shared graph. Retain the current reading and renderer as a client while removing duplicate interpretation paths incrementally.
4. Move scene/model discovery behind an explicit optional interface. Leave existing specialized lenses available as refinements with declared evidence.
5. Evaluate the vertical slice before expanding the grammar or rewriting the interface again. Keep performance and failure observations with the milestone.

Parallel work is useful once the shared contract is agreed: native decomposition, composition/rendering, and adversarial acceptance tests can have separate owners. One owner should integrate the contract changes. Avoid parallel teams extending recognizers against different interpretations of the same mathematical evidence.

Do not present this document as an implemented architecture, promise complete arbitrary-definition unfolding, or use the existing regression total as evidence of human understanding. The next milestone is complete only when the vertical slice works through the actual Lean context and the reading is useful.
