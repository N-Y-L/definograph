# Roadmap

The objective is to help a reader understand mathematical statements from their formal definitions and context. The primary presentation is a visual sequence with a logical overview alongside it. Interaction and numerical examples are secondary. Abstract mathematics must not require coordinates.

The current program is a research prototype. Direct record reflection, checked aliases, scoped reading, and a few specialized views are implemented. The general architecture is not. The next work should establish a reusable decomposition path and evaluate its explanatory value before expanding the catalogue of mathematical lenses. See [the architecture decision](design/architecture-decision.md) for the adopted design and its first vertical slice, [the architecture reset](design/architecture-reset.md) for the earlier contracts, and [the code map](architecture.md) for the baseline.

## 0. Establish the baseline and regression boundary

**Deliver:** a reproducible local setup, explicit known limitations, preserved source/context identities, and a small benchmark with expected *meaning*, not just accepted output shapes.

**Gate:** reproduce existing checks, record toolchain and dependency versions, and retain failures as failures. Distinguish successful extraction, structural reading, justified mathematical interpretation, numerical realization, and human comprehension. An unsupported fixture passing its expected fallback is not a fully visualized statement.

Keep the present renderer usable while changing its inputs. No large file move or broad rewrite is a milestone by itself. Existing tests are regression evidence; their count is not the progress metric.

## 1. One checked decomposition path for objects and laws

**Deliver:** a bounded, demand-driven decomposition graph that can inspect a primary term, a field's type, a nested record, or a supplementary law using the same operation and evidence contract. Preserve the original named expression as a folded node. Share repeated terms and expose fold reasons.

Start with a Lean implementation and a small prover-neutral result schema. Do not add a second prover yet. Initial operations are alias/definition exposure, direct field inspection, and logical decomposition. Reuse existing checks; replace separate preview and reflection routing incrementally.

**Gate:** the vertical slice in [the reset proposal](design/architecture-reset.md#first-vertical-slice) passes. It must include unseen and renamed user definitions, a nested record, a law hidden behind ordinary definitions, an existing library structure, alternating quantifiers, opaque boundaries, repeated subterms, and budget termination. The same supported law must read the same way at the root and inside a record. No fixture-specific recognizer may be added to pass the gate.

## 2. Compose an explanatory view from the shared representation

**Deliver:** reusable introduction, application, constraint, dependent-family, and logical-frame operations. Render directly from their typed ports and scopes. Add a trace showing which source facts each visual component encodes.

Use deterministic candidate selection with explicit admissibility rules before any readability score. Open definitions only when they reveal relevant relationships at an acceptable complexity. Preserve a folded overview and let the reader inspect what was omitted. Do not replace a useful abstraction with a full record inventory merely because its fields are available.

**Gate:** the milestone 1 fixtures remain useful with specialized lenses disabled. Renaming symbols preserves representation topology; changing quantifier order or branch scope changes the relevant dependencies. A candidate that hides an unsatisfied constraint cannot win by being smaller. The selection trace explains its choice, and fixed inputs give reproducible selections.

Conduct a small, recorded reading evaluation: can readers correctly identify the objects, the conclusion, required assumptions, and witness dependencies? Compare with the original formal statement and a readable typeset version. Report errors and confusion. Do not infer comprehension from screenshots or renderer tests.

## 3. Recursive, inductive, and dependent definitions

**Deliver:** finite descriptions of constructors, alternatives, indexed families, and recursive references. Expose one useful layer on demand; never enumerate an infinite type or normalize an arbitrary program merely to obtain a picture. Preserve constructor conditions and branch-specific indices.

**Gate:** unseen inductive and mutually referenced examples terminate with explicit fold reasons; dependent indices remain attached to the correct branch. Repeated references share semantic nodes without merging occurrences from incompatible scopes. Cache invalidation includes the actual environment and selected context. Unsupported elimination principles remain explicit rather than receiving guessed semantics.

This milestone may require revising the proposed IR. Keep the revision evidence and migration small; do not claim that one minimal vocabulary has been proved sufficient for all mathematics.

## 4. Certified abstraction rules and optional models

**Deliver:** reusable abstraction rules over exposed structure, with explicit premises and evidence. For example, display a map with a return law because the law is available, regardless of field spelling. A theorem-backed replacement must carry its checked application and hypotheses; a visual resemblance is insufficient.

Introduce optional extensional models through a separate interface: concrete finite graphs, coordinate geometry, numerical functions, or supplied witnesses. Each model states its relation to the abstract object and any approximation or omitted information. A chosen realization must not alter the source statement.

**Gate:** mathematically different instances with similar syntax remain distinct; every stronger interpretation has visible evidence. Removing a required premise invalidates the abstraction. Concrete samples do not discharge universal conditions or create existential witnesses. High-dimensional views explain their preserved information without implying that a slice is the ambient object.

## 5. Serious mathematical stress tests

Use related families of statements rather than a single polished theorem demonstration:

- Fibers, sections, local charts, and bundle maps test dependency, locality, and composition.
- Tangent fields and nonvanishing conditions test whether geometric structure and quantified obstructions become understandable; a dependent function alone is not a smooth vector field.
- Linear maps, derivatives, and constant-rank hypotheses test algebraic structure and local normal forms; two arrows are not a visualization of the constant-rank theorem.
- Coloring constraints and planar embeddings test the distinction between abstract relations, finite data, and geometric assumptions; a coloring diagram is not the four-color theorem.

**Gate:** explain new members of each family from shared rules, report the remaining mathematical frontier, and repeat the reading evaluation. Hairy-ball, constant-rank, and four-color statements are ambitious tests of generality, not renderer dispatch keys. No release should claim these are supported merely because some component objects are drawn.

## 6. Reliable editor use and broader environments

**Deliver:** verified installation and use in an actual Lean editor host, incremental context reuse, cancellation, stale-result rejection, and a supported toolchain policy. Keep project dependencies and configuration unchanged unless explicitly requested.

**Gate:** a user can select a statement in a real project, inspect nested definitions, edit the buffer, and obtain an updated reading without stale context or unintended project writes. Measure latency and memory on declared hardware. Native Windows and additional Lean versions need their own checks.

A Rocq adapter becomes appropriate only after the shared representation handles the Lean milestone fixtures without depending on Lean-specific rendering logic. It will need its own checked treatment of contexts, universes, coercions, modules, and inductive definitions.

## Guidance for later agents

Start at the first unmet gate. Read the design proposal and the relevant current module before editing. Build one complete path from real Lean output through composition to a usable reading; avoid adding disconnected infrastructure or another named-object showcase. Delegate independent validation or bounded modules, with one owner for the contract they share.

Record what is implemented, what remains proposed, and what the checks actually establish. Update the known limitations when a boundary moves. Ask the project owner about mathematical usefulness and acceptable information loss when examples expose a real tradeoff; routine technical defaults do not need a decision.
