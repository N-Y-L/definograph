# Direction and acceptance criteria

The goal is general mathematical statement visualization through deterministic decomposition and a small shared vocabulary of visual primitives. Mathematical objects are assembled from definitions and conditions; the implementation should expose and compose those ingredients instead of requiring a dedicated renderer for every library object. Optional adapters can provide concise views of familiar contracts, but an expanding name catalogue is not the general solution.

The implemented foundation includes direct Lean structure-field reflection, scoped law trees, checked type-head aliases, bounded proposition unfolding, shared expression identities, typed maps and data, logical composition, and explicit unknown regions. Existing graph, set, metric, and restricted-map views complement this foundation. It is not the completed general visualizer.

The primary experience remains a visual sequence with its overview alongside. Abstract objects and relationships must work without coordinates. Examples or samples cannot supply unstated assumptions or erase quantifiers.

## Next general foundations

1. **Extend checked decomposition beyond direct records.** Current reflection reads direct fields and laws, follows at most two type-head aliases, and leaves inherited subobjects explicit. Develop bounded recursive inspection of nested records, arbitrary definition values, and inductive data while preserving exact identities and original names. Every stop must retain the uninterpreted expression and a reason; unrestricted unfolding is not an acceptable substitute.
2. **Compose shared primitives into useful explanations.** Reuse types, elements, maps, dependent families, sets, relations, quantifiers, and conditional laws. Intermediate expressions must be shared across applications and comparisons. Select useful levels of abstraction so a large definition does not become an unreadable field inventory. A diagram of a record's laws must remain conditional on its owning object and lexical context.
3. **Expose the mathematical frontier.** Distinguish a definition that was read, a law whose logic was decomposed, a relation with a visual meaning, and a condition whose mathematical meaning remains opaque. Make partial progress inspectable without suggesting complete understanding. Recognize equivalent exposed structures through checked expressions, not field-name resemblance.
4. **Evaluate unseen definitions and statement reading.** Use fresh project-defined records, renamed fields, dependent carriers, opaque predicates, nested scopes, limits, and malformed metadata. These tests must work without changing the recognizer table. Assess visual usefulness separately from extraction and compositional correctness; no fixed corpus provides a percentage of all mathematics.
5. **Choose representations automatically while preserving information.** Related conditions should compose without crossing branch boundaries. A coordinate model, projection, slice, graph, or abstract relationship view must say which information it encodes. No numerical sample proves a quantifier. The present planner is a bounded heuristic, not a verified optimum.
6. **Deepen prover integration.** The VS Code controller and native InfoTree sidecar use active project context. Actual VS Code GUI installation/use still needs validation. More Lean versions, incremental extraction, and useful incomplete-term recovery remain future work. A Rocq adapter needs its own tested term, structure, and context export before sharing the reader.

## Mathematical stress tests

Fibers, projections, and sections test whether dependent families and maps compose into understandable relationships. Tangent bundles and vector fields additionally require their actual geometric and algebraic conditions; a dependent function alone is not a smooth field.

Linear maps, derivatives, and rank conditions test whether shared algebraic structure and local hypotheses expose a useful statement reading. Constant-rank normal forms involve more than drawing two arrows and an equality. Restricted equivalences and open partial homeomorphisms now have a concise audited view, but this does not implement arbitrary charts, bundle trivializations, or the constant-rank theorem.

Graph coloring tests relations and quantifier-dependent assignments. Current symbolic constraints do not construct a finite graph or establish planarity. A complete graph view needs actual finite data; a planar view needs an appropriate embedding. The four-color theorem remains an unfinished case, as does the hairy-ball theorem.

These are probes of reusable foundations, not requests to hardcode a presentation of each named theorem.

## Definition unfolding and upstream reuse

The existing automatic inspection considers a few small proposition definitions in the original elaboration context and chooses at most one useful checked expansion. Type aliases and direct structure fields now provide additional general decomposition. These mechanisms preserve the original statement, use bounded work, and do not replay source commands. Recursive value and inductive decomposition remain future work.

Reuse checked mathematical and rendering infrastructure when it supplies a concrete capability. Lean's structure metadata and projection APIs directly support generic reflection. Mathlib supplies actual mathematical definitions. 3Blue1Brown/Manim and Penrose inform ordered constructions, persistent identity, and separation of relationships from presentation; they are credited design references rather than bundled runtimes. See [the architecture](architecture.md), [structure reflection](structure-reflection.md), and [visual-method notes](visual-method.md).

## Decisions that benefit from mathematical judgment

- What level of definition detail makes a statement comprehensible without hiding its main mathematical content?
- Which relationships must remain visible when a representation cannot preserve every geometric feature?
- When do two checked decompositions support the same visual abstraction, and what evidence justifies that substitution?

These guide evaluation and architecture. They should not require the user to choose a renderer manually for each statement.
