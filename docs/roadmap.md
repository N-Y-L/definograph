# Direction and acceptance criteria

The goal is general mathematical statement visualization. Named theorems can be regression inputs, but the implementation grows through reusable semantic and representation rules. Release 0.6 separates Lean extraction, semantic interpretation, guided reading, rendering, coverage assessment, and optional numerical exploration. It adds graph constraints and bounded automatic definition inspection to the existing sets, maps, dependent signatures, and metric vocabulary. It is not the completed general visualizer.

The primary experience is a visual sequence with its overview alongside. Abstract objects and relationships must work without coordinates. A new rule must preserve scope and identities, survive binder renaming, reject near-miss constructors and unaudited instances, and state what its drawing does not encode.

## Next shared foundations

1. **Restricted maps and local inverses.** Interpret typed maps with explicit source/target regions and inverse laws valid only there. One contract can support partial equivalences, local homeomorphisms, charts, and parts of bundle trivializations. Showing a source set alone is not sufficient.
2. **Fibers, projections, and sections.** Build on existing dependent signatures to relate a base, indexed fibers, a total space, and a projection. Continuity, linear structure, and local triviality must come from explicit mathematical structure. A dependent function must not silently become a smooth vector field.
3. **Linear operators and local differential conditions.** Add audited image/kernel/rank and derivative relationships, including mathematical operands currently hidden in implicit type arguments. Coordinate charts and local normal forms require their own contracts. This is groundwork toward constant-rank statements, not a claim that they are already visualized.
4. **Graphs beyond symbolic constraints.** Current adjacency, coloring, homomorphism, and embedding diagrams are reusable conditions. A complete finite graph view needs actual finite vertex/edge data. A planar representation needs an embedding contract; a graph embedding in the current vocabulary does not mean a planar embedding. The four-color theorem remains outside the implemented semantics.
5. **Shared scenes and representation choice.** Compose related conditions while retaining branch boundaries. Choose charts, slices, projections, or symbolic diagrams for the mathematical information they preserve. Distinguish an admissible witness strategy, a numerical sample, and a verified claim. Quantifiers must never disappear because a sample looks convincing.
6. **Evaluate semantic reach and visual usefulness separately.** Extend the [coverage corpus](coverage-corpus.md) with new mathematical vocabulary and adversarial formulations. Extraction success, interpreted constructors, faithfulness, and human understanding are different outcomes. The corpus already gives reproducible missing-constructor reports; those reports are not a percentage of all mathematics or a substitute for reader evaluation.
7. **Deepen prover integration.** The current VS Code controller and native InfoTree sidecar provide active project-context extraction. Actual VS Code GUI installation/use still needs validation. More pinned Lean versions, incremental extraction, and useful incomplete-term recovery remain future work. A Rocq adapter would need its own tested kernel-term and context handling before sharing these views.

## Definition inspection and upstream reuse

Automatic inspection now considers a few small, checked proposition definitions in the original elaboration context and chooses at most one useful expansion. It does not normalize arbitrary mathematics, synthesize semantics, or rerun project commands. Future inspection should earn its complexity by exposing a reusable construction while retaining the original statement and its provenance.

Reuse mathematical and rendering infrastructure when it provides a concrete capability. The graph iteration uses mathlib's actual coloring/map definitions. 3Blue1Brown/Manim and Penrose inform guided attention, identity, and domain/style separation; they are credited design references, not bundled runtimes. Current symbolic graph constraints need no additional graph-layout library. See [the graph iteration](graph-iteration.md) and [visual-method notes](visual-method.md).

## Questions where mathematical judgment matters

- Which information must remain visible when a representation cannot preserve every geometric feature?
- When does a symbolic diagram clarify a statement, and when does it hide the main mathematical obstacle?
- What makes two representations equivalent enough that the planner can substitute one automatically?

These are ongoing design and evaluation questions, not a requirement to choose a renderer manually for every statement. Tangent-bundle and vector-field meaning, local differential normal forms, and planar graph structure remain substantial missing vocabulary.
