# Direction and acceptance criteria

The goal is general mathematical statement visualization. Named theorems can be regression inputs, but the implementation should grow through reusable semantic and representation rules.

The current 0.3 foundation separates Lean extraction, semantic interpretation, complete statement reading, rendering, and optional numerical exploration. The primary experience is a visual sequence with its overview alongside. Abstract objects and maps do not require coordinates; a statement must be understandable before the user changes any numerical value. It also permits deeper inspection of definitions. It is not the completed universal visualizer.

## Next foundations

1. **An active Lean document adapter.** Read elaborated expressions and local context through InfoTree/RPC in the user's chosen project, without rewriting its environment. Preserve document versions, source provenance, diagnostics, and partial elaboration states. The current fixed-environment worker remains a reproducible standalone mode.
2. **Composable spatial constraints.** Unite related geometric conditions in one scene, rather than only giving their objects shared identities. Rules must retain logical branches, quantify which mathematical information a representation preserves, and distinguish projections, sections, charts, and symbolic encodings.
3. **Witness dependencies and families.** Make the permitted dependence of a witness on earlier choices visible as a symbolic family. Separate a proposed strategy, a sampled response, and a formally checked claim. Never use numerical success to silently discharge a universal quantifier.
4. **Richer reusable domains.** Add finite graphs and coloring constraints, tangent spaces and vector fields, products, quotients, fibers, charts, and commutative diagrams by construction. Each new rule needs positive and near-miss tests and must work under renamed binders and reordered equivalent contexts.
5. **Automatic planning with explicit quality criteria.** Score information preserved, ambiguity introduced, shared relationships, cognitive load, and layout stability. A viewpoint should be chosen for a mathematical reason; a difficult dimension alone is not a reason to drop the statement.
6. **Corpus-level evaluation.** Measure coverage on diverse Lean statements, abstraction changes, custom instances, nested quantifiers, dependent types, and unusually large inputs. Separate extraction coverage, semantic recognition, visual usefulness, and correctness failures. Future Rocq extraction can reuse those contracts and renderers after its own kernel-term adapter is tested.

## Questions where mathematical judgment matters

- Which information must remain visible when a representation cannot preserve every geometric feature?
- When does a symbolic diagram clarify a statement, and when does it hide the main mathematical obstacle?
- What makes two representations equivalent enough that the planner can substitute one automatically?

These are design and evaluation questions for ongoing development, not prompts to manually choose a renderer for every statement.
