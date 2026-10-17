# Documentation map

One line per page. Extracting a definition, preserving its logic and explaining
its mathematical meaning are different levels of progress; the pages below say
which one they describe. A discrepancy between a page and the code is a
documentation bug to fix, not permission to invent support.

## Start here

- [Principles](principles.md): what Definograph is for and the standard every change is held to.
- [Status](status.md): what exists, what remains unsolved, code entry points, validation commands and known failing checks.
- [Architecture](architecture.md): the code that exists, its data flow, code map and trust boundaries.
- [Roadmap](roadmap.md): the next general capabilities and their acceptance gates.
- [Agent guide](../AGENTS.md) and [contributing](../CONTRIBUTING.md): invariants, the exact checks, how to add a test and the commit rules.

## Contracts

- [Lean contract](lean-contract.md): standalone extraction, expression metadata, kernel checks, setup and limits.
- [Editor integration](editor-integration.md): actual project context, source selection, execution trust and host limits.
- [Editor source snapshots](editor-source-snapshots.md): exact original and prepared frames, chosen occurrence checks, saved records and revision invalidation.
- [Editor definition exposure](editor-definition-exposure.md): one safe definition body, original and result readings, exact trace and separate typing and conversion outcomes.
- [Reader relations](reader-relations.md): prefix-specific provenance, formation, supply, whole-attempt outcomes and passive navigation.
- [Saved packet reader](packet-reader.md): separate packet import, exact syntax and readback, and unverified reported outcomes; not an editor-snapshot importer.
- [Structure reflection](structure-reflection.md): direct record fields, projected identities, scoped laws and export budgets.
- [Semantic contract](semantic-contract.md): objects, relations, scope, recognition and representation fidelity.
- [Guided reading](guided-reading.md): the statement skeleton, identity colour, the step sequence and the optional construction graph.
- [Coverage corpus](coverage-corpus.md): hand-reviewed expectations and what their results do not measure.
- [Axiom policy](../scripts/axiom-policy.json): the axioms the proved core may use, its listed exceptions and its certificate theorems; checked by `npm run test:axioms`.

## Components

- [Compositional sets](set-constructions.md): union, intersection, difference and complement, read compositionally.
- [Graph constraints](graph-semantics.md): canonical Mathlib simple-graph adjacency, colourings and graph maps.
- [Restricted maps](restricted-semantics.md): maps with inverse laws on designated regions, such as `PartialEquiv`.
- [LeanTeX integration](leantex-integration.md): the pinned LeanTeX printer behind the optional notation.

These describe specific capabilities. They are not a checklist of mathematical
names to exhaust.

## References

- [Reading research](reading-research.md): checked sources on recognizing structure in a drawing, misreading statements, proved statements that miss the intention, and existing tools.
- [Third-party notices](../NOTICE): reused code, runtime dependencies and design inspiration, kept apart.

## Records

- Design records: the [architecture decision](design/architecture-decision.md), the [TNF specification](design/tnf-specification.md) it amends and the earlier [architecture reset](design/architecture-reset.md). Each opens with a status line; none describes built code.
- [History](history/README.md): frozen records of earlier work, including the closed verification record. They describe the code of their day.

Generated native corpus reports and local build logs stay in the ignored
`.local/` directory; they are not reproducible source files and are not
committed.
