# Documentation map

Start with [current status](status.md), then read [architecture](architecture.md)
and [roadmap](roadmap.md). This is a research implementation. Extracting a
definition, preserving its logic, and explaining its mathematical meaning are
different levels of progress.

## Current direction and contracts

| Document | Use it for |
| --- | --- |
| [Status](status.md) | What exists, principal gaps, code entry points, and validation commands |
| [Current architecture](architecture.md) | Existing implementation, code paths, and limitations |
| [Architecture decision](design/architecture-decision.md) | Adopted design: fundamental objects, decomposition, composition algebra, meaning/presentation boundary, first vertical slice and reading gates |
| [TNF specification](design/tnf-specification.md) | Round-1 design specification that the decision amends |
| [Architecture reset](design/architecture-reset.md) | Earlier proposal and 0.7 findings; superseded by the decision where they differ |
| [Roadmap](roadmap.md) | Next general capabilities and acceptance criteria |
| [Lean contract](lean-contract.md) | Standalone extraction, expression metadata, kernel checks, setup, and limits |
| [Editor integration](editor-integration.md) | Actual project context, source selection, execution trust, and host limits |
| [Structure reflection](structure-reflection.md) | Direct record fields, projected identities, scoped laws, and export budgets |
| [Semantic contract](semantic-contract.md) | Objects, relations, scope, recognition, and representation fidelity |
| [Guided reading](guided-reading.md) | Ordered constructions and retained logical context |
| [Coverage corpus](coverage-corpus.md) | Hand-reviewed expectations and what their results do not measure |
| [Verification](verification.md) | Dated local results, environments, and unverified workflows |
| [Contributing](../CONTRIBUTING.md) / [agent guide](../AGENTS.md) | Change workflow, isolation, and handoff rules |

Contract documents grew alongside the implementation and may retain historical
version labels. Use current code and the status page to distinguish implemented
behavior from proposals; the editor guide describes the current trusted-project path. A discrepancy is a
documentation issue to fix, not permission to invent support.

## Component details and references

- [Compositional sets](set-constructions.md)
- [Graph constraints](graph-semantics.md)
- [Restricted maps](restricted-semantics.md)
- [LeanTeX integration](leantex-integration.md)
- [Visual-method research and references](visual-method.md)
- [Third-party notices](../NOTICE)

These describe specific capabilities and sources. They are not a checklist of
mathematical names to exhaust.

## Historical iteration records

The following preserve the reasoning and acceptance evidence of earlier work.
They are not the current roadmap, and their claims are limited to the tested
iteration:

- [Statement-first review](statement-first-review.md)
- [Atlas iteration](atlas-iteration.md)
- [Graph iteration](graph-iteration.md)
- [Restricted-map iteration](restricted-iteration.md)
- [Generic decomposition iteration](decomposition-iteration.md)

Generated native corpus reports and local build logs remain in ignored
`.local/`; they are not reproducible source files and should not be committed.
