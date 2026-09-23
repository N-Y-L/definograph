# Current implementation status

This is an early research implementation of a general mathematical statement
reader. It has a working Lean extraction and visual-reading pipeline, with
generic direct-record reflection as one useful foundation. It has **not** solved
automatic mathematical explanation, general definition decomposition, or the
selection of the best visual abstraction.

This page describes the underlying 0.7 implementation, retained in the 0.7.1
identity and repository cleanup. The
[architecture](architecture.md) maps current code; the [architecture decision](design/architecture-decision.md), the earlier [reset proposal](design/architecture-reset.md)
and [roadmap](roadmap.md) describe future work, not implemented behavior.

## What exists

| Capability | Implemented boundary |
| --- | --- |
| Checked Lean input | Restricted standalone proposition terms and imported declarations in a pinned environment; selected propositions from a trusted Lean editor buffer using actual built project dependencies |
| Typed and logical structure | Exact exported expression identities, binder order, quantifier dependencies, assumptions, branches, typed objects, and unresolved applications |
| Generic record reflection | Up to 16 direct fields with checked projections and instantiated types; supplementary field laws remain in the owning object's scope; unfamiliar record/field names need no recognizer |
| Checked definition views | Bounded type-head aliases and proposition previews, explicit bounded expansion, original names and expressions retained |
| Compositional readings | Maps, applications, dependent signatures, relationships, logical regions, a visual sequence, and a linked overview |
| Optional mathematical lenses | Sets, audited metric regions, graph constraints, and restricted maps within their documented contracts |
| Readable notation | Optional pinned LeanTeX output rendered locally through KaTeX; fallback preserves the original Lean expression |
| Editor package | A local VS Code controller and native context sidecar; configuration and identifiers retain the internal StatementLens name |

Record reflection is intentionally bounded: 16 direct fields, 120 expression
nodes per exported field expression/type, depth 24, and a 128 KiB optional
structure envelope. Parent subobjects remain explicit. More detail is in
[the reflection contract](structure-reflection.md).

## What remains unsolved

- **General decomposition.** Arbitrary value definitions, recursive inductive
  objects, and nested record structures do not yet have a general compositional
  inspection mechanism. Current bounded unfolding is not that mechanism.
- **Useful abstraction.** A correct inventory of fields or a diagram of logical
  syntax can still be a poor explanation. The current heuristic planner does
  not reliably find the mathematical abstraction that helps a reader. For
  example, the default ball reading exposes implementation fields of `ℝ` and
  `EuclideanSpace` before reaching the ball condition. Correct reflection can
  actively distract from the statement; automatic abstraction selection must
  address this.
- **Mathematical meaning.** A reflected record is not automatically recognized
  as a manifold, bundle, topological obstruction, normal form, or other useful
  concept. Unknown predicates remain unknown. The hairy-ball theorem, constant
  rank theorem, and four-color theorem are not complete supported readings.
- **Evaluation.** Automated fixtures establish bounded contracts and catch
  regressions. They do not establish that readers understand unfamiliar
  mathematics better, or measure a percentage of mathematics covered.
- **Complete boundary reporting.** Some early native heartbeat or oversized
  type exits retain the original object without a specific omission reason.
- **Broader integration.** Lean 4.28.0 is the only targeted version. Actual VS
  Code GUI installation and full extension-host use remain unverified. Native
  Windows, remote editor hosts, Rocq, incremental elaboration, and incomplete
  term recovery are not implemented or validated as general workflows.

The standalone browser cannot execute pasted structure declarations or import
arbitrary project modules. Use the trusted editor path for project-defined
objects. That sidecar re-elaborates the full active buffer, so Lean macros,
elaborators, initializers, and commands may execute project code. A selected
range does not sandbox the rest of the file. Existing source, configuration,
dependencies, and global toolchain settings must remain unchanged.

## Code entry points

| Boundary | Main files |
| --- | --- |
| Lean statement and definition export | [`Export.lean`](../lean/StatementLens/Export.lean), [`Worker.lean`](../lean/StatementLens/Worker.lean), [`Response.lean`](../lean/StatementLens/Response.lean) |
| Project-context extraction | [`Context.lean`](../lean/StatementLens/Context.lean), [`server/editor-context.ts`](../server/editor-context.ts), [`extension/src/extension.ts`](../extension/src/extension.ts) |
| Native setup and pins | [`scripts/lean-build.mjs`](../scripts/lean-build.mjs), [`lean/lean-toolchain`](../lean/lean-toolchain), [`lean/lake-manifest.json`](../lean/lake-manifest.json) |
| Exported expression types | [`src/core/types.ts`](../src/core/types.ts), [`src/protocol.ts`](../src/protocol.ts) |
| Record metadata validation and decomposition | [`src/decomposition/reflection.ts`](../src/decomposition/reflection.ts), [`compiler.ts`](../src/decomposition/compiler.ts), [`types.ts`](../src/decomposition/types.ts) |
| Semantic objects, identities, scopes, and rules | [`src/semantic/compiler.ts`](../src/semantic/compiler.ts), [`types.ts`](../src/semantic/types.ts), [`registry.ts`](../src/semantic/registry.ts), [`expression.ts`](../src/semantic/expression.ts) |
| Shared applications and typed constructions | [`src/semantic/application-flow.ts`](../src/semantic/application-flow.ts), [`src/constructions/model.ts`](../src/constructions/model.ts) |
| Reading sequence and representations | [`src/reading/compiler.ts`](../src/reading/compiler.ts), [`src/reading/types.ts`](../src/reading/types.ts), [`src/semantic/planner.ts`](../src/semantic/planner.ts) |
| Primary reader and reflected objects | [`src/visual/GuidedReading.tsx`](../src/visual/GuidedReading.tsx), [`StatementReadingView.tsx`](../src/visual/StatementReadingView.tsx), [`StructuralObjectFigure.tsx`](../src/decomposition/StructuralObjectFigure.tsx) |
| Interpretation frontier | [`src/semantic/coverage.ts`](../src/semantic/coverage.ts), [`inspection.ts`](../src/semantic/inspection.ts), [`src/visual/InterpretationCoverage.tsx`](../src/visual/InterpretationCoverage.tsx) |
| Optional lenses and sampling | [`src/set-constructions/`](../src/set-constructions/), [`src/graphs/`](../src/graphs/), [`src/restricted/`](../src/restricted/), [`src/statement-geometry/`](../src/statement-geometry/), [`src/core/scenario.ts`](../src/core/scenario.ts) |
| Transport and cancellation | [`server/http.ts`](../server/http.ts), [`session.ts`](../server/session.ts), [`worker.ts`](../server/worker.ts), [`src/editor/host.ts`](../src/editor/host.ts) |
| Independent fixtures | [`corpus/cases.ts`](../corpus/cases.ts), [`corpus/structures.ts`](../corpus/structures.ts), [`corpus/ProjectDependency.lean`](../corpus/ProjectDependency.lean) |

Data moves from native checked export to semantic objects/relations, then to the
reading and presentation layers. A renderer must not independently guess a
mathematical meaning from labels. Source locations originate in Lean's InfoTree;
derived diagrams and unfolded expressions are not automatically exact source
spans.

## Validation and evidence

The **0.7 baseline** reports **725 checks** on macOS arm64 with Lean 4.28.0.
That is a historical local result, not a claim that this count was rerun for the
publication cleanup or by GitHub CI, or that the objective is complete. See
[verification](verification.md) for suite counts, environment, browser
observations, and explicit gaps.

| Command | What it checks |
| --- | --- |
| `npm run build` | Strict TypeScript and production assets |
| `npm test` | Unit and renderer contracts, including checked fixtures; no live Lean worker |
| `npm run test:server` | Local HTTP/IPC, process lifecycle, cancellation, request boundaries, and mocked workers |
| `npm run check:extension` | Type checking, mocked controller/lifecycle checks, and local VSIX packaging; no editor installation |
| `npm run test:structure-export` | Actual native field reflection, type aliases, bounds, source isolation, and response trimming |
| `npm run test:decomposition` | Unfamiliar and renamed user records through native extraction, shared semantics, and the production reader |
| `npm run test:editor` | Native project-context extraction and unchanged fixture project files |
| `npm run test:corpus` | Hand-reviewed interpreted and unresolved relationships, scope, identities, and native binary provenance |
| `npm run check` | Build, unit/server tests, and all current native integration suites; requires a configured built native engine |

GitHub CI intentionally runs only build, unit, server, and extension checks. It
does not provision Lean or download mathlib. Native suites must run after an
explicit [isolated setup](lean-contract.md), with no concurrent worker rebuild.

The strongest existing generality check renames a complete unfamiliar record
and its fields while requiring the same primitive topology without additional
recognizers. That checks name independence, not the usefulness or completeness
of the explanation. Further progress needs both adversarial semantic cases and
direct evaluation with people reading unfamiliar statements.

## Handoff priorities

Use the [roadmap acceptance criteria](roadmap.md) to select a coherent next
foundation. Before expanding the recognizer catalogue, identify why existing
decomposition or composition cannot express the required relation. Preserve the
current useful extraction, scope, and identity machinery while evaluating
architectural replacements against the same independent fixtures.

Do not treat a brand cleanup, test count, example gallery, or successful render
as progress on automatic mathematical explanation by itself.
