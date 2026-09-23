# Current implementation

Definograph is an experimental Lean statement reader. The current code can preserve logical context, expose direct structure fields, and compose several typed relationships. It does **not** yet implement the general decomposition and representation architecture needed for the project's objective.

Read [the architecture decision](design/architecture-decision.md) for the adopted design (it amends the [TNF specification](design/tnf-specification.md) and supersedes [the architecture reset](design/architecture-reset.md) where they differ) and [the roadmap](roadmap.md) for delivery gates. This page describes the code that exists. Older iteration documents are historical records, not evidence that the general problem is solved. `StatementLens`, `statementLens`, and related protocol/module identifiers remain internal compatibility names.

## Existing data flow

```text
Fixed-environment input       Trusted Lean editor selection
        │                              │
        Worker.lean                Context.lean / InfoTree
        └────────── Export.lean ────────┘
                  │
        Analysis: expressions, logical tree,
        optional fields, aliases, definition previews
                  │
        semantic/compiler.ts
        identities, scopes, relations, unknown portions
                  │
        reading/compiler.ts + reading/cues.ts
        sequence and logical overview
                  │
        visual/StatementReadingView.tsx
        generic constructions + specialized figures
```

The optional numerical path passes through `src/core/scenes.ts`, `src/semantic/planner.ts`, and `src/SceneView.tsx`. It is separate from the default statement reading but still shares types and compilation with it. There is no independent general-purpose decomposition service or graph yet.

## Code map

| Responsibility | Implementation | Important boundary |
|---|---|---|
| Standalone elaboration | `lean/StatementLens/Worker.lean` | Fixed imports and restricted declarative input; not arbitrary project syntax |
| Project-context extraction | `lean/StatementLens/Context.lean`, `server/editor-context.ts` | Trusted source is elaborated in a separate process; selected terms retain their local context |
| Typed export | `lean/StatementLens/Export.lean`, `src/core/types.ts` | Logical trees and expression ASTs; selected metadata and optional bounded views |
| Response bounds | `lean/StatementLens/Response.lean`, `server/protocol.ts` | Optional views may be dropped to preserve the mandatory result |
| Identity and scoped interpretation | `src/semantic/compiler.ts`, `expression.ts`, `types.ts` | Exact expression identity and scopes; domain-specific relation variants remain in the shared schema |
| Direct-record decomposition | `src/decomposition/reflection.ts`, `compiler.ts` | Checked field projections; supplementary laws are separate semantic documents with inherited identities |
| Definition inspection | `src/semantic/inspection.ts` | Chooses at most one of a few native proposition previews; not a recursive engine |
| Reading order and logical context | `src/reading/` | Binder roles, premises, branches, negation, expression dependencies, and guided cues |
| Abstract rendering | `src/visual/StatementReadingView.tsx`, `src/constructions/`, `src/decomposition/` | Typed maps, families, fields, and laws; dispatch and composition also contain specialized cases |
| Optional mathematical lenses | `src/set-constructions/`, `src/graphs/`, `src/restricted/`, `src/statement-geometry/` | Audited contracts for selected operations; no theorem-title dispatch |
| Numerical models | `src/core/geometry.ts`, `scenario.ts`, `scenes.ts`, `src/SceneView.tsx` | Audited operations and metrics; finite samples do not establish quantified statements |
| Readable notation | `lean/StatementLens/ReadableMath.lean`, `src/notation/` | LeanTeX and KaTeX output is presentation only |
| Editor host and browser bridge | `extension/`, `src/editor/`, `src/protocol.ts` | Versioned selections, invalidation, and source reveal; an actual VS Code GUI workflow remains unverified |
| Regression fixtures | `corpus/`, `scripts/*integration.ts`, colocated tests | Extraction, scope, semantics, and renderer checks; not a measure of mathematical understanding |

## What generic decomposition currently means

The exporter reads Lean's direct structure metadata for a bound value. It constructs the actual field projections, infers and checks their types, and exports their declaration order and exact earlier-field dependencies. Proposition-valued fields also get logical trees. Names are labels, so fresh and renamed records can reuse ordinary maps, sets, applications, and comparisons.

The optional record envelope permits at most 16 direct fields, 120 expression nodes and depth 24 per field expression/type, and 128 KiB per binder. Type-head aliases are limited to two checked steps. Parent subobjects remain fields. Supplementary law trees disable further structure reflection. See [the reflection contract](structure-reflection.md).

Proposition inspection is a different mechanism: the native exporter considers at most three small logical-head definitions, prepares one-step previews, and the browser may choose one preview that reduces unknown regions. Those previews are attached to the primary analysis. Reflected laws do not receive the same preview pipeline. In particular, a top-level `Function.LeftInverse` can unfold while the same predicate inside an `Equiv` field law stays folded. Unifying these paths is the first architecture milestone.

## Trust and meaning

Lean checks that submitted expressions have the expected types and that accepted expansions preserve definitional equality. This does not prove an arbitrary submitted proposition. A record law is available from its owning value inside the relevant context; it is not a global theorem. Unknown predicates retain their expressions and enclosing logic.

The browser validates bounded export shapes and uses the native worker's check markers. It does not independently check Lean certificates. TypeScript interpretation, representation selection, and rendering are tested code, not formally verified transformations. A schematic view supplies no unstated coordinates, cardinality, geometric realization, or witness.

Editor extraction accepts trusted project source that may execute elaborators or commands. The worker process is not a security sandbox. It reads built dependencies without rewriting the user's project or changing its toolchain. Standalone browser requests expose a narrower input interface. See [editor integration](editor-integration.md) and [verification](verification.md).

## Reuse

Lean and mathlib supply the formal environment. LeanTeX supplies the isolated expression-to-LaTeX printer; KaTeX renders it. React and CodeMirror provide interface infrastructure. [NOTICE](../NOTICE) and [the LeanTeX record](leantex-integration.md) track attribution. 3Blue1Brown/Manim and Penrose are design references, not bundled visualization engines or copied scenes.

Rocq support is not implemented. The existing semantic document is independent of React, but still imports Lean-shaped expressions and includes domain-specific variants. A genuinely prover-neutral contract is proposed, not complete.
