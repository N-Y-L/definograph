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
        optional scoped construction graph
```

The optional numerical path passes through `src/core/scenes.ts`, `src/semantic/planner.ts`, and `src/SceneView.tsx`. It is separate from the default statement reading but still shares types and compilation with it. There is no independent general-purpose decomposition service. The optional construction graph composes relations already supplied by the semantic reading; it does not discover or interpret new operations.

Saved composition packets use a separate exact input boundary:
`packets/packet.ts` validates bytes and attachment consistency,
`packets/syntax.ts` resolves contextual syntax, and `packets/semantic.ts` builds a
scoped presentation directly. The result feeds the same reading and rendering
modules. It does not pass through the legacy semantic compiler or acquire its
native-check markers. The explicit expression identity hook also governs shared
typed constructions; unsupported dependency structure stays unavailable. This
client and the reusable Lean checking module have separate responsibilities;
see [their integration boundary](packet-reader.md).

`packets/structure.ts` additionally builds a constructor drawing directly from
the uniquely associated captured expression. Its independent reader reconstructs
the input from node fields, ordered child roles and declaration homes.
`StructuralReading.tsx` displays those roles and homes, with marked folds and
attached exact-field inspectors. It remains usable where the specialized guided
view has a nested-constructor boundary; neither view adds typing or evidence.
The separate positional schema accepts a selected occurrence's exact telescope,
term and inferred type. It shares constructor rendering while resolving ambient
bound positions in their actual prefix scopes. Its independent reader recovers the
whole selected triple; `editor/source-occurrence-structure.ts` compares that result
with the occurrence before display. Named registries keep their original semantics.

The same exact presentation compiler also accepts a positional component directly
through `compilePositionalComponent`. It introduces actual context telescope entries
in prefix order and then the explicitly chosen term or type; it does not manufacture
packet receipts, free-variable identities or closing lambdas. Its neutral component
mode produces generic applications and parameter/definition introductions for the
shared guided reader. Presentation metadata separates surrounding context from the
selected root and prevents grouping them into a single introduction. Source links
resolve to actual context entries or expression fields. This semantic document is
partial; the independent full readback remains in the structural view.

Definition-head exposure extends this path with one explicit native operation.
The host retains the original occurrence and supplies its expected selected triple;
the worker obtains the definition from its initial environment after a fresh exact
selection match. A bounded structural substitution retains the body and complete
step trace. The client independently replays that step and reconstructs all nine
available check declarations. The result enters the positional reader as a genuine
term/carrier pair with its own source identity. Original receipts are never attached
to that derived expression. See [the exposure contract](editor-definition-exposure.md).

Explicit continuations extend that same exact-source path with exposure, focus,
direct field catalogues/projections, type inspection and one-layer logical
inspection. The host binds the retained capture and chosen prefix; the browser
reconstructs the steps and their receipt associations. `source-provenance.ts` and
`source-supplier.ts` derive pure readings of that prefix, preserving complete
scope, formation evidence and typing-declaration axioms. Whole-attempt outcomes
also retain later checks excluded from the prefix. Displaying these readings and
following section links starts no Lean process. Saved records do not acquire a
current editor session or native authority. This path remains distinct from the
legacy interpreted-expression compiler; general automatic decomposition and
explanatory usefulness are not established. See [reader relations](reader-relations.md)
and the [continuation contract](editor-definition-exposure.md#continue-inside-a-result).

The optional clause graph in `reading/scoped-graph.ts` consumes existing reading
relation groups. The source tree and presentation grouping provide its logical
frames; relation occurrences provide scope and ports. Globally shared object IDs
do not move an occurrence into the object's first-recorded scope. Measured layered
layout reserves node and port dimensions, with separate routes for explicit
arguments and results. `StatementReadingView` retains the existing clause-cue
authority and keeps guided reading as the default. See [the reading guide](guided-reading.md).

Plot-label notation is a separate frontend layer. `notation/math-display.ts`
converts bounded typed display nodes, exact supported expression constructors, and
explicit admitted-relation templates to TeX; `components/MathLabel.tsx` renders
local KaTeX HTML/MathML and participates in glyph measurement. Unsupported forms
retain source-label fallbacks. Typography supplies neither semantic identity nor
per-object native printing authority. Native Lean notation for inspected results
is separately associated with its captured result by `editor/source-presentation.ts`.

## Code map

| Responsibility | Implementation | Important boundary |
|---|---|---|
| Standalone elaboration | `lean/StatementLens/Worker.lean` | Fixed imports and restricted declarative input; not arbitrary project syntax |
| Project-context extraction | `lean/StatementLens/Context.lean`, `server/editor-context.ts` | Trusted source is elaborated in a separate process; selected terms retain their local context |
| Exact editor source capture | `lean/StatementLens/SourceSnapshot.lean`, `src/editor/source-snapshot.ts` | Original and prepared frames, exact binding/receipt validation, independent raw readback and explicit failure states; no portable authority |
| Chosen source occurrences | `src/editor/source-occurrence.ts`, `SourceSnapshot.captureOccurrence` | Fresh exact parent matching, positional dependent homes and six separate typing outcomes; original paths and earlier process receipts are not reused |
| Occurrence guided reading | `src/editor/source-occurrence-reading.ts`, `SourceOccurrenceGuidedReading.tsx`, `packets/semantic.ts` | Neutral context and ordered applications; selected term/type targets stay separate and source-linked, with structural fallback |
| Definition-head exposure | `SourceSnapshot.captureHeadExposure`, `src/editor/source-head-exposure.ts`, `head-exposure-replay.ts`, `SourceHeadExposureReading.tsx` | One initial-environment safe body, exact syntactic replay, unchanged positional home and separate result/conversion outcomes |
| Exact continuation histories | `src/editor/source-decomposition.ts`, `extension/src/continuation.ts`, `SourceDecompositionReading.tsx` | Exact capture/prefix replay, bounded v1/v2/v3 operations and separately associated outcomes |
| Prefix provenance and supply | `src/editor/source-provenance.ts`, `source-supplier.ts`, `SourceProvenanceReading.tsx`, `SourceSupplierReading.tsx` | Pure derived readings; full scope and axiom audit, no invented proof or current-source authority |
| Typed export | `lean/StatementLens/Export.lean`, `src/core/types.ts` | Logical trees and expression ASTs; selected metadata and optional bounded views |
| Response bounds | `lean/StatementLens/Response.lean`, `server/protocol.ts` | Optional views may be dropped to preserve the mandatory result |
| Identity and scoped interpretation | `src/semantic/compiler.ts`, `expression.ts`, `types.ts` | Exact expression identity and scopes; domain-specific relation variants remain in the shared schema |
| Direct-record decomposition | `src/decomposition/reflection.ts`, `compiler.ts` | Checked field projections; supplementary laws are separate semantic documents with inherited identities |
| Definition inspection | `src/semantic/inspection.ts` | Chooses at most one of a few native proposition previews; not a recursive engine |
| Reading order and logical context | `src/reading/` | Binder roles, premises, branches, negation, expression dependencies, and guided cues |
| Scoped construction graph | `src/reading/scoped-graph.ts`, `src/visual/ScopedStatementGraph.tsx`, `scoped-graph-layout.ts`, `scoped-graph-math.ts` | Optional source-scoped operation graph; preserves existing ports and logical frames without new extraction or interpretation |
| Typed plot-label presentation | `src/notation/math-display.ts`, `src/components/MathLabel.tsx`, `math-label-measure.ts`, `use-diagram-text.ts` | Local bounded KaTeX and measured glyphs; exact source identities and source fallbacks remain separate |
| Native inspected-result presentation | `src/editor/source-presentation.ts`, `SourceResultPresentation.tsx`, `SourceSnapshot.lean` | Bounded native Lean notation associated with the recorded result; optional display text is not an additional check |
| Abstract rendering | `src/visual/StatementReadingView.tsx`, `src/constructions/`, `src/decomposition/` | Typed maps, families, fields, and laws; dispatch and composition also contain specialized cases |
| Optional mathematical lenses | `src/set-constructions/`, `src/graphs/`, `src/restricted/`, `src/statement-geometry/` | Audited contracts for selected operations; no theorem-title dispatch |
| Numerical models | `src/core/geometry.ts`, `scenario.ts`, `scenes.ts`, `src/SceneView.tsx` | Audited operations and metrics; finite samples do not establish quantified statements |
| Readable notation | `lean/StatementLens/ReadableMath.lean`, `src/notation/` | LeanTeX and KaTeX output is presentation only |
| Editor host and browser bridge | `extension/`, `src/editor/`, `src/protocol.ts` | Versioned selections, invalidation, and source reveal; automated macOS development-host and installed-extension journeys cover inspection, cancellation and refusal recovery |
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

Lean and mathlib supply the formal environment. LeanTeX supplies the isolated expression-to-LaTeX printer; KaTeX renders it. React and CodeMirror provide interface infrastructure. [NOTICE](../NOTICE) and [the LeanTeX record](leantex-integration.md) track attribution. 3Blue1Brown/Manim and Penrose are design references, not bundled visualization engines or copied scenes. The optional graph uses a local measured layered layout; [ELK Layered](https://eclipse.dev/elk/reference/algorithms/org-eclipse-elk-layered.html) and its [explicit hierarchy/port model](https://eclipse.dev/elk/documentation/tooldevelopers/graphdatastructure.html) are design references, with no ELK implementation or package reused.

Rocq support is not implemented. The existing semantic document is independent of React, but still imports Lean-shaped expressions and includes domain-specific variants. A genuinely prover-neutral contract is proposed, not complete.
