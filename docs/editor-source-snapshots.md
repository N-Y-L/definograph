# Exact source snapshots in the Lean editor

After **Definograph: Visualize Selection**, open **Source data**. The reader keeps the selected Lean expression and its local declarations independently of the guided diagram. A proof term remains a proof term in this record, even when the guided reader displays its proposition type. If no proposition is eligible, the smallest available elaborated term can still provide source data while the guided reader reports its selection boundary.

| Section | Contents |
| --- | --- |
| Original data | The selected `TermInfo.expr`, original local declarations, and a type inferred in that captured context |
| Checker input | A separately prepared frame, with explicit universe parameters used for checking |
| Expected type | The elaborator's optional expectation; never a replacement for failed type inference |
| Check outcomes | Every retained declaration submitted to the kernel, its resource bound and outcome, and its axiom audit |

Original and prepared frames use `definograph.raw-frame.v1`, with exact natural-number profile 2. Metadata, names, declaration indices, genuine local definitions and ignored stored values remain explicit. Raw drawing readback reconstructs constructor data; it does not establish scope or typing.

## Capture and preparation

The adapter uses the selected InfoTree's environment, metavariable context, name generator and local context. Original capture, prepared capture and the existing guided exporter run separately from that saved context. The original and prepared branches each infer the original expression's type before modifying declarations. Their inferred types must match as exact raw data. The prepared branch keeps its own inference state; passing an inferred expression alone between runs could leave its newly created metavariables without their declarations.

Preparation applies Lean's `instantiateMVars` to the selected expression, the inferred type, local types and genuine defining values. It preserves declaration identities and leaves `nondep = true` stored values unchanged. There is no explicit zeta rewrite of the retained expression/local context, metadata erasure, proof-to-type replacement or independent solving pass. Type inference may reduce internally and introduce assignments or constraints; instantiation may normalize assignment maps, expand delayed assignments and perform associated beta reduction. Those effects remain inside the isolated run. The record names these operations; it does not prove equivalence of the original and prepared frames.

The checking universe parameters are exact, deduplicated names collected from prepared semantic fields in chronological local-declaration order, then the term and inferred type, including constant universe instances. Ignored stored values do not contribute. This is an explicit checking context, not recovery of every unused universe parameter in the original declaration.

The pinned `captureNamedSource` API checks the prepared named context and component. Semantic metadata or unresolved metavariables can remain outside its strict admission profile while still being available as raw data. Placeholder-containing terms, types and genuine defining values are marked unsupported before checking. Ignored stored values are excluded from that semantic placeholder guard. Kernel acceptance is a typing outcome, not evidence that a proposition is true or a diagram is correct. Axiom audits remain visible.

## Failures, limits and identity

The `definograph.source-snapshot.v1` attachment has independent expected-type, original, prepared and checking states. Failed inference never fabricates a complete frame or uses the expected type as a fallback. A raw serialization failure can coexist with independently retainable prepared data. A guided export failure leaves the snapshot available. Failure before a snapshot can be formed produces a bounded `sourceSnapshotUnavailable` reason while guided export proceeds independently.

For unavailable checking, `attempted` means that the source capture API was invoked. It does not mean any kernel callback ran. Captured records retain the actual receipt sequence, including rejected and unknown outcomes or receipts preceding an action error. An output limit omits the entire checking section with an explicit reason; it never truncates receipts into apparent success.

The editor profile uses these limits:

| Resource | Limit |
| --- | --- |
| Source buffer / process deadline | 512 KiB / 45 seconds |
| Each original or prepared raw frame | 256 KiB encoded output |
| Expected-type raw expression | 128 KiB encoded output |
| Raw encoding | 20,000 JSON nodes, depth 96, 128 KiB UTF-8 text, 10,000 digits per natural |
| Context admitted to checking | 128 declarations |
| Each kernel check | 200,000 heartbeats |
| Complete checking record / snapshot | 768 KiB / 1.5 MiB |
| Complete checking record nesting | 120 levels; deeper records are explicitly omitted before the snapshot's 128-level parser boundary |
| Guided response / combined transport | 2 MiB / 4 MiB |

The host associates a result with its actual source hash, generated capture identifier, native executable and package fingerprints, document revision and selection. It verifies the executable/configuration before and after execution. This identifies one local process snapshot. Project library paths are recorded, but the complete imported environment is not hashed and later compiled/external dependency changes are not continuously watched. Document edits, selection changes, edits in open Lean buffers in the same workspace, configuration changes and cancellation invalidate the editor attachment.

**Save source snapshot** exports an explicitly unverified saved record. Serialized hashes or recorded origin fields cannot recreate a live editor session. This path does not construct composition banks, issue a Supervisor packet or certify arbitrary source transformations.

## Check a chosen occurrence

In **Checker input**, choose a constructor inside the prepared term and press **Check chosen occurrence**. The reader reruns the current buffer and compares its selected range, exact prepared frame and universe parameters with the displayed snapshot. If they differ, extraction does not begin. Original-data paths are separate: instantiation can change the expression's constructor structure, so an original path is not reused in the prepared term.

Selection supports the whole term and ordinary application, lambda, product, let and projection children, up to 64 path steps. The prepared frame's separate source-type field, external local declarations, metadata and derived-view positions remain inspection data. A body selection includes the binder it enters; a domain or defining-value selection does not. Newly opened binders retain their exact dependent context and positional references; repeated names do not identify variables. An owned source `have` retains its defining value and original `nondep` flag, while an external opaque local declaration remains an input without a defining equation.

The separate `definograph.source-occurrence.v1` record retains the exact selected context, term and inferred type. A completed extraction has six typing outcomes: supplied-source context/component, inferred-root context/component, and selected context/component. A rejected root remains visible even if its selected child is accepted. An invalid path can retain the two source outcomes before reporting an action error. A returned result or completed action does not establish that all checks accepted.

**Guided reading** presents the selected candidate through the shared reading sequence and overview. **Selected term** and **Inferred type** are separate targets; switching them resets the display focus without requesting another native capture. A proof term is never automatically replaced by the proposition it proves on this occurrence route. Surrounding context entries remain separate from binders introduced inside the displayed expression, including unused entries and local definitions with their original defining values.

This presentation is deliberately neutral. Function applications retain their head and every argument in source order, sharing repeated intermediate objects by exact scoped identity. Dependent function type syntax is shown through parameters and domains, without inferring that it is a universally quantified proposition. Even `And` and `Eq` applications remain generic applications here. No specialized mathematical property, numerical model, type metadata or extra kernel evidence is invented. Unsupported nested binding, let and projection expressions retain an explicit boundary and exact source association.

Select a reading step or object to inspect its actual expression constructor or context entry, source path and preceding scope. The guided document is a partial presentation; the separate **Structure** view provides the complete constructor reconstruction. Its available source data and all typing outcomes remain accessible when the guided compiler reaches a limit. After full positional validation, the guided compiler additionally caps traversal at 30,000 visits and expression depth 128.

The selected candidate also has a structural view of its complete surrounding context, term and inferred type. Context declarations appear oldest first; each declaration's type and defining value use only the preceding declarations. Term and type share the complete context, while their own internal binders have separate identities. Reference buttons locate the declaration addressed by each bound position, so repeated printed names remain distinct. Unused context entries are retained. Exact-field inspectors and marked folds expose the remaining constructor data.

The view uses `definograph.structure.positional.v1`, with separate build and read APIs. Its reader reconstructs the exact context telescope, arity, term and type from declaration fields, ordered constructor edges and scopes. The editor compares this reconstruction with the selected candidate before displaying it. No original Lean free-variable identity is invented for a context position. The existing named-context drawing format is unchanged and continues to resolve free-variable identities separately.

Every positional `letE` retains its defining value and original flag, including an owned `have` with `nondep = true`. An original external opaque declaration has already become a context input and is displayed as such; its ignored stored value remains in the original-data inspector. The view consumes those recorded roles directly.

Structural readback does not establish typing, authenticate the source or imply acceptance of any kernel outcome. An available candidate can be drawn even when source or root checks failed. A rendering limit produces an explicit unavailable message while the exact data and check outcomes remain accessible. The structural budget is 100,000 data/work nodes, depth 256, two million text characters and 256 context declarations, including validation of the serialized drawing; these bounds are independent of native capture bounds.

Each click starts a new local process with its own capture identifier and outcomes. The parent capture identifier records the request association; matching syntax does not prove that imported definitions are unchanged. The extension accepts clicks only from its current retained capture and invalidates them on the same document, selection, configuration, dependency-buffer and cancellation events as ordinary analysis.

The complete occurrence attachment is limited to 768 KiB and 120 JSON levels. If it or the combined 4 MiB response would exceed a bound, the complete occurrence checking record is omitted with an explicit reason. Source data and guided output keep their independent bounds. Saving a snapshot with occurrence outcomes produces saved-record version 2, still explicitly unverified.

**Expose definition head** can open one safe definition at the retained selected
term or inferred type. It keeps the original occurrence and a separate fresh result,
exact trace and nine available typing/conversion outcomes. This does not manufacture
a source occurrence for the derived expression. See [definition exposure](editor-definition-exposure.md).
Saving an exposure bundle uses saved-record version 3 and retains the original and
fresh captures separately, with unverified provenance and no live action.

## Build and verification

Normal `npm run setup:lean` verifies the [25-module source dependency](../vendor/DefinographCapture/README.md), compiles it with Lean 4.28.0 and links it only into the project-context executable. All `StatementLens` compiled modules share one module search root; the foundation modules use a separate build directory. Runtime elaboration still receives only the project's library paths. The standalone reader's imports and protocol remain separate.

```sh
npm run test:source-dependency
npm run test:source-snapshot
npm run test:source-snapshot-controls
npm run test:source-occurrence
npm run test:source-occurrence-controls
npm run test:source-head-exposure
npm run check:extension
```

The source-snapshot integration command uses temporary Lean projects and actual InfoTrees. Set `DEFINOGRAPH_SOURCE_SNAPSHOT_CAPTURES` to a path outside the repository to retain its corpus for independent raw readback and interface tests. Native integration and mocked extension-controller tests do not replace validation in a real VS Code GUI.
