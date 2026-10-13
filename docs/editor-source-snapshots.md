# Exact source snapshots in the Lean editor

After **Definograph: Visualize Selection**, open **Source data**. The reader keeps the selected Lean expression and its local declarations independently of the guided diagram. A proof term remains a proof term in this record, even when the guided reader displays its proposition type. The view does not draw a selected proof: one closed leaf stands in its place and shows the statement it proves (see [A selected proof](#a-selected-proof)). If no proposition is eligible, the smallest available elaborated term can still provide source data while the guided reader reports its selection boundary. Among elaborated terms that cover the same source range, the outermost is chosen, so an anonymous constructor `⟨…⟩` is captured as the whole term and not as the constructor constant Lean synthesizes for it.

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

## A selected proof

The reader is for statements. A selected proof is read through the statement it proves, and its body is not drawn.

With every capture the native adapter reports `selectionClass`: `proposition`, `proof` or `other`. It is the result of Lean's `Meta.isProp` on the chosen term and on its inferred type, and a term whose classification fails is `other`. The class is a top-level key of the response, beside the guided result and the snapshot. It is reported when the guided reading is refused or fails, and it is kept when an oversized guided reading is replaced by its size refusal. It is the elaborator's report, not a kernel check. It is not a field of the snapshot record and is not written to a saved file.

A capture that reaches the reader without the class is not read as "not a proof". This happens with an engine or an installed extension built before the class existed. The drawer then says in one line that Lean's class was not reported, that the term may be a proof and that no proof inside it is labelled, and adds that the engine must be rebuilt and the matching extension installed. A record shown without a live origin never holds the class and gets the same line without that advice. The line is not shown once a retained kernel check has read the type of the whole term.

When the class is `proof`, **Original data** and **Checker input** still draw the local declarations and the source type. The source term position holds one leaf, and no constructor of the term is drawn or offered as an occurrence. The undrawn term spends none of the raw view's initial fold.

The leaf is short. The statement comes first and is its largest text. One line under it gives the verdict, for example "Typing: accepted by Lean’s kernel. Axioms: Classical.choice, propext, Quot.sound. Statement is a proposition: reported by Lean’s elaborator." A recorded expected type that differs adds one line, and the statement check follows when it is offered. Everything else is behind one disclosure, which is closed until the reader opens it. Its label stays in view and counts what is not drawn, for example **What was checked · 4 constructor nodes not drawn**.

Every line of the leaf is read from the prepared frame and its receipt. On **Original data** the verdict therefore opens with its subject, "Prepared term.", and the disclosure is labelled **What was checked: the prepared term**, with the same count. Inside, it says that the position holds the original term, that every line of the leaf is about the prepared term under **Checker input**, and that the record does not prove the two frames equivalent. The original term stays in the saved snapshot.

| Part of the leaf | Where | Source |
| --- | --- | --- |
| `(⋯ : statement)` | In view, first | The form Lean's own printer uses for an elided proof. The statement is the inferred type of the term. If no text of it fits on one line, the leaf shows `⋯` and, directly under it, the sentence that the type is not written on one line and stays in the record. |
| Verdict | In view, one line | The opening sentences of the Typing, Axioms and *Statement is a proposition* lines below, in that order, and nothing else, except the subject "Prepared term." on **Original data**. It reads "accepted by Lean's kernel" only where the line it opens does. The main panel shows the same line, and the expected-type line under it, through the same component. |
| Expected type | In view, when it differs | Shown only when the snapshot records an expected type that is not, as exact data, the prepared inferred type. For `rfl` selected in `example : 2 + 2 = 4 := rfl` the leaf reads `(⋯ : 2 + 2 = 2 + 2)`, and this line points to **Expected type**. It reports that two recorded expressions differ and nothing more: an expectation that still holds a metavariable differs too. |
| What the leaf stands for | What was checked | **Term reported as a proof, not drawn**, or **Proof term, not drawn** only on the kernel basis described below. |
| Statement | What was checked | Which text is shown: Lean's printed text from the guided reading, where local definitions are substituted, or, without a guided reading, the recorded inferred type written out with every argument explicit. If neither fits on one line, the sentence that the type stays in the record is in view under `⋯` instead. |
| Typing | What was checked | The outcome of the snapshot's component receipt: the prepared term at its inferred type, closed over the captured context. It reads "accepted by Lean's kernel" only for a recorded accepted declaration and names the prepared term. A rejected, unknown or missing outcome is worded as such, with its recorded reason. |
| Axioms | What was checked | The axiom audit of that declaration, as recorded. The list is shown and never changes the verdict: a term that depends on a lemma proved with `sorry` is accepted, with `sorryAx` in the list. After an accepted typing the line ends with the supply panel's own sentence: kernel acceptance is a typing outcome in the captured environment, not a statement that the proposition is true. |
| Statement is a proposition | What was checked | "reported by Lean's elaborator", with the note that no kernel check of this is recorded, until the accepted receipts described below exist. The label names the judgement: that the statement is a proposition, not that it holds. |
| Data | Label in view; detail under What was checked | The number of constructor nodes recorded for the prepared term is on the disclosure's label. Inside: that the term stays in the record as data, and where its exact form can be read: under **Check outcomes** when a receipt for the term is recorded, and in the saved snapshot. |

**Check with the kernel that this statement is a proposition** runs two existing operations in turn: the check of the whole selected term, then **Inspect type** on the checked pair. Each reruns the current buffer. When the retained history then holds an accepted typing receipt for the term and an accepted type-component receipt that checks the statement at `Sort 0`, the verdict and the *Statement is a proposition* line read "accepted by Lean's kernel", and that line names the attempt and its outcome numbers; the [supply reading](reader-relations.md) of that attempt lists the full conditions. Without both accepted receipts the line keeps the elaborator's wording. This kernel basis closes the term even when no class was reported. If the kernel establishes that the inferred type is a type and not a proposition, the term is not closed, whatever the elaborator reported.

The check is not offered when the snapshot's own check could not begin, for example beyond 128 context declarations: the rerun would stop at the same place, and the Typing line gives the recorded reason. It is not offered again after a whole-term check that returned no checked pair; the leaf then says, in view, where that check's record is. While the check is offered, the last line under **What was checked** says that it reruns the buffer twice and that the term stays closed.

After the whole term is checked, its occurrence views show the type first. On the elaborator's report the two targets keep their neutral titles, **Selected term** and **Inferred type**. On the kernel basis they read **Selected proof term** and **Statement**. The term target shows the same leaf and compiles no reading of the term, and the **Structure** view draws the context and the type with the term root closed, and says that the term root is not drawn. The original pair then offers only **Inspect type**; the logical-layer, field, whole-term and term-head actions are not offered on a proof. The definition head of its type can still be exposed from the type target. From the type, every existing operation works as before.

The record, its validators and the saved-file versions are unchanged. The exact recorded term stays reachable as data: under **Check outcomes** in each exact declaration and in the exact source binding when a check record was captured, under **Exact selected term** after a check, and always in the saved snapshot. The leaf names **Check outcomes** only when a receipt for the term is recorded.

One limit remains, and the first lines of the drawer state it for every selection. For a selection that is not shown as a proof, proof arguments inside the selected term are not yet folded. A structure instance with a proof field, an anonymous constructor carrying a proof, or `show … from …` inside data is drawn as ordinary structure and is not labelled as a proof. For a selection shown as a proof, the drawer says that the term is closed at **Source Term** as `(⋯ : statement)`, and that proof arguments inside the statement and in local definitions are still drawn as ordinary structure. A local declaration whose recorded value is a proof is drawn as recorded in both cases.

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

In **Checker input**, choose a constructor inside the prepared term and press **Check chosen occurrence**. This choice is offered for a selection that is not shown as a proof; a selected proof has the single statement check described [above](#a-selected-proof). The reader reruns the current buffer and compares its selected range, exact prepared frame and universe parameters with the displayed snapshot. If they differ, extraction does not begin. Original-data paths are separate: instantiation can change the expression's constructor structure, so an original path is not reused in the prepared term.

Selection supports the whole term and ordinary application, lambda, product, let and projection children, up to 64 path steps. The prepared frame's separate source-type field, external local declarations, metadata and derived-view positions remain inspection data. A body selection includes the binder it enters; a domain or defining-value selection does not. Newly opened binders retain their exact dependent context and positional references; repeated names do not identify variables. An owned source `have` retains its defining value and original `nondep` flag, while an external opaque local declaration remains an input without a defining equation.

The separate `definograph.source-occurrence.v1` record retains the exact selected context, term and inferred type. A completed extraction has six typing outcomes: supplied-source context/component, inferred-root context/component, and selected context/component. A rejected root remains visible even if its selected child is accepted. An invalid path can retain the two source outcomes before reporting an action error. A returned result or completed action does not establish that all checks accepted.

**Guided reading** presents the selected candidate through the shared reading sequence and overview. **Selected term** and **Inferred type** are separate targets; switching them resets the display focus without requesting another native capture. For the whole term of a selected proof the type is shown first, and the term target shows the closed leaf in place of a reading of the term. The two targets are titled **Selected proof term** and **Statement** only on the kernel basis. The record still holds the proof term and its inferred type as separate fields, and neither replaces the other. Surrounding context entries remain separate from binders introduced inside the displayed expression, including unused entries and local definitions with their original defining values.

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

Normal `npm run setup:lean` verifies the [26-module source dependency](../vendor/DefinographCapture/README.md), compiles it with Lean 4.28.0 and links it only into the project-context executable. All `StatementLens` compiled modules share one module search root; the foundation modules use a separate build directory. Runtime elaboration still receives only the project's library paths. The standalone reader's imports and protocol remain separate.

```sh
npm run test:source-dependency
npm run test:source-snapshot
npm run test:source-snapshot-controls
npm run test:source-occurrence
npm run test:source-occurrence-controls
npm run test:source-head-exposure
npm run check:extension
```

The source-snapshot integration command uses temporary Lean projects and actual InfoTrees. It includes the equal-range selection rule for an anonymous-constructor proof and data body, and the reported class of a proof whose guided reading is refused. Set `DEFINOGRAPH_SOURCE_SNAPSHOT_CAPTURES` to a path outside the repository to retain its corpus for independent raw readback and interface tests. Native integration and mocked extension-controller tests do not replace validation in a real VS Code GUI.
