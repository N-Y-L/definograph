# Lean editor context adapter

Definograph includes a local VS Code extension that exports selected mathematical propositions from the project's actual Lean environment. The standalone website still uses its separately pinned, closed-term worker. The editor adapter does not copy a selected string into that fixed environment.

## Install and use

The first adapter targets Lean **4.28.0**, local macOS and Linux installations,
and existing compiled project dependencies. Build with Node.js **22.12+**; use
VS Code **1.95+** with the official Lean extension (`leanprover.lean4`). Native
Windows linking is not supported. See [installation qualification](#installation-qualification)
for the exercised platform and remaining release limits.

From the Definograph checkout, using an existing cache matching the
[pinned Lean and mathlib environment](lean-contract.md#reproducible-setup):

```sh
npm ci --ignore-scripts
npm run setup:lean -- \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --packages /absolute/path/to/built/.lake/packages
npm run build
npm ci --prefix extension --ignore-scripts
node --import tsx scripts/verify-local-setup.ts
npm run package --prefix extension -- --out /absolute/path/to/new/statement-lens-editor-0.7.1.vsix
```

For a separate fresh cache, use the documented
[`--download` alternative](lean-contract.md#reproducible-setup) instead of
`--packages`. Setup does not install Lean or change global toolchain settings.
After initial configuration, `npm run setup:lean` reuses the saved local paths.

The verifier checks recorded source-capture inputs, configuration and build
fingerprint, checks the browser entry's linked assets, and runs one disposable
native capture. It does not build, download dependencies or edit a user's project. Run
it after the native and browser builds and before packaging. Keep the accepted
sources fixed during final assembly; do not edit or build concurrently. Record
the VSIX, browser build and native engine identities together, and rebuild and
verify again if their inputs change.

Packaging builds only the extension controller. It refuses to overwrite an
existing VSIX; choose a new `--out` path for each retained build. Without `--out`,
the default is `.local/statement-lens-editor-0.7.1.vsix`. Package timestamps use
`SOURCE_DATE_EPOCH` (default: 2000-01-01 UTC); UTC and file permissions are
normalized so fixed input bytes and the same packaging dependencies reproduce
the archive. Run the focused packaging controls with
`node --test extension/package.test.mjs`.

Install the generated
file with **Extensions: Install from VSIX…**, then use VS Code **User settings** to set
`statementLens.engineDirectory` to the absolute path of the matching built
checkout. The VSIX contains only the controller; browser assets, the native
engine, the configured Lean toolchain and compiled libraries remain separate
prerequisites. Building and packaging do not install an extension into the
user's VS Code profile.

With the official Lean extension enabled, open a saved `.lean` file in a trusted workspace. Select a complete proposition and run **Definograph: Visualize Selection**. A nonempty selection must match an elaborated proposition or proof term, apart from surrounding whitespace. An empty selection chooses the smallest containing proposition or proof term with a proposition type. Arbitrarily selecting a variable does not silently expand a nonempty selection into a different statement.

The **Source data** tab independently captures the original term, local declarations,
prepared checker input and available source-check outcomes. If no proposition is
eligible, the smallest available elaborated term can supply a raw snapshot while
the guided reader reports that it cannot read that selection. See
[exact source snapshots](editor-source-snapshots.md) for its separate contract.

The guided reader labels a selected proof **Statement of your selected proof**
and displays its inferred proposition with the recorded context. **Inspect a
definition in this statement** retains the current clause and ordered context
beside a searchable list of applications from the whole exact statement. Choose
an occurrence with its actual arguments and scope to check it and expose one
eligible definition head. Its result and individual check outcomes remain
separate from the original reading. **Return to reading** restores the exact
guided step; reopening can reuse a matching retained history. Opaque, unsupported
or unavailable heads report their outcome. See the
[statement inspection workflow](editor-definition-exposure.md#inspect-from-the-statement)
for search and history bounds.

**Check chosen occurrence** selects an ordinary constructor inside the prepared
term. It reruns the buffer, compares the exact prepared parent, and retains the
chosen dependent context and separate source, inferred-root and selected typing
outcomes. An accepted child does not hide a rejected root. Its new process capture
does not inherit earlier results or prove unchanged imported definitions.

From that retained occurrence, **Expose definition head** runs a fresh request for
the chosen term or inferred type. It retains the original reading and shows one
definition body with its exact transformation, result typing and conversion checks.
Choose a part of that result and use **Check chosen part** to retain its full
context and newly inferred type, then explicitly expose another definition head.
Earlier continuations remain inspectable, including when a later step stops.
After an explicit inspection, the open Source data view moves keyboard focus to
the returned record or its unavailable notice. Host errors also remain visible
inside the drawer. A result does not reopen a closed drawer or switch back from
another tab.
Opening a view or switching its target does not run Lean. See
[definition exposure](editor-definition-exposure.md) for supported heads and limits.

The active buffer may have unsaved changes. Imported definitions come from the project's **built `.olean` dependencies**, as in Lean's normal import workflow. Save and build changed dependencies with the project's normal tools before refreshing; saved source alone is not a fresh compiled dependency. Other dirty Lean buffers in the same workspace are refused. Changes to another open Lean buffer in that workspace invalidate the view as well.

Refresh uses the current selection if the original editor is visible, or the remembered selection otherwise. Reveal only targets that original document, and checks the version and request again after VS Code opens it. Editing or closing the analyzed document, changing its selection, or changing the adapter configuration cancels pending work and clears the diagram and source snapshot. No automatic re-elaboration runs on every keystroke.

The reader's base surfaces are pure white in light mode and pure black in dark
mode. The VS Code webview uses the host's light, dark or high-contrast body theme
classes, which take precedence over the operating-system preference. The
standalone reader follows the system preference. Mathematical regions retain
semantic color fills in both modes.

## Installation qualification

Retained local checks used macOS arm64, Node.js 24.18.1/npm 11.16.0 and VS Code
1.138. The npm installation/build preflight, native setup and isolated editor
journeys have separate evidence scopes; they do not qualify every combination
of these components. Linux, WSL, remote hosts, other architectures and the
declared minimum Node.js/VS Code versions have not been qualified.

Dependency installation uses `--ignore-scripts`, matching CI and the exercised
npm preflight. Later explicit build/setup/package commands still execute code;
this option does not provide a sandbox. Use the committed lockfiles.

A complete public release still needs a matched source/browser/controller/native
distribution, canonical download origin and publisher, and clean installation,
upgrade, rollback and uninstall checks on each advertised platform. The VSIX
alone is not that distribution. `.local/config.json` contains installation-specific
absolute paths and must be generated for the destination, not copied from another
machine. Keep the previous matched controller and engine available when qualifying
an upgrade. Existing local and historical checks do not establish these release
claims.

## Semantic contract

`server/editor-context.ts` discovers the nearest `lean-toolchain`, accepts exactly `leanprover/lean4:v4.28.0` (or `v4.28.0`), reads `lake-manifest.json`, and gathers the existing standard project/package library directories. It does not execute `lakefile.lean`, invoke Lake, fetch dependencies, choose a different toolchain, or write a project file. `statementLens.libraryPaths` supplies additional built library roots for custom layouts. These precede the discovered paths. Custom source roots, Lake setup options, native plugins, and other nonstandard build configurations are not reconstructed by this first adapter; errors remain explicit.

The separate `StatementLens.Context` native process parses the active buffer's own imports and elaborates the **complete buffer** with those actual modules. It obtains the expression, local context, metavariable context, namespace, options, and enclosing declaration from Lean `InfoTree` entries. It uses `TermInfo.runMetaM` with the saved `ContextInfo` and independently calls `checkWithKernel` on the selected expression and its displayed proposition. The shared `StatementLens.Export` module is compiled into the native adapter; it is not injected into the formal project's imports or environment.

A fragment's ordinary free local objects become **context parameters**, not implicit universal assertions. Ordinary local proof hypotheses become **assumptions**, scoped over the displayed fragment. Recorded `auxDecl` and `implDetail` entries receive neutral context labels instead. Guided export substitutes local `let` entries whose recorded `nondep` flag is false, including a second placeholder check after substitution. Exact source frames retain recorded local definitions. A selected proof expression is displayed as its proposition type, with `selectionKind: "proof-type"`. Placeholder-containing proof values are refused even when their type is a valid proposition. Later proof errors may be reported as diagnostics while an independently valid selected statement remains inspectable. This checks the selected term's type; it does not certify that the surrounding theorem is proved.

Exact safe definition names may be expanded on request, with at most 12 names and depth 1–3. Every expansion is kernel checked and checked for definitional equality; unresolved terms and `sorry` introduced by unfolding are refused. The adapter also requests bounded small-definition previews within the same elaboration; the reader selects at most one when it reduces unknown meaning and retains the original reading. Generating these previews does not replay the buffer again. See [the graph and inspection iteration](graph-iteration.md) for limits. Opaque or otherwise unsupported mathematics remains typed structure, with no invented properties.

Editor provenance uses:

```ts
validation: 'kernel-type-checked-context-fragment'
provenance: {
  assistant: 'lean', inputMode: 'editor', inspected: 'context-fragment',
  fileName, parentDeclaration, selectionKind,
  startByte, endByte, requestedStartByte, requestedEndByte,
  contextParameters, localLetBindings: 'substituted-definitionally'
}
```

`source` is the complete active buffer; `sourceTerms` coordinates are UTF-8 byte offsets into it. The separate host document metadata uses VS Code's zero-based UTF-16 line/character positions and records URI, file name, document version, and original selection. These coordinate systems are converted explicitly and never interchanged.

## Conservative interpretation in project environments

The fixed worker's trusted global instance environment cannot be assumed for an arbitrary project. Editor exports therefore disable numerical domain classification and metric samples. Imported metric objects still have symbolic typed relationships, but no Euclidean or other numerical interpretation is asserted.

Name-based mathematical recognition is limited by an exact audited **declaring-module** table for the imported constructors. A project declaration spelled `Set` or `Metric.ball` receives `canonical: false`, retaining its exact identity and printed name without set or metric semantics. Frontend recognizers must respect that field. Numerical/overloaded operations with instance arguments are conservatively nonstandard, except for explicitly audited canonical set instances, natural-number literals, and the bundled graph function coercions described in [graph semantics](graph-semantics.md). In particular, a project's high-priority global replacement for `Union (Set Nat)` does not become canonical just because that environment synthesizes it. The module audit is a semantic compatibility boundary for trusted projects, not a signature-verification mechanism for hostile compiled libraries.

## Reading a captured history

The original selected pair and completed continuation pairs offer **Inspect type**
and **Read logical structure of this term (one layer)**. The latter always inspects
the term: use **Inspect type** first to read an inferred type’s logical structure.
Actions disappear while the editor is busy and on saved records.

Below the selected step, ordered provenance identifies relations and their
recorded checks. The supply panel displays the accepted reading model’s links,
full ordered conditions, formation judgements and typing-declaration axioms.
Outcome numbers refer to the visible numbered list for that attempt. Auxiliary
entries remain present with their recorded kinds, while ordinary context choices
omit them. These panels are display-only and are not serialized in saved files.
See the [maintained relation table](reader-relations.md) for the meaning and limits
of each relation.

## Execution and isolation limits

Workspace Trust is required because Lean elaborators, macros, imported initializers, and commands such as `#eval` can execute project code. The whole buffer is replayed, including commands outside and after the selected range. This is **not a security sandbox**. The adapter itself writes only a private temporary response file; trusted source code can perform whatever IO the host account allows. Elaborators depending on process working directory or a custom Lake launch environment may behave differently: the sidecar runs in a private temporary working directory.

A request has a 512 KiB source limit, 128 local declaration limit for guided export and source admission, bounded expression traversal, a 45-second process deadline and 128 KiB console-output limit. The guided response retains its 2 MiB limit; the independent source snapshot has a 1.5 MiB cap inside a 4 MiB combined transport limit. An occurrence request has at most 64 path steps and a complete attachment bound of 768 KiB; a definition-exposure attachment has a 1 MiB bound. A continuation permits eight exposure, focus, field-catalogue, projection, type-component or logical-inspection operations (at most 30 local/base checks) and a 2 MiB request/checking record. The host retains at most eight continuation attempts within 16 MiB of aggregate source/history data. Oversized checking records are explicitly omitted. Cancelled requests terminate the process group on POSIX; temporary files are removed. A private response file separates protocol data from ordinary project console output. No project code is executed by discovery, extension activation, or source-change listeners; execution happens only on an explicit visualization, refresh, occurrence-check, definition-exposure, field-inspection or continuation command.

## Host bridge and validation

The webview loads the same built application from local extension-approved URIs with a restrictive CSP and no HTTP analysis server. It posts `statementlens.ready`, `statementlens.refresh` (optionally with bounded expansion), and `statementlens.reveal`. The extension sends `statementlens.status`, `statementlens.analysis`, and `statementlens.error`, each with a monotonically increasing request ID and exact document metadata. Status `stale` invalidates the reader immediately. Results are discarded if their ticket, buffer version, or selection is obsolete. A replaced panel cannot receive old HTML or old reveal effects.

Verified automated checks:

- `node --import tsx scripts/editor-integration.ts`: native cases against an isolated fixture with a genuinely compiled imported dependency; unsaved active buffer, custom definitions and expansion, proof assumptions, dependent types, Unicode coordinates, later proof errors, selected errors, hidden/expanded placeholders, fake constructor names, canonical versus global replacement set instances, symbolic metric handling, trust/version/cancellation/deadline boundaries and separation of project console output, and unchanged project source/configuration.
- `node --import tsx --test server/editor-context.test.ts`: UTF-16/CRLF/surrogate bounds, pre-access trust refusal, and read-only standard/path-package discovery.
- `npm test --prefix extension`: controller execution against mocked VS Code APIs, including real generated webview HTML, message ordering, expansion forwarding, stale-result rejection, other-buffer invalidation, fresh visible selection, reveal races, configuration failure recovery, and generation lifecycle.
- `npm run check --prefix extension` and `npm run package --prefix extension`: TypeScript and the official VS Code packaging tool produce the local VSIX.
- `node --import tsx scripts/host-journey.ts`: an automated real macOS VS Code development-host journey exercises six actual DOM clicks for type and logical inspection on original, derived and first-exposure pairs, checking each command's exact four fields and one native process. It also exercises native continuations, backtracking, cancellation, stale-result rejection, dirty-buffer refusal, recovery and Reveal. Setup, refusal, cancellation and refresh controls still use the extension's registered message handler; this is not a manual webview-button test.

These checks exercise the native Lean adapter and extension controller. They do
not establish every webview-button interaction, acceptance of a final installed
VSIX, or compatibility with arbitrary project-specific metaprogramming.

## Why a separate context process

Lean's public editor protocol offers interactive goals, term goals, diagnostics, and RPC references. A custom RPC that exports arbitrary expressions must be present in the environment of the selected document. Adding such a module would require changing formal imports or restarting/configuring its existing server. The isolated sidecar provides a working first integration without those changes. A future version can use an explicitly enabled project RPC provider for incremental analysis.

Primary references: [Lean server protocol overview](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Server/ProtocolOverview.lean), [Lean InfoTree and context APIs](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/InfoTree/Main.lean), [Lean frontend](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/Frontend.lean), [official Lean VS Code exports](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/src/exports.ts), and [VS Code webviews](https://code.visualstudio.com/api/extension-guides/webview).
