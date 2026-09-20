# Lean editor context adapter

Statement Lens 0.5 includes a local VS Code extension that exports selected mathematical propositions from the project's actual Lean environment. The standalone website still uses its separately pinned, closed-term worker. The editor adapter does not copy a selected string into that fixed environment.

## Install and use

The first adapter supports Lean **4.28.0**, local macOS and Linux installations, and existing compiled project dependencies. Native Windows linking is not supported. Remote VS Code hosts have not been validated.

From the Statement Lens checkout:

```sh
npm ci
npm run setup:lean   # after the initial pinned-cache configuration in README.md
npm run build
npm ci --prefix extension --ignore-scripts
npm run package --prefix extension
```

Install `.local/statement-lens-editor-0.7.0.vsix` with **Extensions: Install from VSIX…**. Set `statementLens.engineDirectory` to the absolute checkout path. The VSIX contains the extension controller; its local engine and browser assets remain in that checkout. No extension is installed into the user's VS Code profile by building or packaging it.

With the official Lean extension enabled, open a saved `.lean` file in a trusted workspace. Select a complete proposition and run **Statement Lens: Visualize Selection**. A nonempty selection must match an elaborated proposition or proof term, apart from surrounding whitespace. An empty selection chooses the smallest containing proposition or proof term with a proposition type. Arbitrarily selecting a variable does not silently expand a nonempty selection into a different statement.

The active buffer may have unsaved changes. Imported definitions come from the project's **built `.olean` dependencies**, as in Lean's normal import workflow. Save and build changed dependencies with the project's normal tools before refreshing; saved source alone is not a fresh compiled dependency. Other dirty Lean buffers in the same workspace are refused. Changes to another open Lean buffer in that workspace invalidate the view as well.

Refresh uses the current selection if the original editor is visible, or the remembered selection otherwise. Reveal only targets that original document, and checks the version and request again after VS Code opens it. Editing or closing the analyzed document cancels pending work and marks the diagram stale. No automatic re-elaboration runs on every keystroke.

## Semantic contract

`server/editor-context.ts` discovers the nearest `lean-toolchain`, accepts exactly `leanprover/lean4:v4.28.0` (or `v4.28.0`), reads `lake-manifest.json`, and gathers the existing standard project/package library directories. It does not execute `lakefile.lean`, invoke Lake, fetch dependencies, choose a different toolchain, or write a project file. `statementLens.libraryPaths` supplies additional built library roots for custom layouts. These precede the discovered paths. Custom source roots, Lake setup options, native plugins, and other nonstandard build configurations are not reconstructed by this first adapter; errors remain explicit.

The separate `StatementLens.Context` native process parses the active buffer's own imports and elaborates the **complete buffer** with those actual modules. It obtains the expression, local context, metavariable context, namespace, options, and enclosing declaration from Lean `InfoTree` entries. It uses `ContextInfo.runMetaM` and independently calls `checkWithKernel` on the selected expression and its displayed proposition. The shared `StatementLens.Export` module is compiled into the native adapter; it is not injected into the formal project's imports or environment.

A fragment's free local objects become **context parameters**, not implicit universal assertions. Local proof hypotheses become **assumptions**, scoped over the displayed fragment. Local `let` values are substituted definitionally before export, including a second placeholder check after substitution. A selected proof expression is displayed as its proposition type, with `selectionKind: "proof-type"`. Placeholder-containing proof values are refused even when their type is a valid proposition. Later proof errors may be reported as diagnostics while an independently valid selected statement remains inspectable. This checks the selected term's type; it does not certify that the surrounding theorem is proved.

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

## Execution and isolation limits

Workspace Trust is required because Lean elaborators, macros, imported initializers, and commands such as `#eval` can execute project code. The whole buffer is replayed, including commands outside and after the selected range. This is **not a security sandbox**. The adapter itself writes only a private temporary response file; trusted source code can perform whatever IO the host account allows. Elaborators depending on process working directory or a custom Lake launch environment may behave differently: the sidecar runs in a private temporary working directory.

A request has a 512 KiB source limit, 128 local declaration limit, bounded expression traversal, a 45-second process deadline, 128 KiB console-output limit, and 2 MiB structured-response limit. Cancelled requests terminate the process group on POSIX; temporary files are removed. A private response file separates protocol data from ordinary project console output. No project code is executed by discovery, extension activation, or source-change listeners; execution happens only on the explicit command/Refresh.

## Host bridge and validation

The webview loads the same built application from local extension-approved URIs with a restrictive CSP and no HTTP analysis server. It posts `statementlens.ready`, `statementlens.refresh` (optionally with bounded expansion), and `statementlens.reveal`. The extension sends `statementlens.status`, `statementlens.analysis`, and `statementlens.error`, each with a monotonically increasing request ID and exact document metadata. Status `stale` invalidates the reader immediately. Results are discarded if their ticket, buffer version, or selection is obsolete. A replaced panel cannot receive old HTML or old reveal effects.

Verified automated checks:

- `node --import tsx scripts/editor-integration.ts`: 23 native cases against an isolated fixture with a genuinely compiled imported dependency; unsaved active buffer, custom definitions and expansion, proof assumptions, dependent types, Unicode coordinates, later proof errors, selected errors, hidden/expanded placeholders, fake constructor names, canonical versus global replacement set instances, symbolic metric handling, trust/version/cancellation/deadline boundaries and separation of project console output, and unchanged project source/configuration.
- `node --import tsx --test server/editor-context.test.ts`: UTF-16/CRLF/surrogate bounds, pre-access trust refusal, and read-only standard/path-package discovery.
- `npm test --prefix extension`: controller execution against mocked VS Code APIs, including real generated webview HTML, message ordering, expansion forwarding, stale-result rejection, other-buffer invalidation, fresh visible selection, reveal races, configuration failure recovery, and generation lifecycle.
- `npm run check --prefix extension` and `npm run package --prefix extension`: TypeScript and the official VS Code packaging tool produce the local VSIX.

These checks exercise the native Lean adapter and extension controller. They do not claim a manual end-to-end test inside a running VS Code extension host or validation of arbitrary project-specific metaprogramming.

## Why a separate context process

Lean's public editor protocol offers interactive goals, term goals, diagnostics, and RPC references. A custom RPC that exports arbitrary expressions must be present in the environment of the selected document. Adding such a module would require changing formal imports or restarting/configuring its existing server. The isolated sidecar provides a working first integration without those changes. A future version can use an explicitly enabled project RPC provider for incremental analysis.

Primary references: [Lean server protocol overview](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Server/ProtocolOverview.lean), [Lean InfoTree and context APIs](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/InfoTree/Main.lean), [Lean frontend](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/Frontend.lean), [official Lean VS Code exports](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/src/exports.ts), and [VS Code webviews](https://code.visualstudio.com/api/extension-guides/webview).
