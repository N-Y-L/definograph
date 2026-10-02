# Definograph for Lean

Read a selected Lean proposition as a visual sequence of typed objects, assumptions, and mathematical relationships in its actual project context.

This is an optional local extension for a built Definograph checkout. It targets Lean **4.28.0** projects on macOS and Linux; retained editor-host evidence is from macOS arm64. Linux, WSL and remote hosts remain unqualified, and native Windows linking is not implemented. It does not modify a project's source, Lake configuration, toolchain, or compiled dependencies, and it does not run Lake or download dependencies.

Build with Node.js **22.12+**. Use VS Code **1.95+** with the official Lean
extension (`leanprover.lean4`). From a Definograph checkout with an existing built
cache matching its pinned Lean 4.28.0/mathlib environment:

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

For the exact dependency pins and the separate `--download` alternative, see
`docs/lean-contract.md` in the checkout. After initial configuration,
`npm run setup:lean` rebuilds using the saved local paths. The verifier checks
build identities and runs one disposable native capture; it does not build,
download dependencies or edit a user's project.

Packaging rebuilds only the controller and refuses to overwrite an existing
VSIX. Without `--out`, it writes `.local/statement-lens-editor-0.7.1.vsix`; choose a
new `--out` path if that file exists. The VSIX requires the matching checkout's
built browser assets and native engine, along with its configured Lean toolchain
and compiled libraries. Keep accepted sources fixed and avoid concurrent edits
or builds during final assembly; see `docs/editor-integration.md` in the checkout.

Node.js 22.12 and VS Code 1.95 are declared minimum versions, not a tested version
matrix. Retained checks used Node.js 24.18.1 and macOS VS Code 1.138. The documented
source setup and controller package are not a qualified complete public installer;
clean installation and upgrade/rollback qualification remain release work.

1. Build and verify the checkout, then produce the VSIX with the commands above.
2. Install that VSIX using **Extensions: Install from VSIX…**.
3. In VS Code **User settings**, set `statementLens.engineDirectory` to the absolute path of that checkout.
4. Open a saved Lean file in a trusted workspace with its dependencies already built.
5. Select a complete proposition and run **Definograph: Visualize Selection** from the command palette or editor context menu. With an empty selection, the nearest enclosing elaborated proposition is used.

The active buffer may have unsaved changes. Other unsaved Lean buffers in the same workspace must be saved and built first. **Refresh** uses the current selection when that Lean editor is visible; otherwise it uses the remembered selection. Editing or closing the analyzed document, changing the selection, or changing adapter settings clears its previous diagram and source snapshot. **Reveal** returns to the original source.

Ordinary local objects are displayed as context parameters and ordinary local proof hypotheses as assumptions. Recorded `auxDecl` and `implDetail` entries receive neutral context labels. A selected proof term displays its proposition type under **Statement of your selected proof**. A valid statement can still be inspected when a later proof is incomplete; Lean diagnostics remain visible. Selected placeholders, unresolved metavariables, and definition expansions containing `sorry` are rejected.

**Inspect a definition in this statement** opens a workspace beside the original
clause and its ordered context. Search applications from the whole retained
statement, then choose the exact occurrence with its actual arguments and scope.
The workspace checks that application, exposes one eligible definition head, and
shows the result in its own scope with individual check verdicts. Opaque or
unsupported heads report their outcome. **Return to reading** restores the exact
guided step; reopening can reuse a matching retained history. Source or selection
changes close the workspace. See `docs/editor-definition-exposure.md` in the
checkout for bounds and the detailed contract.

The reader uses pure white base surfaces in light mode and pure black in dark
mode, following the VS Code body theme ahead of the system preference.
Mathematical regions retain their semantic colors. Dense typed-map diagrams keep
readable labels and offer keyboard-accessible horizontal scrolling.

**Source data** separately retains the original selected expression and local
declarations, prepared checker input, optional expected type, and available kernel
outcomes and axiom audits. Raw data can remain inspectable when the guided view or
source checks are unavailable. **Save source snapshot** creates an unverified saved
record; it does not certify a proposition or the diagram. Imported libraries are
recorded as process context, without continuously tracking later compiled changes.

In **Checker input**, choose a constructor inside the prepared term, then press
**Check chosen occurrence**. This reruns the buffer, requires an exact match with
the prepared source, and displays the selected dependent context and all retained
source, root and selected typing outcomes. A failed root remains visible even if
the selected child checks successfully. Original-data paths are not reused after
preparation changes the term. Saved occurrence outcomes remain unverified.

In that occurrence's guided reading, choose the term or inferred type and press
**Expose definition head** to open one safe definition body. The original remains
available alongside the exposed result, its exact trace, and fresh result typing
and conversion outcomes. Opaque or unsupported heads and resource limits produce
an explicit refusal. This operation runs only on request and does not recursively
open further definitions. Saved records cannot launch live exposure actions.

The adapter re-elaborates the complete active buffer in a separate trusted process using the project's built imported modules. Lean elaborators, macros, initializers, and `#eval` may execute project code. Workspace Trust is required. This is **not a security sandbox**, and selecting a small range does not prevent other commands in the buffer from executing. The process has time and output limits and is cancelled when the document changes.

The first context adapter is deliberately conservative about numerical interpretation: set constructors and imported mathematical relationships can be read symbolically, while numerical domains and metric samples are disabled. Project-defined global instances must not silently inherit the fixed demo environment's numerical meanings.

Standard Lake library layouts are discovered from the project root and `lake-manifest.json`. For a custom layout, configure `statementLens.libraryPaths` with existing compiled library directories. Lake plugins, custom setup options, custom source roots, and nonstandard build behavior may require a later adapter; failures are reported without changing the project.

See `docs/editor-integration.md` in the checkout for the architecture and verified coverage. The extension's local engine and browser application are prerequisites; the VSIX does not bundle a Lean toolchain or Mathlib cache.

Credits: Codex under the supervision of Neil Yuanting Li.

### Record fields in a continuation

After checking a source occurrence, **Inspect fields of original occurrence** lists
its direct record fields. **Check field** checks one named projection and retains
its exact owner, context, inferred type and local outcomes. A nested field can be
inspected again; a law proof's type can be exposed and focused through the same
history. Listing metadata requests no field typing checks. Nonliteral owner types,
including aliases, receive an explicit refusal.

New histories support eight operations and eight retained attempts within 16 MiB.
Earlier prefixes and legacy exposure seeds remain available. Save and Refresh to
change the fixed original selection; merely viewing history never starts Lean.
See `docs/editor-definition-exposure.md` in the checkout for the operation and
evidence boundaries; checkout documentation is not bundled in the VSIX.
