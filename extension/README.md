# Statement Lens for Lean

Read a selected Lean proposition as a visual sequence of typed objects, assumptions, and mathematical relationships in its actual project context.

This is an optional local extension for a built Statement Lens checkout. It currently supports Lean **4.28.0** projects on macOS and Linux. It does not modify a project's source, Lake configuration, toolchain, or compiled dependencies, and it does not run Lake or download dependencies.

1. In the Statement Lens checkout, run `npm run build` and `npm run setup:lean` after the documented initial Lean setup.
2. Install the locally produced VSIX using **Extensions: Install from VSIX…**.
3. Set `statementLens.engineDirectory` to the absolute path of that checkout.
4. Open a saved Lean file in a trusted workspace with its dependencies already built.
5. Select a complete proposition and run **Statement Lens: Visualize Selection** from the command palette or editor context menu. With an empty selection, the nearest enclosing elaborated proposition is used.

The active buffer may have unsaved changes. Other unsaved Lean buffers in the same workspace must be saved and built first. **Refresh** uses the current selection when that Lean editor is visible; otherwise it uses the remembered selection. Editing or closing the analyzed document invalidates its previous diagram. **Reveal** returns to the original source.

Local values are displayed as context parameters and local propositions as assumptions. A selected proof term displays its proposition type, explicitly labeled as such. A valid statement can still be inspected when a later proof is incomplete; Lean diagnostics remain visible. Selected placeholders, unresolved metavariables, and definition expansions containing `sorry` are rejected.

The adapter re-elaborates the complete active buffer in a separate trusted process using the project's built imported modules. Lean elaborators, macros, initializers, and `#eval` may execute project code. Workspace Trust is required. This is **not a security sandbox**, and selecting a small range does not prevent other commands in the buffer from executing. The process has time and output limits and is cancelled when the document changes.

The first context adapter is deliberately conservative about numerical interpretation: set constructors and imported mathematical relationships can be read symbolically, while numerical domains and metric samples are disabled. Project-defined global instances must not silently inherit the fixed demo environment's numerical meanings.

Standard Lake library layouts are discovered from the project root and `lake-manifest.json`. For a custom layout, configure `statementLens.libraryPaths` with existing compiled library directories. Lake plugins, custom setup options, custom source roots, and nonstandard build behavior may require a later adapter; failures are reported without changing the project.

See `docs/editor-integration.md` in the checkout for the architecture and verified coverage. The extension's local engine and browser application are prerequisites; the VSIX does not bundle a Lean toolchain or Mathlib cache.

Credits: Codex under the supervision of Neil Yuanting Li.
