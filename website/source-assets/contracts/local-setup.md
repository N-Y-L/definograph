# Local setup and installation qualification

This guide preserves the manual assembly sequence and release qualifications from `docs/editor-integration.md` and `docs/lean-contract.md`. It assumes a trusted source checkout with matching reader, native engine and controller revisions. Source is available in the Definograph repository; a qualified installer or Marketplace release is not provided. Consult the documentation in your checkout when using a newer revision.

## Prerequisites

Use Lean **4.28.0**, Node.js **22.12+**, and Git. Editor use additionally requires VS Code **1.95+**, the official Lean extension (`leanprover.lean4`), and a trusted project with built imports. The declared minima are distinct from the exercised versions described below.

Supply an existing Lean 4.28.0 executable. Setup does not install Lean or change the global Elan default. The native build targets macOS and Linux; native Windows linking is not implemented. The standalone setup requires the pinned mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` and matching transitive dependencies.

## Assemble from a matching checkout

The paths below are placeholders. Replace them with actual paths on your computer. Run these commands from the Definograph checkout with an existing matching built cache:

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

For a fresh isolated dependency cache, replace the setup command with:

```sh
npm run setup:lean -- \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --download
```

Use either `--packages` or `--download`. The download uses the checkout's ignored `.local/` area and can consume several GB. Do not run dependency updates in an existing formal project merely to configure Definograph.

The setup verifier checks recorded build identities and the browser entry's linked assets, then runs one disposable native capture. It does not rebuild or download dependencies. Keep sources fixed during final assembly. Packaging rebuilds only the extension controller and refuses to overwrite an existing VSIX; choose a new output path.

Install the generated package with **Extensions: Install from VSIX…**. In VS Code **User settings**, set `statementLens.engineDirectory` to the absolute path of the matching built checkout. The extension's package and setting names use the project's internal name, Statement Lens. The VSIX contains only the controller; browser assets, the native engine, Lean, and compiled libraries remain separate prerequisites.

For the local browser application, `npm run dev` serves a development build of Definograph at `http://127.0.0.1:5173`. After `npm run build`, `npm start` serves it at `http://127.0.0.1:4317`. These addresses refer to your own machine. Its **Lean source** field accepts a statement term, not a complete file of declarations.

## Installation qualification

Retained local checks used macOS arm64, Node.js 24.18.1/npm 11.16.0 and VS Code 1.138. The npm installation/build preflight, native setup and isolated editor journeys have separate evidence scopes; they do not qualify every combination of these components. Linux, WSL, remote hosts, other architectures and the declared minimum Node.js/VS Code versions have not been qualified.

Dependency installation uses `--ignore-scripts`, matching the exercised npm preflight. Later explicit build/setup/package commands still execute code; this option does not provide a sandbox. Use the committed lockfiles.

A complete public release still needs a matched source/browser/controller/native distribution, canonical download origin and publisher, and clean installation, upgrade, rollback and uninstall checks on each advertised platform. The VSIX alone is not that distribution. `.local/config.json` contains installation-specific absolute paths and must be generated for the destination, not copied from another machine. Existing local and historical checks do not establish those release claims.

## Trusted editor input

The editor sidecar re-elaborates the whole active buffer against existing built imports. Commands, macros, and elaborators can execute project code; selecting a range does not isolate the rest of the file. Save and build changed imported dependencies using the project's normal tools before refreshing. Saved source alone is not a fresh compiled dependency.

[Return to the reference](/reference/).
