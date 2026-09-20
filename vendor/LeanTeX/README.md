# LeanTeX source subset

These original files are vendored from [kmill/LeanTeX](https://github.com/kmill/LeanTeX) at the revision recorded in `UPSTREAM.json`, under the accompanying Apache-2.0 license. Their SHA-256 checksums are verified during the local build. The source files in `upstream/` are unchanged.

`lean-4.28.patch` documents the compatibility changes applied to isolated copies under `.local/leantex/`:

1. Lean 4.28 requires explicit `public` visibility for the three generated `aux_def` declarations.
2. `String.split` now returns an iterator; `Builtins.lean` materializes its mapped result as a list.
3. The optional `#latex` command similarly materializes strings before whitespace joining.

The build uses the six library modules through `Builtins`. `LatexCmd` is retained for upstream provenance and isolated compatibility tests, but its command is not imported by the worker. The ProofWidgets integration, top-level module importing widgets, and upstream Lake dependencies are deliberately not included in the production dependency graph.

StatementLens calls the genuine `LeanTeX.run_latexPP` API on the already elaborated Lean expression. The small project-owned module `lean/StatementLens/ReadableMath.lean` adds conventional display rules for the exact `Real` and `Rat` constants. Pretty-printed notation is a reading aid, not a lossless replacement for the Lean expression or semantic document. The upstream printer intentionally hides some elaboration details; exact Lean remains available alongside it.

Upstream attribution remains with LeanTeX and its contributors. Compatibility work and integration: Codex under the supervision of Neil Yuanting Li.
