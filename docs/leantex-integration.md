# Optional mathematical notation with LeanTeX

StatementLens uses the real expression printer from [kmill/LeanTeX](https://github.com/kmill/LeanTeX/tree/d66db4582b6cb4d9fa0b6309168103a248a5fd46), pinned at `d66db4582b6cb4d9fa0b6309168103a248a5fd46`. It calls `LeanTeX.run_latexPP : Lean.Expr → LeanTeX.Config → Lean.MetaM String` on the elaborated expression. The output is not a regular-expression translation of Lean source. A statement and a declaration's bounded definition body receive separate notation fields.

The readable notation is a companion to the visual reading sequence. It does not participate in semantic recognition, metric auditing, kernel checking, or the choice of diagrams. The exact Lean source, checked type, and semantic tree remain authoritative. LeanTeX intentionally simplifies presentation: it may hide implicit arguments or universes and can display equality of propositions as logical equivalence. Such notation is a reading aid, not a round-trip serialization or a proof.

## Dependency and compatibility

The original [upstream toolchain](https://github.com/kmill/LeanTeX/blob/d66db4582b6cb4d9fa0b6309168103a248a5fd46/lean-toolchain) is Lean `4.18.0-rc1`. The six core modules through `LeanTeX.Builtins` compile under this project's pinned Lean `4.28.0` with two compatibility changes:

1. Three generated `aux_def` declarations need explicit `public` visibility.
2. `String.split` returns an iterator in Lean 4.28; the character-conversion rule materializes its mapped result with `.toList`.

The optional `LatexCmd` module also needs iterator materialization; it was checked separately but is not imported by the worker. The source subset, original checksums, [Apache-2.0 license](https://github.com/kmill/LeanTeX/blob/d66db4582b6cb4d9fa0b6309168103a248a5fd46/LICENSE), exact revision, and a compatibility patch are retained under `vendor/LeanTeX/`. Build-time checksum checks protect the upstream originals; compatibility edits apply only to copies under `.local/leantex/`.

The companion [LeanTeX-mathlib](https://github.com/kmill/LeanTeX-mathlib/tree/02f8d141abf202f91ca634c0cac82c1a819a3095) was inspected at `02f8d141abf202f91ca634c0cac82c1a819a3095`. Its entry point imports all of Mathlib and the widget entry point, so it is not a dependency. Project-owned rules for the exact `Real` and `Rat` constants provide conventional blackboard-bold types without additional Mathlib imports. The generic upstream expression printer supplies the rest.

## Runtime boundary

The worker dynamically imports the fixed `StatementLens.ReadableMath` module along with its fixed Mathlib imports. It evaluates only the trusted, compile-time name `StatementLens.ReadableMath.render` as an `Expr → MetaM Json` function. Client expressions are its input data; neither module names nor evaluated code entry points come from clients. The existing term syntax allowlist is unchanged, and no client source file or declaration is executed.

The printer runs from imported local oleans. Statically linking its custom extensions while also importing those oleans caused duplicate extension initialization in the standalone executable; the single interpreted entry point avoids that registry conflict. Only Lean and the printer-independent response serializer are statically linked into the worker. The worker does not import ProofWidgets, the upstream top-level widget module, or the `#latex` command module.

All required analysis work, including semantic encoding and Lean pretty-printing, completes before optional notation begins. The printer saves and restores Lean's meta and environment state. Configuration disables MathJax tooltips and family subscripts, retains binders, and preserves explicit implication grouping. Failures return an `unavailable` notation result while retaining the semantic response.

The optional printer applies these bounds:

| Resource | Limit |
| --- | --- |
| Expression depth / unshared size | 64 / 2,000 nodes |
| Printer recursion | At most 128 |
| Printer allocation heartbeats | At most 20,000,000 raw heartbeats, while reserving 1,000,000 in the enclosing request |
| Each LaTeX result | 32,768 characters and 65,536 UTF-8 bytes |
| Whole serialized response | Existing 2 MiB transport limit, including request ID and newline |

The final serializer replaces optional notation with a small `unavailable` record if the enriched response exceeds the transport limit. If those records still cannot fit, it removes only the optional notation fields. It never truncates semantic fields. Responses whose mandatory content already exceeds the limit keep the existing transport failure behavior.

The browser uses local KaTeX with trust disabled, strict errors, bounded macro expansion, and per-render macro state. Unsupported output falls back to Lean text. The display cannot authorize metric semantics: a custom membership instance can be rendered with conventional notation while the semantic compiler still declines to treat it as standard set membership.

## Reproduction and verification

Run `npm run setup:lean` to rebuild from the existing pinned configuration, then `npm run test:notation`. All generated oleans, experiments, fixtures, and executables remain in this repository's ignored `.local/` directory. Existing formal project caches are read only. The final executable is linked to a sibling temporary path and atomically renamed, so an older running worker is not overwritten in place.

The notation suite checks all interface examples through the actual native worker and strict KaTeX, quantifier order, typed binders, negation and arithmetic parentheses, higher-order applications, partial constants, custom membership, and separate declaration signature/body rendering. Trusted Lean fixtures exercise the real serializer at the 2 MiB UTF-8 boundary, preserve request IDs and mandatory trees, and verify repeated size fallback does not contaminate subsequent printing. The main native semantic and reading suites independently verify that optional notation leaves their existing contracts intact.

Upstream credit: LeanTeX and its contributors. Integration and compatibility work: Codex under the supervision of Neil Yuanting Li.
