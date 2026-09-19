# Lean worker contract

StatementLens type-checks **statements**, not proofs. In particular, `False` is a valid input because it has type `Prop`; acceptance does not establish that it is true. The plotting code is an approximate interpretation of selected typed fragments and is outside Lean's trusted kernel.

## Reproducible setup

The worker is pinned to Lean **4.28.0** and mathlib commit **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. `lean/lake-manifest.json` pins every transitive dependency. Native macOS and Linux builds use the compiler distributed with Lean. Native Windows linking is not implemented; use WSL.

Use the Lean 4.28.0 release for your platform from the [official release](https://github.com/leanprover/lean4/releases/tag/v4.28.0). Extracting a release into a dedicated directory does not require changing an existing Elan default or formal project. Supply its actual `bin/lean` path below.

For an existing, built cache at this revision, run from the StatementLens repository:

```sh
node scripts/lean-build.mjs \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --packages /absolute/path/to/project/.lake/packages
```

This mode only reads the selected toolchain and package directories. It writes the worker, intermediate C file, and machine-specific configuration into this repository's ignored `.local/` directory. It does not run Lake in the selected project.

For a fresh, separate cache:

```sh
node scripts/lean-build.mjs \
  --lean /absolute/path/to/lean-4.28.0/bin/lean \
  --download
```

The optional download copies the checked-in Lake manifests into `.local/mathlib-lean/`, uses that directory as Lake's working directory, and fetches the pinned official dependencies. It requests only `Mathlib.Topology.MetricSpace.Basic`, `Mathlib.Analysis.InnerProductSpace.PiL2`, and their transitive module caches. The mathlib download cache is also directed into `.local/mathlib-download-cache/`. It does not install Lean or change global Elan settings. This can download a substantial amount of data. The read-only cache build and a fresh-download smoke test have both been exercised on macOS. The fresh setup used an empty isolated directory with the preinstalled pinned Lean toolchain, fetched 2,372 module-cache files, and produced a working worker in approximately two minutes. It used about 3 GB on disk, including about 145 MB of compressed mathlib cache files; download size and timing vary by platform and network. A four-dimensional sphere statement passed kernel type-checking using that newly downloaded cache.

After configuration, `node scripts/lean-build.mjs` rebuilds the worker and `node scripts/lean-test.mjs` runs the native integration checks. Use `npm run check` for the complete build, web, server, and native integration checks. No setup step pushes to GitHub.

## Processing boundary

The compiled executable reads one JSON request per stdin line:

```json
{"source":"∀ x : ℝ, x < 1 → x < 2","requestId":7}
```

`requestId` is optional and is echoed on successes and failures. One compressed JSON object is written per line. A persistent process loads fixed mathlib imports once, then creates fresh `CoreM`, `MetaM`, and `TermElabM` state from the original immutable imported environment for each request. No user declaration is added to that environment.

The worker performs these steps:

1. Parse exactly one Lean **term**, with no trailing commands, using `Lean.Parser.runParserCategory`.
2. Walk the syntax against a closed list of declarative mathematical syntax forms. Tactics, `sorry`, placeholders, quotations, custom syntax forms, `do`, declarations, imports, and user-defined elaborators are rejected.
3. Elaborate with expected type `Prop`, disabled automatic implicit variables, and disabled error-to-`sorry` recovery.
4. Complete postponed elaboration and instance synthesis. Reject remaining metavariables and any occurrence of `sorryAx`.
5. Check the resulting expression using `Lean.Meta.checkWithKernel`, which calls the kernel expression checker.
6. Export the logical tree and supported expression metadata.

The server passes source over stdin; it never constructs Lean source files or shell commands from the input. The syntax walk is limited to depth 128; elaboration uses maximum recursion depth 256 and 400,000 heartbeats. The server separately limits request size, output size, elapsed time, and concurrency. Source positions for individual semantic nodes are not exported in this version.

The selected toolchain and compiled mathlib caches are trusted dependencies. Importing Lean modules initializes their registered extensions. The worker is a separate process, **not an operating-system sandbox** for arbitrary third-party Lean code. This is why it imports fixed modules and does not accept project imports, plugins, or unrestricted Lean programs. The worker's `unsafe` entry point is required for trusted imported extension initialization; it does not weaken the kernel check or expose an input-controlled evaluator.

## Logical tree and expression export

A successful response includes `ok`, `source`, `pretty`, `type: "Prop"`, `validation: "kernel-type-checked-statement"`, `tree`, `expression`, and `diagnostics`.

Logical nodes have stable path-based `id` values, a `kind`, display text, `children`, and a portable expression. Kinds are `forall`, `exists`, `implies`, `and`, `or`, `iff`, `not`, and `predicate`. A binder records its distinct identity, display name, type, role, recognized domain, dimension, and previously introduced non-assumption binders in `dependsOn`. These dependencies describe permissible witness dependence from quantifier order; they do not assert that a particular witness actually depends on every earlier choice. Shadowed names retain distinct identities.

The portable expression represents constants, local variables, literals, applications, lambdas, dependent function types, sorts, and opaque terms. Applications retain fully elaborated arguments, including implicit type arguments. Class arguments are rendered as opaque descriptive text after auditing. The optional `binderType` expression preserves the domain of a lambda or universal binder; for implication, it is the antecedent. Tree children are the authoritative representation of logical structure. The export is intended for conservative interpretation; it is not a proof certificate or a complete lossless serialization of Lean's internal expression type.

## Metric and arithmetic interpretation

Geometry is identified from elaborated constants, not source text or notation. The current geometric constants are `Metric.ball`, `Metric.closedBall`, `Metric.sphere`, and `Dist.dist`.

| Lean domain | Recognized standard metric |
| --- | --- |
| `ℝ` | Absolute-value distance |
| `ℝ × ℝ` | Maximum/product distance: square balls |
| `EuclideanSpace ℝ (Fin n)` | Euclidean/L2 distance |
| `Fin n → ℝ` | Maximum/supremum distance |

Finite dimensions through 12 can be identified. Renderer capability may be narrower; unsupported dimensions remain typed but do not receive an invented projection. A Euclidean sphere in ambient dimension four is an intrinsic three-sphere. A coordinate slice is explicitly a slice, not the whole sphere and not a Hopf fibration.

A type name alone is insufficient to identify a metric. For each application, the worker synthesizes the canonical imported typeclass instances in an **empty local context** and checks definitional equality with the actual class arguments. A supplied custom or abstract instance gets `standard: false`; a metric application then gets `metric: "unknown"`. The same audit protects overloaded arithmetic from being interpreted as ordinary real operations when its instance has been replaced. Recognition in the browser additionally restricts operator names and numerical domains.

A statement may mix supported geometry with abstract types, higher-order conditions, or unrecognized predicates. The full accepted statement is type-checked, while supported fragments can be selected independently. An incomplete or ill-typed input is rejected as a whole. This release does not recover plots from a statement that Lean cannot elaborate.

## Upstream references

- [Lean 4.28 parser implementation](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Parser/Extension.lean)
- [Lean 4.28 term elaboration](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/Term/TermElabM.lean)
- [Lean 4.28 kernel-check wrapper](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Meta/Check.lean)
- [Pinned mathlib metric definitions](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean)
- [Pinned mathlib cache command](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Cache/Main.lean)

Developed by Codex under the supervision of Neil Yuanting Li.
