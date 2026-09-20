# Lean worker contract

Definograph type-checks **statements**, not proofs. In particular, `False` is a valid input because it has type `Prop`; acceptance does not establish that it is true. The plotting code is an approximate interpretation of selected typed fragments and is outside Lean's trusted kernel.

## Reproducible setup

The worker is pinned to Lean **4.28.0** and mathlib commit **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**. `lean/lake-manifest.json` pins every transitive dependency. Native macOS and Linux builds use the compiler distributed with Lean. Native Windows linking is not implemented; use WSL.

Use the Lean 4.28.0 release for your platform from the [official release](https://github.com/leanprover/lean4/releases/tag/v4.28.0). Extracting a release into a dedicated directory does not require changing an existing Elan default or formal project. Supply its actual `bin/lean` path below.

For an existing, built cache at this revision, run from the Definograph repository:

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

The optional download copies the checked-in Lake manifests into `.local/mathlib-lean/`, uses that directory as Lake's working directory, and fetches the pinned official dependencies. It requests `Mathlib.Topology.MetricSpace.Basic`, `Mathlib.Analysis.InnerProductSpace.PiL2`, `Mathlib.Combinatorics.SimpleGraph.Coloring`, `Mathlib.Topology.OpenPartialHomeomorph.Defs`, and their transitive module caches. The mathlib download cache is also directed into `.local/mathlib-download-cache/`. It does not install Lean or change global Elan settings. This can download a substantial amount of data. The read-only cache build and a fresh-download smoke test have both been exercised on macOS. The historical geometry-only fresh setup used an empty isolated directory with the preinstalled pinned Lean toolchain, fetched 2,372 module-cache files, and produced a working worker in approximately two minutes. It used about 3 GB on disk, including about 145 MB of compressed mathlib cache files; download size and timing vary by platform and network. A four-dimensional sphere statement passed kernel type-checking using that newly downloaded cache.

After configuration, `node scripts/lean-build.mjs` rebuilds the worker and `node scripts/lean-test.mjs` runs the native extraction checks. `npm run test:semantic` exercises the real backend through semantic compilation and automatic view selection, including scoped assumptions, partial applications, custom-instance refusals, declaration bodies, 21-dimensional geometry, and preservation of relationships under binder renaming and conjunction regrouping. Use `npm run check` for the complete build, web, server, and native integration checks. No setup step pushes to GitHub.

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
6. Export the logical tree, typed object descriptors, context, source occurrences, and definition metadata. Bounded optional structure reflection reads actual checked field projections and scoped laws. Type-head alias views and proposition previews preserve checked definitional equality; explicit bounded expansion is also available. These additions reuse the same elaboration rather than replaying source commands.

The server passes source over stdin; it never constructs Lean source files or shell commands from the input. The syntax walk is limited to depth 128; elaboration uses maximum recursion depth 256 and 400,000 heartbeats. The server separately limits request size, output size, elapsed time, and concurrency. The v2 exporter records exact typed source occurrences from Lean’s InfoTree; see the coordinate contract below. They are separate from transformed logical nodes.

The selected toolchain and compiled mathlib caches are trusted dependencies. Importing Lean modules initializes their registered extensions. The worker is a separate process, **not an operating-system sandbox** for arbitrary third-party Lean code. This is why it imports fixed modules and does not accept project imports, plugins, or unrestricted Lean programs. The worker's `unsafe` entry point is required for trusted imported extension initialization; it does not weaken the kernel check or expose an input-controlled evaluator.

## Logical tree and expression export

A successful response includes `ok`, `schemaVersion: 2`, `source`, `pretty`, `type`, `validation`, `tree`, `expression`, and `diagnostics`. Term input has `type: "Prop"` and `validation: "kernel-type-checked-statement"`. Declaration signature input can have another type and uses `kernel-type-checked-declaration-type`.

Logical nodes have stable path-based `id` values, a `kind`, display text, `children`, and a portable expression. Kinds are `forall`, `exists`, `implies`, `and`, `or`, `iff`, `not`, `predicate`, and `parameter`. A `parameter` belongs to a declaration’s function/type signature; it does not assert a universally quantified proposition. A binder records its distinct identity, display name, type, role, recognized domain, dimension, and previously introduced non-assumption binders in `dependsOn`. These dependencies describe permissible witness dependence from quantifier order; they do not assert that a particular witness actually depends on every earlier choice. Shadowed names retain distinct identities. Display names erase Lean macro scopes; imported internal hygiene suffixes are never used as user-facing binder identities.

The portable expression represents constants, local variables, literals, applications, lambdas, dependent function types, sorts, and opaque terms. Applications retain fully elaborated arguments, including implicit type arguments. Class arguments are rendered as opaque descriptive text after auditing. The optional `binderType` expression preserves the domain of a lambda or universal binder; for implication, it is the antecedent. Tree children are the authoritative representation of logical structure. The export is intended for conservative interpretation; it is not a proof certificate or a complete lossless serialization of Lean's internal expression type.

Binders can additionally carry optional `typeExpansion` and `structure` views. These preserve original types and names while exposing bounded checked aliases and direct fields/laws. The same field expressions provide shared identities inside supplementary law readings. Missing or omitted views do not invalidate the original statement. [The structure-reflection contract](structure-reflection.md) documents exact bounds, unknown-frontier behavior, and aggregate response trimming.

Encoded Lean constants additionally retain `levels: string[]`, in Lean's universe-argument order, with each level written as a symbolic Lean universe expression. For example, two `ULift` applications can have levels `["1", "0"]` and `["2", "0"]` even when their ordinary printed labels agree. Expression identity includes these levels; constructor recognition and display labels still use the constant name. The frontend field is optional for compatibility with older exports and synthesized logical heads; monomorphic constants export an empty array.

## Version 2 inputs and provenance

The request retains the original `source` and optional `requestId` fields. Additional options are:

```json
{
  "source": "∀ (X Y : Type) (f : X → Y), Function.Injective f",
  "inputMode": "term",
  "expansion": {"constants": ["Function.Injective"], "maxDepth": 2}
}
```

`inputMode` defaults to `term`. In `declaration` mode, `source` must be one exact imported declaration name, for example `Metric.mem_ball` or `Function.comp`. There is no substring search, theorem-name special case, source-file load, import command, or mutation of the imported environment.

- A theorem or axiom exposes its **statement type**, never its proof body.
- A general definition exposes its **typed signature** with `parameter` nodes and binder roles. For example, the arguments of `Function.comp` are parameters, not a claim that all functions have some property.
- A zero-argument proposition-valued definition exposes the named proposition. Explicit expansion can reveal its definition.
- A safe definition also exposes `definitionExpression` and `definitionTree` for its body when its internal expression is at most 1,500 nodes and depth 80. Otherwise both fields are `null`. The body tree uses `definition` as its root path. Outer lambda arguments become `parameter` nodes, after which proposition-valued bodies expose their quantifiers and connectives. For example, `Function.Injective` has parameters for its domain, codomain, and function, followed by the two universally bound inputs and the equality implication. Consumers may explicitly switch to this body tree while preserving the response’s original signature tree. `definitionBodyStatus` is `available`, `export-size-limit`, or `not-a-definition`. A lambda body is never silently converted into a universally quantified assertion.

`provenance` contains `assistant: "lean"`, `inputMode`, `inspected` (`statement`, `signature`, or `proposition-definition`), `mathlibRevision`, and either a declaration record or `null`. A declaration record contains `name`, `kind`, `type`, `module`, `canExpand`, and `universeParameters`. `module` is obtained from Lean’s imported environment, rather than inferred from the name. The record distinguishes theorems, definitions, axioms, opaque declarations, inductives, constructors, recursors, and quotient primitives.

The fixed imported environment is still a deliberate boundary: an otherwise valid name from an unimported mathlib module is unknown. Arbitrary imports are not accepted by this standalone worker. The separate editor adapter reads trusted project environments; partial elaboration recovery is not implemented. Generality here means a uniform typed representation for accepted mathematics, not a claim that every installed Lean project is currently accessible.

## Definition expansion

`definitions` lists safe imported definitions occurring in the original expression (at most 128), along with the inspected definition itself. Each uses the declaration record above. Constants found only in implicit instance arguments may appear; the visual planner must not confuse them with user objects.

`expansion.constants` accepts at most 12 exact definition names, each at most 512 bytes. `maxDepth` is an integer from 1 through 3, defaulting to 2. Unknown names, theorems, axioms, unsafe definitions, and partial definitions are rejected. Expansion is opt-in: ordinary processing does not globally reduce mathematical vocabulary to implementation details.

An expanded logical node retains `expansion` metadata:

```typescript
{
  constant: string;
  before: string;
  after: string;
  originalExpression: Expr;
  definitionalEquality: true;
  depth: number;
}
```

Unfolding uses Lean’s definition unfolding operation, followed by a kernel type check and definitional-equality check. Context and binder identities remain scoped under the node. `tree` and `expression` contain the selected expansion; `originalExpression` at response level preserves the original unexpanded input with its own path-based binder identities. `expansionPolicy` echoes the exact selected names and depth. Expansion currently acts at the head of logical nodes, not arbitrarily deep inside every arithmetic or type argument.

## General typed objects and argument roles

Binders, variables, constants, and applications carry optional `typeDescriptor` metadata. This is derived from typed Lean expressions, not labels or theorem names:

```typescript
interface TypeDescriptor {
  kind: 'real' | 'natural' | 'integer' | 'rational' | 'finite' |
    'type' | 'set' | 'map' | 'relation' | 'proposition' | 'structure' | 'unknown';
  lean: string;
  head?: string;
  cardinality?: number;
  dimension?: number;
  numericalDomain?: string;
  element?: TypeDescriptor;
  domain?: TypeDescriptor;
  codomain?: TypeDescriptor;
  dependent?: boolean;
}
```

`Set X` retains its element type. Maps retain domain/codomain and whether the codomain depends on the argument. Curried predicates retain the chain of argument types as relations. Other named types remain `structure` with their exact type head, and abstract local types remain `unknown`. This descriptor is bounded to six recursive layers. It does not imply that a structure has a geometric realization.

Applications additionally include `argumentKinds`, aligned one-for-one with `args`: `type`, `instance`, `proof`, or `value`. Display adapters can hide implementation arguments without discarding their role in the typed expression. Logical nodes include `scope`, an ordered list of the binder identities in scope before the node. Existing `binderType` expression fields preserve the complete exported domain of a binder.

The declarative syntax allowlist now includes composition, subsets, set unions/intersections, complements/differences, empty sets, and typed set builders from the trusted imported library. Their nested contents remain subject to the same syntax walk. This does not enable arbitrary macros, tactics, commands, or custom elaborators supplied by a client.

## Exact source occurrences

`sourceTerms` contains up to 512 deduplicated occurrences emitted by Lean’s InfoTree:

```typescript
{
  startByte: number;
  endByte: number;
  lean: string;
  type: string;
  isBinder: boolean;
  origin: 'lean-infotree';
}
```

Ranges are half-open **UTF-8 byte offsets** into `source`; JavaScript consumers must convert them before using UTF-16 string selection APIs. Only canonical source ranges with instantiated, non-placeholder expressions are exported. Each occurrence is pretty-printed in its original local context. Nested occurrences can overlap. Declaration lookup has no term-elaboration source occurrences and returns an empty array.

These records are exact source-to-typed-term evidence. They are deliberately not guessed source spans on expanded or reconstructed logical nodes: notation can create several semantic nodes, and definition expansion can create nodes absent from the source. A future editor adapter should use InfoTree expression/context identities to connect those transformations precisely.

## Metric and arithmetic interpretation

Geometry is identified from elaborated constants, not source text or notation. The current geometric constants are `Metric.ball`, `Metric.closedBall`, `Metric.sphere`, and `Dist.dist`.

| Lean domain | Recognized standard metric |
| --- | --- |
| `ℝ` | Absolute-value distance |
| `ℝ × ℝ` | Maximum/product distance: square balls |
| `EuclideanSpace ℝ (Fin n)` | Euclidean/L2 distance |
| `Fin n → ℝ` | Maximum/supremum distance |

Literal finite dimensions are read directly from the elaborated `Fin n` type, including dimensions beyond 12. Renderer capability may be narrower; unsupported dimensions remain typed but do not receive an invented projection. A Euclidean sphere in ambient dimension four is an intrinsic three-sphere. A coordinate slice is explicitly a slice, not the whole sphere and not a Hopf fibration.

A type name alone is insufficient to identify a metric. For numerical applications, the worker synthesizes the canonical imported typeclass instances in an **empty local context** and checks definitional equality with the actual class arguments. Canonical set-operation instance constructors are additionally recognized by exact typed constant identity: their meaning is parametric in an abstract element type. A local replacement set instance is still rejected by this audit. A supplied custom or abstract instance gets `standard: false`; a metric application then gets `metric: "unknown"`. The same audit protects overloaded arithmetic from being interpreted as ordinary real operations when its instance has been replaced. Recognition in the browser additionally restricts operator names and numerical domains.

A statement may mix supported geometry with abstract types, higher-order conditions, or unrecognized predicates. The full accepted statement is type-checked, while supported fragments can be selected independently. An incomplete or ill-typed input is rejected as a whole. This release does not recover plots from a statement that Lean cannot elaborate.

## Editor and Rocq adapter direction

Lean’s [InfoTree API](https://lean-lang.org/doc/api/Lean/Elab/InfoTree/Types.html) stores elaborated terms, local contexts, and source syntax. The current [editor adapter](editor-integration.md) extracts the same v2 representation from the active document’s environment in an isolated sidecar process. Direct integration with the editor’s existing Lean server remains future work. [Lean RPC](https://lean-lang.org/doc/api/Lean/Server/Rpc/Basic.html) provides session-relative references for heavy server objects. [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) provides React components and Lean widget integration. These are suitable foundations for an infoview panel; they do not supply the mathematical abstraction and view-selection semantics of this project.

A Rocq adapter is architecturally feasible at the typed semantic-document boundary, but is not implemented. [Rocq LSP](https://github.com/rocq-community/rocq-lsp) supplies document checking and tooling interfaces built on Flèche. Its kernel terms, universes, coercions, modules, and local contexts differ from Lean’s; a separate extractor and validation suite would be necessary. Sharing renderers and view contracts is plausible; reusing the Lean parser or pretending the two expression formats are interchangeable is not.

## Upstream references

- [Lean 4.28 parser implementation](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Parser/Extension.lean)
- [Lean 4.28 term elaboration](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/Term/TermElabM.lean)
- [Lean 4.28 kernel-check wrapper](https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Meta/Check.lean)
- [Pinned mathlib metric definitions](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean)
- [Pinned mathlib cache command](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Cache/Main.lean)

Developed by Codex under the supervision of Neil Yuanting Li.

## Optional readable mathematical notation

`readableMath` describes the original elaborated expression; `definitionReadableMath` describes an available bounded definition body separately. Each has `provider: "leantex"`, a `status` of `rendered` or `unavailable`, and either `latex` or a fallback `reason`. These are optional response fields; the typed semantic data remains authoritative.

A pinned LeanTeX source subset and a small display adapter are built into this repository's ignored `.local/leantex/` directory. The worker dynamically imports that fixed adapter once, then calls its exact trusted declaration. Clients cannot choose an entry point, module, printer, or command. Pretty printing is bounded, restores its local state, and runs after required semantic extraction. If optional notation would exceed the aggregate response limit, the serializer removes it while preserving mandatory fields and request identity. The browser uses local KaTeX with external links, images, and arbitrary HTML disabled.

See [LeanTeX integration](leantex-integration.md) for the upstream revision, compatibility patch, resource limits, and tests. This adds no Mathlib imports or changes to existing formal projects.
