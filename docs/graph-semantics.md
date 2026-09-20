# Graph and coloring constraints

The graph grammar interprets canonical Mathlib simple-graph definitions. It is not a collection of named-theorem demonstrations and it does not invent a finite graph from a quantified statement.

The pinned dependency is Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` with Lean 4.28.0. The fixed worker imports `Mathlib.Combinatorics.SimpleGraph.Coloring`; setup fetches that module's cache closure into the isolated project cache. Editor requests use the selected project's own built imports.

## Meaning and ports

| Lean construction | Semantic kind | Exact ports | Meaning |
| --- | --- | --- | --- |
| `G.Adj u v` | `graph-adjacency` | graph, left vertex, right vertex | Symmetric, irreflexive adjacency in this graph, within the surrounding logical context. |
| `G.Colorable n` | `graph-colorable` | graph, color bound | Existence of a proper coloring into `Fin n`: at most `n` available colors. No coloring is supplied. |
| `c : G.Coloring C` | `graph-coloring` | graph, coloring, colors | The introduced bundled map sends adjacent vertices to different colors. |
| `c u` for that coloring | `graph-coloring` | graph, coloring, colors, vertex, color | Application of the audited bundled map; the color port is this exact application expression. |
| `f : SimpleGraph.Hom G H` | `graph-map` | source graph, target graph, map | Adjacency is preserved. Injectivity, surjectivity, and reflection of adjacency do not follow. |
| `f : SimpleGraph.Embedding G H` | `graph-map` | source graph, target graph, map | An injective map preserving and reflecting adjacency; its image is an induced subgraph. |
| `f u` for either map | `graph-map` | above, source vertex, target vertex | The exact vertex and its image under the audited bundled map. |

Graph-map metadata distinguishes `graphMapKind: 'homomorphism' | 'embedding'`. A coloring type alone never fabricates a coloring object. The compiler calls `graphBinderSemantics` only for an actual introduced value, with the exact exported binder type and lexical scope. Universal and existential introductions retain their original roles. A coloring in one alternative cannot supply a witness to another alternative.

The graph constraint figure is schematic. Vertex slots are not an enumeration of the graph and spatial distance has no meaning. Actual repeated endpoints retain one mathematical identity. Negations, antecedents, and alternatives remain attached to their clauses. `Colorable 0` does not make the statement impossible without an additional nonempty-vertex hypothesis: an empty graph can have an empty palette. A finite palette describes available labels, never the number of colors actually used.

## Native audit

The graph plugin requires `canonical: true`, the exact number and kinds of application arguments, and a suitable native result descriptor. These signatures are audited:

- `SimpleGraph.Adj`: `[type, value, value, value]`, result `Prop`.
- `SimpleGraph.Colorable`: `[type, value, value]`, result `Prop`.
- `SimpleGraph.Coloring`: `[type, value, type]`, a type constructor.
- `SimpleGraph.Hom` / `SimpleGraph.Embedding`: `[type, type, value, value]`, type constructors.
- `DFunLike.coe`: `[type, type, value, instance, value, value]` for an applied bundled map.

The last case also requires `standard: true`: native export recognizes the exact imported `RelHom.instFunLike` or `RelEmbedding.instFunLike` constructor and its four parameters. A local or global replacement instance remains untrusted even if it is definitionally equivalent to the canonical instance. Printed instance names are never parsed. Native natural-number literals additionally audit `instOfNatNat`; this permits exact finite color bounds without enabling an unaudited real metric or arithmetic environment.

Editor canonical provenance is checked against exact defining modules: `SimpleGraph`/`Adj` in `Mathlib.Combinatorics.SimpleGraph.Basic`; graph map types in `.Maps`; coloring/colorability in `.Coloring`; bundled map instances in `Mathlib.Order.RelIso.Basic`; and the coercion projection in `Mathlib.Data.FunLike.Basic`. Project definitions with matching names stay opaque. This is a semantic audit for trusted compiled imports, not a signature-verification system for hostile module files.

Current boundaries include direct `RelHom.toFun` projections, reducible aliases hiding the recognized bundle type, graph isomorphisms, multigraphs, directed graphs, and graph enumerations supplied by executable computation. Their typed structure remains available; none is silently promoted to the supported graph grammar. A partial `G.Adj u`, `G.Colorable`, or coerced coloring function without a vertex is not a fully applied graph relation.

## General examples

```lean
∀ (V C : Type) (G : SimpleGraph V) (c : G.Coloring C) (u v : V),
  G.Adj u v → c u ≠ c v

∀ (V : Type) (G : SimpleGraph V) (n : Nat), G.Colorable n

∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W)
  (f : SimpleGraph.Hom G H) (u v : V),
  G.Adj u v → H.Adj (f u) (f v)
```

`src/graphs/semantics.test.ts` covers constructor shape, identity, saturation, coercion replacement, witness creation, and map-kind boundaries. `scripts/graph-integration.ts` checks real native exports through semantic compilation and graph models, including abstract/finite/zero palettes, quantifier and branch scopes, editor canonical provenance, and fake definitions.

The source definitions are the authority: [simple graphs](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Basic.lean), [graph maps](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Maps.lean), and [proper colorings](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Combinatorics/SimpleGraph/Coloring.lean).
