# Atlas iteration: semantic review and validation

This iteration groups the visual reading into logical regions and adds typed constructions for arbitrary mathematical objects. Its purpose is to make the statement easier to read while preserving the distinctions already present in Lean's elaborated tree. It does not change a statement into a collection of independently asserted pictures.

## Reviewed boundaries

The presentation planner operates after the semantic and reading documents. It groups only adjacent binders of the same kind and direct, right-associated implication chains. Every original node retains an exact source-node association. A quantifier, disjunction, equivalence, negation, or implication inside an antecedent stops the relevant grouping. Selection changes emphasis without rewriting or dropping the statement.

Typed constructions use exported binder type expressions and variable identities. Ordinary unary maps may share carrier vertices. Curried functions retain ordered inputs; type families and dependent outputs retain their dependence rather than receiving an invented fixed codomain. Identically spelled names in sibling branches do not become the same object. Invalid groups that cross logical scopes are rejected.

The default atlas supplies no numerical inputs or coordinates. A membership diagram is attached to its complete clause, with the surrounding implication, alternative, or negation retained. Recognizing a geometric subexpression inside an unknown predicate must not replace that enclosing predicate with a membership assertion.

## Findings addressed in this iteration

- Natural dependent arrow syntax, such as `(a : A) → B a`, was absent from the worker's declarative syntax allowlist. Adding `Lean.Parser.Term.depArrow` lets the existing elaborator and kernel handle that syntax. A native regression compares it with the equivalent `∀ a : A, B a`; their exported expression identities and construction models agree. The original command, tactic, quotation, and placeholder rejection tests remain in force.
- The earlier display budget truncated the list of ancestors to protect. The atlas now protects the entire selected ancestor path, allowing the visible-node count to exceed the normal budget when necessary. A 120-level negation fixture verifies that a selected deep clause remains reachable inside its logical envelope.
- Compact scalar constraints need the same source-node associations as full figures. The integration checks require every atomic clause to remain identifiable before and after selection, regardless of its visual size.
- Proposition-valued arguments, such as the membership condition in `F (x ∈ Metric.ball 0 1)` for `F : Prop → Prop`, were incorrectly filtered with ordinary type arguments. They now survive application traversal based on their exported proposition type, including quantified propositions. The enclosing predicate remains the root claim, and recognized children remain contained expression parts. Ordinary implicit types, instances, and proof arguments are still excluded from displayed input ports; their original expressions remain available.
- Constant identities now retain Lean's universe instantiations. Display labels and constructor recognition stay unchanged, while differently instantiated polymorphic constants no longer collapse into one structural identity.

## Integration checks

`scripts/atlas-integration.ts` sends declarative fixtures to the real native Lean worker, compiles semantic and reading documents, plans the atlas, checks typed constructions, and renders the actual React reader to static markup. Vite transforms TSX and CSS in process with file watching, HMR, and WebSocket listeners disabled; no browser or network listener is required.

The completed suite passes **21/21 checks** against the rebuilt Lean 4.28 worker. Its standalone strict TypeScript check also passes. Run it with `npm run test:atlas`; it is included in `npm run check`.

The checks cover:

- `∀`/`∃` order and permitted witness dependencies.
- Nested antecedents, successive assumptions, intervening binders, alternatives, negation, and both directions of an equivalence.
- Exact source-node coverage under presentation grouping and selection.
- Shared carriers and ordered map composition over arbitrary types.
- Dependent families, dependent outputs, relations, and curried functions.
- Distinct universe instantiations of identically printed carrier types.
- Same-named binders in separate branches and rejection of cross-branch construction groups.
- Unknown enclosing predicates and locally bound expressions.
- Partially applied constructors without fabricated geometric objects.
- Declaration signatures versus parameterized definition bodies.
- Alpha-renaming invariance and deep selected-context visibility.

Static rendering validates semantic associations and rendered content. Browser checks remain necessary for layout, scrolling, focus behavior, drawer operation, and responsive dimensions; this script does not claim to establish those properties.

Implementation and review: Codex under the supervision of Neil Yuanting Li.
