# Semantic document and representation planning

The browser consumes a versioned semantic document rather than selecting the first recognized plot. The initial implementation is in `src/semantic`, with a Lean adapter and representation-independent objects, scoped relations, and provenance. Rocq is a reserved prover identifier; no Rocq adapter is implemented.

```ts
const document = compileSemanticDocument(analysis);
const plan = planViews(document, { selectedNodeId, maxDetailedViews: 4 });
```

`maxDetailedViews` limits numerical and function scene cards. It does not remove semantic relations, source fragments, or scoped choices from the document. Generic maps and choice views remain available alongside the highest-ranked concrete representation. The UI explicitly reports any overview display limits.

## Meaning and identity

- Bound-variable identities use introduction order, not printed variable names. Shadowed names remain distinct. One object is shared across fragments that refer to the same bound variable.
- Compound identities use expression structure and audited metric/operator metadata. Instances are retained in identity because changing an instance can change mathematical meaning. Hidden type, instance, and proof arguments are omitted from visual ports when the prover supplies their argument kinds.
- Every relationship retains its original expression, source node, and expression occurrence path. Presentation labels are never used to decide numerical meaning.
- Relations belong to lexical scopes. Implication hypotheses become available only in the consequent. Disjunction branches do not exchange choices. Lambda inputs have local body scopes.
- Witness dependencies refer to semantic object IDs. They state what a candidate may depend on, not that a witness exists. Definition parameters are distinct from universal quantifiers.

Compound identities are stable for the exported expression structure; opaque prover text can affect an identity when the prover does not expose that structure. This is not an alpha-equivalence decision procedure for arbitrary dependent Lean expressions.

## Recognition and coverage

`createSemanticRegistry` accepts explicit versioned rules with declared capabilities and limitations. Built-in rules recognize audited set membership and inclusion, images and preimages, mappings and abstract relations, equality, audited comparisons, and metric regions. They match elaborated constructors and audited instances, never theorem titles.

Generic applications always retain argument links. An unknown definition produces an `OpaqueRegion`; recognized children remain available, and fragment coverage becomes `partial`. A fragment without a semantic interpretation remains `structural`. `interpreted` means the exported relationship has a supported symbolic interpretation, not that its truth has been established or that all its objects have numerical models.

The compiler consumes the currently inspected statement, declaration-signature tree, or definition-body tree. A declaration can offer both a signature and a bounded body; the UI selects one tree at a time and resets its selection and scenario. Definition-body lambda parameters remain function parameters; propositions inside the body retain their own logical binders. Explicit kernel-checked unfolding is consumed through the same tree contract.

## Automatic representation selection

`representationCapabilities` declares each view's requirements, preserved information, omitted information, fidelity, and base score. Ranking additionally considers fragment selection, shared objects, and relation coverage. The selection is deterministic and favors direct audited geometry when available; it is a heuristic, not a claim of universal perceptual optimality.

Every plan retains a generic structure view. Metric instances and dimension checks remain prerequisites for numerical geometry. Unsupported metrics receive symbolic region diagrams. Higher-dimensional objects offer an all-coordinate distance profile when a point is available, and adjustable coordinate slices. A slice keeps its ambient dimension and slice condition visible; it does not project off-slice points onto the drawing.

The semantic compiler never evaluates proof terms or modifies a prover environment. Numerical sampling uses the existing audited evaluator, retains expressions at full exported fidelity, and does not establish universal or existential statements.

## Regression evidence

Semantic tests cover bound-variable alpha-renaming, shadowing, conjunction regrouping, application association in identity, metric-instance distinctions, custom-instance refusal, inherited assumptions, sibling branch isolation, lambda scopes, unknown parents with recognized children, higher-order partial constructors, universe labels, source selection, large literal retention, and deterministic automatic ranking. Native integration tests exercise the actual Lean exporter and semantic compiler together.
