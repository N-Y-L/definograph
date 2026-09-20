# Statement-first reading review

This review concerns what a reader sees first. The native Lean exporter and semantic document already retain the relevant logical information. Ranking one geometric or relational fragment above the surrounding statement can nevertheless hide the meaning the reader came to understand.

The findings below were reproduced against the pinned native Lean worker and the previous `planViews` first-view composition. They use general mathematical constructions rather than named theorem demonstrations.

## Five concrete failures

### 1. A ball does not communicate witness order

```lean
∀ c : ℝ, ∃ p : ℝ, p ∈ Metric.ball c 1
```

```lean
∃ p : ℝ, ∀ c : ℝ, p ∈ Metric.ball c 1
```

Both opened an **Open ball in 1D** as their primary view. Its node was the membership leaf in both cases. The typed documents correctly distinguish the dependency: the first witness may depend on `c`, while the second is chosen before `c`. A picture of one ball and one point cannot carry that distinction by itself.

Acceptance: the first composition visibly reads “for every `c`, there exists `p`,” and the second “there exists `p`, for every `c`.” Each point-in-ball diagram belongs inside that quantified statement. A representative point must not replace the quantified claim or be treated as a witness proof. Quantifier groups may combine adjacent binders of the same kind; they must not reorder them or cross a branch.

### 2. Positive geometry inside a negation loses the outer assertion

```lean
∀ x : ℝ, ¬ (x ∈ Metric.ball 0 1)
```

The old first view was again **Open ball in 1D**, built from the positive membership leaf. The negation survived as a context tag and in an alternate structure view. That is useful metadata, but it makes the reader reconstruct the actual assertion around the picture.

Acceptance: the negation must structurally contain the membership condition in the initial composition. Selecting the condition retains the enclosing negation. The same rule applies to `¬ ∃ x, P x`: its existential is not an unqualified invitation to find a witness. The model must retain the negated edge, even if a renderer later uses an exterior region or another specialized depiction.

### 3. Showing the consequence alone hides an implication

```lean
∀ x : ℝ, x ∈ Metric.ball 0 1 → x ∈ Metric.ball 0 2
```

The old primary view selected the radius-two ball in the consequent. Its primary node list contained only that consequent leaf. The statement is about a condition implying another condition, so both regions and the implication are essential to reading it.

Acceptance: the premise and conclusion occupy distinct roles in one composition, with their shared `x` preserved. The premise is an assumption of the consequent, not an independently asserted fact. Its proof binder is unavailable while reading the premise itself and must not leak into a sibling conjunction or disjunction branch. Selecting either side retains the implication envelope.

### 4. A list of relations is not a disjunction

```lean
∀ x : ℝ, x < 0 ∨ x > 1
```

The old first view was **Connected objects**, containing two inequality cards. Branch labels were present, but the composition still made the user assemble the “either/or” relation between cards. The same visual list could easily be mistaken for two simultaneous requirements.

Acceptance: both children remain under an explicit disjunction, with alternative edge roles. A conjunction must instead communicate that both conditions belong together. An equivalence must expose both directions with exchanged premise and conclusion roles; it must not be rendered as equality or as two independently assumed facts. Separate branches retain separate binder groups and assumptions.

### 5. A graph of one side is not an equality of functions

```lean
∀ f : ℝ → ℝ, f = (fun x : ℝ => x * x)
```

The old primary view was **Graph in x**, sampling the quadratic lambda. The equality relation and the universally quantified `f` existed in the semantic document but were outside the primary picture. A graph of the right side alone omits what is being stated about `f`.

Acceptance: the equality remains the atomic clause, with `f` and the lambda as its two arguments. Any graph is attached to the appropriate argument as a supporting representation. The lambda’s input has its own local scope. Relations inside a lambda body must not become unconditional neighbors of the outer equality or predicate.

## Product decision: a visual sequence first

The default experience is a **visual sequence in the statement’s reading order**, with an overview alongside it. The sequence explains what is introduced, what is assumed, how alternatives or conditions are nested, and what relation is stated next. An integrated diagram can support that sequence; it is not automatically the primary experience.

Relationships shown by default must be supported by the typed source and its logical context. Here “supported” means the source actually contains that relationship in that position; it does not mean that the application has proved the proposition. Concrete examples, coordinates, sliders, and samples belong to secondary exploration. They must not be prerequisites for reading an abstract statement.

Coordinate-free mathematics is a primary case. Arbitrary carriers, functions, relations, and dependent morphism families can receive a typed visual sequence without a numerical model. The acceptance suite includes composition of functions between arbitrary types and an associativity *condition* on a declared family `Hom : Obj → Obj → Type`. That condition is not supplied with a proof, and the renderer must not invent categorical laws, inverses, injectivity, or cardinalities.

The fixed worker imports currently do not include mathlib’s `CategoryTheory` modules, so a declaration such as `CategoryTheory.Category` is not available through this worker merely because its source exists elsewhere in mathlib. That is an import/environment integration limitation. It is not a geometric limitation of category theory or a requirement that abstract objects acquire coordinates. No category-specific substitute definitions were added to the worker.

## Invariants for the reading model

The new `compileReading` contract is a composition of the statement, not a winner selected from its fragments:

- Every Lean statement node appears once in source preorder and retains its identity, kind, children, and immediate parent.
- Every atomic leaf has a reading panel, including opaque, abstract, and only partially interpreted mathematics. Semantic coverage and logical coverage are separate facts.
- Child edges distinguish quantified bodies, assumptions, conclusions, conjuncts, alternatives, equivalence sides, negation, and definition results.
- Relation groups are restricted to one clause and one expression scope. Shared-object connections cannot transfer a relation from a lambda, branch, or hypothesis into another scope.
- Selection highlights a part of the statement without removing other nodes or panels. Its ancestor chain, available objects, and local assumptions remain inspectable.
- A declaration signature has parameters rather than universal claims. A definition body has parameter binders around its result; quantifiers inside a proposition-valued result remain distinct from those parameters.
- No sampled scenario is required to construct a reading. Numerical exploration may supplement the reading; it cannot establish its quantified assertions.

These are representation checks, not proofs of the submitted statements. False propositions remain valid inputs for reading, as they are for Lean type checking.

## Native acceptance suite

`scripts/reading-integration.ts` runs the actual local worker, compiles the semantic document, and then compiles the reading. It checks the five cases above together with general connective combinations, branch-local hypotheses, local lambda relations, unsupported topology, arbitrary typed relations, coordinate-free composition, dependent morphism families, imported signatures, and definition bodies. It also verifies that selecting a fragment preserves the complete logical envelope and that a definition body never mutates the original signature.

Developed by Codex under the supervision of Neil Yuanting Li.
