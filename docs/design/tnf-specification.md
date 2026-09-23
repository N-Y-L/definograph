**Status: round-1 design specification, amended by the [architecture decision](architecture-decision.md), which takes precedence wherever the two differ. Nothing here is implemented.**

# Definograph: a compositional architecture

**Telescope Normal Form with a bounded frame algebra** — round-1 specification, after adversarial review.

Three critiques (unpublished; the bracketed tags in §8 cite their points) were run against the synthesis, the draft that merged round 1's four architectures. Nine of their findings were fatal to specific mechanisms and forced design changes; the rest are accepted limits or refuted below. §8 dispositions every point. Line numbers refer to this repository at commit `62259ef`.

---

## 0. What the review changed

The architecture survives. Five of its load-bearing mechanisms did not survive in the form proposed:

1. **The generator-table key was not finite.** All three critiques found this independently. Fixed in §3.4 by keying on *unary* frame cells (which the κ-monoid already provides) rather than on whole telescopes, and by replacing the unbounded "fusion pattern" with a bounded **binder valence**.
2. **Fixture 1 was a tautology.** `∀ S T, S ⊆ T → ∀ x, x ∈ S → x ∈ T` unfolds premise and conclusion to the same term up to binder name; `expressionKey` is alpha-invariant (`src/semantic/expression.ts:99`, binders keyed `` `local:${level}` ``), so A5 merges them. The flagship demonstration demonstrated nothing. Replaced in §5.2.
3. **`⊗` was not associative as constraint *sets*** — the same error the synthesis correctly diagnosed in `Sep`. Fixed by quotienting anchors (§3.2), which in turn forces `≡` to be a single equivalence relation (`expressionKey` equality), not `isDefEq`.
4. **The decoration/topology wall was drawn in the wrong place.** §3.4's own worked example had a "decoration" (type shape) feeding a containment constraint. The line moves in §4: **port kind is meaning; glyph is presentation.**
5. **Two growth channels were uncounted** — δ-hints and decorations, both name-keyed, neither in $\mathcal{B}$ nor under the name-blindness grep. Fixed in §5.3.

Plus: the F4 universe demotion is **withdrawn** (its own argument refuted it — see §8, S12/B7); `Q = \mathrm{mode}\oplus\pi` is **restricted** to its constructively valid half; instantiation **never** discharges; and the first slice **shrinks** by roughly half on the buildability critique's three cuts.

The architectural objection that motivated this work remains correct, and the repository still confirms it quantitatively: `RelationKind` is a flat 19-member union (`src/semantic/types.ts:23`) with five per-domain optional fields (`:41-45`, `:107-111`); `RelationFigure` is an 11-arm dispatch emitting ~190 absolute coordinates into a fixed `viewBox="0 0 500 230"` (`src/visual/StatementReadingView.tsx:98-153`, `:152`). Two sets grow together — vocabulary and pictures. **This architecture closes the picture set and leaves the vocabulary open.**

---

## 1. What qualifies as a Fundamental Object

An FO is not a mathematical object. It is a **former**: a node shape in a normalized term language with a typed port interface and a frame that emits constraints. `Metric.ball` is not a candidate; it is a term.

Let $\rho(\Phi)$ be the facts a reader extracts from a fragment with zero inference. **$\rho$ is computed from the port graph** — fusion classes, frame containment, wire chains — not from the rendered drawing. (The synthesis defined it both ways, which made F3 circular; this pins it.)

### The six tests

**F1 — Name-blindness.** The recognizer may read the kernel constructor, typing/sort judgements, and binder-occurrence relations. Never a constant's spelling or module path. Formally $F(\nu(e)) = F(\nu(\sigma e))$ for type-preserving renamings $\sigma$.

*Kills:* `canonicalModule` (`lean/StatementLens/Export.lean:71-102`), a ~60-name array which via `canonicalConstant` (`:104-109`) gates `tree`'s recognition of `And`/`Or`/`Iff`/`Not` (`:504`, `:516`). In project-context mode unlisted constants return `false`, so on the editor path unlisted mathematics is architecturally uninterpretable. Also kills every `graph-*`/`restricted-*` member of `RelationKind`.

**F2 — Shape-definability.** `∧,∨,∃,=,⊤,⊥` are names, yet must be admitted. They are admitted by an **environment shape query**: type sort, constructor count, constructor field sorts and arity, index count. `And` = Prop-valued, one constructor, two Prop fields, no indices ⇒ binary meet. `Or` = two constructors, one Prop field each ⇒ join. `Exists` = one constructor, one Type field + one dependent Prop field ⇒ Σ-in-Prop.

**Extended on review:** `Not` is `def Not a := a → False` — *not* an inductive, so the original F2 could not reach it, and it generates every $\varepsilon=1$ in the polarity algebra. F2 therefore queries the shape of the constant's **whnf after one kernel-checked δ step**, not only `inductInfo`. `Not a` reduces to `Tel(Π, Prop, o{=}0)` over `⊥`; `Ne` likewise. Still name-blind, one extra `whnf`.

**F3 — Irredundancy (rejection test).** Remove $F$; re-run the normalizer on its defining term; if it decomposes totally *with the same $\rho$*, reject as derivable. **Demoted on review from a decision procedure to a rejection filter**: six of the eight formers (`Tel`, `App`, `Struct`, `Atom`, `Sort`, `Fold`) have no defining term — they are kernel constructors or pipeline artifacts — so F3 cannot *admit* them. Its teeth are real and they are all on the rejection side.

**F4 — Finite index.** $F$'s variants must be indexed by $\iota: \mathrm{dom}(F)\to I$ with $I$ finite and computed from typing judgements, bounded independently of the library.

**Corrected.** The synthesis claimed $|I_{\mathsf{Tel}}| = 18$. That is the index of *one binder*; `Tel` carries a per-binder vector and a dependency matrix $D\in\{0,1\}^{n\times n}$, giving $6^n 2^{n^2}$ — unbounded in statement size, which is worse than unbounded in library size. The repair is forced by the κ-monoid the architecture already has: **an $n$-binder telescope is a word of $n$ unary frames**, so the *generator* table keys on the unary cell (18) and $D$ is realized by **port fusion**, not by a table entry. Nothing reads the matrix.

Consequently the universe demotion is **withdrawn**. Within one statement the distinct levels present are finite, so the level-equality pattern is a finite index bounded by binder count — exactly like $D$. Keeping levels also preserves `AGENTS.md:17` ("preserve … universe distinctions") and avoids a genuine unsoundness: `expressionKey` includes levels (`expression.ts:89`), so dropping them would **fuse `Set.{0}` with `Set.{1}`** — an asserted identity between distinct objects, violating A5 and F6.

**F5 — Port-locality and no own canvas.** Ports are holes: the recognizer never inspects below a port. The former supplies typed anchors and emits **constraints only** — no coordinate, no `viewBox`.

*Kills every branch of `RelationFigure`*: membership inspects `producedBy(element)` (`:107`), subset inspects for an `image` head (`:114`), equality inspects `expressionMapPath` (`:129`). Each reaches below a port, which is precisely why they cannot nest; each returns its own `<svg viewBox=…>` (`:152`), which is why a clause can only CSS-stack three of them (`:206`).

**A candidate that fails F5 is rejected, full stop.** There is no composite-matching rule layer. This is the line to hold.

**F6 — Discharged surplus.** $\Sigma(F) = \rho(V_F)\setminus\llbracket F\rrbracket$ must be empty after conventions from a **closed** list: open-world exterior, shading, non-committal boundary, explicit fold marker, schematic placement, and — **added on review** — *coincident-boundary containment*. A caption is not a discharge. The repository currently discharges in prose: `StatementReadingView.tsx:118` reads *"The sets may be equal; spacing does not express proper inclusion"* while `:115` draws a strictly smaller region inside a larger one. The review showed the synthesis's replacement had the same defect — a slack `Contain` constraint draws a visible annulus reading "$T\setminus S\neq\emptyset$". Hence the new discharge glyph, and it is emitted, not narrated.

### The eight formers

`Tel` (dependent telescope: mode $\Pi/\lambda/\Sigma$, sort class, occurrence bit, dependency matrix) · `Junct` (finite meet/join in Prop; **negation is not a member** — it normalizes to `Tel` over `⊥`) · `Ident` · `App` (spine with typed argument roles, already exported at `Export.lean:243-246`) · `Struct` (limit cone) · `Atom` (content-addressed leaf) · `Sort` · `Fold` (typed opacity carrying reason, polarity, and recovered interior).

**Two disambiguations forced by review.** `And` and `Iff` are Lean 4 `structure`s with projections, so they match both `Junct` and `Struct`. N3's precedence: **`Junct` wins iff every field is Prop-sorted; `Struct` wins iff at least one field is Type-sorted.** The critique objected that this erases a user's Prop-valued record. It does, and correctly: Prop is proof-irrelevant, so the joint-monicity content of a Prop-only cone is vacuous — `structure Bounded : Prop where lo; hi` *is* `lo ∧ hi`. The record name survives as a fold label. `Subtype`/`Sigma` have data fields and go to `Struct`.

**Not FOs:** `Metric.ball` (fails F1 and F3 — it is `Tel∘App∘Ident` once `Set` and the comprehension unfold; currently a hardcoded hook at `Export.lean:257-260` plus an ~86-literal bespoke figure). `SimpleGraph.Adj` (fails F1; F2 explicitly *refuses* it, since no shape query separates it from any binary relation — the correct outcome). Proper colouring, subset, membership, image, preimage. A **dependent-family former** — rejected by F3, which dissolves the invented notation two panel proposals conceded had no prior art; the reading survives as a free ride from the port graph.

---

## 2. Decomposition

**Normalization $\nu$** (Telescope Normal Form), six passes in fixed order: N1 telescoping (generalizing `src/constructions/model.ts:132-147`, which already walks a forall-chain deriving per-input dependency indices and classifies `relation`/`family`/`dependent-map` **entirely from typing, no names** — the strongest existing evidence that a general approach works); N2 polarity stamping; N3 Prop-inductive classification via F2, with the `Junct`/`Struct` precedence above — **names are discarded here and nothing downstream sees them**; N4 spine/projection normalization (already `Export.lean:262-265`); N5 instance demotion to typed witnesses; N6 folding.

**Every rewrite is certified.** $\delta_c$ by `unfoldDefinition? (ignoreTransparency := true)` + `checkWithKernel` + `isDefEq` (`Export.lean:293, 297-298, 468, 471-472`); $\sigma_S$ by `getStructureInfo?` + `mkProjection` + kernel check + the client's re-validation that a field expression really is $\text{projection}(\text{owner})$ (`src/decomposition/reflection.ts:79-80`). Soundness is structural and holds *before* any scoring.

**Admissibility (hard constraints).**

- **A1 Seal.** A port escapes $\llbracket\cdot\rrbracket_\kappa$ iff $\mathrm{FV}(t)\cap\Delta_\kappa=\emptyset$. One rule replacing three; already enforced at runtime (`src/semantic/compiler.ts:94-98, 133-141, 159-165`) and asserted with throws at `src/reading/cues.ts:124, 148`.
- **A2 Skolem faithfulness — corrected.** The synthesis required the drawn dependency set to equal the scope prefix $\{x_j : j<i,\ Q(x_j)=\forall\}$. That is the Skolemization *upper bound*, not the dependency: for `∀ n, ∃ y, y = 0` it draws an edge $n\to y$ the statement does not license — a direct F6 violation, making A2 and A3 jointly unsatisfiable on most existentials. **A2 now intersects with free-variable occurrence.** The repository contains both computations: the wrong one for binders (`Export.lean:178` — all preceding non-assumption binders, no occurrence test) and the right one for structure fields (`:376-377` — `fieldType.find? (· == expression)`). Fix `:178` to match `:376-377`. Where the occurrence set is a proper subset of the scope prefix, *that* is a free ride worth drawing.
- **A3 — rescoped.** The synthesis required every induced reading to lie in $\mathrm{Cn}(e_0)$, the deductive closure. Deciding that is theorem proving, which §7 concedes the system cannot do. A3 is now: every fired generator declares its induced readings, and a **post-solve audit over an enumerated geometric predicate set** (zone nesting, overlap, shading, boundary crossing, relative area, annulus) finds no undeclared one. This is what AC9 actually checks. Consequently the $\lambda_1$ "unintended assertion" term is **dropped from $J$** — under a hard constraint it was identically zero on the admissible set.
- **A4** budget closure · **A5** identity coherence (content-addressed store, `expression.ts:80-114` + `compiler.ts:70-85` including the full-key collision loop at `:75`) · **A6** renaming equivariance · **A7** realizability.

**δ-policy is not a name list.** Candidates are produced by querying the environment for heads actually present — `isDefinition ∧ ¬isRecursive ∧ unfolds-in-one-step-to-a-different-head` — ranked by yield (new former nodes exposed / size increase). `Metric.ball` unfolds because unfolding exposes a comprehension, not because it is listed.

**The objective $J$ is computed, not optimized.** $J = \sum_{f\in\mathrm{Obs}\cap\mathrm{Rel}} w(f) - \lambda_2 C(d) - \lambda_3\Omega(d)$, where $\mathrm{Obs}$ enumerates free rides over port-graph topology. It replaces `src/semantic/inspection.ts:44` — `gain = (beforeUnknown−afterUnknown)*4 + min(8,Δinterpreted) − (size−beforeSize)/12`, which ranks by counting opaque regions and, via `:36`, **silently substitutes a different statement tree than the one you typed** — and `src/semantic/planner.ts:7-13`, whose fixed table gives numerical scenes 110 and 105 against 60–81 for every symbolic view, so a coordinate picture structurally outranks reading the statement.

Slice 1 **runs no search**: one deterministic policy, $J$ computed for the winner and the empty-hint alternate, both shown with the separating term. The weights are underivable and optimizing an uncalibrated proxy is the same structural error as the formula it replaces, one level up. Known residual bias, accepted: $\Omega$ penalizes folds, and every theorem-dependent fact is a fold, so $J$ rewards δ-expansion past readability. Visible but not acted on in slice 1.

---

## 3. Composition

### 3.1 The judgement

$\Gamma;\ \pi \vdash \Phi : P$ — a fragment well-formed in telescope $\Gamma$ at polarity $\pi\in\mathbb{Z}/2$ with port interface $P$: ports $(\ell:\text{role},\ t:\text{identity},\ \theta:\text{type},\ d\in\{\mathsf{in},\mathsf{out}\})$. A port is exactly a maximal subterm the fragment does not decompose, so $P$ is the frontier.

**$\equiv$ is `expressionKey` equality — one relation, fixed.** The synthesis used the symbol for three (key equality, `isDefEq`, propositional `Eq`). `isDefEq` is budget-bounded (`Export.lean:298, 344, 472`) hence **not transitive**, so it induces no quotient and $\sqcup_\equiv$ would be ill-defined. `≡` is therefore syntactic-up-to-alpha. Accepted cost: `f (x+0)` and `f x` draw as two anchors. `isDefEq` survives as a *guard* on wiring (may fail ⇒ no wire), never as an identification.

### 3.2 $\otimes$ — juxtaposition is conjunction

$$\frac{\Gamma;\pi\vdash\Phi_1:P_1 \qquad \Gamma;\pi\vdash\Phi_2:P_2}{\Gamma;\pi\vdash\Phi_1\otimes\Phi_2 : P_1\sqcup_\equiv P_2}$$

Same $\Gamma$, same $\pi$. Ports with equal identity fuse. Conjunction has **no visual operator** — co-location in one frame *is* conjunction. This replaces `StatementReadingView.tsx:206`, where a clause CSS-stacks up to three independent `<svg>` blocks with no shared coordinate space.

Fusion has two levels: *identity-fuse* (same object; safe anywhere, including across $\sqcup$-siblings) and *assertion-fuse* (jointly asserted; legal only under $\otimes$). That one distinction discharges "no facts cross sibling alternatives" compositionally, with no disjunction case.

**Non-overlap is not in $\otimes$** — it is a frame-level solve obligation applied once per frame after composition. (Separation constraints are globally generated, so a `Sep`-in-$\otimes$ definition is not associative.)

**Anchors are quotiented.** $R$'s codomain is constraint sets over **union-find classes of anchors**, not over anchor names. Without this, $(\Phi_1\otimes\Phi_2)\otimes\Phi_3$ and $\Phi_1\otimes(\Phi_2\otimes\Phi_3)$ emit `Fuse` between different *pairs* of names and AC3's exact-set-equality test fails on any three fragments sharing a port. Over classes the two bracketings are identical sets. This is well-defined precisely because $\equiv$ is an equivalence relation (§3.1).

$(\mathrm{Frag},\otimes)$ is a commutative idempotent monoid. Its unit is the **empty fragment**, which is *not* $\top$ — by F2, `True` is a `Junct` cell with a frame template and emits boundary constraints.

### 3.3 $\triangleright$ — typed plugging

Side condition purely typed: identical term identity, `isDefEq`-guarded types. No relation-kind test. This is `src/semantic/application-flow.ts` with its four-case switch (`:18-30`: `application`, `restricted-application`, `graph-coloring`, `graph-map`) deleted — a fifth applicative domain needs a fifth case today and none under `App` + $\triangleright$, because every `App` exposes a `result` out-port and `arg[i]` in-ports by construction.

Associative, non-commutative, partial. **Interchange with $\otimes$ holds iff the chains are port-disjoint and FAILS on shared intermediates.** Stated as a law failure rather than engineered around: a shared intermediate is exactly the structure a reader should see.

### 3.4 $\llbracket\cdot\rrbracket_\kappa$ and the bounded generator table

$\kappa=(\Delta,\varepsilon,\rho)$: bound telescope, per-child polarity flip, port-export relation. Every logical former is a *value* of $\kappa$ — $\forall$, $\exists$, $\to$, $\neg$, `Junct` child, `Struct` law. Frames compose: $\llbracket\llbracket\Phi\rrbracket_{\kappa_2}\rrbracket_{\kappa_1} = \llbracket\Phi\rrbracket_{\kappa_1\cdot\kappa_2}$, associative and unital, **non-commutative in $\Delta$ — and that non-commutativity is quantifier alternation.**

**Quantifier reading — restricted on review.** $Q(x_i)=\mathrm{mode}(x_i)\oplus\pi(x_i)$ was presented as a uniform law. It is not: $\Sigma$-at-odd $=\forall$ (i.e. $\neg\exists \equiv \forall\neg$) is intuitionistically valid, but $\Pi$-at-odd $=\exists$ is a **classical** import into the one layer claiming kernel evidence throughout. The XOR is now used for what it validly computes — *scope and drawn dependency* — and a $\Pi$-at-odd binder is marked as a classically-existential reading with an explicit badge, never silently drawn as a witness anchor.

**Framing is LAX over $\otimes$, and the laxity is De Morgan**: strict exactly when $\varepsilon=0 \wedge \Delta=\varnothing$, lax otherwise. Deeply nested negations therefore produce large indivisible frames.

**The generator table — the part to press on.** One frame template per former (8), plus constraint generators keyed on

$$\big(\text{unary frame cell},\ \text{port type},\ \text{binder valence}\big)$$

- **Unary frame cell**: $\{\Pi,\lambda,\Sigma\}\times\{\text{Prop},\text{Type},\text{inst}\}\times\{0,1\}\times\mathbb{Z}/2 = 36$. An $n$-binder telescope is a κ-word of $n$ unary frames (§3.4's monoid), so no key ever mentions $n$ or $D$.
- **Port type**: $\{\text{element},\text{region},\text{map},\text{family},\text{sort},\text{proposition}\}$ — a *single* port's type, not a vector.
- **Binder valence**: for the frame's own binder, the number of condition-anchors it feeds in each child, **capped at $\{0,1,2,{\ge}3\}$**. This replaces the synthesis's "fused on that binder" phrase, which was a set partition over ports and therefore superexponential — the buildability critique's deepest finding.

Product: $36\times6\times16 = 3456$ cells maximum, most emitting the same default. **None of the three factors is a function of the mathematical library, and none grows with statement size.**

**Worked example.** For $S\subseteq T$ expanded to $\forall x, x\in S\to x\in T$: `S`, `T` are `Atom`s with type $\alpha\to\text{Prop}$ so their ports are *region* kind; both `App`s are condition anchors; $x$'s anchor fuses across them by $\otimes$ (the line of identity — a free ride); the generator at cell (Π/Type/o=1/π=+, region, valence 1-and-1) emits coincident-permitting `Contain`. **One entry.** It fires for `Continuous f → s ⊆ f⁻¹(t)` at the appropriate sub-frame. It does **not** fire for `Adj u v → c u ≠ c v`, whose conclusion is an `Ident`-negation rather than a condition anchor on the shared binder. No entry mentions subset, membership, image, ball, adjacency or colouring.

**Solver schedule is forced, not chosen.** Because framing is lax, a frame's interior cannot be re-laid-out from outside. Frames *are* the stages: innermost first, frozen as rigid boxes, non-overlap applied per stage. All cross-frame constraints are linear.

### 3.5 Manipulation

A gesture is a move in the algebra. **Dragging** pins a layout variable and re-solves one stage; a drag that would carry a port across a frame boundary changes $\rho$ — what escapes a quantifier or negation — and is *rejected with a stated reason*, not silently clamped.

**Instantiation never discharges.** The synthesis let a supplied value discharge a binder at $Q=\exists$. Two holes: under $\neg\neg\exists$ the binder is $\Sigma$-at-even yet yields no witness; and there was no check that the supplied value satisfies the body, so `∃x, P x` plus any user-chosen $v$ drew an assertion of $P(v)$. Instantiation now always produces a **labelled illustration frame** that does not discharge, unless the user supplies a Lean term that typechecks as a witness, in which case the certificate is recorded. A coordinate model is a decoration provider consulted only here — contrast today, where `discoverScenes` is called unconditionally from inside the intensional compiler (`compiler.ts:1, 67`) and `Scene` is a first-class field of `SemanticDocument` (`types.ts:98`).

---

## 4. Meaning versus presentation

```
src/adapter/lean/        src/tnf/                  src/draw/
Expr, kernel checks      ν, 8 formers              constraint systems
isDefEq, handles         ⊗ ▷ ⟦·⟧, κ-monoid         staged solver
trust policy             A1–A7, J                  glyphs, palette, SVG
─────────────────        ───────────────           ──────────────
no drawing               no visual vocabulary      no Lean
                         no mathematical names     no former laws
                         no coordinates            all numbers live here
```

**Crossing downward:** former kind; ports with **opaque** identity (hash, never spelling); types as normalized terms; **port kind**; polarity; frame data; fold reasons and directions; provenance spans (`types.ts:7-11`).

**Never crossing downward:** a constant name, a module path, a coordinate, a `viewBox`, a domain tag, an English phrase.

**Crossing upward, exactly two things:** a cost report ($C$, realized $\mathrm{Obs}$) and a realizability failure. Presentation can influence *which* of several equally sound decompositions is shown; never what one *means*.

**The line moved.** The critique showed the synthesis called type-shape a "decoration" and then had it feed a containment constraint. The correct boundary: **port kind (element/region/map/family/sort/proposition) is meaning and may determine topology; glyph, badge, colour and label text are presentation and may not.** Port kind is derived from the port's type $\theta$, which §4 always said crosses downward.

**Three enforcement mechanisms.** (a) `Label` is an **opaque token** — a drawing rule that wants to branch on "is this `Set.image`" has no expression that could do so, making the catalog *unwritable* rather than discouraged. (b) **No coordinate exists above the solver, by type**: geometric fields have type `Var`, not `number`; writing a literal is a type error. Baseline to beat: ~190 such literals in `RelationFigure` alone. (c) **Functoriality is a property test**, exact constraint-set equality over anchor classes.

**Where domain knowledge may live:** the δ-hint file, upstream of $\nu$, whose output is re-typed by F1–F6. A hint may say "prefer unfolding `Metric.ball` to depth 1"; it cannot say "draw it as a circle". **On review, hints and decorations are now counted** (§5.3) — otherwise both doors stand open while the falsifier reports them shut.

This fixes a property that currently refutes the docs: `formatExpression` is reached for *every* object via `compiler.ts:82` → `reflection.ts:132-138`, and it imports `graphSemanticPlugin` and `restrictedMapParts` (`expression.ts:4-5`) and branches on them (`:128-138`). Disabling the graphs lens today changes the label of every object in the app, which is why reset criterion 5 cannot be met.

---

## 5. The first vertical slice

**Scope:** ∀/∃ alternation + implication + set-shaped application + structure laws. Zero domain-specific code, zero mathematical constant names in the meaning or drawing layers, **no optimizer, no general solver, standalone worker only.** The last three are cuts taken from the buildability critique; each removes a major cost without weakening a single acceptance criterion.

### 5.1 What gets built

**Lean (~700–900 lines, revised up from 250–300).**

1. One node-addressed `expand(handle, op, policy, budget)` replacing the four non-composable paths (`tree` `:459`, `binderTypeExpansion` `:271`, `reflectBinder` `:319`, `definitionPreviews` `:584`).
2. **Fix the law callback *and* the budget together.** All four sites (`Export.lean:483, 496, 511`; `Context.lean:46`) pass `fun e bs path => tree e bs path {} 0 0 false` — empty policy, zeroed depth, reflection off. This is the mechanical cause of the root-versus-field asymmetry (`architecture-reset.md:18`). But the synthesis called it "one literal", and it is not: `reflectBinder:321-329` computes `budget := min 2000000 (remaining - 1000000)` in `Nat`, so once the callback is live a depth-3 nested law truncates to `budget < 1000` and **silently returns `basic`** — no structure, no `stopReason`. The budget/stop-reason redesign *is* this change, and the recursion becomes genuinely mutual with no structural decrease (`tree` is `partial`, `reflectBinder` is not; the only bounds are `depth > 80 → throwError` at `:462` and the heartbeat ladder).
3. The **F2 shape recognizer** over `ConstantInfo.inductInfo` **plus one-step whnf** (for `Not`/`Ne`), replacing the name tests at `:504, :516`.
4. **Instance-projection reduction.** Verified by grep over `lean/StatementLens/*.lean`: zero occurrences of `whnfCore`, `whnfR`, `unfoldProjInst`, `reduceMatcher?`, `matchMatcherApp`, `getEqnsFor?`, `getConstructors`, `mkAppM`, `withReducible`. `unfoldDefinition?` alone cannot reduce `@Membership.mem _ _ Set.instMembership S x` to `S x`. **And the policy schema cannot express it:** `ExportPolicy` is `constants : Array String` capped at 12 (`:443`) with `maxDepth` hard-validated to 1–3 (`:448`). Both need changing, on the wire and in both clients.
5. Instance witnesses (stop erasing to `{kind:"opaque", text: pp a}` at `:246-247`, keeping `standardInstances`' synthesize-in-empty-context + `isDefEq` mechanism at `:206-207` and dropping its name lists at `:192-193, 199, 202`); typed stop reasons everywhere.

**TypeScript (~2200–3000 lines, revised down).** `src/tnf/`: 8 formers, $\nu$, three operators as fallible constructors, $\rho$, free-ride enumerator, A1–A7, $J$. `src/draw/`: constraint algebra + **bottom-up extent sweep**, not Cassowary. Every §5.2 fixture's layout is a frame tree with linear containment/separation/ordering on a DAG, already the pattern in `src/constructions/TypedConstructionFigure.tsx:35-59` and `src/decomposition/StructuralObjectFigure.tsx:55-71` — the only two genuinely computed layouts in the repository. **AC3 and AC4 are about constraint *sets*, not the solver**, so nothing is weakened. There is no solver dependency today (`package.json` runtime deps: CodeMirror ×6, katex, react, react-dom) and writing kiwi.js is ~1.5–2 kLOC that buys nothing yet.

**Preparatory work the synthesis missed:** `src/semantic/expression.ts` must be **split before** `src/tnf/` imports it — lines 4–5 import the graph and restricted silos, so AC2's grep fails on day one. And "keep `expressionKey` verbatim" is false: `:95` folds `metric`/`metricInstance`/`dimension`/`standard`/`operator` into every `app` key, so deleting those exporter fields is a keyed-schema migration through every object id and fingerprint.

### 5.2 Fixtures

Fixture 1 is replaced: the original was a tautology under $\nu$. Five of the synthesis's six were already in `corpus/cases.ts`; fixture 6 below is new and fixture 7 is deliberately out of reach.

1. `∀ (S T U : Set α), S ⊆ T → T ⊆ U → S ⊆ U` — three regions, two premises, one conclusion; premise and conclusion are genuinely distinct terms. (The tautology detection is retained as an incidental positive: a statement that normalizes to $A\to A$ *should* draw one frame twice.)
2. `∀ (f : α → β) (S : Set α) (y : β), y ∈ f '' S → ∃ x, x ∈ S ∧ f x = y` — $\triangleright$-wiring, `Ident` fusing a chain endpoint, $\mathrm{Dep}(x)$ by occurrence.
3. `∀ ε > 0, ∃ δ > 0, ∀ a, |a − c| < δ → |f a − f c| < ε` — **reclassified as a binder-structure test whose body is expected to fold.** Its content is `abs`/`HSub`/`LT`/`OfNat`, exactly the computational material §7 says folds. Four-binder κ-word, $\mathrm{Dep}(\delta)=\{\varepsilon\}$; the folds are a *pass*, recorded in the trace.
4. `Function.LeftInverse g f` at the root **and** as a law field inside a user record.
5. A held-out user record isomorphic to `PartialEquiv`, differently named, **with permuted field order**. Today impossible: `src/restricted/semantics.ts` matches the constant, and the existing "aliased record" case (`corpus/cases.ts:118-120`) passes only because Lean unfolds the alias back to that same name.
6. `∀ V (G : SimpleGraph V) (c : G.Coloring C) (u v : V), G.Adj u v → c u ≠ c v` — the anti-hollow test. Needs δ on `Ne`, δ on `Not`, projection reduction for `G.Adj`, and instance-projection reduction for `⇑c u`, i.e. the §5.1(4) primitive in at least three places.
7. **Hairy ball**, `Even n → Continuous v → (∀ x ∈ sphere 0 1, ⟪x, v x⟫ = 0) → ∃ x ∈ sphere 0 1, v x = 0`. Included precisely because the architecture cannot reach it: `Even` is arithmetic, `Continuous`'s field bottoms out in instance projections through `EuclideanSpace → PiLp → WithLp → MetricSpace → UniformSpace`. **It passes if it comes out mostly-`Fold` with correct polarities, typed reasons and a drawn binder/implication skeleton.** Without one such fixture, slice 1 only demonstrates that a general mechanism reproduces the existing catalog's coverage, and $\mathcal{B}$ cannot distinguish that from the claim at issue.

### 5.3 Acceptance criteria

1. **Vocabulary budget, as an assertion.** $$\mathcal{B} = |\text{formers}| + |\text{templates}| + |\text{generators}| + |\text{decorations}| + |\text{δ-hints}|$$ Hints and decorations are **in the sum** — they were the two uncounted name-keyed growth channels. CI asserts $\mathcal{B}\le$ a ceiling declared at slice freeze; a raise is a reviewed commit. **And AC1 records which cells fired per fixture: a generator cell firing for exactly one fixture is flagged as a catalog entry regardless of table size.** This is the falsifier.
2. **Name-blindness.** Zero Mathlib/user constant names in `src/tnf/**`, `src/draw/**`, **and the hint and decoration files**. CI grep, hard fail.
3. **Functoriality**, over generated fragment **triples with shared intermediates** (pairs structurally cannot detect the coherence failure the architecture admits): $R(\Phi_1\otimes\Phi_2)=R(\Phi_1)\cup R(\Phi_2)\cup\mathrm{Fuse}$ as exact set equality **over anchor classes**; plus every drawn edge has two drawn endpoints, for every figure. This fails every branch of today's `RelationFigure`, which is the point.
4. **No coordinates in meaning.** Zero numeric literals in geometric positions in `src/tnf/**`, `src/adapter/**`.
5. **Root-vs-field identity, corrected.** The law *fragment's own* constraint set is byte-equal at both locations, **modulo the owner-field telescope prefix**. The synthesis demanded byte-equality outright, which A1 forbids: a `Struct` law's $\Delta$ must include the owner and preceding fields (`Equiv.left_inv` references two sibling fields), or every sibling reference escapes the law frame. `scripts/decomposition-integration.ts:101` currently asserts the opposite ("Law reflection must not recursively expand nested records") and is deleted visibly.
6. **Rename + field-permutation invariance.** Strengthens `decomposition-integration.ts:43-69`, which indexes fields *positionally* (`` `field:${index}` `` at `:46`) so cannot survive reordering, and whose law comparison at `:68` is a sorted multiset of relation kinds — two structurally different laws fingerprint identically today.
7. **Hint erasure is a no-op on topology.** Strip every glyph hint; $\rho$ and every topological predicate unchanged. Degradation must be decoration loss, not structure loss.
8. **Empty-hint control.** With the δ-hint file empty, every fixture yields a connected figure with ≥1 $\triangleright$-chain and ≥1 non-trivial frame — never a generic caption fallback. Operationalizes reset criterion 5 (`architecture-reset.md:137`), currently unchecked anywhere.
9. **Surplus audit** over the enumerated predicate set including the annulus, seeded with a deliberate negative that must fail. **Scope stated honestly: this is a geometric-predicate lint against an authored declaration, not a proof of $\Sigma=\varnothing$.**
10. **Determinism.** Byte-identical trace over 100 runs and shuffled rule-registration order. No bare null, bare `true` or free-form string for any failure.
11. **Recorded reading review — human, blocking.** A reader who is not the implementer identifies the objects, premise, conclusion and allowed witness dependencies per fixture. Every structural gate above passes perfectly on an empty or unreadable constraint set; `docs/status.md:48-50` and `architecture-reset.md:140` already say so. Make it blocking.
12. **Held-out set**, sealed after contract freeze, CI forbidding a same-commit `src/` diff. A repository-wide grep for "held-out" returns exactly one line — `architecture-reset.md:142`. None exists.
13. **CI must run Lean.** `.github/workflows/check.yml:41-42` states: *"This workflow does not install Lean, run Lake, or fetch mathlib."* All 20 native suites in `package.json:15` are CI-invisible. **And `lakefile.toml` pins a mathlib rev whose upstream cache is garbage-collected over time** — budget a vendored cache artifact or self-hosted runner, or criteria 5, 6, 8, 9 and 12 silently stop running and this document is prose.
14. **Over-interpretation must fail.** `scripts/corpus-audit.ts:99` is `assert.ok(kinds.includes(kind))` — subset, not equality — so a reading asserting *more* than the statement licenses passes silently. Exact set equality on $\mathrm{Obs}$.

---

## 6. Migration

**Coexist first.** `src/tnf/` and `src/draw/` are a second consumer of the same `Analysis`. They do not touch `SemanticDocument`, `RelationKind`, the four domain silos or `StatementReadingView`. Nothing is deleted until the new path beats the old on the corpus by AC1, AC8 and AC11.

Order: (1) failing native regression for the root-vs-field asymmetry; (2) **law callback + budget/stop-reason redesign together**; (3) split `src/semantic/expression.ts` from the silos; (4) F2 recognizer, instance-projection primitive, policy-schema change, instance witnesses; (5) build `src/tnf/` and `src/draw/` beside the existing path, on the **standalone worker** (`Worker.lean:123-136` already has a persistent loop and a stable environment; `Context.lean:173` reads one stdin line and exits, and `:139` hard-fails if `messages.hasErrors`, so a user mid-edit gets nothing — handles, retention and revisions move to slice 2); (6) run both on the corpus, publish AC1 and AC11; (7) only then delete.

**Keep verbatim.** `expression.ts:80-107` (`expressionKey` — becomes $\equiv$, the fusion congruence, A5 and the memo key) and `:110-114` + `compiler.ts:70-85` interning; `types.ts:7-11` `Provenance`; the scope/assumption discipline at `compiler.ts:94-98, 133-141, 159-165` → A1; the runtime throws at `cues.ts:124, 148`; `OpaqueRegion` (`types.ts:69-78`, `compiler.ts:210-212`) → `Fold`; `reflection.ts:60-84`; `coverage.ts:58`; `visual/object-identity.ts:1-6`; `corpus/structures.ts`; `server/*.test.ts`; Lean `encode` `:211-266` minus `:251, 256, 257-260`; `reflectBinder` `:319-407`; **the kernel-check-then-`isDefEq` discipline at `:297-298, 343-344, 372-373, 471-472, 577-578` — the evidence contract, preserve exactly**; `Context.lean:36-53`, `Response.lean:13-40`, `ReadableMath.lean:22-46`.

**Refactor.** `src/constructions/model.ts:89-170` is the nucleus — promote it, deleting only `headName(fn) === 'Set'` at `:157` in favour of the type-shape test $\alpha\to\text{Prop}$. `src/reading/presentation.ts:26-57` becomes the κ-word extractor: binder runs at `:33-40`, right-associated implication chains at `:42-51`, negation at `:53`, all domain-free and prover-free. Note it consumes `ReadingDocument`, so this is a 32-line reimplementation, not a free carry-over. Compute it **once** per document — today it is recomputed at `cues.ts:106`, `StatementReadingView.tsx:336` and its own export.

**Delete, after AC1/AC8/AC11 pass.** `types.ts:23, 41-45, 107-111`; `compiler.ts:23, 27-35` (`relationMetadata` silently drops anything unlisted); `registry.ts:5-6, 17-19`; `expression.ts:4-5, 128-138`; `application-flow.ts:18-30`; `StatementReadingView.tsx:5-12, 71, 98-153, 206, 347-359`; the five per-kind switches (`reading/compiler.ts:27-48`, `reading/cues.ts:157-185`, `SemanticView.tsx:15, 90-101`, `coverage.ts:26-29`, `App.tsx:30`); `planner.ts:6-13`; `core/scenes.ts` and its coupling at `compiler.ts:1, 67`, `types.ts:1, 98, 124`, `App.tsx:203-210`; `inspection.ts:36, 44`; `src/graphs/`, `src/restricted/`, `src/set-constructions/`, `src/statement-geometry/`; `Export.lean:71-102, 112-132, 251, 256, 257-260, 271-315, 552-615`.

Evaluation apparatus: `corpus/cases.ts:10-22`'s `relationKinds`/`absentKinds` schema goes with `RelationKind`; `scripts/core-integration.ts:25` is vacuous (`scenes.length > 0 || relations.length > 0` is always true, since `compiler.ts:208` pushes a structural `predicate` relation for every application); `src/visual/statement-reading.test.ts` asserts English prose and CSS class substrings against hand-built trees with hardcoded `Set.Mem`/`Metric.ball`/`Set.image`; `scripts/decomposition-integration.ts:131-160` is fixture-id-keyed, so meaning is checked for three hand-picked fixtures and any new one gets shape checks only.

**One loss to replace deliberately.** `corpus/cases.ts:96-97` (`fake-graph-name`: a project-local `SimpleGraph.Adj (x y : Nat) : Prop := x = y` that must stay opaque) becomes vacuous — real and fake both become `App(h; u, v)`. Its replacement must be written: the fake is a `def` and **unfolds** to `Ident`, while Mathlib's is a structure field and does not. Different pictures, for a structural reason rather than an allowlist.

**On the existing reset proposal.** The findings of `docs/design/architecture-reset.md` are verifiable. This sharpens it: §1 → the 8 formers with an admission criterion; §2 → `expand`; §3's operation table → frame templates, and its "What must not be inferred" column (`:90-97`) → F6/A3; its admitted gap at `:117` — *"There is no established objective function"* — gets $J$, with the rider that $J$ is uncalibrated and advisory in slice 1.

---

## 7. What this does not solve

**Hard walls.** *Recursion*: `unfoldDefinition?` on a recursive definition yields `brecOn`/`WellFounded.fix`, there is no matcher reduction anywhere, and `Export.lean:296` bails when the head is unchanged — so `List.length`, any recursively defined function, and every induction principle fold at the first recursive head. *Theorems*: only `.defnInfo` satisfies `isDefinition` (`:420-436`), and `synthInstance` is used to audit (`:206-207`), never to harvest — "this metric space is complete" is unobtainable unless definitionally true. *Arithmetic*: this system does not reach computational mathematics. *Quotients*: `Quot` has no `.defnInfo` and folds. *`HEq`*: two indices, so F2's identity query misses it and every heterogeneous equality — ubiquitous in `Fin`/`Vector`/`Matrix` reindexing — falls through to an opaque binary `App`.

**Two limits the critiques established that the synthesis did not state.**

*Arithmetic on indices is unreachable at any cost.* A spectral sequence's only visual content is the relation $(p,q)\mapsto(p+r, q-r+1)$ between two `App` argument spines. No former reads arithmetic; no port-local decoration sees across two nodes; no generator cell keyed on (frame cell, port type, valence) can encode an index shift. The only route is a composite-matching rule over spines, which F5 forbids. **F3 and F5 together close this architecture against ever being extended to that class** — a stronger statement than "it folds today", and it does not depend on the Lean surface.

*Relational facts about a port have no home.* For a Galois connection, the content that would make the picture legible — "this `≤` is a partial order and $l,u$ are monotone for it" — is typeclass-derived and, worse, is a fact about a port *relative to a sibling hypothesis*. Decorations are port-local by definition. The sibling hypothesis is $\otimes$-composable so the *wires* are drawn; the *emphasis* is not. Meanwhile the frame cell for $l\,a\le b \leftrightarrow a\le u\,b$ is the same cell as a subset's inner frame, so it will draw as nested regions: not unsound, but communicating containment for a statement about adjoints. **Either the table stays small and everything of one type-shape draws identically — a monoculture detectable only by AC11 — or it grows, and AC1's per-cell firing record is the only thing that will say which.**

**Costs the criterion imposes.** Instances are audited, not drawn: two statements differing only in which `Module R M` instance is in scope render identically with a different badge — a silent conflation for instance diamonds. Dependent families lose a dedicated glyph (F3): correct and compositional, probably less vivid, and the first thing to revisit after AC11. Lax framing means deeply nested negations produce large indivisible frames, so the staged solver's advantage evaporates exactly where layout is hardest. **$\nu$ is deterministic, not canonical**: different unfolding orders can reach incomparable normal forms that are definitionally equal, and the pipeline has no mechanism to notice — and because the δ-hint file selects the order, it selects the picture, one constant at a time. That is why hints are in $\mathcal{B}$ and under AC2's grep.

**Research risks.** $\mathrm{Obs}$ is a model of reading, not a measurement of it; if the schema list is wrong, $J$ optimizes the wrong thing confidently — hence no search in slice 1. A3's declarations are authored, not verified: a reader may still read meaning off colour similarity, alignment or proximity, and an author who forgets that two separated regions assert disjointness gets a silently unsound picture passing every gate. **This is the single place where an incorrect mathematical claim can reach a reader with no signal.** Interactive latency is unmeasured. Rocq weakens to "the same shape query with a per-prover sort table", since F2's implementation uses `getStructureInfo?` and Rocq's `match`/`fix` land in `opaque` (`Export.lean:266`); do not start it until the Lean fixtures pass.

**The regression window is real.** The graph, restricted-map and metric figures produce good pictures today because they were hand-tuned for exactly those statements; general rules will initially do worse on exactly those cases. Coexistence contains the damage; it does not eliminate it. And the current corpus cannot detect the problem — `scripts/corpus-audit.ts` never renders anything, so a statement can be "supported" while the renderer falls through to a caption.

**Which goals this does not reach.** The goal is *arbitrary* statements. This reaches: first-order-shaped statements over definitionally transparent vocabulary — quantifier structure, implication and negation scope, typed objects and applications, one-to-three-step unfolding, structure fields and their laws — with typed, polarity-annotated folds everywhere else. **And "one-to-three-step" is narrower than it sounds**: `Set α` is *definitionally* `α → Prop` in one step, which is why fixture 1 works; membership through `SetLike` (`Submodule`, `Subgroup`, `Ideal`, `Filter` — most real `∈` in Mathlib) is four to six. A first honest measurement over Mathlib may well report *"most statements are mostly Fold."* That is a truthful result, it will look like failure, and it is still better than a generic caption or a confidently wrong hand-drawn picture.

The central quality claim — that a composed picture from eight formers and one generator table communicates structure better than the hand-tuned pictures it replaces — **is unproven, is not provable by any machine criterion in §5, and is what AC11 exists to test.** If AC11 fails, revisit the frame templates and the decoration layer. Do not reintroduce composite-matching rules. That distinction is the whole architecture.

---

## 8. Disposition of every critique point

**FIXED in the design (13).** Generator key not finite / `Tel`'s 18 is per-binder / port-type vector unbounded → unary frame cells, §3.4 [C-F4, S6, B6a]. "Fused on that binder" is an unbounded set partition → binder valence, capped [B6b]. Fixture 1 is a tautology → replaced, §5.2 [S1]. A2 mandates an F6 violation → occurrence-intersected, and `Export.lean:178` fixed to match `:376-377` [S2]. $\Pi$-at-odd-$\pi$ = $\exists$ is a classical import → restricted to its valid half + badge [S3a]. Instantiation discharges unsoundly under $\neg\neg$ and without a satisfaction check → never discharges, §3.5 [S3b]. A3 is undecidable / $\lambda_1$ dead → rescoped to the audited predicate set, $\lambda_1$ dropped [S4]. The `Contain` annulus is undischarged surplus → coincident-boundary discharge added to F6's closed list [S5]. $\otimes$ not associative as constraint sets → anchors quotiented, §3.2 [S7]. $\equiv$ is three relations / `isDefEq` non-transitive → one relation, `expressionKey` [S8]. $\rho$'s circularity in F3 → $\rho$ defined on the port graph, F3 demoted to a rejection filter [S9]. `Junct`/`Struct` both match `And`/`Iff` → explicit sort-based precedence, N3 [S10, B7c]. F2 cannot reach `Not` → F2 queries one-step whnf [S11]. Decoration feeds topology → the line moves: port kind is meaning, glyph is presentation, §4 [S12a]. Universe demotion unsound *and* self-inconsistent ($D$ is unbounded too) *and* contradicts `AGENTS.md:17` → **withdrawn** [S12b, B7a]. $\otimes$'s unit conflated with $\top$ → distinguished [S14b]. AC3 over pairs cannot detect coherence failure → triples with shared intermediates [S14c]. δ-hints and decorations uncounted → both in $\mathcal{B}$ and under AC2 [C-1, C-2]. AC1 is a log line → an assertion with a ceiling **and per-fixture cell firing** [C-AC1, B6]. Law callback is not one literal (Nat-truncating heartbeat ladder, silent `basic` at depth 3, mutual recursion) → merged with the budget/stop-reason redesign, cost revised up [B1]. Policy schema cannot express projection reduction; ≤12 constants, depth 1–3 → schema change named [B2]. `expressionKey` not verbatim; `expression.ts:4-5` breaks AC2 on day one → split step added before migration step 4 [B3]. `presentation.ts` consumes a deleted type → counted as a reimplementation [B3]. AC5 unsatisfiable against A1 → restated modulo the owner telescope [S13]. Fixture 3 contradicts §7 → reclassified, folds expected [B7d]. Five of six fixtures already in the corpus → fixture 7 (hairy ball) added, mostly-`Fold` counts as a pass [C-final]. `fake-graph-name` control becomes vacuous → replacement control specified, §6 [C-4c].

**ACCEPTED as stated limitations (11).** Index arithmetic unreachable at any cost — F3+F5 close it permanently [C-c]. Relational/typeclass facts have no home; Galois draws as nested regions [C-b]. Monoculture risk: ten entries means ten pictures, detectable only by AC11 [C-F4]. Theorem hypotheses carry the weight and fold, so reach is inversely correlated with mathematical interest [C-4b]. `Set` is the special case; `SetLike` membership is 4–6 steps [B2]. Colorable's 8-step δ chain may exceed the caps [C-4a]. `HEq` falls through [S14a]. $J$ rewards δ-expansion past readability [S14d]. Solver, handle table, mathlib cache are the three real costs [B4, B5, B8]. Honest growth estimate ~2–7 name-keyed entries per theorem area against ~30 edits across 17 files today: **a 5–10× constant-factor win, confined to one layer, not the categorical win §0 originally claimed.**

**REFUTED (2).** *"`Junct` winning erases a user's Prop-valued record, contradicting `Struct`'s justification"* [S10]: Prop is proof-irrelevant, so a cone all of whose legs land in Prop is degenerate — `structure Bounded : Prop where lo; hi` *is* `lo ∧ hi`, and drawing it as a conjunction is correct. The name survives as a fold label; `Subtype`/`Sigma` have data fields and go to `Struct`. *"AC3/AC4 need a real solver"* [implicit in B5]: they compare constraint *sets*, so the extent-sweep cut weakens neither.

**ACCEPTED cuts, which shrink the slice rather than inflating it (3).** No general solver. Standalone worker only — removes handles, retention, revisions, `Elab.async false` cold start and the `messages.hasErrors` hard fail, and costs nothing the fixtures need. No optimizer. With these, the slice is roughly a 2–3 month single-person project rather than 6–12, and AC1(+cells), AC2, AC3, AC8 and AC11 survive all three intact.

**Written before any code:** the generator-table key, as a definition rather than a phrase. AC1 is the declared falsifier and cannot be counted until the key is pinned — which is exactly the failure this document exists to avoid repeating.