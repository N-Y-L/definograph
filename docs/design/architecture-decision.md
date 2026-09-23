# Definograph: architecture decision

**Status: design decision, not an implementation.** Nothing described here is built yet. It amends the [round-1 TNF specification](tnf-specification.md) (cited below as `tnf-specification.md:line`); the earlier [architecture reset](architecture-reset.md) remains the record of the 0.7 findings.

**What it answers.** The design follows a three-step method set by the project supervisor: identify fundamental objects, decompose statements into them, and compose them so that the picture communicates a statement's structure rather than a set of disconnected figures. It answers four questions: what qualifies as a fundamental object, how decomposition works, how composition works, and how mathematical meaning is separated from visual presentation.

**How it was reached.** Round 1: four architectures written independently from different priors (type-theoretic, categorical, Penrose-style, diagrammatic logic), scored against each other, synthesized, and attacked by three adversarial critiques. Round 2: an audit of every code citation, a growth-rate stress test that ran seven statements from seven areas through the pipeline by hand, an independent architecture written without seeing round 1's result, and three red-team reviews (mechanisms, reader comprehension, mathematical content). "The independent architect" and "the content red team" below refer to those round-2 reviews.

## Decision: adopt TNF as the logical layer, with five amendments

**Adopt Telescope Normal Form (TNF, the [round-1 specification](tnf-specification.md)) as the logical layer, amended: (1) a counted layer of *certified readings* carries mathematical content into the picture (§2); (2) δ-hints, decorations and the generator key are deleted (§3); (3) decomposition optimizes lexicographically, law readings first (Q2); (4) two blocking human gates, G0 and G1 (§7); (5) a website first and a Lean infoview widget second, over one core (§5). Withdraw tnf-specification.md's central slogan.**

**Why not reject TNF.** The growth test did not refute it. Seven statements from seven areas (ε-δ, group homomorphisms, Galois connections, hairy ball, four-colour, spectral sequences, `Equiv`) needed one new logical entry, a `relation` port kind for $\alpha\to\alpha\to\mathrm{Prop}$, which adjacency, order and relation homomorphisms all reuse.

**Why not adopt it unchanged.** Growth was flat because the drawing layer could not see mathematics. The seven statements produced exactly the eight frame templates (one per former, tnf-specification.md:126) and no order, graph, ball or sphere; only the homomorphism square and the `Equiv` round trip were informative. That fails step 3 of the method, composition that communicates structure.

**The slogan "closes the picture set and leaves the vocabulary open" (tnf-specification.md:23) is false** for any system that meets step 3; it holds for the logical layer only because vocabulary never reaches a picture there. The replacement:

> The logical picture set is closed: 8 formers, 8 frame templates. Mathematical content enters only through a **counted list of certified readings**: name-free proposition schemas, each paired with a visual template. The list grows per *theory* (containment, order, symmetric relation), never per object, theorem or constant name. An entry is admitted only if the kernel certifies it at every use, it recurs across unrelated areas of a pre-registered Mathlib sample, and it reads back correctly on every small finite model.

This answers the charge, raised when the round-1 architectures were scored, that the catalog was "relocated to the presentation-rule registry, where nothing bounds it": the name-keyed hatches are abolished, and the registry is bounded by measurement.

**Notation.** `path:line` refers to this repository at commit `62259ef`; **[inf]** marks an inference by this document's author, [recalled] a Lean or Mathlib fact not checked here. No Lean toolchain was installed where this was written (`lean/.lake` was absent), so nothing was executed.

---

## 1. Factual corrections to tnf-specification.md

| tnf-specification.md says | True |
|---|---|
| `canonicalModule` is "a ~60-name array" | **94** constant names in 19 module buckets (`Export.lean:71-102`). |
| On the editor path (`Context.lean:57`), unlisted mathematics is "architecturally uninterpretable" | The allowlist caps interpretation, not parsing. Unlisted constants reach `encode` with full argument structure (`Export.lean:233-261`) and become `predicate` nodes (`:523`). They never get an interpreted type descriptor (`:151-152`), pass the instance audit (`:204`), or read as connectives (`:504-505, :516`). |
| "Five of the synthesis's six were already in `corpus/cases.ts`; fixture 6 below is new" (tnf-specification.md:197) | **Backwards.** Only fixture 6 (colouring) is there (`cases.ts:40`, used at `:87`). Fixtures 1–4 appear nowhere. Fixture 5's nearest relative is `corpus/structures.ts:64`. |
| "All 20 native suites … are CI-invisible" | 18 of 20. CI (the checks run on every push) runs `npm test` and `test:server` (`check.yml:36, :38`). |
| `RelationFigure` is "an 11-arm dispatch emitting ~190 absolute coordinates into a fixed `viewBox`" | The 11 is right: 3 guard returns plus 8 arms (`StatementReadingView.tsx:98-153`). The 190 are numeric literals, of which 114 are x/y/width/height/rx attributes and 12 are `from`/`to` points (the round-2 citation audit's 73 undercounts). There are two viewBoxes (`:151-152`). |
| `:115` draws the nesting; a clause "can only CSS-stack three" | Drawn at `:116-117`. Three figures show by default, the rest behind a button (`:206`). |
| "the only two genuinely computed layouts" (tnf-specification.md:191) | Three: add `SemanticView.tsx:42, :51`. |
| "the five per-kind switches" | Three per-`RelationKind` (`reading/compiler.ts:27-47`, `reading/cues.ts:158-184`, `SemanticView.tsx:15, :90-101`), plus two label tables keyed on vocabulary and view kind (`semantic/coverage.ts:26-29`, `App.tsx:30`). |
| `core-integration.ts:25` is "always true" | Near-vacuous: every uninterpreted non-numeric application yields a structural relation (`compiler.ts:199-208`). |
| Smaller items | `inspection.ts:36`'s substitution is recorded (`:47-48`), not silent. `ExportPolicy.constants` is `Array Name` (`Export.lean:417`). Correct lines: `model.ts:133-152` (Set test `:156`), `decomposition-integration.ts:45`, `cases.ts:117-119`, `Export.lean:323-325`. `Not := a → False` and Mathlib-cache expiry are external facts. |

The two largest corrections favour tnf-specification.md's thesis; they show only that its numbers were unchecked.

---

## 2. How content reaches the picture without per-object specifications

### 2.1 Certified readings

A **reading** is a triple $r=(\sigma_r,V_r,S_r)$: a proposition schema $\sigma_r(\vec h)$ over typed holes, built from Π, λ, application and F2's shape-recognized connectives with no constants; a template $V_r$ constraining only the ports bound to $\vec h$; and a surplus list $S_r$, each item discharged by a global convention (Q4). Two sorts:
- **Frame readings** read a subformula. *Contain*: $\forall z,\ h_A z\to h_B z$, drawn as nesting. *MapsTo*: $\forall z,\ h_A z\to h_B(h_f z)$, an arrow between regions.
- **Law readings** (theories) read the law fields of a structure or instance in scope. *Order*: $\{\forall a,\ h_r a a;\ \forall a b c,\ h_r a b\to h_r b c\to h_r a c\}$, a layered Hasse DAG. *Symmetric relation*: $\{\forall a b,\ h_r a b\to h_r b a\}$, undirected edges.

**Firing rule.** $r$ fires on node $n$ with holes $\vec p$ iff:
1. each $p_i$, after ν, is ≡ to a port already present in $n$'s fragment (no invented objects); and
2. the adapter certifies $\sigma_r(\vec p)$ against $n$'s proposition, or the law field's type, with the existing evidence contract `checkWithKernel` plus `isDefEq` (`Export.lean:297-298, :471-472`).

Structure reflection already builds law fields with `mkProjection` and kernel-checks them (`Export.lean:365, :372-373`), so tnf-specification.md's rule "Instances are audited, not drawn" (tnf-specification.md:256; the audit is `Export.lean:206-207`) is reversed for exactly this. The reset design asks for a rule that "matches exposed structure and available laws rather than theorem or field names" (`architecture-reset.md:86`).

**Why this is not a catalog [inf].** Order fires on the `≤` of every preorder, partial-order or lattice hypothesis in scope, including a user structure written yesterday, with no registration. The `fake-graph-name` control (`cases.ts:96-98`) becomes structural: its `def Adj x y := x = y` has no symmetry field, so it gets no edges, while `SimpleGraph` stores `symm` and `loopless` as fields [recalled]. Today `src/graphs/semantics.ts:75` keys on the string `'SimpleGraph.Adj'` instead. This reopens the composite matching tnf-specification.md:55 forbade, legitimately only because patterns carry no names, every firing is certified, and every entry earns its place by measured reuse.

### 2.2 What is bounded, and how

$$\mathcal B=|\text{formers}|+|\text{frame templates}|+|\text{port kinds}|+|\text{readings}|+|\text{conventions}|=8+8+7+4+6=33$$

This is the count at slice-1 freeze; CI asserts the ceiling (AC1). The port kinds are element, region, map, family, sort, proposition and relation. Name-keyed entries: **zero** (AC2).

**Growth.** Re-tracing the seven statements with a law-shape layer, the content red team needed about **45** name-free entries against round 1's one: 6–18 when a statement brings a new theory, 1–2 when it reuses one. Five of seven gained geometry specific to their mathematics: order axes (Galois), a sphere with pullback and right angle (hairy ball), a graph (four-colour), and conditionally ε-δ balls (via a bridge, §8) and a spectral-sequence grid (via an F5 exception). This document adopts that estimate: it puts $\mathcal B$ near 68, and each new geometry brings a surplus hazard needing a convention. Growth is no longer flat, and should not be; what survives is growth **sublinear in objects and zero per name**. tnf-specification.md's 3,456-cell generator table (tnf-specification.md:134) is deleted, not re-keyed.

---

## 3. Dispositions: round-2 defects D1–D6 and tnf-specification.md's §0 repairs

| | Defect | Disposition |
|---|---|---|
| D1 | `Contain` fires without containment: on normalized `Continuous v` (`∀ s, IsOpen s → IsOpen (v⁻¹' s)`) and on `sets-and-image`'s `∀ x, x ∈ s → ⋯ → f x ∈ t` (`cases.ts:28, :45-47`), nesting `s : Set X` inside `t : Set Y`. | **Fixed by construction.** In the second, $\forall z,\,s z\to t z$ is ill-typed, so certification fails; the premise `Set.image f s ⊆ t` gets a certified *hypothetical* Contain, and `f x` reaches `t` along x → f → f x. In the first, $h_B=\lambda s.\,\mathrm{IsOpen}(v^{-1}s)$ is not an existing port. |
| D2 | δ ranking is blind to multi-step payoff (`GT.gt→LT.lt`, `RightInverse→LeftInverse`, `Colorable→Nonempty`, `EuclideanSpace→PiLp→WithLp`). | **Fixed.** ν always unfolds `@[reducible]` heads (a transparency test, not a name test), keeping the original as label and provenance (`AGENTS.md:20-22`). Other definitions are ranked over a $k\le3$ lookahead, matching `Export.lean:448`, by new formers + fusions + certifiable readings. |
| D3 | tnf-specification.md:171 puts domain knowledge in a δ-hint file that tnf-specification.md:210 greps for names. | **Resolved in the grep's favour.** Hints and decorations are abolished; labels are opaque tokens resolved to Lean's printed text, with no glyph field. |
| D4 | Port kinds are uncounted. | **Fixed.** Counted in $\mathcal B$; a new kind enters only with a reading that passes T3. |
| D5 | "Condition anchor" is undefined; the key is arity-blind; F2's Σ-shape (tnf-specification.md:39) excludes `Nonempty`. | **Key deleted;** arity is the reading's hole list. Σ-shape: Prop-valued, one constructor, a first field whose declared sort is not `Prop`, then only Prop fields. This admits `Exists` and `Nonempty` and leaves `And` to meet. |
| D6 | tnf-specification.md:254 says Galois draws as nested regions, which tnf-specification.md's own revised key (:131) refutes. | **Deleted.** Under Order it draws as two order axes with `l`, `u` as opposing arrows, the textbook adjunction picture; monotonicity, a consequence, is correctly not drawn. |

**The mechanisms red team on tnf-specification.md's §0 repairs.**
- The unary key with valence re-imports $D$ and fires by binder order: **accepted; the key is gone.**
- ≡ = `expressionKey` **stays**, for determinism: printed-text keys (`Export.lean:221, :246, :266` → `expression.ts:92`) become structural, level strings (`:216, :224`) are normalized, `.proj` (`:262-264`) and projection functions (`:365`) share one form, and memoized ν stops the heartbeat ladder (`:323-325`) making normal forms position-dependent.
- Port kind as meaning: **accepted**, pinned to certification. tnf-specification.md's AC7 (hint erasure) is vacuous, since ρ comes from the port graph, and is deleted.
- Coincident-boundary containment traded "T∖S≠∅" for "S=T": **withdrawn** for conventions 1–2.
- Keeping universe levels is **right for the wrong reason**: `Set.{0}`/`Set.{1}` cannot collide; `Sort` nodes (`expression.ts:91`) and `ULift` can.

---

## 4. The four design questions

### Q1. What qualifies as a Fundamental Object?

**Tier 1 is closed: eight logical formers.** `Tel` (Π/λ/Σ telescope), `Junct` (meet or join in Prop; negation normalizes to `Tel` over ⊥), `Ident`, `App` (a spine with kernel argument roles), `Struct` (a record as a limit cone), `Atom`, `Sort` and `Fold` (typed opacity, with a reason).

Admission tests: **F1** name-blindness, $F(\nu e)=F(\nu\sigma e)$ for every type-preserving renaming $\sigma$; **F2** shape-definable connectives, replacing `head == And` at `Export.lean:516`; **F3** irredundancy, as a rejection filter only; **F4** finite index; **F5′** port-locality, a former never inspects below a port; **F6** discharged surplus.

**Tier 2 is open but counted: readings.** Each test is a script with a verdict.
- **T1, name-blind.** No constant appears in the schema (CI grep).
- **T2, certified.** The reading obeys the firing rule; a seeded tampered reading is rejected.
- **T3, reach.** On a pre-registered random sample of 2,000 theorems from the pinned Mathlib, run through the worker's declaration mode (`Worker.lean:36-56`) with imports widened, the reading certifies on ≥2% of statements across ≥8 top-level namespaces, and it fires on ≥2 fixtures from different areas. (The independent architect proposed 5% and 15; slice 1 harvests only from binders in scope.) The numbers are fixed before the first run; a failing reading is removed, not tuned.
- **T4, free ride.** Some law of $\sigma$ is nomic in $V$, true of every layout $V$ can produce, as transitivity is of upward paths.
- **T5, finite-model soundness.** Lay out every model up to size $k$ (preorders on ≤4 points, symmetric relations on ≤5 vertices) and read it back from the geometry; the read-back must equal the model modulo $S_r$. This rejects a linear axis for preorders, where incomparable elements would read as ordered.
- **T6, interface.** The template constrains only its own ports and emits no coordinates.

**What is not an FO.** `Metric.ball`, `SimpleGraph.Adj`, subset, membership, image and colouring are terms that normalize into formers and may fire readings. F5′ lets readings, never formers, read port *types* and the law *declarations* of objects in scope, when certified.

### Q2. How does decomposition work, and what is optimized?

**Normalization.** ν runs six passes, each rewrite certified: (1) telescoping; (2) polarity; (3) F2 classification, which discards names; (4) spine and projection normalization, including instance-projection reduction; (5) demotion of instances to typed witnesses; (6) folding, with δ chosen as in D2. Passes 4 and 6 need new Lean code: today the adapter unfolds only with `unfoldDefinition?` (`Export.lean:293, :340, :468, :573`) and plain `whnf` (`:243, :506`); `whnfCore`, `whnfR`, `unfoldProjInst`, `withReducible` and `mkAppM` occur 0 times in `lean/StatementLens/*.lean`.

**Hard constraints.**
- **A1:** a port escapes a frame iff $\mathrm{FV}(t)\cap\Delta=\varnothing$.
- **A2:** $\mathrm{Dep}(x_i)=\{x_j:j<i,\ Q(x_j)=\forall\}\cap\mathrm{FV}(\mathrm{body}_i)$, replacing `Export.lean:178`'s list of all prior non-assumption binders with the occurrence test already at `:376-377`.
- **A3** (authored surplus declarations) is replaced by certification and Q4's conventions.
- **A4–A7:** budget, identity coherence, renaming equivariance, realizability. The budget is at most 40 visible nodes per frame, provisional and recalibrated only from G0/G1 data.

**Objective.** $\mathcal D(e)$ is the fold/open decisions per certified δ-candidate, times the choice among readings certifying on the same ports. Selection is lexicographic, following the repository's "inspectable order" (`architecture-reset.md:107-113`), so no weights need calibrating:

$$d^*=\operatorname*{lexmax}_{d\in\mathcal D_{\rm adm}(e)}\big(L,\ F,\ -O,\ -N,\ -\delta,\ -\mathrm{hash}\big)$$

Here $L$ counts law readings realized, $F$ frame readings, $O$ opaque atoms among top-level premises and conclusion, $N$ visible nodes, and $\delta$ unfolding depth. $L$ ranks first because the adjacent formula does not display it (transitivity of `≤` appears nowhere in a Galois statement), answering the reader-comprehension red team's point that tnf-specification.md's objective rewarded what the formula already shows.

**Search.** Exhaustive at ≤12 choice points, doubling as the test oracle; above that, a deterministic beam of width 16, checked against exhaustive search on fixtures. The trace records winner, runner-up and the first coordinate where they differ. The ordering itself is a hypothesis G1 tests.

### Q3. How does composition work, and which laws hold?

**Judgement.** $\Gamma;\pi\vdash\Phi:P$ means fragment $\Phi$ is well-formed in telescope $\Gamma$ at polarity $\pi\in\mathbb Z/2$, with frontier $P$ of undecomposed subterms; each port carries a role, an opaque identity, a type and a direction. It is Peirce's Beta graphs with rectangular cuts (reader-comprehension red team); G1 decides whether that reads better than the formula.

**Identity.** ≡ is `expressionKey` equality after ν: α-invariant (`expression.ts:99`) and level-sensitive (`:89`). `isDefEq` never identifies ports; it only guards wiring and certifies readings.

| Operation | Typing | Holds | Fails |
|---|---|---|---|
| $\otimes$: juxtaposition, read as conjunction | keyed union; same Γ and π | associative, commutative, idempotent; unit = empty fragment (⊤ is not drawn); exact as sets | nothing within a frame |
| $\triangleright$: plugging an `App` result into an argument | identical identity; `isDefEq`-guarded types | associative; partial | commutativity; interchange with ⊗ on shared intermediates; $(h\circ g)\circ f=h\circ(g\circ f)$ only after a certified δβ step |
| $\llbracket\cdot\rrbracket_\kappa$: framing, $\kappa=(\Delta,\varepsilon,\mathrm{export})$ | seals every port whose key mentions Δ | $\llbracket\llbracket\Phi\rrbracket_{\kappa_2}\rrbracket_{\kappa_1}=\llbracket\Phi\rrbracket_{\kappa_1\kappa_2}$; unital | commutativity in Δ (that failure *is* quantifier alternation); strictness over ⊗ (lax, as De Morgan predicts); $\forall x(P\wedge Q)$ and $(\forall xP)\wedge(\forall xQ)$ are different pictures related by a proved manipulation |
| reading on node $n$ | firing rule | local to $n$, so preserved by ⊗ and by weakening Γ | status (obligation or hypothetical) flips with polarity |

**Global properties.** $R(\Phi\otimes\Psi)=R(\Phi)\cup R(\Psi)$ holds exactly, because firing is node-local. Layouts are not claimed to compose (each frame stage is solved globally); rendering consumes the canonical document, so no coherence theorem is owed; ν is deterministic but not canonical.

**Quantifiers.** Binders are drawn by their actual constructors. Σ at odd polarity reads as ∀, intuitionistically valid; Π at odd polarity reads as ∃ only classically, so it gets a badge, never a witness anchor. Dependency is permission by nesting (an ∃-frame inside a ∀-frame may use its binder), and the dependency label lists A2's smaller occurrence set. Witness status comes from the path to the root: *obligation* through only ∀, ∃, ⇒-conclusion and ∧; *hypothetical* on entering exactly one ⇒-premise; otherwise no label. So `¬¬∃` never shows a witness.

**Manipulation.** Slice 1 has two gestures: opening or closing a fold (a certified δ-step) and dragging within a frame; a drag across a frame boundary is refused with its reason. Proof-carrying gestures wait for slice 2 and a bounded tactic primitive (`mkAppM`: 0 occurrences): equivalence needs a proof of $s\leftrightarrow s'$, specialization one of $s\to s'$, and a supplied witness stays an open obligation until Lean discharges it.

### Q4. How is meaning separated from presentation?

**Meaning is what the prover certified.** The boundary is pinned to that one external fact.
- **Crossing down to `src/draw`:** formers; ports with opaque identity, type and port kind; polarity and frames; typed folds; certified readings with hole bindings and evidence handles; provenance.
- **Never crossing:** names, module paths, coordinates, viewBoxes, English text.
- **Crossing up:** realizability failures and a cost report.

A template may show only the image of a former or a certified reading, or a fact discharged by one of six conventions:
1. Zones never assert non-emptiness; only element dots do.
2. Unrelated regions are drawn overlapping, and area means nothing.
3. Size, distance and relative position of unconnected elements mean nothing. Distinct dots are distinct names, not necessarily distinct objects.
4. In an Order panel, only upward paths along drawn edges mean ≤.
5. Dashed means hypothetical; solid means obligation.
6. A Fold box means "not opened" and states its reason.

**Enforcement.** Labels are opaque tokens, so no rule in `src/draw` can branch on a name. Geometric fields have type `Var`, not `number` (the baseline is `RelationFigure`'s 114 geometric literals). **AC4** re-derives containment, overlap, crossings and height order from the *rendered SVG*, failing on any predicate neither certified nor conventional and on any certified reading not drawn. It replaces tnf-specification.md's AC9 (surplus audit), and with AC3's exact-set check it replaces AC14. It is not a comprehension test; G1 is. Port kind depends on how far ν unfolded; that is accepted as meaning relative to the recorded decomposition, and the trace keeps the alternative.

---

## 5. Product surfaces: website first, Lean extension second, one core

**What exists today.** The web reader (Vite, `vite.config.ts:6`) proxies to a local API (`:8`; `server/index.ts:7, :19`) that drives the persistent standalone worker (`Worker.lean:123-136`). The VS Code extension (`extension/package.json:3`, requiring `leanprover.lean4` at `:78-79`) loads the same bundle into a webview (`extension.ts:20-34`; `vite.config.ts:3-4`). Its editor path spawns a process per request (`server/editor-context.ts:107, :161`) that re-elaborates the whole file (`Context.lean:140`), fails if the project's imports do not load (`:139`), and accepts only Lean v4.28.0 (`editor-context.ts:54`).

**Decision.**
- **One core.** `src/tnf`, `src/readings` and `src/draw` are pure TypeScript behind `render(StatementDocument, viewState) → scene tree`, with no I/O or host API; CI forbids host imports into them. Shared React components render the scene tree in every host.
- **Slice 1: website.** The local app, plus a static build that renders pre-exported documents without Lean and doubles as the G1 harness, since readers need only a browser. A public site with live input would need hosted Lean and Mathlib, outside this plan.
- **Slice 2: Lean extension, as a ProofWidgets infoview widget** (a panel in the Lean editor's goal view). ProofWidgets is already a transitive dependency (`lean/lake-manifest.json:53-64`); its RPC would run the adapter inside the Lean server's already-elaborated file [recalled], removing per-request re-elaboration and the separate import load. Gate: a one-week spike rendering one document; if it fails, keep the webview extension. **[inf]** F1 deletes `canonicalModule`, `realType` (`Export.lean:61`) and the name tests at `:112-132, :153-160, :257-260`, so the adapter names no Mathlib constant and is coupled to Lean and ProofWidgets versions, not Mathlib's.
- **Rocq.** A separate adapter emitting the same `StatementDocument`, begun after the Lean slice passes. It needs F2 queries over inductives, conversion-certified readings and law harvesting from records, harder under MathComp's Hierarchy-Builder packing **[inf]**.

---

## 6. Convergence: same logical layer, different content source

**Where it converged.** The independent architect, without reading tnf-specification.md, reached the same logical half: normal-form frames, constraint emission, opaque labels, free-variable scoping, coexistence migration and a blocking human gate. It also argued, before the stress test confirmed it, that no system drawing domain structure has a closed picture set.

**Where it diverged: the content source.** It drew content from kernel-checked typeclass instances of a few visual signatures, via **named bridges** (`instance [Preorder α] : Order (· ≤ ·)`) bounded by a reach test, and kept nine logic names where F2 needs none. The content red team reached the same content without names, by harvesting laws stored as fields of objects in scope. That buys coverage of unseen user structures with no registration, and no bridge code compiled against one Mathlib release, which would re-couple the extension to Mathlib versions. The cost is Lean engineering (parent recursion, structural instance export) and a gap on closed instances such as `≤` on ℝ (§8).

**Adopted from it:** admission tests T3–T6, the lexicographic objective with exhaustive or beam search, dependency as permission by nesting, path-based witness labels, the non-tautology check and the ProofWidgets host. Two independent routes to *content = structure recognized from laws* is a second convergence signal.

---

## 7. First vertical slice

**Scope.** Website only, on the standalone worker, for closed terms elaborable in its imports (`Worker.lean:12-18`, adding an import line where a fixture needs one): the logical layer, four readings, six conventions, an evaluation page, and tnf-specification.md's bottom-up extent-sweep layout (tnf-specification.md:191) with a layered sub-layout for Order. Excluded: tuned weights, a general solver, the editor path, bridge lenses, instance search on concrete carriers.

**Fixtures.**
- **X1** `∀ (α : Type) (S T U : Set α), S ⊆ T → T ⊆ U → S ⊆ U`: two dashed Contains, one solid.
- **X2** `sets-and-image` and its renamed twin (`cases.ts:28-29, :45-50`), the D1 regression: `s` is never drawn inside `t`.
- **X3** Pointwise vs uniform continuity of `f : ℝ → ℝ`: the frame trees differ, and the point $c\in\mathrm{Dep}(\delta)$ iff pointwise. With `f` and `c` bound, A2 gives $\{f,c,\varepsilon\}$, not tnf-specification.md:201's $\{\varepsilon\}$.
- **X4** `GaloisConnection l u → Monotone l` over `[Preorder α] [Preorder β]`: two Order panels; neither class name occurs in the corpus (grep: 0).
- **X5** `Function.LeftInverse g f` at the root and as a user-record law, identical modulo the owner prefix, replacing the opposite assertion at `decomposition-integration.ts:101`.
- **X6** A renamed, field-permuted twin of `PartialEquiv`.
- **X7** Colouring (`cases.ts:40`) beside `fake-graph-name` (`:96-98`): edges for the first, none for the second.
- **X8** Two user structures: a symmetric irreflexive relation gets edges with an empty `src/` diff; a reflexive non-transitive one gets no Order.
- **X9** Hairy ball: no uncertified reading, every fold typed, the frame sequence predicted in writing before the run. tnf-specification.md's "mostly-`Fold`" pass rule (tnf-specification.md:205) is dropped, since the policy opens `Even`, `Continuous` and `sphere`.
- **X10** The homomorphism square `f (a * b) = f a * f b`, which needs instance-projection reduction.

**Acceptance criteria (CI).**
- **AC1** $\mathcal B\le33$; raising it takes a reviewed commit with a T3 report.
- **AC2** Zero names in the core and an empty adapter allowlist; `canonicalModule`, `canonicalConstant` and the name tests (§5; `Export.lean:192-202, :504-505, :516, :564`) are removed.
- **AC3** Every drawn reading has an evidence handle. Each fixture's fired readings equal its pre-registered set **exactly**, replacing the subset check at `scripts/corpus-audit.ts:99`. A seeded tampered Contain on X2 is rejected.
- **AC4** The SVG surplus check passes, and seeded negatives fail.
- **AC5** T3 and T5 hold for every reading.
- **AC6** $R(\Phi\otimes\Psi)=R(\Phi)\cup R(\Psi)$ on triples with shared intermediates; documents byte-identical under renaming, independent-binder permutation, field permutation and ∧-reordering; X3's trees differ; X5 holds.
- **AC7** No silent truncation: the early returns at `Export.lean:276` (`Json.null`) and `:325` (`basic`) become typed stop reasons.
- **AC8** Non-tautology: after bounded unfolding, `intros; assumption` fails on every fixture.
- **AC9** ≥6 held-out statements from ≥3 new areas, sealed by a third party after freeze, render with an empty `src/` diff; results are published whatever they are.
- **AC10** CI installs Lean with a cached Mathlib and runs all 20 suites; today it runs 2 (`check.yml:36, :38`) and installs no Lean (`:42`).

**Comprehension gates (human, blocking).**
- **G0, paper gate** (week 1, before any `src/tnf` code): mock the templates for the G1 items and show them, labels removed, to 3 readers thinking aloud. This forces the visual decisions tnf-specification.md never made.
- **G1, product gate,** passed before any old path is deleted.
  - *Readers:* 6 who have not seen the design: ≥2 readers from sciences outside mathematics, ≥2 CS students, ≥1 mathematician.
  - *Conditions:* F the typeset formula, P the product, D the diagram with neutral tokens, in a Latin square: each reader sees each item once, and each item meets each condition twice.
  - *Items:* five minimal-contrast pairs (∀c∃p vs ∃p∀c, `docs/statement-first-review.md:12, :16`; pointwise vs uniform continuity; a subset chain vs one premise reversed; `LeftInverse` at the root vs in a field; ∨ vs ∧, `:46`), one surplus probe ("does the X2 picture claim s ⊆ t?") and two long items, X4 and X10. A TA picks two items, against implementer bias.
  - *Measures:* a two-choice discriminating question ("must δ work for every point?"), time to answer, and the first 30 s of think-aloud scored for claims the statement does not entail.
  - *Pass rules,* committed before the first session. The red team's "5 of 6 correct per item" in D is infeasible under its own Latin square, so these count the 16 responses per condition:
    1. *Encoding:* ≥14 of 16 D responses correct (chance 50% each), and no item missed by both its D readers.
    2. *Non-inferiority:* P correct ≥ F correct, with no item both P readers miss and both F readers get right; where F is at ceiling, P's median time ≤1.5× F's.
    3. *Benefit:* on the long items P is more accurate than F, or as accurate and faster; otherwise the recorded result is "correct renderer, no reading benefit".
    4. *Soundness:* a surplus claim by ≥2 readers on one picture blocks until a template or convention changes and AC4 gains that predicate.

G1 restores the comparison with the typeset statement that `docs/roadmap.md:31` requires and tnf-specification.md dropped. With n=6 it can falsify the design, not prove it. Reader sessions may need approval from course staff before they run.

**Cost [inf].** Lean 1,100–1,500 lines (tnf-specification.md's 700–900 plus parent recursion, instance export, certification), TypeScript 2,800–3,600, tests about 600: roughly 3–4 months for one person. On a shorter term, cut to X1–X5 with Contain and Order; never cut G0 or G1.

---

## 8. What this does not solve

- **Content carried by theorems** (`IsCompact` as closed-and-bounded, `Planar`, completeness) folds. Bridge lenses, certified rewrites by a library theorem that add no pictures, would reach it; they are deferred to a slice-2 decision on G1 data, ceiling 16. Until then Mathlib's filter encoding draws analysis as filter comparisons (`ContinuousAt f b` is `Tendsto f (𝓝 b) (𝓝 (f b))` [recalled]), so analysis is the weakest area.
- **Closed instances on concrete carriers** (`<` on ℝ) need upward subclass search, deferred to slice 2; in slice 1, ℝ comparisons are plain relation anchors.
- **Laws proved as theorems** rather than stored as fields are invisible, and **equivalent axiomatizations** degrade to no content; neither misfires.
- **Intent absent from types:** `v : E → E` is drawn as a self-map, not a vector field.
- **Recursion** folds at its first recursive head; quotients and `HEq` fold.
- **Index arithmetic** needs a ninth, coordinate former; spectral sequences are out of scope, though not impossible.
- **Instance diamonds** stay unfused.
- **Short statements:** the formula may simply be faster. The formal statement stays beside every diagram (`AGENTS.md:11-12` already makes the default "a visual sequence with its logical overview alongside"), and G1 decides where the diagram earns its place.

## 9. Research risk versus engineering work

**Research risk** (outcome unknown until measured):
1. Whether P beats F for anyone (G1).
2. Whether `isDefEq` certification with pattern holes succeeds, at acceptable cost, on instance-heavy Mathlib terms.
3. How much of Mathlib has laws harvestable along projection paths; T3's first run may reject Symmetric relation.
4. The cost of closed-instance subclass search.
5. Hasse-layout soundness beyond tiny $k$.
6. Extent-sweep quality past about four nested frames.
7. React and RPC compatibility of ProofWidgets.

**Engineering work** (method known, cost uncertain):
- the law callback and budget/stop-reason redesign (`Export.lean:483, :496, :511`; `Context.lean:46`; `Export.lean:274-276, :323-325`);
- instance-projection reduction and the `ExportPolicy` wire change in both clients (`Export.lean:416-457`; `extension.ts:13`);
- structural instance export (`Export.lean:245-246`) and parent recursion (`:387`);
- the F2 recognizer and occurrence-based `dependsOn` (`:178`);
- splitting `expression.ts:4-5` and migrating its key (`:95`);
- the three core directories, static build and evaluation page;
- Lean in CI with a cached Mathlib;
- layout: the extent sweep with a layered sub-layout, or elkjs as the independent architect suggested (an EPL-2.0 dependency, which needs a licensing decision).

Sources: this repository at commit `62259ef` and the [round-1 TNF specification](tnf-specification.md).
