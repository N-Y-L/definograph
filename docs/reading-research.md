# What research says about reading statements

Reviewed on 2026-10-12, after the project owner suggested starting from human pattern recognition. This page records one bounded round of reading: what is known about how people recognize structure in a drawing, how they misread formal statements, how a proved statement can still miss the intention, and which existing tools draw statements. The statement skeleton and the identity colours described in [Guided reading](guided-reading.md) were built from it; the [roadmap](roadmap.md) was written earlier and has not been reordered around it.

How to read this page:

- Every source listed under References was opened during the review, and a second, independent pass checked that it exists, that its citation is right, and that it supports what is said here. Section 6 lists the sources that could be read only as an abstract or a record.
- Nothing was copied from any source. Findings are summarized in our own words, and no code, figure or text from another project is in this repository because of this review.
- Each design rule states its kind of evidence: an **experiment**, a design **framework**, or our own **inference**. None of the experiments studied drawings of Lean statements. Every rule is therefore a hypothesis for the reading evaluation that the [roadmap](roadmap.md) and the [architecture decision](design/architecture-decision.md) call for, not a result.

## 1. Design rules for a drawing a person can recognize

1. **A drawing helps only when it is built to.** Larkin and Simon (1987) trace a diagram's advantage to three things: related information sits in one place, location replaces the matching of labels, and some inferences are made by the eye. Tversky, Morrison and Betrancourt (2002) report that the graphics shown to help were carefully designed static ones. So each figure answers three questions: is everything about one object in one place, can an object be followed without re-reading its name, and is every relation the eye picks up true of the term? *Framework and review.*
2. **A drawing can say too much.** The spatial constraints that give a diagram its cheap inferences also force it to show things nobody stated (Stenning and Oberlander 1995; Stapleton 2018; Shimojima and Katagiri 2013). Euler circles cannot show partial knowledge and can force an overlap the premises do not require (Shin, Lemon and Mumma, SEP). Use a geometric relation only where everything a viewer can read off it follows from the term. Nesting for scope is safe, since scope and containment are both transitive. A nested ellipse for `⊆` is not automatically safe: it suggests a proper, non-empty subset. *Framework.*
3. **Order goes on one fixed axis.** Position along a common scale is the most accurately read channel for quantities (Cleveland and McGill 1984); Mackinlay (1986) extends the ranking to unordered data and says that extension was not tested. Constraint diagrams were sometimes ambiguous about the order of quantifiers until an explicit reading tree was added (Howse et al., project report; Fish, Flower and Howse 2005). So binder order and the step from Given to Then use top-to-bottom position plus nesting, and nothing else may use vertical order. *Experiment for quantities; framework and a recorded failure for the rest.*
4. **Scope is a frame, drawn the same way at every depth.** In a randomized trial with 27 participants, nested conditionals without indentation took about twice as long to read as indented ones (Hanenberg, Morzeck and Gruhn 2024). *Experiment, on code.*
5. **One channel answers one question.** A target that differs in a single feature is found quickly whatever the size of the display; a target defined by a combination of features usually is not, and colour differences mask shape differences (Healey and Enns 2012; Wolfe and Horowitz 2017). One experiment reported there found up to seven colours of equal luminance could be told apart at a glance. So hue carries object identity and nothing else, from at most seven hues that also differ in lightness, assigned in order of introduction and never reused; and every colour cue has a label or a line style beside it (W3C, WCAG 1.4.1). *Experiment and standard.*
6. **About four new things at a time.** Working memory holds three to five chunks (Cowan 2001, 2010), and up to about four items are counted at a glance where more are counted one by one (Trick and Pylyshyn 1994). A step that introduces more should group like binders into one chunk or fold a whole unit behind a stub that says what it is and how many it holds. *Experiment, transferred from basic perception.*
7. **Set pictures only where they are faithful.** In a comparison of diagram types, aligned line segments were read fastest and with fewest errors and Venn diagrams worst (Chapman et al. 2014). Redrawing real Euler diagrams to ten guides at once lowered errors from 21.4% to 10.3% in one study (Blake et al. 2016), and curves that run together or zones that split hurt comprehension (Rodgers, Zhang and Purchase 2012). Draw nested or overlapping curves only with no zone the term is silent about and about three curves at most; otherwise use aligned bars or keep the clause symbolic. *Experiment, on Euler diagrams.*
8. **Small graphs, straight paths, no crossings.** Edge crossings hurt most among the layout properties tested (Purchase 1997); after path length, bends and crossings on the path matter (Ware et al. 2002); above about twenty vertices a matrix beat a node-link drawing on most tasks except finding a path (Ghoniem, Fekete and Castagliola 2005). *Experiment.*
9. **The reader sets the pace.** Reported advantages of animation shrink when content and interactivity are equated (Tversky et al. 2002). Side-by-side frames were faster than animation in one study and less accurate on two of its tasks (Archambault, Purchase and Pinaud 2011), and animation was the least effective for analysis in another (Robertson et al. 2008). Keep Previous and Next, no autoplay, and the whole statement always available. *Experiment, mixed.*
10. **Labels go on the thing, with no legend.** Text placed on or beside what it describes gave better learning than text placed apart: an overall effect of g = 0.63 across 58 comparisons (Schroeder and Cenkci 2018; Ginns 2006). *Meta-analysis.*
11. **Layout will be read as meaning.** When spacing conflicted with operator precedence, accuracy on equations where precedence mattered fell by 38.7 points (Landy and Goldstone 2007). People who have mastered algebra attend to sub-expressions as visual objects (Marghetis, Landy and Goldstone 2016). Readers also take informal layout as information (Green and Blackwell 1998). The reader's own rule is that spacing carries no meaning; that is a rule for the grammar. The rule for the page is stronger: proximity, enclosure and alignment must never suggest a grouping the term does not have, and the same view must always give the same picture. *Experiment and framework.*
12. **Show a hidden thing by a mark, and a difference by pointing at it.** Students shown both orders of a quantified statement sometimes worked out that the order matters (Piatek-Jimenez 2010, six students). A comparison can be drawn by juxtaposition, by overlay, or by encoding the difference itself (Gleicher et al. 2011). For look-alike statements we infer: the same layout side by side, the differing element marked and named, and an instance, a hidden argument or an extra hypothesis shown by something present on the page. *Small study and our inference.*
13. **A diagram can be a formal language.** Spider diagrams have an abstract syntax, a drawn syntax, and sound and complete rules (Howse, Stapleton and Taylor 2005). For monoidal categories a drawing's meaning is invariant under a stated class of deformations (Selinger 2011). A calculus of string diagrams has the expressive power of first-order logic (Bonchi et al. 2024). We read these as precedent for a possible later step that nothing here commits to, proving that a drawing reads back to its statement (the [architecture decision](design/architecture-decision.md) says no coherence theorem is owed for rendering): the combinatorial drawing is the abstract syntax, the layout is the drawn syntax, and "spacing and routes carry no meaning" becomes an equivalence under which readback does not change. *Our reading of formal results.*
14. **Published checklists are not guarantees.** Moody (2009) proposes principles for visual notations; we could confirm them only through secondary summaries. Notations redesigned to those principles showed no outright advantage in three experiments on model construction (El-Attar 2022). Use the checklists to audit, then test.
15. **Liked is not the same as helped.** Highlighted, narrated proofs were popular and gave no gain in comprehension, with a larger drop two weeks later; a short self-explanation training did help, by about 0.4 standard deviations in a class of 107 (Alcock et al. 2015). Type annotations were felt to help and had almost no measured effect (Alznauer et al. 2026). The outcome measure is correctness and time on a question that discriminates, never preference.

## 2. How people misread statements

Each entry gives a question a reading session can ask.

| Misreading | Evidence | Question |
| --- | --- | --- |
| "There exists … for all" read as "for all … there exists" | 94% of 63 students read at least one such statement that way (Dubinsky and Yiparaki 2000). None of six read a three-quantifier statement correctly (Piatek-Jimenez 2010). Before a proof course, context drove the reading more than quantifier order (Dawkins and Roh 2020, abstract) | May `y` depend on `x`? Asked once per witness |
| Reading from the name or the topic, not the definition | 21 of 22 final-year students judged a false theorem about limits true (Tall and Vinner 1981). After being shown a definition, 29% of 187 students classified examples fully in line with it (Alcock and Simpson 2011) | Does this boundary instance satisfy the definition? |
| Hidden structure not recovered | 8 of 94 attempts to write an informal statement with explicit quantifiers succeeded (Selden and Selden 1995) | List every variable: is it given, arbitrary or chosen? |
| "For all" taken collectively; "there exists" taken as exactly one | Two students over eleven sessions (Vroom 2022) | Could two different `x` get two different `y`? Could there be two such `y`? |
| A formal notation does not remove reasoning errors | A pilot posed the selection task as a Z schema and found the familiar error, compared with published results for the original task (Loomes and Vinter 1996). In LTL, errors appeared when reading a formula, when writing one, and when judging a trace, and most often when writing a formula from an English intent (Greenman et al. 2023) | Does this plain-language claim match this statement? |
| Structure is seen, and can be trained | Practice at recognizing which equation is a legal transformation of another, with no solving, cut solving time from about 28 s to about 12 s per problem for school algebra students (Kellman, Massey and Son 2010) | Which of these two statements does this drawing show? |

We found no published study of people reading Lean, Rocq or Isabelle statements. That is the limit of this search, not a finding about the field. The studies above mostly observed undergraduates reading semi-formal English, so their transfer to Lean terms is an assumption a session would test.

For the sessions themselves: use a within-subject design with the order of tasks and tools counterbalanced, decide before the first session when the clock starts and what counts as success, and run a pilot (Ko, LaToza and Burnett 2015). Of 95 code-comprehension experiments, most were within-subject and most measured correctness together with time (Wyrich, Bogner and Wagner 2023). About five people expose most usability problems in qualitative testing (Nielsen 2000); six readers can falsify a design, not establish an effect, so results are reported as counts per question.

## 3. How a proved statement can miss the intention

The Lean reference separates whether a theorem has a valid proof from what its statement means ("Validating a Lean Proof"). The three layers below are our own way of organizing the documented failures.

- **A. Verdict.** Was the declaration really established, and on which axioms? Covered by tools: `#print axioms`, the `leanchecker` replay that ships in the toolchain, and [comparator](https://github.com/leanprover/comparator) and [SafeVerify](https://github.com/GasStationManager/SafeVerify) with their lists of permitted axioms. A kernel defect is outside all of them: in July 2026 an axiom-free proof of `False` was reported and fixed (lean4 issue #14576; de Moura's postmortem). This project treats kernel soundness as outside its scope.
- **B. Identity.** Is the statement that was established the one that was asked? The tools above answer this only against a trusted reference statement. Without one, a person has to read the elaborated statement, because the source text can stay the same while the term changes. We confirmed four such cases on Lean 4.28.0 with core only (the test files are not in this repository), each reporting no axioms: a local instance that redefines divisibility, a local macro rule that rewrites `≤`, a section `variable` that adds an instance hypothesis, and a misspelled variable that Lean binds automatically. A report on a prover checkpoint that had learned to cheat lists nine patterns, among them macros, added `variable`s, redefined names and local instances; of its 1,003 attempts that passed a syntax check, 999 also passed a comparison of statement text (Wang et al. 2026).
- **C. Fidelity.** Does the asked statement say what was meant? No tool decides this. An audit of miniF2F reports discrepancies between the formal and informal statements in more than half of its 488 problems (Ospanov, Farnia and Yousefzadeh 2025). In Lean 4 ports of ProofNet, 118 of 371 entries had formalization errors (Poiroux et al. 2024). A static audit of five Lean benchmarks raised 4,833 findings, 398 of them with a machine-checked certificate that the statement is unprovable or vacuous (Ammanamanchi, Bhat and Biderman 2026). The Formal Conjectures project records 291 corrected statements over its history (Firsching et al. 2026).

Provers have used such flaws: a statement with truncated subtraction on the naturals (Lample et al. 2022), an interface bug that left a hole unreported, and a hypothesis that is contradictory at zero (Ren et al. 2025).

| Class (layer C) | Example | What a reader would have to show |
| --- | --- | --- |
| Totalized operations | `x / 0 = 0`, `2 - 3 = 0` on `ℕ`, `Real.sqrt` of a negative (Common Lean Pitfalls) | Each such occurrence marked, with the hypothesis that guards it or "none found" |
| Meaning set by a type or a coercion | `(1 / 2 : ℕ)`; the distance on `Fin n → ℝ` is the sup metric | The carrier of every operation; each coercion as a step |
| Boundary cases | `n = 0` not excluded; points not required distinct | The range of each bound variable; distinctness shown or visibly absent |
| Binder structure | Quantifier order; a second binder that shadows the first; a type bound outside an `∃` that should be inside | What each witness may depend on; one object per bound variable even when names coincide |
| Hypotheses | Missing, extra, contradictory, or an instance argument that quantifies over all structures (`[Ring ℤ]`) | The full hypothesis list, instance hypotheses included; the result of a bounded attempt to derive `False` |
| Conclusion | An equality case dropped; the answer written into the statement | The shape of the conclusion; an answer as a definition body |
| Familiar name, different concept | A project-local `Prime`; a library notion that is not the textbook one | Each definition opened; the module that declares each constant |
| Notation | A misplaced parenthesis around a big operator | The structure of the elaborated tree, with each operator's scope as a frame |
| Universe and sort | `Sort _` resolved to `Prop` | The sort of each type binder |

Sources for the table: Common Lean Pitfalls; Myers's conventions for IMO statements; the appendix of Firsching et al.; Ammanamanchi et al. The same communities' practice for the human step is text: challenge and solution files kept apart, written conventions, test lemmas and curated examples that act as a specification (Commelin and Topaz 2024), and review by a Lean expert ("Did you prove it?"). Tao (2026) names subtle errors in the statement as one of two risks that remain for machine-written Lean proofs. We found no reader or visual tool aimed at that step.

Two facts for the axiom policy: the Lean 4.28.0 reference lists three compiler-trust axioms, `Lean.trustCompiler`, `Lean.ofReduceBool` and `Lean.ofReduceNat`; and it describes them for versions up to 4.28.0, so the names can change with the toolchain. A policy must therefore be an allowlist and never a list of forbidden names.

## 4. Existing tools

- **General statement readers show text.** The Lean infoview makes every displayed subexpression a link to its term, with types and implicit values on hover (Nawrocki, Ayers and Ebner 2023). Isabelle/jEdit, doc-gen4, Verso and Alectryon are likewise text with links. This is the baseline a reading session should compare against.
- **Statement diagrams in Lean are per-domain.** Mathlib's commutative-diagram and string-diagram widgets and the ProofWidgets Venn demonstration each match particular constants; the string-diagram widget states that it ignores associators and unitors. A category-theory project's theorem visualizer (co-dh/freyd, pull request 48) is the nearest relative we found; it carries no licence, so nothing may be taken from it.
- **Proof tools are a different job.** Paperproof draws proof steps; leanblueprint draws dependency graphs between results.
- **A display that reads back is unclaimed.** Lean's aid for printing terms that elaborate back (`pp.analyze`) is documented in its source as neither sound nor complete. Wiedijk (2012) names the property, a system that can parse what it prints, and a remedy: print, parse back, and fall back to a fully explicit form on a mismatch. Definograph's rule that a drawing reads back to its view is the diagram form of that property, and its runtime readback in the source-structure view is that remedy.
- **Two routes to "readable" carry no guarantee.** Penrose lays diagrams out by numerical optimization from hand-written input; one input can have several pictures, and in a stress test about half of 2,000 random programs had constraints that could not all be met (Ye et al. 2020). Informalization by a language model reports accuracy, not faithfulness (Gao et al. 2024). A rule-based alternative for prose exists (Ranta 2026).
- **Diagram logics stop at first-order logic.** Constraint diagrams (Fish, Flower and Howse 2005), the flower calculus (Donato 2024) and string diagrams for first-order logic (Bonchi et al. 2024) do not treat dependent types, implicit arguments, instances or universes, in what we read. That part has no precedent to copy.

Licence boundary: Lean, Mathlib, ProofWidgets, doc-gen4, Verso, comparator, SafeVerify and LeanAide are Apache-2.0, and Penrose and Paperproof are MIT, which are compatible with this repository if code were ever reused. No code is to be taken from copyleft projects (rocq-lsp and coq-dpdgraph are LGPL-2.1, jsCoq is AGPL) or from repositories with no licence.

## 5. Where the reader stood against these rules on 2026-10-12

Items 1 to 4 were addressed on 2026-10-13, and item 6 in part; [Guided reading](guided-reading.md) describes what was built. Items 5 and 7 to 9 stand.

An audit of `src/visual`, `src/reading` and the recorded views found:

1. **The two quantifier orders look alike.** `∀ x, ∃ y, x < y` and `∃ y, ∀ x, x < y` have the same silhouette in every default view. In the Choices view both show two cards with a chip box in the second; a 10px caption differs. In the default guided step the visible difference is the order of two small chips.
2. **The skeleton is text.** Nested frames are drawn only in the optional Construction graph, which simple statements never get. The default views carry scope by labels, breadcrumbs and list order.
3. **One spatial relation is wrong.** The Whole-statement outline stops indenting below depth 3, so the innermost parts of a long statement are drawn as siblings of their ancestors ([statement-reading.css](https://github.com/N-Y-L/definograph/blob/c25d9605dbbfc14e542fb4cfc1569ead3f02d61f/src/visual/statement-reading.css) at the audited revision, the `.sr-overview-deep` rule, since removed).
4. **Colour collides.** Identity colour is a hash into eight colours of nearly equal lightness ([object-identity.ts](https://github.com/N-Y-L/definograph/blob/c25d9605dbbfc14e542fb4cfc1569ead3f02d61f/src/visual/object-identity.ts) at the audited revision, since replaced). Nine of the thirteen recorded views that colour objects show two different objects in one colour.
5. **One object, several looks.** A function is an arrow in one figure and a box in the next; the same label is drawn at 23px and at 34px; `x` appears twice inside one equality figure.
6. **The largest text is an instruction.** The step title is 29px and the statement's own clause 23px; a one-line statement takes 5 to 20 clicks.
7. **A figure looks the same whether its clause is assumed, negated or concluded.**
8. **Opened definitions are not delimited.** A variable from inside an unfolded definition appears among the statement's own binders.
9. **Long statements are cut at the inner end,** where dependence matters most: the Choices view shows 12 of the Lebesgue-number lemma's 14 choices and drops the last witness.

## 6. Not confirmed

Read only as an abstract or a record: Stenning and Oberlander; Shimojima and Katagiri; Cleveland and McGill; Cowan 2001; Trick and Pylyshyn; Rodgers et al.; Hanenberg et al.; Purchase; Ware et al.; Ghoniem et al.; Robertson et al.; Archambault et al.; Schroeder and Cenkci; Ginns; Gleicher et al.; Piatek-Jimenez and Dawkins and Roh (in one of the two reviews); El-Attar; Moody. Not opened at all, and so not cited: Green and Petre (1996), Bertin, Ware's book, Edwards and Ward (2004), Inglis and Alcock (2012) beyond its abstract. The exact order of Mackinlay's ranking for unordered data was seen only as an image.

## References

Perception and notation

- Alcock, L., Hodds, M., Roy, S., Inglis, M. (2015). Investigating and improving undergraduate proof comprehension. *Notices of the AMS* 62(7), 742–752. <https://hdl.handle.net/2134/17470>
- Alznauer, N., Peitek, N., Abdelsalam, Y., Bergum, A., Wyrich, M., Apel, S. (2026). Eye-tracking insights into the effects of type annotations and identifier naming. ICPC '26. <https://doi.org/10.1145/3794763.3794801>
- Archambault, D., Purchase, H., Pinaud, B. (2011). Animation, small multiples, and the effect of mental map preservation in dynamic graphs. *IEEE TVCG* 17(4), 539–552. <https://doi.org/10.1109/TVCG.2010.78>
- Blake, A., Stapleton, G., Rodgers, P., Howse, J. (2016). The impact of topological and graphical choices on the perception of Euler diagrams. *Information Sciences* 330, 455–482. <https://doi.org/10.1016/j.ins.2015.05.020>
- Bonchi, F., Di Giorgio, A., Haydon, N., Sobocinski, P. (2024). Diagrammatic algebra of first order logic. arXiv:2401.07055. <https://arxiv.org/abs/2401.07055>
- Chapman, P., Stapleton, G., Rodgers, P., Micallef, L., Blake, A. (2014). Visualizing sets: an empirical comparison of diagram types. Diagrams 2014, LNCS 8578, 146–160. <https://doi.org/10.1007/978-3-662-44043-8_18>
- Cleveland, W. S., McGill, R. (1984). Graphical perception: theory, experimentation, and application to the development of graphical methods. *JASA* 79(387), 531–554. <https://doi.org/10.1080/01621459.1984.10478080>
- Cowan, N. (2001). The magical number 4 in short-term memory. *Behavioral and Brain Sciences* 24(1), 87–114. <https://doi.org/10.1017/S0140525X01003922>
- Cowan, N. (2010). The magical mystery four: how is working memory capacity limited, and why? *Current Directions in Psychological Science* 19(1), 51–57. <https://pmc.ncbi.nlm.nih.gov/articles/PMC2864034/>
- El-Attar, M. (2022). Empirically evaluating the effect of the Physics of Notations on model construction. *IEEE TSE* 48(7), 2455–2475. <https://doi.org/10.1109/TSE.2021.3060344>
- Ghoniem, M., Fekete, J.-D., Castagliola, P. (2005). On the readability of graphs using node-link and matrix-based representations. *Information Visualization* 4(2), 114–135. <https://doi.org/10.1057/palgrave.ivs.9500092>
- Ginns, P. (2006). Integrating information: a meta-analysis of the spatial contiguity and temporal contiguity effects. *Learning and Instruction* 16(6), 511–525. <https://doi.org/10.1016/j.learninstruc.2006.10.001>
- Gleicher, M., Albers, D., Walker, R., Jusufi, I., Hansen, C. D., Roberts, J. C. (2011). Visual comparison for information visualization. *Information Visualization* 10(4), 289–309. <https://doi.org/10.1177/1473871611416549>
- Green, T., Blackwell, A. (1998). Cognitive dimensions of information artefacts: a tutorial (version 1.2). <https://www.cl.cam.ac.uk/~afb21/CognitiveDimensions/CDtutorial.pdf>
- Hanenberg, S., Morzeck, J., Gruhn, V. (2024). Indentation and reading time: a randomized control trial on the differences between generated indented and non-indented if-statements. *Empirical Software Engineering* 29(5). <https://doi.org/10.1007/s10664-024-10531-y>
- Healey, C. G., Enns, J. T. (2012). Attention and visual memory in visualization and computer graphics. *IEEE TVCG* 18(7), 1170–1188. <https://doi.org/10.1109/TVCG.2011.127>
- Howse, J., Stapleton, G., Taylor, J. (2005). Spider diagrams. *LMS Journal of Computation and Mathematics* 8, 145–194. <https://doi.org/10.1112/S1461157000000942>
- Howse, J., Bosworth, R., Fish, A., Taylor, J., Rodgers, P., Stapleton, G., Thompson, S. (undated, about 2005). Reasoning with Diagrams: final report. Universities of Brighton and Kent. <https://www.cs.kent.ac.uk/projects/rwd/Documents/rwdFinalReport.pdf>
- Landy, D., Goldstone, R. L. (2007). How abstract is symbolic thought? *Journal of Experimental Psychology: Learning, Memory, and Cognition* 33(4), 720–733. <https://doi.org/10.1037/0278-7393.33.4.720>
- Larkin, J. H., Simon, H. A. (1987). Why a diagram is (sometimes) worth ten thousand words. *Cognitive Science* 11(1), 65–100. <https://doi.org/10.1111/j.1551-6708.1987.tb00863.x>
- Mackinlay, J. (1986). Automating the design of graphical presentations of relational information. *ACM Transactions on Graphics* 5(2), 110–141. <https://doi.org/10.1145/22949.22950>
- Marghetis, T., Landy, D., Goldstone, R. L. (2016). Mastering algebra retrains the visual system to perceive hierarchical structure in equations. *Cognitive Research: Principles and Implications* 1:25. <https://doi.org/10.1186/s41235-016-0020-9>
- Moody, D. L. (2009). The "Physics" of Notations: toward a scientific basis for constructing visual notations in software engineering. *IEEE TSE* 35(6), 756–779. <https://doi.org/10.1109/TSE.2009.67> (abstract only; principles confirmed through secondary summaries)
- Purchase, H. C. (1997). Which aesthetic has the greatest effect on human understanding? Graph Drawing '97, LNCS 1353, 248–261. <https://doi.org/10.1007/3-540-63938-1_67>
- Robertson, G., Fernandez, R., Fisher, D., Lee, B., Stasko, J. (2008). Effectiveness of animation in trend visualization. *IEEE TVCG* 14(6), 1325–1332. <https://doi.org/10.1109/TVCG.2008.125>
- Rodgers, P., Zhang, L., Purchase, H. (2012). Wellformedness properties in Euler diagrams: which should be used? *IEEE TVCG* 18(7), 1089–1100. <https://doi.org/10.1109/TVCG.2011.143>
- Schroeder, N. L., Cenkci, A. T. (2018). Spatial contiguity and spatial split-attention effects in multimedia learning environments: a meta-analysis. *Educational Psychology Review* 30(3), 679–701. <https://doi.org/10.1007/s10648-018-9435-9>
- Selinger, P. (2011). A survey of graphical languages for monoidal categories. In *New Structures for Physics*, Lecture Notes in Physics 813, 289–355. <https://arxiv.org/abs/0908.3347>
- Shimojima, A., Katagiri, Y. (2013). An eye-tracking study of exploitations of spatial constraints in diagrammatic reasoning. *Cognitive Science* 37(2), 211–254. <https://doi.org/10.1111/cogs.12026>
- Shin, S.-J., Lemon, O., Mumma, J. (2001, revised 2025). Diagrams and diagrammatical reasoning. *Stanford Encyclopedia of Philosophy*. <https://plato.stanford.edu/entries/diagrams/>
- Stapleton, G. (2018). Reasoning with diagrams: observation, inference and overspecificity. DMS 2018, invited paper. <https://research.brighton.ac.uk/en/publications/reasoning-with-diagrams-observation-inference-and-overspecificity/>
- Stenning, K., Oberlander, J. (1995). A cognitive theory of graphical and linguistic reasoning: logic and implementation. *Cognitive Science* 19(1), 97–140. <https://doi.org/10.1207/s15516709cog1901_3>
- Trick, L. M., Pylyshyn, Z. W. (1994). Why are small and large numbers enumerated differently? A limited-capacity preattentive stage in vision. *Psychological Review* 101(1), 80–102. <https://doi.org/10.1037/0033-295X.101.1.80>
- Tversky, B., Morrison, J. B., Betrancourt, M. (2002). Animation: can it facilitate? *International Journal of Human-Computer Studies* 57(4), 247–262. <https://doi.org/10.1006/ijhc.2002.1017>
- W3C Web Accessibility Initiative. Understanding Success Criterion 1.4.1: Use of Color (WCAG 2.2). <https://www.w3.org/WAI/WCAG22/Understanding/use-of-color.html>
- Ware, C., Purchase, H., Colpoys, L., McGill, M. (2002). Cognitive measurements of graph aesthetics. *Information Visualization* 1(2), 103–110. <https://doi.org/10.1057/palgrave.ivs.9500013>
- Wolfe, J. M., Horowitz, T. S. (2017). Five factors that guide attention in visual search. *Nature Human Behaviour* 1, 0058. <https://doi.org/10.1038/s41562-017-0058>

Reading statements

- Alcock, L., Simpson, A. (2011). Classification and concept consistency. *Canadian Journal of Science, Mathematics and Technology Education* 11(2), 91–106. <https://repository.lboro.ac.uk/articles/journal_contribution/Classification_and_concept_consistency/9370916>
- Dawkins, P. C., Roh, K. H. (2020). Assessing the influence of syntax, semantics, and pragmatics in student interpretation of multiply quantified statements in mathematics. *IJRUME* 6(1), 1–22. <https://doi.org/10.1007/s40753-019-00097-2>
- Dubinsky, E., Yiparaki, O. (2000). On student understanding of AE and EA quantification. *Research in Collegiate Mathematics Education IV*, 239–289. <https://www.math.kent.edu/~edd/OlgaPaper.pdf>
- Greenman, B., Saarinen, S., Nelson, T., Krishnamurthi, S. (2023). Little tricky logic: misconceptions in the understanding of LTL. *The Art, Science, and Engineering of Programming* 7(2), 7:1–7:37. <https://doi.org/10.22152/programming-journal.org/2023/7/7>
- Kellman, P. J., Massey, C. M., Son, J. Y. (2010). Perceptual learning modules in mathematics: enhancing students' pattern recognition, structure extraction, and fluency. *Topics in Cognitive Science* 2(2), 285–305. <https://pmc.ncbi.nlm.nih.gov/articles/PMC6124488>
- Ko, A. J., LaToza, T. D., Burnett, M. M. (2015). A practical guide to controlled experiments of software engineering tools with human participants. *Empirical Software Engineering* 20(1), 110–141. <https://doi.org/10.1007/s10664-013-9279-3>
- Loomes, M., Vinter, R. (1996). Formal methods: no cure for faulty reasoning. University of Hertfordshire, Technical Report 265. <https://uhra.herts.ac.uk/id/eprint/12213/>
- Nielsen, J. (2000). Why you only need to test with 5 users. Nielsen Norman Group. <https://www.nngroup.com/articles/why-you-only-need-to-test-with-5-users/>
- Piatek-Jimenez, K. (2010). Students' interpretations of mathematical statements involving quantification. *Mathematics Education Research Journal* 22(3), 41–56. <https://doi.org/10.1007/BF03219777>
- Selden, J., Selden, A. (1995). Unpacking the logic of mathematical statements. *Educational Studies in Mathematics* 29(2), 123–151. <https://philpapers.org/archive/SELUTL.pdf>
- Tall, D., Vinner, S. (1981). Concept image and concept definition in mathematics with particular reference to limits and continuity. *Educational Studies in Mathematics* 12, 151–169. <https://wrap.warwick.ac.uk/id/eprint/507/>
- Vroom, K. (2022). A functional perspective on student thinking about the grammar of multiply quantified statements. *Journal of Mathematical Behavior* 67, 100992. <https://par.nsf.gov/servlets/purl/10485533>
- Wyrich, M., Bogner, J., Wagner, S. (2023). 40 years of designing code comprehension experiments: a systematic mapping study. *ACM Computing Surveys*; arXiv:2206.11102. <https://arxiv.org/abs/2206.11102>

Proved statements and intent

- Ammanamanchi, P. S., Bhat, S., Biderman, S. (2026). Faults in our formal benchmarking: dataset defects and evaluation failures in Lean theorem proving. ICML 2026; arXiv:2606.29493. <https://arxiv.org/abs/2606.29493>
- Commelin, J., Topaz, A. (2024). Abstraction boundaries and spec driven development in pure mathematics. *Bulletin of the AMS* 61(2), 241–255. <https://arxiv.org/abs/2309.14870>
- de Moura, L. (2026). Postmortem for kernel soundness bug #14576. <https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/>
- Firsching, M., Lezeau, P., Mercuri, S., Horváth, M. Z., Dillies, Y., Sönne, C., Wieser, E., Zhang, F., Hubert, T., Agüera y Arcas, B., Kohli, P. (2026). Formal Conjectures: an open and evolving benchmark for verified discovery in mathematics. arXiv:2605.13171. <https://arxiv.org/abs/2605.13171>
- Lample, G., Lachaux, M.-A., Lavril, T., Martinet, X., Hayat, A., Ebner, G., Rodriguez, A., Lacroix, T. (2022). HyperTree proof search for neural theorem proving. arXiv:2205.11491. <https://arxiv.org/abs/2205.11491>
- Lean community. Common Lean pitfalls. <https://leanprover-community.github.io/extras/pitfalls.html>
- Lean community. Did you prove it? <https://leanprover-community.github.io/did_you_prove_it.html>
- Lean developers (2026). The Lean Language Reference, version 4.28.0: "Validating a Lean Proof" and "Axioms". <https://lean-lang.org/doc/reference/4.28.0/ValidatingProofs/>, <https://lean-lang.org/doc/reference/4.28.0/Axioms/>
- Lean FRO. comparator (repository, Apache-2.0). <https://github.com/leanprover/comparator>
- lean4 issue #14576 (2026). Kernel accepts wrong-structure projections, allowing an axiom-free proof of False. <https://github.com/leanprover/lean4/issues/14576>
- Myers, J. (2025). IMO Lean formalization conventions. <https://github.com/jsm28/IMOLean>
- Ospanov, A., Farnia, F., Yousefzadeh, R. (2025). miniF2F-Lean revisited: reviewing limitations and charting a path forward. arXiv:2511.03108. <https://arxiv.org/abs/2511.03108>
- Poiroux, A., Weiss, G., Kunčak, V., Bosselut, A. (2024, revised 2025). Reliable evaluation and benchmarks for statement autoformalization. arXiv:2406.07222. <https://arxiv.org/abs/2406.07222>
- Ren, Z. Z., et al. (2025). DeepSeek-Prover-V2: advancing formal mathematical reasoning via reinforcement learning for subgoal decomposition. arXiv:2504.21801. <https://arxiv.org/abs/2504.21801>
- SafeVerify (repository, Apache-2.0). <https://github.com/GasStationManager/SafeVerify>
- Tao, T. (2026). Post on confidence in AI-generated proofs and Lean certificates. <https://mathstodon.xyz/@tao/116059100709081011>
- Wang, J., et al. (2026). LongCat-Flash-Prover: advancing native formal reasoning via agentic tool-integrated reinforcement learning. arXiv:2603.21065. <https://arxiv.org/abs/2603.21065>
- Wiedijk, F. (2012). Pollack-inconsistency. *Electronic Notes in Theoretical Computer Science* 285, 85–100. <https://doi.org/10.1016/j.entcs.2012.06.008>

Existing tools

- co-dh/freyd, pull request 48 (2026). A theorem visualizer (no licence). <https://github.com/co-dh/freyd/pull/48>
- Donato, P. (2024). The flower calculus. FSCD 2024, LIPIcs 299, 5:1–5:24. <https://arxiv.org/abs/2402.15174>
- Fish, A., Flower, J., Howse, J. (2005). The semantics of augmented constraint diagrams. *Journal of Visual Languages and Computing* 16(6), 541–573. <https://doi.org/10.1016/j.jvlc.2005.03.001>
- Gao, G., Wang, Y., Jiang, J., Gao, Q., Qin, Z., Xu, T., Dong, B. (2024). Herald: a natural language annotated Lean 4 dataset. arXiv:2410.10878. <https://arxiv.org/abs/2410.10878>
- Lean 4, version 4.28.0. `src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean` and `Options.lean` (Apache-2.0). <https://github.com/leanprover/lean4/tree/v4.28.0/src/Lean/PrettyPrinter/Delaborator>
- leanblueprint (repository). <https://github.com/PatrickMassot/leanblueprint>
- Mathlib. `Mathlib/Tactic/Widget/CommDiag.lean` and `StringDiagram.lean` (Apache-2.0). <https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Tactic/Widget>
- Nawrocki, W., Ayers, E. W., Ebner, G. (2023). An extensible user interface for Lean 4. ITP 2023, LIPIcs 268, 24:1–24:20. <https://doi.org/10.4230/LIPIcs.ITP.2023.24>
- Paperproof (repository). <https://github.com/Paper-Proof/paperproof>
- Pit-Claudel, C. (2020). Untangling mechanized proofs. SLE 2020, 155–174. Alectryon repository: <https://github.com/cpitclaudel/alectryon>
- ProofWidgets4 (repository, Apache-2.0); doc-gen4 and Verso (repositories, Apache-2.0). <https://github.com/leanprover-community/ProofWidgets4>, <https://github.com/leanprover/doc-gen4>, <https://github.com/leanprover/verso>
- Ranta, A. (2026). Symbolic informalization: fluent, productive, multilingual. arXiv:2606.16893. <https://arxiv.org/abs/2606.16893>
- Wenzel, M. Isabelle/jEdit (manual). <https://isabelle.in.tum.de/doc/jedit.pdf>
- Ye, K., Ni, W., Krieger, M., Ma'ayan, D., Wise, J., Aldrich, J., Sunshine, J., Crane, K. (2020). Penrose: from mathematical notation to beautiful diagrams. *ACM Transactions on Graphics* 39(4), article 144. <https://doi.org/10.1145/3386569.3392375>

Research and recommendations: Claude, working under the direction of Neil Yuanting Li. The item budgets in section 1 and the three layers in section 3 are our own organization of the sources.
