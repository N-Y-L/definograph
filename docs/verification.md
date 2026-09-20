# Verification record

Verified on 2026-09-19 using macOS arm64, Node.js 24.18.1, Lean 4.28.0, and pinned mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## Release 0.3 checks

The statement-first release passes strict TypeScript, the production build, and **305 automated checks**:

| Suite | Passed | Added assurance |
|---|---:|---|
| `npm test` | 157 | Complete reading composition, scoped sequences, semantic diagrams, composed map paths, symbolic radius cases, identity preservation, bounded safe KaTeX rendering, and prior core checks |
| `npm run test:server` | 26 | Local transport, cancellation, request limits, process replacement, and static asset containment |
| `npm run test:lean` | 45 | Real Lean elaboration, kernel checks, instance audits, signatures/bodies, and rejection of executable input |
| `npm run test:integration` | 15 | All 14 interface examples through the actual worker plus combined geometry/dependency behavior |
| `npm run test:semantic` | 21 | Typed object/relationship recognition, scope, partial applications, and declaration behavior |
| `npm run test:reading` | 20 | Whole-statement sequence and overview, negation, alternatives, both iff directions, witnesses, abstract composition, and dependent morphism families |
| `npm run test:notation` | 21 | Actual LeanTeX output through strict KaTeX, binder order, logical grouping, definition bodies/signatures, custom instances, fallback recovery, and aggregate response limits |

The default UI was checked in the in-app browser for symbolic geometry, abstract sets, an equation between composed maps, fixed-before-universal witness order, and negation inside a disjunction. No numerical sliders appear in the default reading; the separate exploration action retains the numerical views. Mathematical notation rendered from real worker output with local fonts. Mobile-width DOM checks at a browser-reported 500 pixels showed no horizontal document overflow. Deep overview indentation was capped after the desktop screenshot exposed narrow text columns. No console errors appeared in the final exercised workflows.

Review found and corrected a diagram drawing the same center expression as two distinct points. It now shows one object and the distance-to-self condition. Native notation integration also required resolving duplicate printer-extension initialization; the final worker dynamically imports the fixed printer once and calls only its trusted entry point. Worker builds atomically replace the executable. Optional notation cannot enlarge an otherwise accepted response beyond the transport limit: it is dropped before required semantic fields.

LeanTeX source is pinned and checksummed. Compatibility changes are applied only to isolated build copies. No additional Mathlib modules were introduced. See [the LeanTeX integration record](leantex-integration.md) and [the statement-first acceptance review](statement-first-review.md).

## Historical release 0.2 checks

`npm run check` passes: strict TypeScript, production build, and **213 automated checks**.

| Suite | Passed | Behaviors exercised |
|---|---:|---|
| `npm test` | 107 | Numerical interpretation, semantic identities, rule completeness, scopes, automatic planning, UTF-8 source mapping, layout bounds, high-dimensional geometry, bounded controls |
| `npm run test:server` | 26 | Host/origin checks, request options and limits, cancellation, timeout recovery, persistent protocol matching, static-path containment |
| `npm run test:lean` | 45 | Actual Lean parsing/elaboration/kernel checks, imported declarations, definition bodies and expansion, typed roles, exact source occurrences, custom instances, rejected executable input |
| `npm run test:integration` | 14 | Every interface example through native Lean and the semantic/numerical pipeline, plus combined geometric and witness-state checks |
| `npm run test:semantic` | 21 | Native Lean through semantic extraction and automatic planning across independent mathematical structures |

The semantic end-to-end suite includes abstract sets, images/preimages, function composition, arbitrary curried relations, uninterpreted topology, known geometry inside an unknown predicate, replacement membership and metric instances, 21-dimensional spheres, scoped witnesses, lambda bodies, imported theorem statements, parameterized definition bodies, and explicit unfolding. Renaming binders and regrouping conjunctions preserve recognized mathematical relationships.

Higher-order partial applications of equality, image, and ball constructors are checked explicitly: a constructor awaiting arguments must not be rendered as a completed relation or geometric region. Both modern typed metadata and older full-arity fixtures are exercised. Implication hypotheses are available only in the consequent.

Numerical tests include the final coordinate of 21D and 256D vectors in Euclidean and maximum distances, slices, and complete distance profiles. Larger numerical vectors remain symbolic. A million-coordinate type does not allocate a million controls. Other cases include negative/nonpositive radii, tangent intersections, filled maximum-metric sphere slices, huge integers, finite-domain numerals, division by zero, custom operations, and unknown predicates. `False` remains a valid proposition with no implied proof.

## Historical release 0.2 browser checks

The production interface was exercised in the Codex in-app browser:

- Default geometric selection and generic set relationship diagrams.
- Declaration lookup, automatic definition-body inspection, and switching between body and typed signature.
- Shared source-fragment inspection retaining implication context.
- A 21-coordinate point whose final coordinate changes the full distance from 0 to 3 and changes sample membership.
- Switching from the high-dimensional profile to a slice, selecting a late coordinate axis, then analyzing a 2D statement without stale axis state.
- Lean abbreviation entry (`\\forall` plus Tab), immediate removal of stale diagrams after edits, unknown-name diagnostics, and recovery to valid analysis.
- Responsive layouts at browser-reported widths 480, 780, and 2560 pixels without horizontal document overflow. The in-app browser's viewport override has a minimum width, so a 390-pixel layout was not verified.
- No browser console errors in the exercised workflows.

These checks found and corrected stale BallView coordinate state, misleading inherited-choice priority for a selected relation, source/example label mismatch, and signature/body state handling. Browser checks are recorded observations, not a complete automated UI regression suite.

## Isolation and reproducibility

Development used an isolated local checkout. Its worker read StatementLens's own dedicated mathlib cache and the pinned installed Lean binary. No other formal project or global toolchain setting was modified. The source contains no machine-specific runtime paths; those stay in ignored `.local/config.json`. No commits were pushed and no remote repository was configured.

The original clean-cache download smoke test remains applicable: setup fetched 2,372 pinned transitive module caches into a dedicated directory and built a working worker. Release 0.2 adds no Lean imports or mathlib dependencies. CodeMirror dependencies are pinned in `package-lock.json`; the editor is split into a separate production chunk.

## What remains unverified or incomplete

Passing these checks is not a proof that the renderer is bug-free. Lean's kernel checks the submitted expression or definition expansion; the TypeScript semantic rules, layout, and floating-point evaluator have regression tests rather than formal correctness proofs. Numerical samples cannot certify universal statements or exact real equality.

The fixed imported environment and allowlisted term syntax do not accept every Lean project or incomplete expression. Source occurrences are exact, but transformed-node-to-source mapping is not guessed. Definition unfolding is bounded and acts at logical heads. The planner uses explicit heuristics and representation contracts, not a verified global optimum. Rich geometric realization for arbitrary structures, witness strategies, active Lean editor extraction, and Rocq support remain future work.
