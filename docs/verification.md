# Verification record

Verified on 2026-09-19 using macOS arm64, Node.js 24.18.1, Lean 4.28.0, and pinned mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## Release 0.7 checks

The deterministic decomposition iteration passes strict TypeScript, the production build, and **725 automated checks**: 721 in `npm run check`, plus four extension checks. Counts come from `.local/check-0.7.log` and `.local/extension-check-0.7.log`; builds and packaging are not tests.

| Suite | Passed | Main coverage |
|---|---:|---|
| `npm test` | 369 | 30 files, including generic reflected fields, malformed metadata, shared applications, scope, and rendering |
| `npm run test:server` | 29 | HTTP/IPC boundaries, cancellation, editor context, and request validation |
| `npm run test:lean` | 46 | Native elaboration, kernel checks, syntax isolation, and universes |
| `npm run test:integration` | 26 | All 25 interface examples and numerical/dependency behavior |
| `npm run test:semantic` | 21 | Typed semantics and conservative recognition |
| `npm run test:reading` | 20 | Logical reading and dependencies |
| `npm run test:notation` | 32 | LeanTeX/KaTeX and all interface examples |
| `npm run test:atlas` | 21 | Typed constructions through the production renderer |
| `npm run test:cues` | 15 | Ordered constructions and retained context |
| `npm run test:sets` | 7 | Compound sets and unknown instances |
| `npm run test:editor` | 23 | Actual context extraction and unchanged project files |
| `npm run test:graphs` | 15 | Graph contracts and lookalike rejection |
| `npm run test:graph-reading` | 8 | Native graph semantics through the production reader |
| `npm run test:inspection` | 5 | Checked automatic inspection and single source execution |
| `npm run test:definition-previews` | 8 | Preview budgets, placeholders, and mandatory response preservation |
| `npm run test:corpus` | 25 | Supported, partial, and unknown vocabulary with stable native hashes |
| `npm run test:restricted` | 18 | Optional restricted-map lens, aliases, and custom-coercion boundaries |
| `npm run test:restricted-reading` | 15 | Actual editor context through scoped restricted-map diagrams |
| `npm run test:structure-export` | 8 | Native reflection, parent fields, law-only records, bounded aliases, source isolation, and transport trimming |
| `npm run test:decomposition` | 10 | Unseen definitions, full renaming, internal carriers, aliases, opaque fields/laws, separate witnesses, and production diagrams |
| Extension checks | 4 | Mocked VS Code request lifecycle and stale-result rejection |

The generic acceptance cases require no additions to the mathematical recognizer catalogue. Completely renamed records and fields produce the same primitive topology. Reflected fields keep their exact projected identities in law applications. Internal carrier fields stay shared with operations and elements. Local hypotheses and separate existential alternatives keep their fields in the owner's scope. The original statement remains intact alongside supplementary laws.

Browser checks used actual native editor exports through the hosted-browser bridge. They exercised unfamiliar maps and sets, a function-type alias, switching field laws, a composed round trip under its membership hypothesis, an internal carrier with a binary operation, a 23-field record with seven visibly omitted fields, a law-only hypothesis at its conditional step, and the explicit two-step alias boundary. The checked final-build workflows produced no console warnings or errors. A browser-reported 1272-pixel view had no horizontal document overflow; mobile layouts were not reverified in this iteration.

These checks exposed and corrected lost alias applications, missing hypothesis diagrams, missing projected fields in conclusion scope, and indistinguishable shortened map labels. An older SSR helper incorrectly stopped at a nested law reader; the corrected helper verifies that the original compact graph views remain present.

The extension packages as `.local/statement-lens-editor-0.7.0.vsix`. It has not been installed or published by this iteration. Actual VS Code GUI activation and complete extension-host use, and native Windows operation, remain unverified. The checked local browser bridge is not a substitute for that host validation.

Direct structure reflection and bounded unfolding are implemented foundations, not universal geometric understanding. Early native budget/type-size exits may retain only the original typed object without a specific reason; recursive value/inductive decomposition and automatic abstraction selection remain incomplete. See [the decomposition record](decomposition-iteration.md) and [the roadmap](roadmap.md).

## Historical release 0.6 checks

The graph-constraints and definition-inspection iteration passes strict TypeScript, the production build, and **587 automated checks**: 583 in `npm run check`, plus four extension checks. Counts come from `.local/check-0.6.log` and `.local/extension-check-0.6.log`; builds and packaging are not tests.

| Suite | Passed | Main coverage |
|---|---:|---|
| `npm test` | 297 | 25 files including graph contracts, scope and identity guards, coverage reports, preview selection, and existing behavior |
| `npm run test:server` | 29 | HTTP/IPC boundaries, cancellation, editor context, and preview-option validation |
| `npm run test:lean` | 46 | Native elaboration, kernel checks, syntax isolation, universe metadata |
| `npm run test:integration` | 22 | All 21 interface examples and combined geometry/dependency behavior |
| `npm run test:semantic` | 21 | Native typed semantics, scope, and conservative recognition |
| `npm run test:reading` | 20 | Logical reading and dependencies |
| `npm run test:notation` | 28 | Native LeanTeX/KaTeX, all examples, bounded fallback |
| `npm run test:atlas` | 21 | Native typed constructions through the React renderer |
| `npm run test:cues` | 15 | Scoped construction order and guided context |
| `npm run test:sets` | 7 | Boolean sets and unknown-instance preservation |
| `npm run test:editor` | 23 | Real project-context extraction and unchanged fixture files |
| `npm run test:graphs` | 15 | Real graph declarations, overloaded applications, and lookalike rejection |
| `npm run test:graph-reading` | 8 | Native graph semantics through cues and actual React SSR, including branching, Fin 0, source identity, and no React warnings |
| `npm run test:inspection` | 5 | Automatic selection, explicit-policy isolation, preserved originals, and exactly one execution of a trusted editor command |
| `npm run test:definition-previews` | 8 | Native preview budgets, local-assumption scope, caps, placeholder rejection, and preservation of mandatory response fields |
| `npm run test:corpus` | 18 | Audited supported, partial, and unsupported vocabulary probes with native binary/source provenance |
| Extension checks | 4 | Mocked VS Code request lifecycle and stale-result rejection |

Browser checks exercised proper-coloring introductions, graph application steps under an adjacency premise, finite available palettes, automatic left-inverse inspection, restoration of the original statement, and actionable coverage gaps. The inverse reading exposes both maps and their output equality while retaining the original named condition. Review also caught and corrected missing inspection metadata for a definition occurring only in a local hypothesis; its regression checks that the opened premise stays scoped over the conclusion. Visual inspection caught and corrected a missing arrowhead on one branch. No console warnings or errors appeared in the exercised workflows. At the browser-reported width of 1200 pixels, the checked graph reading had no horizontal document overflow; this run's viewport backend did not provide the requested 600-pixel width, so mobile behavior was not reverified.

A hosted-browser fixture using actual native context output also checked a definition used only in a local assumption, buffer-edit invalidation, rejection of obsolete results, and refresh. This fixture produced no browser warnings or errors; it tests the browser bridge, not the VS Code host.

The extension packages as `.local/statement-lens-editor-0.6.0.vsix`. Native context tests and mocked controller checks do not replace an actual VS Code GUI session: installation, activation, and the full editor-host workflow remain unverified. Native Windows operation is also unverified.

The corpus has 18/18 passing expectations, including deliberately unsupported inputs; this is not 18 fully visualized statements. Its report records the mathematical vocabulary still missing. No planarity/four-color-theorem, tangent-field/hairy-ball, derivative, or constant-rank-normal-form grammar is claimed. See [the iteration record](graph-iteration.md), [graph contracts](graph-semantics.md), and [corpus](coverage-corpus.md).

Setup adds the pinned Mathlib coloring module to StatementLens's own dependency cache. Existing formal projects and global toolchain settings remain unchanged. Optional previews run in the original checked Lean context without an additional source replay. Explicit user-requested refreshes and expansions still perform a new analysis. See [editor execution limits](editor-integration.md).

## Historical release 0.5 checks

The guided-constructions iteration passes strict TypeScript, the production build, and **487 automated checks**: 483 in `npm run check`, plus four extension checks. Counts below are recorded from `.local/release-0.5-check.log` and `.local/release-0.5-extension.log`; builds and packaging are not counted as tests.

| Suite | Passed | Added assurance |
|---|---:|---|
| `npm test` | 259 | 21 test files covering guided cues, compositional set regions, identities, scoped reading, host messages, and existing semantic/numerical behavior |
| `npm run test:server` | 29 | Local transport, request bounds, cancellation, asset containment, and editor-context boundaries |
| `npm run test:lean` | 46 | Real Lean elaboration, kernel checks, syntax isolation, and constant universe metadata |
| `npm run test:integration` | 18 | All 17 interface examples and combined geometry/dependency behavior |
| `npm run test:semantic` | 21 | Typed semantic recognition, application completeness, and scope |
| `npm run test:reading` | 20 | Whole-statement logic, witnesses, and abstract relationships |
| `npm run test:notation` | 24 | Native LeanTeX output through strict KaTeX, interface examples, and bounded fallback |
| `npm run test:atlas` | 21 | Native Lean through typed constructions, grouped regions, and the actual React renderer |
| `npm run test:cues` | 15 | Native statements through scope-preserving guided reading cues |
| `npm run test:sets` | 7 | Native Boolean set constructions, composition, and preservation of unknown instances |
| `npm run test:editor` | 23 | Native project-context extraction and its trust, selection, diagnostic, and resource boundaries |
| Extension tests in `npm run check:extension` | 4 | Mocked VS Code controller and lifecycle checks |

The native editor suite uses a temporary Lean project with a compiled imported dependency. It exercises unsaved buffer contents, local parameters and proof assumptions, dependent types, Unicode selections, later file errors, placeholder rejection, canonical-constant and custom-instance guards, toolchain compatibility, cancellation, and deadlines. Its source and configuration fixtures remain unchanged. These are real native extraction checks, not a running VS Code GUI session.

The extension checks compile TypeScript and exercise mocked VS Code APIs, including request ordering, stale-result rejection, selection/reveal behavior, configuration failures, and invalidation after another buffer changes. Packaging also succeeds, producing `.local/statement-lens-editor-0.5.0.vsix` (six files). Packaging verifies the artifact can be built; **installation, activation, and the complete workflow in an actual VS Code GUI have not been tested**. The controller uses the separately configured local engine and assets. Remote editor hosts and native Windows operation remain unverified.

Browser checks covered the guided sequence, abstract maps, compositional sets, and scoped assumptions. At a browser-reported width of 600 pixels, the checked layout had no horizontal document overflow. A hosted-browser fixture used actual native extraction output: local parameters and assumptions rendered, editing cleared the old result, stale responses were discarded, refresh restored the result, source reveal emitted the expected host message, and file diagnostics remained visible with the correct filename and count. This checks the browser side of the editor bridge; it does not substitute for VS Code extension-host testing.

A final pass loaded the rebuilt production reader, the dynamically loaded LeanTeX component, and the CodeMirror source editor. The exercised workflows produced no browser console errors. These browser observations are manual checks, not an exhaustive UI regression suite.

See [guided reading](guided-reading.md), [set constructions](set-constructions.md), and [editor integration](editor-integration.md) for implemented behavior and limits. No Manim runtime was added. Editor extraction replays trusted Lean source in a separate process; it is not a security sandbox and does not certify the surrounding theorem. Existing user projects and global toolchain settings were not modified by these checks.

## Historical release 0.4 checks

The atlas iteration passes strict TypeScript, the production build, and **357 automated checks**:

| Suite | Passed | Added assurance |
|---|---:|---|
| `npm test` | 183 | Typed constructions, exact carrier identities, ordered inputs, dependent families, logical-region grouping, contained expressions, and existing semantic/numerical checks |
| `npm run test:server` | 26 | Local transport, cancellation, request bounds, and asset containment |
| `npm run test:lean` | 46 | Kernel checks, syntax isolation, and constant universe metadata |
| `npm run test:integration` | 17 | All 16 interface examples and combined geometry/dependency behavior |
| `npm run test:semantic` | 21 | Typed semantic recognition and scope |
| `npm run test:reading` | 20 | Whole-statement logic, witnesses, and abstract relationships |
| `npm run test:notation` | 23 | Every interface example through LeanTeX and strict KaTeX, plus bounded fallback and identity checks |
| `npm run test:atlas` | 21 | Real Lean through typed constructions, grouped regions, and the actual React renderer, including universe-distinct carriers and deep selection |

Browser checks covered the default geometry, abstract map paths, dependent type families, contained-expression disclosure, mathematical notation, object inspection, and declaration body/signature switching. Editing invalidates old diagrams immediately; invalid input reports Lean's diagnostic and recovers to valid input. Default reading has no numerical sliders, while the separate exploration panel exposes sample choices. Native dialogs restore focus after Escape and keep editing available during the initial analysis. At browser-reported widths 1272, 650, and 500 pixels, the checked layout had no horizontal document overflow. Widths below 500 pixels were not verified by this browser backend.

A preview rebuild exposed a missing lazy editor chunk that previously blanked the reader. Optional editor and notation components now have local error boundaries. A fault-injection check temporarily withheld the generated editor asset: the existing statement remained visible, a basic text editor accepted a new expression, and native Lean analysis succeeded. The asset was restored immediately. Ordinary final workflows produced no browser console errors; the fault-injection case intentionally produced a handled loading error.

Review also corrected a pending analysis dismissing a different drawer opened after submission. Completion now dismisses only the drawer that initiated that request. Arrow routing separates adjacent maps from a longer composed route.

See [the atlas review](atlas-iteration.md) for semantic boundaries and [the visual-method research](visual-method.md) for the 3Blue1Brown reference and proposed guided-reading foundation. This release adds no Manim dependency and no extra Mathlib import. Existing formal projects and global toolchain settings remain unchanged.

## Historical release 0.3 checks

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

Development used an isolated local checkout. Its worker read StatementLens's own dedicated mathlib cache and the pinned installed Lean binary. No other formal project or global toolchain setting was modified. The source contains no machine-specific runtime paths; those stay in ignored `.local/config.json`. No commits were pushed and no external remote repository was configured.

The original clean-cache download smoke test remains applicable: setup fetched 2,372 pinned transitive module caches into a dedicated directory and built a working worker. Release 0.2 adds no Lean imports or mathlib dependencies. CodeMirror dependencies are pinned in `package-lock.json`; the editor is split into a separate production chunk.

## What remains unverified or incomplete

Passing these checks is not a proof that the renderer is bug-free. Lean's kernel checks the submitted expression or definition expansion; the TypeScript semantic rules, layout, and floating-point evaluator have regression tests rather than formal correctness proofs. Numerical samples cannot certify universal statements or exact real equality.

The standalone reader's fixed imported environment and allowlisted term syntax do not accept every Lean project or incomplete expression. The editor adapter adds trusted project-context extraction, with the toolchain, import, source-selection, and execution limits documented in [editor integration](editor-integration.md). Source occurrences are exact, but transformed-node-to-source mapping is not guessed. Definition unfolding is bounded and acts at logical heads. The planner uses explicit heuristics and representation contracts, not a verified global optimum. Rich geometric realization for arbitrary structures, witness strategies, and Rocq support remain future work. Actual VS Code GUI installation and end-to-end extension-host use remain unverified in release 0.7.
