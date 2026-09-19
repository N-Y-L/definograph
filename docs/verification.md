# Verification record

Verified on 2026-09-19 using macOS arm64, Node.js 24.18.1, Lean 4.28.0, and pinned mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## Automated checks

| Check | Result | What it exercises |
|---|---|---|
| `npm run build` | Pass | Strict TypeScript compilation and production build |
| `npm test` | 43 passed | Instance-aware recognition, numerical domains, boundary cases, quantifier state, and coordinate intersections |
| `npm run test:server` | 25 passed | Request origin/host validation, size limits, cancellation, timeout recovery, process reuse, protocol matching, static-path containment |
| `npm run test:lean` | 25 passed | Actual Lean elaboration and kernel type checking, metric-instance metadata, scope, shadowing, and rejection of executable or incomplete input |
| `npm run test:integration` | 11 passed | All ten examples from the interface through native Lean, scene recognition, and numerical geometry, plus combined semantic assertions |

The native integration checks confirm that the product metric produces a square,
the Euclidean metric produces a disk, and the four-dimensional radius-two sphere
has a slice of radius `√3` when one omitted coordinate is fixed at one. They check
that the explicit function `2*x+1` yields the expected graph samples and that
reversing existential and universal order changes witness invalidation.

Adversarial cases include custom metrics and arithmetic, custom membership,
finite-domain numerals that cannot be treated as real numbers, huge integers,
division by zero, open/closed/tangent boundaries, max-metric sphere slices,
shadowed binders, and unknown predicates alongside supported geometry. `False`
is deliberately accepted as a proposition while proof status remains absent.
Commands, tactics, quotations, unresolved metavariables, and `sorry` are rejected.

The persistent worker was measured at approximately 14.75 seconds for its first
request and 1–8 milliseconds for the tested subsequent small statements. These
are local observations, not latency guarantees. An ordinary Lean diagnostic was
followed by a successful valid request without restarting or retaining the failed
request's elaboration state.

## Browser checks

The production interface was inspected in the Codex browser. Checks included
Euclidean ball rendering, switching to a four-dimensional sphere, moving an
omitted coordinate beyond the sphere to produce an empty intersection, hiding an
off-slice point, invalidating a dependent existential witness, retaining a witness
that precedes a changed universal, removing stale diagrams immediately after source
edits, displaying an unknown-identifier diagnostic, and recovering to another
valid example. These checks found and corrected duplicate development startup
requests and display of an unchosen witness as zero.

The final repository was rebuilt and tested at its destination. A fresh mathlib
download was exercised in an empty isolated directory, then its cache was moved
into the final repository. The native 25-case suite and 11 end-to-end checks passed
again with that dedicated cache. No runtime dependency paths point into another
formal project; the existing pinned Lean binary is read-only.

## Interpretation limits

The mathematical renderer has regression tests, not a Lean proof of its
correctness. JavaScript calculations approximate real arithmetic; finite scans
can miss behavior between samples. Near-boundary comparisons can be marked
unknown, but this is not rigorous interval arithmetic. Exact coincidence of
floating-point values does not certify exact real equality.

Every submitted proposition must elaborate in the fixed imported environment.
Selecting a fragment retains its quantifier scope, but recovery from an invalid
outer expression and source-range extraction are not implemented. Functions and
predicates outside the audited numerical subset remain symbolic. Vector views
support ambient dimensions 2–12; scalar real-line views are separate.

The server is a local application with a trusted Lean executable and dependencies.
Its separate process and input restrictions are not an operating-system sandbox
for arbitrary uploaded Lean projects. A clean dependency-download smoke test is
recorded separately in [the Lean contract](lean-contract.md).
