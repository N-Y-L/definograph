# Working on Definograph

Definograph is an early research implementation of a general mathematical statement
reader. Read [current status](docs/status.md), [architecture](docs/architecture.md),
and [roadmap](docs/roadmap.md) before choosing the next implementation task.
Historical iteration reports are evidence about particular changes, not the
current product specification.

## Objective and implementation rules

- Help a reader understand the statement. The default is a visual sequence with
  its logical overview alongside. Numerical exploration is secondary.
- Extend deterministic decomposition and composition of shared primitives.
  Do not add dispatch on a theorem name, corpus case ID, user record name, or
  field spelling to make an example pass. Specialized mathematical lenses need
  an explicit contract and must remain optional refinements.
- Preserve exact expression identity, binder identity, universe distinctions,
  argument roles, quantifier order, and lexical scope. An object's fields and
  laws are available only where the owning object is available.
- Keep the original expression and the reason for a transformation. Checked
  unfolding can expose a definition; it does not establish every mathematical
  consequence or guarantee a useful visual explanation.
- Preserve unresolved expressions and resource boundaries. Never replace an
  unknown predicate with an interpreted child or silently invent coordinates,
  nonempty regions, a metric, continuity, a witness, or a proof.
- Distinguish kernel checking, semantic interpretation, schematic presentation,
  and numerical sampling in code and documentation. A passing corpus measures
  its stated contracts, not understanding of all mathematics.

## Formal environment boundary

The standalone worker accepts restricted terms in a pinned environment. The
editor sidecar re-elaborates a trusted active buffer against existing project
dependencies; its separate process is **not** a security sandbox. Keep those
input modes and trust contracts distinct.

Use this repository's ignored `.local/` directory for native builds, private
dependencies, reports, and machine-specific configuration. Do not change a
user's Lean source, Lake files, compiled dependencies, global toolchain, or
settings as a shortcut. Do not run Lake updates or dependency downloads in a
user's formal project. Native setup can read an existing matching cache or
explicitly download into this repository's isolated cache.

Do not add axioms, `sorry`, or relaxed placeholder checks to make a visualization
succeed. Never log or commit an editor user's buffer as a diagnostic artifact
without a task-specific reason.

## Change and verification workflow

1. State the reusable capability and the meaning it must preserve. Inspect its
   existing code path before adding another representation or registry.
2. Keep the change bounded and compatible with the current typed contracts.
   Internal `StatementLens` Lean namespaces, IPC identifiers, and
   `statementLens.*` settings are retained for compatibility despite the Definograph
   display name; do not rename them as cosmetic cleanup.
3. For semantic changes, use real Lean exports and independent expected
   relationships. Include a renamed or unfamiliar definition where relevant,
   plus a boundary case that must remain unknown. Do not weaken expectations to
   match a new implementation.
4. Run the applicable [checks](CONTRIBUTING.md#validation). Check the actual
   browser when changing reading or interaction. Mocked extension checks are
   not evidence of an actual VS Code host session.
5. Update current status/contracts for changed behavior. Report what was tested,
   what remains unverified, and any migration or compatibility risk. Do not
   turn each small change into another release report.

Current user instructions and authorized task scope govern publication and
other actions; this file does not create an additional approval gate. Keep
unrelated work intact, and do not push, publish, or install software merely
because a local check completed.

## Repository map

See [code entry points](docs/status.md#code-entry-points) for the extraction,
decomposition, semantics, reading, rendering, and editor boundaries. New design
work belongs in the architecture and roadmap; reusable fixture expectations
belong in `corpus/`; generated audit output belongs in `.local/`.
