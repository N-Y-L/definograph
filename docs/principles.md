# Principles

This page says what Definograph is for and the standard every change is held
to. The standard is ahead of the code in places; [the last section](#where-the-code-stands)
says where. The [README](../README.md#what-is-proved-what-is-checked-what-is-only-tested)
says what is proved, checked and tested today, and [status](status.md) gives
the detail and the gaps.

## What it is for

- Definograph helps a person read a Lean statement quickly and understand a
  complicated one. The aim is understanding, and where possible a reader who
  gets better at reading statements.
- It reads statements, not proofs. Tactics are not drawn.
- The reason: when a machine writes a proof and Lean's kernel accepts it, what
  is left for a person is to confirm that the statement says what was meant.
  Definograph serves that step. Lean's kernel is trusted; checking the kernel
  is outside this project.
- A theorem and a definition are the same kind of object, and both are read as
  statements: a theorem's type, and a definition's type and body.
- Proofs stay closed for now. A proof is shown as the statement it proves,
  with the kernel's verdict and the axioms it uses where they were recorded,
  and its body is not drawn. Statements inside proofs are statements too, but
  reading a proof thousands of lines long is left for later.
- The scope is every finished Lean 4 statement. Lean 4.28.0 is the version
  targeted. Another proof assistant may follow; it is secondary.
- The medium is diagrams. They are designed for what a person recognizes at a
  glance, so graphic details matter.
- Definograph is built as a language: the drawing is a notation for Lean terms,
  with a grammar and a way back.

## The standard

1. **The drawing never says what the statement does not.** It shows what the
   elaborated term says, including what the source text hides. Nothing appears
   that the term does not say. A part that was not read or not understood stays
   on screen, marked as such, and is never replaced by a guess. No witness,
   coordinate, metric, region, continuity or proof is invented.
2. **Proved or machine-checked, not reviewed.** Changes are accepted on machine
   checks, not on a person's review. A claim the tool makes is proved in Lean,
   or checked by Lean's kernel, or guarded by a committed test that fails when
   the claim breaks. Anything on screen without such a check behind it is
   labelled unchecked. Generated explanation is never the source of a claim.
3. **Certificates, not trust.** Any code may propose a step: Lean's elaborator,
   the project's Lean programs, TypeScript. Only the kernel establishes one. A
   step shown as checked corresponds to a declaration the kernel accepted, in
   an identified environment, with the axioms it depends on listed. An
   elaborator answer, such as
   `Meta.isDefEq` or `Meta.isProp`, is labelled as the elaborator's.
4. **Lean's standard axioms, and none added.** Definograph follows Lean's
   definition of the standard axioms: `propext`, `Quot.sound` and
   `Classical.choice`. It never adds an axiom to a user's statement. Reading a
   statement changes neither the statement, nor its proof, nor the project it
   comes from, and the axioms its declaration uses are reported as they are.
   The tool's own theorems use only standard axioms, and their proofs never add
   `Classical.choice` (see [what "clean" means](#what-clean-means)).
5. **Coverage is a theorem.** Every finished Lean statement should have a view,
   every view a drawing, and every drawing should read back. A size limit is
   acceptable only when the reader reports it.
6. **The picture is syntax.** A diagram is a third notation for a term, beside
   Lean source and the kernel's expression. Reading a drawing back recovers
   exactly the view it was drawn from, folded parts included. Spacing, line
   routes and the position of unconnected elements carry no meaning. A
   geometric relation (nesting, an edge, upward order in an order panel)
   carries meaning only where the grammar says so, and each such use reads back.
7. **One object, one mechanism.** To the kernel a definition is
   `name : type := value`, and a theorem is the same with a proposition as its
   type and a proof as its value. One set of operations serves both: reading a
   term in a context, `Γ ⊢ t : T`. Unfolding stops at inductive types,
   structures, axioms and opaque constants, and the stored body of a recursive
   definition is Lean's encoding of the recursion, not the equations its author
   wrote; those cases need their own reading.
8. **Usefulness is measured with readers.** A drawing can cover everything and
   explain nothing. Whether it helps is measured by timing readers and counting
   their errors on questions fixed in advance. "It felt clearer" is not a result.

## What "clean" means

A declaration is clean when Lean's kernel accepted it and every axiom it
depends on is on a stated list. The list is an allowlist: an axiom nobody
thought of fails by default. Decide by the allowlist, never by the names of
forbidden axioms, which change with the toolchain.

- `sorryAx` is never clean.
- The axioms behind native evaluation are never clean: in Lean 4.28.0,
  `Lean.trustCompiler`, `Lean.ofReduceBool` and `Lean.ofReduceNat`. They move
  trust from the kernel to the compiler.
- **The tool's own proved core** (`vendor/DefinographCapture`) declares no
  axiom, and no constant in it depends on one outside the three standard
  axioms. Every theorem there uses only `propext` and `Quot.sound`, except the
  theorems listed in [`scripts/axiom-policy.json`](../scripts/axiom-policy.json):
  each of those depends on `Classical.choice` only because its statement
  already does, and the file gives the reason. A proof may still use `propext`
  or `Quot.sound` where its statement does not. The file's rule is that
  entries may be removed and never added; the audit fails on a theorem that
  uses `Classical.choice` without an entry and on an entry that is no longer
  needed, but no test yet refuses a new entry. `npm run test:axioms` runs the
  audit, shows on a negative control that it rejects a planted `sorry`,
  `native_decide`, axiom and unlisted `Classical.choice`, and replays the
  compiled modules through the kernel with `leanchecker`. It needs the built
  native engine and is not run in CI.
- **The mathematics being read** is reported, not refused. Following Lean, a
  statement is clean when it depends only on the standard axioms.
  `Classical.choice` is ordinary there and is shown. Today the editor lists the
  axioms recorded with each check and does not yet classify them: a term that
  depends on a lemma proved with `sorry` is accepted, with `sorryAx` in its
  list.

## What is still trusted

Some code is trusted and not proved: the code that builds each declaration it
submits from what is shown, the code that carries the kernel's answer to the
screen, the compiler and runtime that run the project's Lean programs and the
kernel, and compiled modules as loaded. The aim is to keep this base small,
stated and tested, not to claim it is empty.

## How a change is judged

Ask four questions of any change:

1. What judgment does it show?
2. Where is its certificate, and which axioms does it use?
3. If there is none, what label does the reader see?
4. Does the same code path serve a theorem's statement and a definition?

Then:

- **Start from what a person recognizes.** A visual element earns its place by
  what it lets a person recognize; the rest is removed. Pages and screens use a
  plain reading style.
- **Keep the unknown visible.**
- **No catalogue of names.** Do not key behaviour on a theorem name, a test
  case, a record name or a field spelling. Names are labels, not meaning.
- **Count what was checked, not what was drawn.** A new figure, a larger test
  count or a new example is not progress on rigor by itself.

## Where the code stands

The standard is ahead of the code. The largest gaps:

- The guided reading compares an opened definition with the original through
  Lean's elaborator (`Meta.isDefEq`), not the kernel.
- The proved core is linked only into the editor's context program. The
  guided reading does not run on its theorems, and nothing is proved from its
  shared graph to the picture.
- The drawing is tested TypeScript. The skeleton reads back in tests, not at
  run time, and the other guided figures have no readback.
- Diagram vocabulary (membership, inclusion, image, a metric ball, adjacency)
  is chosen by exact Lean and Mathlib constant names, audited against their
  declaring modules, in `src/semantic/registry.ts`, `src/graphs/semantics.ts`
  and `canonicalModule` in `lean/StatementLens/Export.lean`. It is not
  certified by the kernel at each use and is not labelled on screen as
  unchecked vocabulary.
- A proof inside a selected data term, or inside the statement of a selected
  proof, is still drawn as ordinary structure.
- Some limits are applied without a message: the editor's definition
  inventory stops at 128 entries, and some early heartbeat and oversized-type
  exits keep the original object without saying why.
- The axioms recorded with an editor check are listed, not yet classified as
  clean. They belong to the declaration rebuilt from the selected term, so
  they cover a proof only when the proof is selected; the browser path records
  none.
- Environments are not yet named. A capture identifies one local process; the
  imported modules are not fingerprinted, so a recorded check does not say
  which library state it holds for.
- Whether the drawing helps a reader has not been measured.

The README's table lists what is proved, what the kernel checks, what only the
elaborator checks, and what is only tested. [Status](status.md) lists the gaps,
and the [roadmap](roadmap.md) gives the gates for closing them.
