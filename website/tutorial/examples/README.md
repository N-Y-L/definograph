<!-- description: Toolchain requirements and expected checking results for the Lean tutorial files. -->
# Example notes

These notes list the complete Lean files that accompany [Reading mathematics with Definograph](../README.md), and what Lean reports for each. The eight examples from Lessons 5–7 and the Reference run independently with **Lean 4.28.0**, using the implicit standard `Init` import. The Lebesgue-number example additionally needs Mathlib, as described below.

The statements in lessons 1–4 are not among these files. They come from Definograph's own **Statement** menu, and Definograph checks them against its pinned copy of Mathlib. Lessons 5–7 use the files below.

Run `lean FileName.lean` with the matching toolchain. Some files deliberately produce informational output or warnings:

| File | Purpose | Expected result |
| --- | --- | --- |
| [Scope.lean](Scope.lean) | Form two propositions, one of them false (Lesson 6); compare quantifier order and variable names. | Each `#check` expression has type `Prop`; both proposition-forming declarations are accepted. The constant-choice example has an expected unused-variable warning for `x`. |
| [QuantifierForallExists.lean](QuantifierForallExists.lean) | Select a statement in the editor and inspect it (Lesson 5). | Accepted proposition-forming declaration. |
| [QuantifierExistsForall.lean](QuantifierExistsForall.lean) | The opposite quantifier order, to inspect the same way. | Accepted proposition-forming declaration; this does not prove its proposition. |
| [QuantifierProofs.lean](QuantifierProofs.lean) | Prove the first proposition and refute the second (linked from Lesson 6). | `#print axioms` reports no axiom dependencies for either theorem. |
| [RotorLaw.lean](RotorLaw.lean) | A structure with a law, taken as a parameter (used in the Reference). | Accepted, with an expected unused-variable warning. |
| [RotorExamples.lean](RotorExamples.lean) | Build two `Rotor` structures, one on the natural numbers and one on an empty type, and apply a structure's law at an input. | Accepted; `#print axioms` reports no axiom dependencies for the named definitions and theorem. |
| [Evidence.lean](Evidence.lean) | Compare a local hypothesis with a placeholder dependency (Lesson 6). | `#print axioms` reports no axiom dependencies for `from_hypothesis`. `claimed` produces a `sorry` warning, and `#print axioms` reports that it depends on `sorryAx`. |
| [ReturnMap.lean](ReturnMap.lean) | Read an unfamiliar law and check a counterexample to the opposite round trip (Lesson 7); it also proves that `send` is injective. | Accepted, with an expected unused-variable warning; `#print axioms` reports no axiom dependencies for the named definitions and theorems. |

The [Lebesgue-number walkthrough](../../content/lebesgue-number.md) uses a theorem from Mathlib:

| File | Purpose | Expected result |
| --- | --- | --- |
| [LebesgueNumber.lean](LebesgueNumber.lean) | Select the Lebesgue-number theorem and follow its quantifiers, scope and ball definition. | `#check` displays the existing theorem’s type. Run this file in a Mathlib project using Lean 4.28.0 and Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; the standard `Init` import alone is insufficient. |

`Rotor` is declared independently in its two files so each can be read and run alone. Run the files individually instead of pasting all downloads into one namespace.

Checking a file with Lean checks its source. It does not show that Definograph has a visual reading for every expression in it.
