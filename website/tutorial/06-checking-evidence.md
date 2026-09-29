<!-- description: What a check by Lean establishes: a well-formed statement, a proof from a hypothesis and an unfinished proof, and how Definograph reports each. -->
# 6. Checking evidence

Every reading in this tutorial came with checks by Lean. This lesson says what those checks establish and what they do not. It first names the kinds of evidence that Definograph keeps apart. Then it compares a statement that is only well formed, a proof that depends on a hypothesis, and an unfinished proof. The last section reads the history panels of Lesson 5 in more detail.

## Kinds of evidence

| Information | What it tells you |
| --- | --- |
| Context | Which declarations and entries were available at the selection, including entries that Lean adds itself, such as `_example`. |
| Check outcome | Whether Lean's kernel accepted, rejected or left unknown one declaration that Definograph submitted. The kernel is the part of Lean that has the final say on whether a term has a given type. |
| Axiom audit | The axioms that a checked declaration depends on, as Lean recorded them, or why they are unavailable. An axiom is a fact that Lean assumes without proof. |
| Formation | Whether Definograph read an expression as a proposition, a type or an ordinary term. It reads this only from certain recorded checks. |
| Supply reading | Whether a term is read as supplying a proof of a statement, and under which entries and axioms. |
| Diagnostic | A warning or error that Lean reported while it read the file, such as the warning about `sorry` below. It is separate from any check outcome. |

Keep these apart. An accepted check outcome is not a proof of the statement, and an empty axiom audit does not remove a hypothesis.

## Well formed is not proved

In Lesson 1, Definograph drew two statements, and one of them is false. Lean checked both all the same. What Lean checked is that each statement is a well-formed proposition. Definograph marks its readings as type checked by Lean, and says that a diagram of a statement is not a proof.

The same holds in a Lean file. These two lines are from [Scope.lean](examples/Scope.lean):

```lean
example : Prop := ∀ x : Nat, ∃ y : Nat, y = x
example : Prop := ∃ y : Nat, ∀ x : Nat, y = x
```

Each line asks Lean only to accept the expression as a proposition. Lean accepts both. The second is false: no natural number equals every natural number. [QuantifierProofs.lean](examples/QuantifierProofs.lean) proves the first statement and disproves the second, if you want to see the proofs.

## A proof that depends on a hypothesis

These lines are from [Evidence.lean](examples/Evidence.lean):

```lean
theorem from_hypothesis (P : Prop) (h : P) : P := h
#print axioms from_hypothesis
```

Here P is any proposition and h is an assumed proof of it; the theorem returns h. It is valid, but it does not prove P from nothing: the hypothesis h is one of its inputs. `#print axioms` asks Lean which axioms a declaration depends on. For `from_hypothesis` it lists none, because a hypothesis is not an axiom.

In the editor, select the final `h`, run **Definograph: Visualize Selection**, open **Source data**, and in **Checker input** check the whole term with **Check chosen occurrence**. Then choose **Inspect type of original selected term**. The history now has a step that relates the term h to its type, the statement P. **Supply reading** reads it:

{{view:editor-hypothesis-supply-excerpt}}

- "Relative to the captured environment, including its axioms, and the 3 entries and 0 frames listed, occurrence 1 is read as supplying a proof of the statement at occurrence 2." The occurrences are the expressions that the history reached, numbered in order: occurrence 1 is the term h, and occurrence 2 is its type P. Frames are relations passed on the way from your selection to the term, such as taking a field of a structure. There are none here.
- "Recorded axioms of the typing declaration: none recorded."
- The three entries are listed under **Conditions**: `from_hypothesis`, `P` and `h`. The entry `from_hypothesis` is one that Lean adds while it checks a theorem, under the theorem's own name.
- "Whether the term uses each listed entry is not read here."

So the reading is exact about its conditions: h supplies a proof of P given the listed entries, and one of them is h : P itself.

## An unfinished proof

The rest of [Evidence.lean](examples/Evidence.lean) is deliberately incomplete:

```lean
theorem claimed : 2 + 2 = 5 := sorry
example : 2 + 2 = 5 := claimed
#print axioms claimed
```

`sorry` is a placeholder for a missing proof. Lean accepts the file with a warning that the declaration uses `sorry`, and `#print axioms claimed` reports `sorryAx`, the axiom that stands for the missing proof. The second line uses `claimed`, and so depends on `sorryAx` too.

In the editor, select `claimed` in the `example` line and take the same steps. The supply reading has the same form:

{{view:editor-claimed-supply-excerpt}}

- "Relative to the captured environment, including its axioms, and the 1 entries and 0 frames listed, occurrence 1 is read as supplying a proof of the statement at occurrence 2." The statement is 2 + 2 = 5, and the one entry is `_example`.
- "Recorded axioms of the typing declaration: sorryAx."

This is why the supply reading always names the environment "including its axioms" and lists them beside it. Here the listed axiom is the missing proof. The reading does not claim that 2 + 2 = 5; it says what the term supplies given everything it rests on, and one of those things is `sorryAx`.

## What the checks do not tell you

- **That a statement is true.** An accepted check says that an expression has a type. A false proposition has a type too.
- **That a saved record is current.** A saved record keeps all of these kinds of evidence as they were recorded. **Save source snapshot** writes one to a file, with its origin marked as unverified, and a saved record cannot restart a live session. Figures made from saved records are labelled **from a saved history**. The live editor panel screenshot in lesson 5 is not one of them.
- **That a drawing is right.** A check of a statement is not a check of its drawing. That Definograph's views are right for every valid Lean statement is the project's goal, not an established result; see the [Reference](../content/reference.md).

## Exercises

**Exercise 6.1.** Which of these forms a proposition, which supplies a proof, and which is a step in reading a statement?

1. Lean accepts `example : Prop := ∃ y : Nat, ∀ x : Nat, y = x`.
2. Lean accepts `from_hypothesis`, whose body `h` has the declared type `P`.
3. Definograph's Choices view lists y as a candidate witness.

<details>
<summary>Answer</summary>

The first forms a proposition, and a false one. The second supplies a proof of P, given the hypothesis h. The third is a step in reading: the candidate names what the statement asks for and establishes nothing.

</details>

**Exercise 6.2.** A supply reading says that a term supplies a proof of P, lists `h : P` among its entries, and its recorded axiom audit lists no axioms. Does the term establish P without assuming h?

<details>
<summary>Hint</summary>

The entries and the axiom list answer different questions.

</details>

<details>
<summary>Answer</summary>

No. The reading holds relative to its listed entries, and h : P is one of them. An empty axiom list does not remove a hypothesis. Definograph also does not say whether the term uses each entry: "Whether the term uses each listed entry is not read here."

</details>

**Exercise 6.3.** Someone writes: "All the outcomes were accepted and an axiom audit came back empty, so 2 + 2 = 5 is proved without assumptions." Find the mistakes.

<details>
<summary>Answer</summary>

Accepted outcomes are about typing, not truth. The audit that matters is the one beside the supply reading, for the typing declaration of `claimed`, and it lists `sorryAx`. An empty audit of some other check cannot stand in for it. The summary mixes records and drops the dependency that matters.

</details>

## Reading the evidence panels in detail

This section reads the history of Lesson 5 closely, with step 2 selected. You can skip it until you need it.

The history up to the selected step is its **prefix**. **Ordered provenance** and **Supply reading** read the prefix only. **Attempt outcomes** lists every check of the attempt, numbered, including checks made after the selected step, and says which of them lie outside the prefix.

**Ordered provenance** lists the occurrences of the prefix in order, with the relations that connect them:

{{view:editor-provenance-excerpt}}

- Occurrence 1 is your original selection. Occurrence 2 is the part reached by checking the body of the universal statement. The relation between them is a **Contained part**, with the role "universal statement · body".
- Each occurrence has a formation line: "Formation: established as a proposition" for occurrence 1, and "Formation: not established" for occurrence 2.
- Each occurrence also says where it first appeared, and which recorded outcomes concern it. Definograph labels each attempt with a short random identifier, which you see in brackets.
- The list ends by saying that steps 3 and 4 are outside this prefix and are not read.

**Supply reading** reads a term as a proof only when the prefix has a step that relates a term to its type, like the steps that **Inspect type of original selected term** added in the two examples above. This prefix has none, so the section says that no supply reading is made.

**Exercise 6.4.** In the history of Lesson 5, step 4 checked `y = x`. Does the prefix through step 2 include that check? Does the check prove `y = x`?

<details>
<summary>Answer</summary>

No to both. The provenance list ends by saying that steps 3 and 4 are outside this prefix. **Attempt outcomes** lists the check with the other checks of the attempt, labeled with its step, and says that outcomes of steps after step 2 are outside the selected prefix. And it is a typing check of `y = x` in a context where x and y are available. It establishes nothing about whether y equals x; that depends on the existential, which asks for a suitable y.

</details>

**Exercise 6.5.** Occurrence 2, the part `∃ y, y = x`, reads "Formation: not established". Is it not a proposition?

<details>
<summary>Answer</summary>

It is a proposition. The words "not established" describe what Definograph read from its records, not the mathematics. Definograph reads formation only from its logical inspections and type inspections, and occurrence 2 was reached by checking a part, which is neither.

</details>
