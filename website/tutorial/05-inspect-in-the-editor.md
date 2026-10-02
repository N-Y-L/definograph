<!-- description: Select a statement in Visual Studio Code, see the same views, find its source data, check a part of it and read the history of your steps. -->
# 5. Inspecting a selection in the editor

Lessons 1–4 used statements from Definograph's own **Statement** menu. In Visual Studio Code, Definograph reads a statement that you select in your own Lean file, together with that file's imports and earlier declarations. It shows the same views as before. It also keeps what Lean checked about your selection, and it lets you check parts of the statement one at a time.

## What you need

- Definograph and its Visual Studio Code extension, set up as described in [Setup](../content/install.md).
- A Lean 4.28.0 project that you trust, with its imports built. The file in this lesson needs only Lean's standard library.

Definograph runs your whole file through Lean again, not only the part you select, and a Lean file can contain code that runs while it is checked. Definograph is not a sandbox, so use it only on files you trust.

## About the figures in this lesson

In your editor, the panels in this lesson appear for your current selection. Most figures here are excerpts: each shows only the part of a panel that the text discusses. They were exported from a recorded history of the same steps on the same file. Definograph labels such a record as saved and unverified, and the excerpts keep that label where the panel shows it. Nothing in a recorded figure is checked again, and its buttons do nothing.

## Select a statement and visualize it

Download [QuantifierForallExists.lean](examples/QuantifierForallExists.lean). It holds one line:

```lean
example : Prop := ∀ x : Nat, ∃ y : Nat, y = x
```

`Nat` is the type of natural numbers. The line asks Lean to accept `∀ x : Nat, ∃ y : Nat, y = x` as a proposition, a statement that may be true or false. It does not prove it; Lesson 6 explains the difference.

1. Open the file in your project.
2. Select the proposition after `:=`.
3. Run **Definograph: Visualize Selection** from the command palette.

Definograph opens beside the file. This is its panel, shown on its own page outside the editor:

{{capture:light-editor-panel}}

At the top is the Definograph header, with **Guide** and **Export**. Below it, the statement bar reads **FROM YOUR LEAN EDITOR**, with the name of the file and the buttons **Refresh from editor**, **Lean source ↗**, **Source data** and **Inspect ↗**. Then comes the heading **Your selected expression**, with a note that reading a fragment does not assert a theorem. Below that are the views of Lessons 1–4: the tabs **Visual sequence** and **Explore a sample**, with **Mathematical notation** at the right.

The Visual sequence has four steps. The last three read the statement: for every x, there exists y, and the equality y = x. The first, **Auxiliary entry _example, recorded kind auxDecl**, names an entry that Lean itself adds while it checks an `example`. It belongs to the context of your selection. It is not an assumption of the statement.

If you edit the file or change the selection, Definograph clears its reading. Choose **Refresh from editor** to read the current selection again. Nothing runs on every keystroke.

## Find the source data

Choose **Source data**. It keeps four records of your selection, one per tab:

| Tab | What it holds |
| --- | --- |
| **Original data** | Your selection as Lean read it, with its local context and its type. |
| **Checker input** | The same expression, prepared for checking. This is the version that is checked. |
| **Expected type** | The type Lean expected at the selection, when Lean recorded one. |
| **Check outcomes** | Each check that Lean ran on the selection, with its result. |

{{view:light-editor-forallexists-source-data}}

To check something, Definograph sends one declaration to Lean's kernel, the part of Lean that has the final say on whether a term has a given type. The outcome is accepted, rejected or unknown. Each outcome also has an axiom audit: the axioms, if any, that the checked declaration depends on. An axiom is a fact that Lean assumes without proof. In your editor you can open each outcome to see the exact declaration and its audit; in the figure these rows stay closed.

Here there are two checks. **context** checks the declarations around your selection, and **component** checks the selection itself in that context. Both are accepted. The tab states its own limits: "These checks concern the prepared context and term typing; they do not certify this visualization or assert the selected proposition." An accepted check means that the selection has a type in its context. It does not mean that the proposition is true.

Because the figure comes from a recorded history, it begins "Saved source snapshot. Its origin is unverified." For your current selection, the panel says instead that the data was captured from your Lean buffer.

## Check a chosen part

In **Checker input**, the prepared expression is shown with a **Choose occurrence** button on each part that you can check. Choose the outermost part, the whole expression. Then choose **Check chosen occurrence**. Definograph runs your file again in a fresh Lean process and checks the chosen part together with the declarations around it.

{{view:light-editor-occurrence-excerpt}}

The result names the part, "Whole prepared term", and reports "6 kernel outcomes retained. The action completed." The six checks come in pairs of context and component, and all six are accepted. These too are checks of typing: "Typing outcomes do not assert a proposition or certify the drawing."

In your editor, the chosen part then has its own **Guided reading** and **Structure** below the checks, which show the part as Lean stores it, with its context.

## Read one layer at a time

From here Definograph works through the statement one layer at a time, and each action adds a step to a history.

1. Below the checked part, choose **Read logical structure of original selected term (one layer)**. The history appears, with **Step 1 · Read logical structure**. It reads the outer layer: a universal statement, for every x.
2. In that step's **Guided reading** or **Structure**, choose the body of the universal statement, the part after `∀ x : Nat,`. Choose **Check chosen part**. Step 2 holds `∃ y, y = x`, with x now in its context.
3. Choose **Read logical structure of this term (one layer)**. Step 3 reads the existential layer.
4. Choose the body of the existential, `y = x`, and **Check chosen part**. Step 4 holds `y = x`, with both x and y in its context.

Each action runs your file again and recomputes every earlier step before adding the new one. Definograph keeps all earlier attempts: if you choose an earlier step and act from it, a new attempt starts, and the old one stays.

## Read the history

This is the list of steps after step 4, with step 2 selected:

{{view:light-editor-history-steps-excerpt}}

Each row is one step and says how it was recorded. **matched** means that the step was recomputed and gave the same result as before; **new** marks the step just requested. The number of outcomes is the number of checks the step made. The words after **Check part** name where the part sits in Lean's form of the expression; you do not need them to follow this lesson.

Selecting a row shows the history up to that step. **Section navigation** then links to four sections:

| Section | What it answers |
| --- | --- |
| **Step reading** | Which expression does this step read? |
| **Ordered provenance** | How was that expression reached from your selection, one step at a time? |
| **Supply reading** | Is some term here read as a proof of a statement, and under which conditions? |
| **Attempt outcomes** | Which checks did the whole attempt make, including checks after this step? |

Lesson 6 explains the kinds of evidence that these sections report, and ends with a closer reading of each one.

## What these views do not tell you

- **That the statement is true.** An accepted check says that an expression has a type. A false proposition has a type too.
- **That a part is proved.** Reaching `y = x` by checking a part does not prove it.
- **That a saved record describes your current file.** A saved record keeps its outcomes as they were recorded, and its origin is unconfirmed.
- **Isolation.** Selecting part of a file does not stop the rest of the file from running.

## Exercises

**Exercise 5.1.** In the list of steps above, how many checks did step 1 make, and which step was requested last? Suppose you now act from step 2 and read one more layer. What happens to steps 3 and 4?

<details>
<summary>Hint</summary>

Read the small line under each step.

</details>

<details>
<summary>Answer</summary>

Step 1 made 4 checks ("matched · 4 outcomes"). Step 4 was requested last; it is the one marked "new". Acting from step 2 starts a new attempt that continues from step 2. Steps 3 and 4 stay in the history, in their own attempt.

</details>

**Exercise 5.2.** You have selected a proof of a law. You switch its display to **Inferred type** and want to read that type's universal quantifier next. What must you do first?

<details>
<summary>Hint</summary>

Switching the display does not make the type the next term of the history.

</details>

<details>
<summary>Answer</summary>

Choose **Inspect type of original selected term** (or **Inspect type of this term** on a later step). The type then becomes the term of a new step, and **Read logical structure of this term (one layer)** reads its universal layer.

</details>

**Exercise 5.3.** Every check in this lesson was accepted. Does that tell you whether `∀ x : Nat, ∃ y : Nat, y = x` is true?

<details>
<summary>Answer</summary>

No. The checks say that the expression and its parts have types in their context, so the statement is a well-formed proposition. It happens to be true: for each x, take y = x. But Lean accepts false propositions in the same way; Lesson 6 shows one.

</details>
