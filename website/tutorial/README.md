<!-- description: Seven lessons on reading what Definograph draws for a Lean statement: choices, relations, figures, definitions, editor inspection and evidence. -->
# Reading mathematics with Definograph

Definograph reads a mathematical statement written in Lean and draws what it says: which objects it introduces, which choices may depend on which, how the objects are related, and which parts are only assumed. This tutorial uses those views to read a statement’s assumptions, conclusion and dependencies.

Each lesson takes one statement, shows what Definograph draws for it, explains how to read the drawing, and says what the drawing does not tell you. Then you try it yourself. Every exercise has an answer, and most have a hint. Try the question before opening either.

## Choose where to start

**New to Lean?** Read the worked example’s [short notation guide](../content/lebesgue-number.md#notation), then follow its reading of the Lebesgue-number lemma. The seven lessons below explain individual views when you need more practice.

**Already read Lean?** Go directly to [the theorem and editor selection](../content/lebesgue-number.md#start). Use the same task to identify the hypotheses, compare the quantified choices and read the whole-ball conclusion.

## Before you begin

You should be comfortable with ∀, ∃, sets and functions. You do not need to know Lean. Each lesson explains the few pieces of Lean notation its statement uses, where they first appear. Other terms are explained where they first appear too, and the [Reference](../content/reference.md#glossary) collects them in a glossary.

The figures in the lessons are recorded output of Definograph, with Lean 4.28.0. Each figure says that it is recorded, gives the date it was recorded, and shows the exact source it was made from. A recorded figure is a copy: its buttons do nothing and nothing in it is recomputed. This website does not run Lean or Definograph.

To try the statements yourself, you need Definograph running on your own computer. [Try it yourself](../content/install.md#try-it-yourself), in Setup, says what that takes and what is available today. Lessons 1–4 use statements from Definograph's own **Statement** menu, which it checks against its pinned copy of Mathlib, Lean's mathematics library. Lessons 5–7 use the Visual Studio Code extension with small Lean files that you can download. Those files need only Lean 4.28.0.

## Where the views appear

Definograph shows a statement in several ways. The lessons use the names that appear on its buttons and tabs. This screenshot shows Definograph's window with the first statement of Lesson 1, after choosing **Explore a sample**, with the **Choices** tab open:

{{capture:light-depends-app-context}}

| Name in Definograph | What it shows | Lesson |
| --- | --- | --- |
| **Visual sequence** | The statement one step at a time, with the whole statement alongside. This is what Definograph shows first. | 2 |
| **Choices** | The quantified choices in order, and which earlier choices each may use. It leaves out the conditions. | 1 |
| **Relationships** | Each relation, the objects it connects and the role of each object. | 2 |
| **Structure** | The displayed objects and relations in one overview, with lines between them. | 2 |
| Specialized figures | Set regions, graph colorings, metric regions and maps that are inverse on regions, inside the Visual sequence. | 3 |
| **Inspect** | Definitions opened for reading, the objects, and what Definograph could not interpret. | 4 |
| **Source data** | In the editor: the selected expression, its context and the checks Lean ran. | 5, 6 |

**Explore a sample** holds the other representations of the statement as tabs: **Choices**, **Relationships** and **Structure**, and, for some statements, numerical ones such as **Condition** or **Geometry**. The **Mathematical notation** button shows the statement in ordinary mathematical notation. The **Lean source** panel has a tab also called **Structure**; it lists the statement's logical parts and is a different thing.

## Lessons

| Lesson | What you do | What you should be able to explain |
| --- | --- | --- |
| [1. The order of choices](01-order-of-choices.md) | Compare two statements that differ only in the order of their quantifiers. | Which choices may depend on which, and why the view does not decide truth. |
| [2. Objects and relations](02-objects-and-relations.md) | Trace objects through the relations of a statement. | Which relations are assumed, which are required, and what connects them. |
| [3. Specialized figures](03-specialized-figures.md) | Read set regions, graph colorings, metric regions and restricted inverses. | What each figure adds, and what it states it does not claim. |
| [4. Inside definitions and structures](04-inside-definitions.md) | Open a definition and read a structure's fields and laws. | What a name hides, and what opening it shows. |
| [5. Inspecting a selection in the editor](05-inspect-in-the-editor.md) | Select a statement in Visual Studio Code, find the same views, and check a part of it. | Where Definograph keeps what Lean checked, and how to read it one layer at a time. |
| [6. Checking evidence](06-checking-evidence.md) | Compare a well-formed statement, a proof from a hypothesis and an unfinished proof. | What Lean checked, and what it did not. |
| [7. An unfamiliar structure](07-unfamiliar-structure.md) | Read a new structure, then compare your reading with Definograph's figures. | What the figures show about a definition Definograph has never seen. |

## Three questions to keep asking

1. **What does the statement say?** Its choices, its assumptions and what it requires.
2. **What does this view show, and what does it leave out?** Every view leaves something out; each lesson says what.
3. **What has been checked?** Lean checked that the statement is well formed. That is not a proof, and a drawing of a statement is not evidence that it is true.
