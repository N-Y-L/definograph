<!-- description: Read the Choices view: the order of quantified choices, and which earlier choices each one may use. -->
# 1. The order of choices

A statement with several quantifiers makes its choices in a fixed order. Swapping two quantifiers can change what the statement requires, even though every symbol stays the same. Definograph's **Choices** view lists the choices a statement makes, in order, and says which earlier choices each one may use.

## Two statements

Here are two statements about real numbers. They are entries in Definograph's **Statement** menu, called **For every x, some y** and **Some y, for every x**.

```lean
∀ x : ℝ, ∃ y : ℝ, x < y
```

```lean
∃ y : ℝ, ∀ x : ℝ, x < y
```

You need very little Lean to read them. `∀` means "for every" and `∃` means "there exists". `x : ℝ` introduces a variable `x` that ranges over the real numbers. The comma separates a quantifier from the part of the statement it governs.

The first statement says: for every real number x there is a real number y with x < y. It is true. Take y = x + 1.

The second says: there is a real number y such that every real number x satisfies x < y. It is false. Such a y would have to be larger than every real number, including itself.

The only difference is the order of `∀ x` and `∃ y`.

## What Definograph shows

This is the Choices view of the first statement.

{{view:depends-choices}}

Read it from top to bottom.

- Each numbered step is one choice, in the order the statement makes it.
- Step 1, marked ∀, is an **arbitrary choice**. Whatever value x takes, the rest of the statement must hold for it.
- Step 2, marked ∃, is a **candidate witness**. The statement asks for a suitable y, but the view does not supply one: "Its existence remains an obligation."
- Under y, **May depend on** lists x. Because y is chosen after x, a choice of y may use the value of x. The small gray a before x is a badge that shows the kind of object: a marks a number. It is not part of the statement.
- The view shows the choices only. It leaves out the condition `x < y` and the rest of the statement's structure; the statement itself is printed with the figure.

Now the second statement.

{{view:fixed-choices}}

- y is now step 1. The view says: "Chosen without earlier values. Later choices cannot change this witness."
- x is step 2. It lists y under **Earlier choices in this scope**: every value of x must be handled, and y is already fixed when x is chosen.

## Read the difference

| Statement | Order in the view | What the statement requires |
| --- | --- | --- |
| `∀ x : ℝ, ∃ y : ℝ, x < y` | x, then y. y may depend on x. | For each x, some y larger than that x. |
| `∃ y : ℝ, ∀ x : ℝ, x < y` | y, then x. y is fixed first. | One y larger than every x. |

"May depend" permits dependence. It does not demand it. A statement of the first shape can still have a single y that works for every x; whether it does depends on the condition, not on the order of the choices.

## What the view does not tell you

- **Whether a witness exists.** The two views have the same kind of steps, yet one statement is true and the other is false. Definograph reads statements. It does not prove them.
- **The condition.** The Choices view leaves out `x < y`. Lesson 2 shows views that include it.
- **Which witness.** "Candidate witness" names what the statement asks for, not a value.
- **Anything from the letters.** The view follows each variable by its place in the statement, not by its name. Renaming x and y changes the labels and nothing else.

## Find the view in Definograph

If you have Definograph running on your computer (see [Try it yourself](../content/install.md#try-it-yourself) in Setup), choose **For every x, some y** from the **Statement** menu. Definograph opens with its **Visual sequence**. Choose **Explore a sample**: the other representations of the statement appear as tabs, and **Choices** is the one shown above. For this statement Definograph opens that tab first. The second statement is **Some y, for every x**.

The Visual sequence says the same thing in its list of variables: under y, it notes whether y may use x.

## Exercises

**Exercise 1.1.** Using the first view, choose y when x = 3 and when x = −10. Then give one rule that works for every x.

<details>
<summary>Hint</summary>

The view allows the choice of y to use x.

</details>

<details>
<summary>Answer</summary>

For example, y = 4 and y = −9. The rule y = x + 1 works for every x, because x < x + 1. The rule uses x, which the order of the choices allows.

Checking two values only illustrates the rule. The rule covers every x because x < x + 1 holds for an arbitrary x.

</details>

**Exercise 1.2.** Use the order in the second view to explain why the second statement is false.

<details>
<summary>Hint</summary>

x is chosen after y, and x can be any real number.

</details>

<details>
<summary>Answer</summary>

Whatever y is fixed at step 1, step 2 must allow every real number x, including x = y. For that x the condition reads y < y, which is false. So no y meets the requirement.

This rules out every candidate at once. It is stronger than trying a few values of y and finding none that works.

</details>

**Exercise 1.3.** This statement is Definograph's example **Read ε–δ continuity in pieces**:

```lean
∀ ε : ℝ, 0 < ε →
  ∃ δ : ℝ, 0 < δ ∧
  ∀ x : ℝ, |x| < δ → |x * x| < ε
```

Between two conditions, `→` means "implies" and `∧` means "and". `|x|` is the absolute value of x. Here is its Choices view:

{{view:light-continuity-choices}}

The steps marked ⇒ are the two assumptions, `0 < ε` and `|x| < δ`. They have no names in the statement, so the view labels each of them a; this a is a label, not the gray kind badge before ε, δ and x. A tag such as **Under 1 assumption** counts the assumptions in force at that step, and on an assumption's own step the count includes that assumption. Like the other Choices views, this one leaves out the conditions the choices must satisfy: `0 < δ` and `|x * x| < ε` do not appear in it. Which choices may δ depend on? May δ depend on x? What would the statement say if it could?

<details>
<summary>Hint</summary>

Compare the step numbers of δ and x, and read the list under δ.

</details>

<details>
<summary>Answer</summary>

δ may depend on ε: the view lists ε under **May depend on**. It may not depend on x, which is chosen later, at step 4. So a single δ must work for every x with |x| < δ.

If δ could depend on x, the statement would say almost nothing. For x ≠ 0 you could take δ = |x|. Then |x| < δ is false, so the implication holds for that x whatever the value of `|x * x|`.

</details>

**Exercise 1.4.** In `∀ x : ℝ, ∃ y : ℝ, 0 < y`, y is again chosen after x, so y may depend on x. Does a suitable y need to depend on x?

<details>
<summary>Answer</summary>

No. y = 1 works for every x. The order of choices allows y to use x; the condition decides whether it has to. The Choices view cannot tell these two situations apart, because it leaves the condition out.

</details>

**Exercise 1.5.** Suppose the second statement were written `∃ b : ℝ, ∀ a : ℝ, a < b`. Is it still false?

<details>
<summary>Answer</summary>

Yes. Renaming bound variables consistently does not change a statement. The Choices view would show the same two steps with the new labels. To change what is required you must change the structure: the order of the quantifiers or the condition.

</details>
