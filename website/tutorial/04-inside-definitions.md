<!-- description: See what a named definition hides, open it, find what Definograph could not interpret, and read the fields and laws of a structure. -->
# 4. Inside definitions and structures

Statements often use named definitions: `Function.LeftInverse g f`, `Function.Injective f`, `Nat.Prime 17`. A name stands for a formula that the statement does not spell out. Definograph can open a small definition one step and read the formula inside, and it can list the fields and laws of a structure. It also says which parts it could not interpret. This lesson shows all three.

## A definition Definograph opens by itself

This is Definograph's example **Look inside a left inverse**:

```lean
∀ (A B : Type) (f : A → B) (g : B → A),
  Function.LeftInverse g f
```

`Function.LeftInverse g f` is a definition in Lean's library. It says that g undoes f: g (f x) = x for every x in A.

Definograph does not stop at the name. Its Visual sequence opens the definition and reads what is inside. This is the last step:

{{view:left-inverse-step-compare}}

- The figure compares the route from x through f and then g with x itself. "Compare the outputs of these map paths: they are required to agree."
- **In scope** now includes x, which comes from inside the definition. The statement's own text has no x.

Below the reading, Definograph says what it did: "Reading `Function.LeftInverse` through its checked definition." In Definograph, the **Inspect** panel says which definition was opened and that Lean checked the expansion for definitional equality, and it keeps the statement as written under **Original statement before inspection**.

A definitional-equality check means that Lean confirmed the opened statement and the original are the same statement, differently written. Opening a definition changes what you see, not what is claimed.

## The same statement, unopened

Definograph opens a definition automatically only when it is small and opening it leaves less of the statement uninterpreted. You can turn this off: in the **Inspect** panel, clear **Automatically inspect small definitions**. The Visual sequence then reads the statement as written:

{{view:left-inverse-original}}

- The whole condition is one clause, `Function.LeftInverse g f`, labeled "Argument structure only · this predicate has no interpreted geometric meaning".
- Definograph still shows what the definition is applied to, g and f, in that order. It does not say what the definition means.

Both readings are correct readings of the same statement. The second one shows less.

## Where interpretation stops

The **Inspect** panel ends with **Interpretation coverage**. It counts the parts of the statement that Definograph could interpret, and names the definitions it left folded. This is Definograph's example **Geometry inside a larger statement**:

```lean
∀ (P : ℝ × ℝ) (ε : ℝ),
  P ∈ Metric.ball 0 ε → Nat.Prime 17
```

`ℝ × ℝ` is the plane as pairs of real numbers, and `Nat.Prime 17` says that 17 is a prime number. Its coverage panel:

{{view:partial-coverage}}

- The first line sets the limits: "This reports the vocabulary used in the selected fragment. It does not measure understanding or establish the statement."
- One clause is interpreted: Definograph recognizes the membership in a ball.
- One clause is **Structure only**: `Nat.Prime 17`. Under **Meaning still folded or uninterpreted**, the panel says "A checked definition body is available for inspection." and offers **Look inside definition**, which asks Definograph to open that definition.

## Opening a definition yourself

Lesson 2 ended with Definograph's example **Functions between arbitrary types**:

```lean
∀ (α β : Type) (f : α → β),
  Function.Injective f →
  ∀ x y : α, f x = f y → x = y
```

Definograph recognizes `Function.Injective f` as a property of f, so it does not open it by itself. To open it yourself, open **Inspect**, then **Look inside a definition**. Enter `Function.Injective` as the **Definition name** and choose **Expand definition ↗**. Definograph reads the statement again with that definition opened, and notes that Lean checked the expansion for definitional equality. **Return to original structure** undoes this.

The outline of the opened statement:

{{view:maps-expanded-overview}}

The assumption now reads: for every a₁ and a₂, if f(a₁) equals f(a₂), then a₁ equals a₂. The conclusion reads: for every x and y, if f(x) equals f(y), then x equals y. They are the same condition with the variables renamed. Opening the definition shows why the statement is true. Definograph did not prove it; the argument is yours, and it is short.

## Fields and laws of a structure

Many definitions in Mathlib are structures: a bundle of data together with laws the data must satisfy. In Lesson 3 you met `PartialEquiv A B`. In Definograph, the first step of that example's Visual sequence has a collapsed section below the regions figure, **Read the underlying fields and laws**. The figure below was recorded with it open, and shows what `e` consists of:

{{view:restricted-inverse-fields}}

- The heading reads **Object structure**, **Inside e**, with the declared type `PartialEquiv A B` and the count "4 data fields · 3 laws".
- "These fields belong to this object, within the statement’s current quantifiers and assumptions."
- **What it contains** lists the data: `toFun : A → B`, `invFun : B → A`, `source : Set A` and `target : Set B`. "Arrows show function types. Set frames show membership domains, with no coordinates, shape, size, or chosen elements."
- **What its fields must satisfy** lists the laws in the order Mathlib declares them: `map_source'`, `map_target'` and `left_inv'`. The primes are part of the names Mathlib gives these fields. The first law is read as a small visual sequence of its own: every x in the source region is sent into the target region.
- The last line says where the list stops: "1 further field remains in the declared type." Mathlib's `PartialEquiv` has a fourth law, `right_inv'`. Definograph did not read it, and says so.

The fields belong to the object they are listed under, here `e`: `e.source` is the source region of this `e`. Another partial equivalence `e'` between the same types has its own `e'.source`, and nothing in the figure relates the two.

## What these views do not tell you

- **That anything was proved.** Opening a definition rewrites the statement into an equal one. It adds no evidence.
- **That a folded definition is wrong or false.** "Structure only" is a limit of Definograph's vocabulary, not a verdict on the mathematics.
- **How well the statement is understood.** Coverage counts recognized vocabulary. A fully interpreted statement can still be false, as Exercise 4.1 shows.
- **That a structure's laws hold for some particular object, or that its sets have elements.** The field list describes what any `PartialEquiv A B` consists of.

## Exercises

**Exercise 4.1.** Read the opened left-inverse statement. Is it true?

<details>
<summary>Hint</summary>

f and g are arbitrary functions of the right types.

</details>

<details>
<summary>Answer</summary>

No. Take A and B to be the natural numbers and let f and g both send every number to 0. Then g (f 1) = 0, not 1. The statement claims that every g undoes every f, which is false. Definograph reads it and draws it all the same, and its coverage panel reports every fragment as interpreted.

</details>

**Exercise 4.2.** In the unopened reading, what does Definograph show about `Function.LeftInverse g f`? What does opening the definition add?

<details>
<summary>Answer</summary>

Unopened, it shows only the definition's name and its two arguments, g and f, in order. Opened, it shows the condition inside: for every x in A, g (f x) = x, with the route from x through f and g drawn and compared with x.

</details>

**Exercise 4.3.** Is the statement in **Geometry inside a larger statement** true? Could Definograph have told you?

<details>
<summary>Hint</summary>

The conclusion does not mention P or ε.

</details>

<details>
<summary>Answer</summary>

It is true, because 17 is prime; the assumption about P plays no part. Definograph could not have told you. It left `Nat.Prime 17` folded, and even an interpreted clause is not a proof. Its coverage panel says as much: "It does not measure understanding or establish the statement."

</details>

**Exercise 4.4.** Which law of `PartialEquiv` is missing from the figure? What does it say?

<details>
<summary>Answer</summary>

`right_inv'`. It says that every y in the target region comes back to itself when you apply the inverse map and then the forward map: toFun (invFun y) = y. This is the round trip from the target that Exercise 3.4 relied on.

</details>

**Exercise 4.5.** Suppose `e` and `e'` are two partial equivalences from A to B. The figure lists the laws of `e`. Does `left_inv'` of `e` tell you anything about points of `e'.source`?

<details>
<summary>Answer</summary>

No. The figure says that the fields "belong to this object": `left_inv'` of `e` speaks about `e.source`, `e.toFun` and `e.invFun`. To transfer it to `e'` you would need a separate fact relating `e'` to `e`, for example a proof that the two structures are equal.

</details>
