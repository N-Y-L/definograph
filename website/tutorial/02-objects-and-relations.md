<!-- description: Trace objects through the Relationships, Visual sequence and Structure views, and tell assumptions from what a statement requires. -->
# 2. Objects and relations

Most statements relate a few objects to each other. An element belongs to a set, one set lies inside another, a function sends an input to an output. Definograph keeps one identity for each object and draws each relation with the role that each object plays in it. In this lesson you follow objects through the relations of two statements, and you learn to tell what a statement assumes from what it requires.

## A statement about sets

This is Definograph's example **Sets, membership, and inclusion**:

```lean
∀ (A B : Set ℝ) (x : ℝ),
  A ⊆ B → x ∈ A → x ∈ B
```

`Set ℝ` is the type of sets of real numbers, so `(A B : Set ℝ)` introduces two sets. Between conditions, `→` means "implies", and a chain of them groups to the right: `A ⊆ B → x ∈ A → x ∈ B` means "if A ⊆ B, then if x ∈ A, then x ∈ B". So `A ⊆ B` and `x ∈ A` are assumptions, and `x ∈ B` is what the statement requires.

The statement is true: if every element of A is in B, and x is in A, then x is in B.

## The Relationships view

{{view:light-sets-connections}}

The Relationships view gives each relation a numbered card.

- The small heading on a card names the kind of relation: **Set inclusion** or **Membership**.
- Each object appears with its role in the relation: **subset** and **superset**, **element** and **set**. The gray badge before a name shows what kind of object it is: { } for a set, a for a number. The other badges in this lesson are ↦ for a function, T for a type, ⋯ for an expression built from other objects, and x for a variable of any other type.
- The tags above the objects give the relation's place in the logic of the statement. Card 01 is a **Premise of an implication**. Card 02 is **Conditional on the premise**, is itself a **Premise of an implication**, and sits **Under 1 assumption**. Card 03 is **Conditional on the premise** and sits **Under 2 assumptions**.

Card 03 is the only relation that is not a premise. It is the conclusion, required under the two assumptions in cards 01 and 02.

To follow an object, find every card it appears in. x is the element in cards 02 and 03. A is the subset in card 01 and the set in card 02. B is the superset in card 01 and the set in card 03. Definograph links these appearances because they are the same variable of the statement, not because they print the same letter.

## Read the statement in order

The **Visual sequence** presents the same statement one step at a time. It is what Definograph shows first. For this statement it has five steps: the variables, the step **Given → then** that sets out the implications, the inclusion, and the two memberships.

The small capitals above each step's title say what kind of step it is. **Objects and choices** introduces variables. **Logical structure** sets out implications and other connectives. **Condition** reads a relation such as membership or inclusion, whether it is assumed or required. **Compare** reads an equation or inequality between two expressions. **Construction** reads how an object is built, for example by applying a function. This is step 3, the inclusion condition:

{{view:light-sets-inclusion}}

- **In scope** lists the variables available at this step: A, B and x, each introduced by ∀.
- **Given assumption** says where the condition sits in the statement. It is assumed, not asserted.
- The figure draws A inside B. Its caption states the figure's limits: "Every element of the inner set belongs to the outer set. The sets may be equal; spacing does not express proper inclusion."
- **Lean fragment and source context** holds the Lean text of the part being read, here `A ⊆ B`.

Step 5 is the conclusion:

{{view:light-sets-conclusion}}

- The path reads **Conditional conclusion** twice, once for each implication that encloses this step.
- **2 assumptions in scope** lists `A ⊆ B` and `x ∈ A`.
- The figure places x in B, with the caption "Membership condition · the named element belongs to the region". This is what the statement requires under those two assumptions.

These figures show single steps. In Definograph, **Next** and the **Reading step** menu move from step to step, and an outline of the whole statement sits beside the steps: for every A, B, x; given A is contained in B; given x belongs to A; then x belongs to B.

Below the steps, **Full visual statement** shows the whole reading at once.

## Follow an object through a chain of maps

The second statement is Definograph's example **An equation between two map paths**:

```lean
∀ (A B C : Type) (f : A → B) (g : B → C)
  (h : A → C) (x : A), g (f x) = h x
```

`(A B C : Type)` introduces three arbitrary types, that is, three collections of objects of any kind. `f : A → B` is a function from A to B. Lean writes function application without brackets: `f x` is f applied to x, and `g (f x)` applies g to that result.

The statement says: whatever the types A, B, C and the functions f, g, h between them, applying f and then g to any x in A gives the same result as applying h.

So f(x) lies in B, and g(f(x)) and h(x) both lie in C: the equation compares two elements of C.

Here is the last step of the Visual sequence:

{{view:light-paths-compare}}

The figure draws two routes that start at x. The upper route passes through f and then g and ends at g(f(x)). The lower route passes through h and ends at h(x). The = between the two ends is the condition: "Compare the outputs of these map paths: they are required to agree."

Below the figure, the collapsed section **Inside this expression** holds the three applications that build f(x), g(f(x)) and h(x). In Definograph it opens to show them, with the note "These are parts of the expression, not separate assertions." Writing g(f(x)) builds an object; it does not claim anything about it.

The Relationships view lists the same four relations as cards:

{{view:paths-connections}}

Card 01 is the equation. Cards 02 to 04 are the applications, each with an input, a function and an output. The type under each object says where it lives. Here x has the badge x because its type A is arbitrary, and f(x), g(f(x)) and h(x) have ⋯ because they are built from other objects.

f(x) is the output of card 03 and the input of card 02. That shared object joins f and g into one route.

The **Structure** tab under **Explore a sample** draws all the objects and relations at once, with a line for each role. Here the types A, B and C appear as objects too, with the badge T. Selecting an object highlights its lines. Here x is selected:

{{view:paths-trace-x}}

Two lines from x are highlighted. They are its roles as input 1 in the applications of f and of h. The other lines are dimmed.

The Visual sequence can show the same thing. In Definograph, select x in any figure of the Visual sequence, then open **Full visual statement** and, inside it, **Inside this expression**. Selecting x also opens the **Inspect** panel for x; x stays selected when you close the panel. A dashed line, the identity thread, now joins every place in the Visual sequence where x appears. This screenshot of the Visual sequence was taken in that state:

{{capture:light-paths-identity-trace}}

The reading is at step 1. The thread joins eight appearances of x: the entry x : A in the list of variables and the small x : A box under **Types and maps** at this step, the same two again in the full visual statement, the start of each of the two compared routes, and the inputs of f and of h inside **Inside this expression**.

The thread says only that these eight are one object, the x introduced at the start of the statement. Its route means nothing.

## What these views do not tell you

- **That an assumption holds.** `A ⊆ B` has a card and a figure, but only as a premise. In the words of the Structure view: "A relation may occur inside an assumption, negation, or alternative; its presence is not a claim that it holds."
- **That the statement holds.** The second statement is false (Exercise 2.3). Definograph draws it anyway, because it is a well-formed statement.
- **Geometry.** "These are diagrams of mathematical roles. Relative position and distance carry no geometric meaning." In the subset figure, A is not smaller than B; the two sets may be equal. The curves of the lines in the Structure view mean nothing either.
- **How many elements.** No figure says how many elements a set has, or that it has any.

## Exercises

**Exercise 2.1.** In the Relationships view of the sets statement, which card is the conclusion? How can you tell without reading the Lean?

<details>
<summary>Hint</summary>

Read the tags above the objects.

</details>

<details>
<summary>Answer</summary>

Card 03. It is the only card that is not tagged as a premise. Its tags say that it depends on the premises and sits under two assumptions.

</details>

**Exercise 2.2.** Remove the first assumption:

```lean
∀ (A B : Set ℝ) (x : ℝ), x ∈ A → x ∈ B
```

Is the statement still true? Which card of the Relationships view has no counterpart now?

<details>
<summary>Answer</summary>

It is false. Take A = {0}, B = ∅ and x = 0: then x ∈ A, but x ∉ B.

The **Set inclusion** card has no counterpart, because the statement no longer mentions `A ⊆ B`. Nothing else links A to B any more.

</details>

**Exercise 2.3.** Is the map-path statement true?

<details>
<summary>Hint</summary>

f, g and h are arbitrary functions of the right types.

</details>

<details>
<summary>Answer</summary>

No. Take A, B and C to be ℝ, f and g the identity function, and h the constant function 0. At x = 1 the upper route gives g(f(1)) = 1 and the lower route gives h(1) = 0.

For particular f, g and h, the equation holds at every x exactly when h is the composite of f and then g. The figure shows what the statement requires; it cannot tell you whether that requirement is met.

</details>

**Exercise 2.4.** Trace f(x) in the Relationships view of the map-path statement. In which cards does it appear, and in which roles?

<details>
<summary>Answer</summary>

In card 03 as the output of f, and in card 02 as input 1 of g. It is one object: the result of the first application is the input of the second.

</details>

**Exercise 2.5.** Definograph's example **Functions between arbitrary types** is:

```lean
∀ (α β : Type) (f : α → β),
  Function.Injective f →
  ∀ x y : α, f x = f y → x = y
```

`Function.Injective f` says that f is injective. Which conditions are assumptions, and which one is required? If you have Definograph running, open the Relationships view of this example and compare its tags with your answer.

<details>
<summary>Answer</summary>

`Function.Injective f` and `f x = f y` are assumptions. `x = y` is required, under both of them.

The Relationships view has five cards. The injectivity property is a **Premise of an implication**. The equation f(x) = f(y) and the two applications that build f(x) and f(y) are **Conditional on the premise** and are themselves a premise, **Under 1 assumption**. The equation x = y is **Conditional on the premise**, **Under 2 assumptions**.

</details>
