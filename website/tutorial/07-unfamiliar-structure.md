<!-- description: Read a structure that Definograph has no special rules for: its fields and law, the round trip it draws, and where the proof of the law comes from. -->
# 7. An unfamiliar structure

This last lesson uses a structure that Definograph has no special knowledge of. Whatever it shows comes from the definition itself. You read the definition first, then Definograph's figures of it, and then you follow where the proof of its law comes from. The exercises ask what the figures show.

## The definition

These lines are from [ReturnMap.lean](examples/ReturnMap.lean):

```lean
structure ReturnMap where
  Source : Type
  Target : Type
  send : Source → Target
  back : Target → Source
  returns : ∀ x, back (send x) = x

example (system : ReturnMap) (unused : Nat) :
    ∀ x : system.Source, system.back (system.send x) = x :=
  system.returns
```

A `ReturnMap` bundles two types, `Source` and `Target`, a function `send` from `Source` to `Target`, a function `back` from `Target` to `Source`, and a law `returns`: applying `send` and then `back` gives back every input x. The dot means field access: `system.send` is the `send` field of `system`.

The `example` takes an existing `system` and a natural number `unused`, which it does not use. It states the law for `system`, and its proof is the law stored in `system`, `system.returns`.

## The structure in the editor

With the editor set up as in Lesson 5, select the proposition in the `example`, from `∀` to the final `= x`, and run **Definograph: Visualize Selection**. The first step of the Visual sequence lists the parameters, `system` and `unused`, and opens `system` itself:

{{view:editor-returnmap-structure-excerpt}}

- **Inside system** counts "4 data fields · 1 law", and says: "These fields belong to this object, within the statement’s current quantifiers and assumptions."
- **What it contains** draws the data: the functions `send` and `back`, and the two types they go between, `system.Source` and `system.Target`, labeled "carrier type".
- **What its fields must satisfy** lists the one law, `returns`. In Definograph you can read the law as a small visual sequence of its own.

Definograph has no rule for `ReturnMap`. It found these fields and this law in the definition.

The last step of the main reading draws the round trip:

{{view:editor-returnmap-guided-path}}

## Where the proof comes from

The editor can also show where the proof of the law comes from. Select `system.returns` in the last line of the `example` and run **Definograph: Visualize Selection**. Open **Source data**, and in **Checker input** choose the occurrence of `system` inside `system.returns`. Then choose, in turn, **Check chosen occurrence**, **Inspect fields of original occurrence**, **Check field returns**, **Inspect type of this term** and **Read logical structure of this term (one layer)**.

The history now has four steps: **Inspect fields**, **Check field 5** (`returns` is the fifth field), **Inspect type** and **Read logical structure**. **Ordered provenance** shows how the law was reached from `system`:

{{view:editor-returnmap-provenance-excerpt}}

**Supply reading** reads one of these occurrences as a proof of another:

{{view:editor-returnmap-supply-excerpt}}

## Exercises

**Exercise 7.1.** In the figure of `system`, which parts of the structure are labeled "carrier type"? What does the figure say about their elements?

<details>
<summary>Hint</summary>

Read the labels in the diagram, and the note under it.

</details>

<details>
<summary>Answer</summary>

`system.Source` and `system.Target` are labeled "carrier type"; `send` and `back` are drawn as arrows between them. The note under the diagram says: "Arrows show function types. Set frames show membership domains, with no coordinates, shape, size, or chosen elements." So the figure does not say that either type has elements. Both could be empty, and then the law holds with nothing to check.

</details>

**Exercise 7.2.** In the round-trip figure, where does the route start, which functions does it pass through, and what is its end compared with? Does the figure say anything about a round trip that starts in `system.Target`?

<details>
<summary>Hint</summary>

Read **In scope** first.

</details>

<details>
<summary>Answer</summary>

The route starts at x, which **In scope** lists as `∀ x : system.Source`. It passes through `send` and then `back`, and its end, system.back(system.send(x)), is compared with x: "Compare the outputs of these map paths: they are required to agree."

Nothing in scope ranges over `system.Target`, so the figure says nothing about the opposite round trip, and the law does not give it. For example, let `Source` be `Unit`, a type with one value, and `Target` be `Bool`, with values `false` and `true`. Let `send` always return `false`, and `back` return the single unit value. The law holds, but starting from `true`, `send (back true) = false`. [ReturnMap.lean](examples/ReturnMap.lean) builds this record as `unitToBool` and checks the failure at `true`.

</details>

**Exercise 7.3.** In the provenance and supply figures, which relations lead from `system` to the law, in order? Which occurrence is read as supplying a proof of which, and what is the one frame?

<details>
<summary>Answer</summary>

Two relations. "Projected field 5 · returns" leads from `system`, occurrence 1, to the field `returns`, occurrence 2. "Type of the previous occurrence" leads from the field to its type, the law, occurrence 3. The supply reading says that occurrence 2 is read as supplying a proof of the statement at occurrence 3, relative to "the 3 entries and 1 frames listed". The frame is "Relation 1: projection", taking the field out of `system`. So the proof of the law is the field `returns` of this `system`, as the source said.

</details>

**Exercise 7.4.** The supply reading lists `unused` among its entries. Does the proof use `unused`? What does the figure say about this?

<details>
<summary>Answer</summary>

The figure does not decide it: "Whether the term uses each listed entry is not read here." A listed entry is available, not necessarily used. The source answers the question: `system.returns` does not mention `unused`.

</details>

## Explain the result

Try writing a short explanation without looking back. It should name the types and functions, state the law in the right direction, and say where its proof comes from.

A complete answer could be:

> An existing `system` provides two types and functions between them. Its stored law says that sending a source input and then applying `back` returns that input. The law belongs to this record, and its proof is the record's field `returns`. It says nothing about the opposite round trip.

In the examples of these lessons, you could check each figure against its statement and against the checks Lean recorded. That is a claim about these examples only; the [Reference](../content/reference.md) says what is and is not established in general.
