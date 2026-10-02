<!-- description: Read Definograph’s figures for set regions, graph colorings, metric balls and maps inverse on regions, and what each one does not claim. -->
# 3. Specialized figures

For a few kinds of mathematics Definograph has figures of its own: regions for combinations of sets, a coloring rule for graphs, a ball for a metric condition, and regions for maps that are inverse only on part of their domain. Each figure is drawn from a relation Definograph recognizes, and each one says in its caption what it does not claim. This lesson reads one figure of each kind.

Definograph draws these figures only for the Mathlib definitions it recognizes, such as `SimpleGraph.Coloring`, `Metric.ball` and `PartialEquiv`. The same idea written with other definitions stays visible as ordinary typed and logical structure, as in Lesson 2.

## Regions for combinations of sets

This is Definograph's example **A condition on compound sets**:

```lean
∀ (α : Type) (A B C : Set α) (x : α),
  x ∈ (A ∪ B) ∩ Cᶜ → x ∈ (A \ C) ∪ (B \ C)
```

`α` is any type. `∪` is union, `∩` intersection, `Cᶜ` the complement of C and `A \ C` the set difference.

Step 6 of its Visual sequence reads the assumption:

{{view:light-set-algebra-given}}

- The box stands for the type α and the three circles for A, B and C. The key names the circles by position: A upper left, B upper right, C lower.
- The shaded part is where the assumption allows x to be: in A or in B, and outside C. "The named element must belong somewhere in the highlighted region; no particular membership combination is chosen."
- The collapsed section **How this set is constructed** holds the steps that build the set. In Definograph it opens to show them: A ∪ B, then Cᶜ, then their intersection.
- The caption gives the limits: "Regions encode membership combinations, not elements or sizes. Drawing a region does not assert that it contains an element."

Step 10 reads the conclusion:

{{view:light-set-algebra-conclusion}}

Here the key reads A upper left, C upper right, B lower. Positions can change from one figure to the next, so compare the figures by their labels.

## A coloring rule for graphs

This is Definograph's example **What a proper coloring requires**:

```lean
∀ (V C : Type) (G : SimpleGraph V)
  (c : G.Coloring C) (u v : V),
  G.Adj u v → c u ≠ c v
```

`SimpleGraph V` is a simple graph whose vertices have type V. `G.Adj u v` says that u and v are adjacent in G. `c : G.Coloring C` is a proper coloring of G with colors from C: it gives each vertex a color, and adjacent vertices different colors. `≠` means "is not equal to". The statement says that a proper coloring gives the two ends of any edge different colors.

Step 3 reads the assumption that u and v are adjacent:

{{view:light-coloring-edge-condition}}

The figure marks u and v as the two ends of an edge of G. Its caption: "Positions encode endpoint roles, not distinctness or geometry. This condition does not specify the full graph." The figure is not a picture of G. It shows one required edge, and nothing about the rest.

Step 4 follows the coloring. Its label, **Construction**, marks a step that builds an object. Here the object is c(u), and the line **Constructing part of** names the condition that c(u) belongs to, c(u) ≠ c(v). The step also says: "No concrete coloring is chosen."

{{view:light-coloring-follow}}

- The row marked **source application** is the application written in the statement: the input u goes through c to its color c(u).
- Below it, the figure states the rule that every proper coloring satisfies: if two endpoints are adjacent, their colors differ, "different labels, for every edge". The rule is about every edge of G, not only an edge between u and v, so its two endpoints get new names, v₁ and v₂.
- "Color type or bound C … no finite palette or cardinality is inferred": C may have any number of elements.
- "Endpoint slots stand for arbitrary inputs to the rule. They do not instantiate vertices, assert that an edge exists, or determine the graph’s size or shape."

## A ball for a metric condition

This is Definograph's example **A point in an ε-ball**:

```lean
∀ (c : EuclideanSpace ℝ (Fin 2)) (ε : ℝ),
  0 < ε → ∀ P : EuclideanSpace ℝ (Fin 2),
  P ∈ Metric.ball c ε → dist P c < ε
```

`EuclideanSpace ℝ (Fin 2)` is the Euclidean plane. `Metric.ball c ε` is the open ball of radius ε around c, and `dist P c` is the distance from P to c.

Step 7 reads the assumption that P lies in the ball:

{{view:light-epsilon-ball}}

- The figure shows the open ball with its center c and radius ε, the point P inside, and the condition it stands for, dist(P, c) < ε.
- Above the figure, **Given** lists the assumption 0 < ε, and the caption begins: "Uses the local assumption 0 < ε."
- The rest of the caption gives the limits: "Schematic positions; no coordinates chosen. Named points may coincide. Boundary excluded."

This statement can also be explored with numbers. In Definograph, choose **Explore a sample**; for this statement it opens a **Geometry** tab, **Open ball in 2D**, which draws the ball for one choice of values. It starts with c = (0, 0), ε = 1 and P = (0, 0):

{{view:light-epsilon-sample}}

This figure is one sample, not the statement; Definograph labels it "Numerical illustration". It shows a single choice of c, ε and P, and that choice satisfies the statement's assumptions: ε = 1 is positive, and P lies in the ball because it sits at the center. The statement is about every such choice. No single sample, and no number of samples, shows that it holds for all of them, and a sample is not a proof.

In Definograph you can move P by clicking or dragging in the plot, or open **Sample choices ↗** to change the values. In this recorded copy nothing moves. The **Scenario** tab reports whether the condition holds for the current values, computed approximately, and says that this is not a proof. Changing the values changes the sample, never the statement.

## Maps that are inverse on regions

This is Definograph's example **An inverse valid on a region**:

```lean
∀ (A B : Type) (e : PartialEquiv A B) (x : A),
  x ∈ e.source → e.symm (e x) = x
```

`PartialEquiv A B` comes from Mathlib. It bundles a map from A to B, a map back from B to A, a region `e.source` of A and a region `e.target` of B, and laws that say the two maps undo each other on those regions. `e x` applies the forward map, and `e.symm` is the map back.

Step 3 locates the source region:

{{view:light-restricted-inverse-source}}

- The frames are the two carriers, the whole types A and B that the maps go between. Inside them are the regions e.source and e.target, each marked "possibly empty".
- e and e⁻¹ connect the regions, "inverse on these regions".
- The two round trips state the laws: from the source region, x goes to e(x) and back to x; from the target region, y goes to e⁻¹(y) and back to y.
- The caption: "The letters in the round trips are schematic bound variables, not chosen points. Region frames indicate containment, not shape, size, dimension, connectedness, or a proper subset. The inverse laws apply on the specified regions; no inverse law is asserted on the whole carriers."

Step 6 follows the map back:

{{view:light-restricted-inverse-return}}

**Apply the inverse map** takes e(x) through the inverse map to e.symm(e(x)). The figure writes e(x) as e.toFun(x): `toFun` is the name of the forward map inside `e`. The figure adds: "Its type alone does not establish membership in the valid region; the round-trip law requires that membership." In this statement that membership comes from the assumption x ∈ e.source, which appears above the figure under **Given**.

## What these figures do not tell you

- **That anything is in a set.** No region, graph or ball is asserted to have elements, and no figure says how many.
- **Shapes, sizes or positions.** Every caption in this lesson says that its geometry is schematic.
- **That the statement is true.** Exercise 3.2 is a statement that Definograph draws as carefully as the others, and it is false.
- **Recognition of every encoding.** A statement about sets, graphs, metrics or maps gets these figures only when it uses the definitions Definograph recognizes.

## Exercises

**Exercise 3.1.** Compare the shaded parts of the two set figures by their labels. What do you conclude about the statement? Has Definograph proved it?

<details>
<summary>Hint</summary>

List the shaded combinations in each figure, for example "in A, outside B, outside C".

</details>

<details>
<summary>Answer</summary>

Both figures shade the same three combinations: in A only, in B only, and in both A and B, each outside C. So every x that the assumption allows is also allowed by the conclusion, and the statement is true. In fact the two sets are equal.

That argument is yours: a check of membership combinations, like a truth table. Definograph drew the figures. It did not prove the statement, and Lean checked only that the statement is well formed.

</details>

**Exercise 3.2.** This is Definograph's example **At most four available colors**:

```lean
∀ (V : Type) (G : SimpleGraph V),
  G.Colorable 4
```

`G.Colorable 4` says that G has a proper coloring that uses at most 4 colors. Its only condition step:

{{view:light-colorable-requirement}}

Is the statement true? What do the labels 0, 1, 2 and 3 in the figure stand for?

<details>
<summary>Hint</summary>

Think of five vertices, each adjacent to all of the others.

</details>

<details>
<summary>Answer</summary>

It is false. In the complete graph on five vertices, every two vertices are adjacent, so all five need different colors, and four colors are not enough. Definograph's description of this example points out that planarity is not assumed.

The labels are the colors a coloring may use: "These are available labels, not colors assigned to the displayed endpoint slots. A coloring may use fewer labels." The figure states the requirement. It does not supply a coloring: "Existence remains the statement’s condition; no witness is selected."

</details>

**Exercise 3.3.** In the ball figure, P is drawn away from the center c. May P be equal to c? Does the figure tell you how far P is from c?

<details>
<summary>Answer</summary>

P may equal c: the caption says "Named points may coincide", and the numerical sample starts with P exactly at c. The figure tells you only what the statement requires, dist(P, c) < ε. The drawn distance means nothing.

</details>

**Exercise 3.4.** Definograph's example **The return trip from the target** is:

```lean
∀ (A B : Type) (e : PartialEquiv A B) (y : B),
  y ∈ e.target → e (e.symm y) = y
```

Which round trip in the figure for step 3 does this statement use? Would it still hold without the assumption `y ∈ e.target`?

<details>
<summary>Hint</summary>

The caption says where the inverse laws apply.

</details>

<details>
<summary>Answer</summary>

It uses the second round trip: from the target region, y goes to e⁻¹(y) and back to y.

Without the assumption it would be false. Take A and B to be the natural numbers, both regions to be {0}, and both maps to send every number to 0. The laws hold on the regions, but e(e.symm 1) = 0, not 1. As the caption says, "no inverse law is asserted on the whole carriers."

</details>
