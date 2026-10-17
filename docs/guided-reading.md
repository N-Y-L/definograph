# Guided construction reading

The reader opens with the statement's skeleton: the whole statement drawn once as nested scope frames. Below it, one mathematical step is shown at a time. Previous, Next, and the step selector change the focus, and selecting a row of the skeleton does the same. There is no timed playback. The full static visual statement remains available below the sequence, and the representation is usable with reduced motion.

## The statement skeleton

The skeleton is drawn from the region tree that the step sequence and the full reading already share (`planReadingPresentation` in `src/reading/presentation.ts`). It adds no meaning and infers nothing. Its only text is a node's Lean text, a binder's name and type, and the role words the full reading uses.

- **One row** per group of adjacent binders, per hypothesis, per connective and per clause. A clause row shows the formal clause as Lean prints it wherever the node has Lean text; a row is never empty, and one without any text shows its region kind. The clause row is set larger than every instruction and no smaller than any text of a relation figure. It is not yet the largest text on every step: the metric, graph and restricted-map figures still scale with the column, and a few arrow glyphs are set larger.
- **A row governs exactly the rows inside its frame.** The body of a binder group, the conclusion under its hypotheses, and the parts of a connective each step in by the same amount under a rail, at every depth. Equal indentation would draw a child as a sibling, so no depth removes the step.
- **An arbitrary choice opens a rail. A witness is boxed** together with everything it governs, and its mark and name are bold. The two differ by frame and weight, not by glyph or hue alone, so `∀ x, ∃ y, x < y` is a box inside a rail and `∃ y, ∀ x, x < y` is a rail inside a box.
- **A hypothesis** stands beside a small Given mark. The marks are one column and the hypotheses the next. The conclusion steps in under the hypotheses, so it is always further in than the hypotheses that govern it.
- **What is negated** hangs from a dashed rail as heavy as a witness's box, so it is not taken for an assertion. Conjunction and alternatives still share one frame and differ by glyph and word.
- **A region beyond the display bound** is one stub that names its first row and counts the rows it stands for. Selecting it brings it into view.
- **A binder that comes from inside an opened definition** is not yet marked as such and is drawn among the statement's own binders.

The drawing reads back. `readSkeleton` in `src/visual/skeleton-readback.ts` recovers, from the rendered markup alone, each row's kind, its source nodes, its ordered children with their edges, and the role mark it prints; the result must equal the region tree, stubs included, and each quantifier and connective row must carry its own mark. Unit tests require this of every fixture the reading tests use, and `npm run test:atlas` requires it of every example and standalone corpus statement exported by Lean. The feature that separates the two quantifier orders is named in those tests: the chain of binder rows that enclose the clause row. This is a tested property of the TypeScript renderer, not a theorem; nothing checks it at run time.

The optional Construction graph and the collapsed full reading still draw the same tree when they are opened.

## Identity colour

Hue carries object identity and nothing else. A statement's colours are assigned once (`assignIdentityColors` in `src/visual/object-identity.ts`) and every figure of that reading uses the same assignment.

- Only an object that a binder introduces takes a hue. Hypotheses, recorded context entries and compound expressions such as `f x` or `A ∪ B` are drawn in neutral ink.
- Hues are given in order of first introduction, the statement's own binders before a binder local to one expression, from seven hues that also differ in lightness. The darkest hue is the nearest to ink on a thin glyph and is given last. A hue is never used twice in a statement. Neutral ink is not a hue: from the eighth object on, objects share it and are told apart by their labels.
- A field law read inside a statement keeps the statement's hues and gives its own binders only hues still unused.
- Two objects that print alike are still two objects and never share a hue.
- Colour is never the only carrier: every coloured thing keeps its label.

## The step sequence

A step is named once, in the step selector; no caption repeats it. Under the selector one closed disclosure, **About this step**, holds the longer explanation, the objects in scope, the assumptions the step stands under and its sibling clauses. Its label counts them, for example "About this step · 5 in scope · 1 given". The skeleton already draws all of these with the current row marked, so they are not repeated in view. The step's position among the connectives stays in view as one line beside the figure, because a figure does not yet show whether its clause is assumed, negated or concluded.

A step on a connective has no figure of its own: it is the marked row of the skeleton and the rows inside its frame. In a chain of hypotheses one Given row is marked, the selected hypothesis or otherwise the first.

Motion is limited to a short transition of the progress indicator, turned off under a reduced-motion preference. Objects are not animated, and no step needs playback or chosen coordinates.

A relation figure is drawn at one unit per CSS pixel from the left edge of the column, so a label is the same size in every relation figure and is never stretched with the column. A narrower column shrinks the figure to three quarters at most and then scrolls.

In the VS Code reader, **Inspect a definition in this statement** keeps the
current clause and ordered context alongside the inspection. **Return to
reading** restores the exact selected step, including a construction step within
a clause. The [definition workspace](editor-definition-exposure.md#inspect-from-the-statement)
retains the original reading separately from the inspected result and its checks.

Typed-map figures use measured label dimensions and a shared layout with a
separate route for each map. Dense diagrams keep their readable size and scroll
horizontally in a narrower reading column. An overflowing frame is named and
keyboard-focusable so it can be scrolled without a pointer; a fitting frame adds
no extra Tab stop. The routes and spacing carry no additional mathematical meaning.

The compiler in `src/reading/cues.ts` derives a portable cue plan from the elaborated semantic document and the complete reading document. A cue identifies its exact source nodes, expression scope, enclosing logical branches, assumptions, visible objects, and relations. It carries semantic object identities rather than matching displayed names. Application stages follow their inputs before an outer comparison. Constructors are reusable; there is no dispatch by theorem name.

## Surfaces and theme

Base surfaces are pure white in light mode and pure black in dark mode. The standalone reader follows the system preference. The VS Code webview follows the editor's light, dark or high-contrast theme ahead of the system preference. Objects keep their identity colours in both themes, and dense diagrams keep readable labels and scroll.

## Optional construction graph

Where the current semantic reading supplies a composable group of operations,
**Construction graph** offers a second view of a clause. **Guided reading** remains
the default, including its containment diagrams. The graph is useful for following
how expressions are constructed; it does not replace the geometric meaning of a
supported relation.

The graph retains the current selected clause. If the focus is a binder or logical
region, choose a clause explicitly. This uses the same source-linked cue selection
as the guided sequence. Switching views, selecting an object, and opening a fold
do not choose a different clause or start a native inspection.

Frames follow the actual source tree: quantifier order, antecedents, conditional
conclusions, conjunction siblings, alternatives, equivalence, and negation remain
distinct. A witness's position shows which earlier choices are available, not that
it necessarily depends on them. Object labels refer back to their declaration
frames; repeated binder names include declaration qualifiers. Local expression
folds retain their supplied binder kind, name, and type, or state the missing boundary.

Each operation exposes its supplied ports. Dashed connections attach arguments;
arrowed connections attach explicitly supplied results. Repeated uses of the same
object retain separate port occurrences. Structural applications stay symbolic:
connecting their arguments does not interpret an unknown definition. Types remain
available in declaration details, separately from operation connections.

Labels and ports reserve measured space. Narrow panes scroll locally instead of
shrinking or dropping labels; complex opaque expressions may require substantial
horizontal scrolling. A group exceeding 40 objects, 20 operations, or 100 ports
shows its boundary and keeps the complete source and relation list available.
This view is separate from the neutral positional-component reader and is not
offered when the guided cue plan exceeds its display bound.

## Mathematical labels

Supported plot labels use local KaTeX HTML and MathML. Their display data come
from exported expression constructors or explicit templates for already admitted
relations and their ordered ports. The renderer does not parse printed Lean labels
or infer a mathematical operation from an unfamiliar name. Measured glyph bounds
control spacing, including after fonts load.

This is typed frontend presentation, not a per-object native TeX export or a new
Lean check. Source object IDs, binder IDs, relation ports, and source selection
remain independent of the typography. Unsupported constructors and display limits
retain their source-label fallback, with exact expressions available for inspection.
The optional native statement notation and the separately associated native Lean
notation for inspected results have their own contracts; see
[definition-result presentation](editor-definition-exposure.md#inspect-from-the-statement).

## Meaning that must survive sequencing

- Adjacent binders retain their source order. Existential witnesses may use earlier choices in their scope; later choices cannot silently become dependencies.
- Implications retain assumptions separately from conditional conclusions. Alternatives are not accumulated as assertions, and a negated condition remains under negation while its inner construction is shown.
- A construction inside a clause is an expression-building step. It does not assert an additional proposition. An uninterpreted wrapper is introduced before its recognized contents; local lambda scopes never become outer facts.
- Exact object IDs connect introductions, applications, and comparisons. Types, constant universe arguments, operator instances, and bound-variable identities participate in identity. Similar printed labels do not establish equality.
- The cue plan has a display bound, with explicit omitted counts and source IDs. The underlying complete statement and its selected ancestry remain accessible. Bounded presentation is not reported as complete interpretation.

Each renderer receives the same typed relation and scope used by the static reader. Geometry is substituted only for an entire recognized clause. The guide does not promote a nested metric condition into the meaning of an unknown outer predicate.

The plan is included in version 3 workspace exports. It can be reused by an editor host or another presentation without moving Lean semantics into the renderer. The method follows the construction-first and persistent-identity principles documented in [the 3Blue1Brown research](history/visual-method.md); no Manim code or scene assets are copied.
