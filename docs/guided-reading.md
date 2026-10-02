# Guided construction reading

The default reader presents one mathematical step at a time, with the complete logical overview alongside. Previous, Next, and the step selector change the focus. There is no timed playback. The full static visual statement remains available below the sequence, and the representation is usable with reduced motion.

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

The plan is included in version 3 workspace exports. It can be reused by an editor host or another presentation without moving Lean semantics into the renderer. The method follows the construction-first and persistent-identity principles documented in [the 3Blue1Brown research](visual-method.md); no Manim code or scene assets are copied.
