# Guided construction reading

The default reader presents one mathematical step at a time, with the complete logical overview alongside. Previous, Next, and the step selector change the focus. There is no timed playback. The full static visual statement remains available below the sequence, and the representation is usable with reduced motion.

The compiler in `src/reading/cues.ts` derives a portable cue plan from the elaborated semantic document and the complete reading document. A cue identifies its exact source nodes, expression scope, enclosing logical branches, assumptions, visible objects, and relations. It carries semantic object identities rather than matching displayed names. Application stages follow their inputs before an outer comparison. Constructors are reusable; there is no dispatch by theorem name.

## Meaning that must survive sequencing

- Adjacent binders retain their source order. Existential witnesses may use earlier choices in their scope; later choices cannot silently become dependencies.
- Implications retain assumptions separately from conditional conclusions. Alternatives are not accumulated as assertions, and a negated condition remains under negation while its inner construction is shown.
- A construction inside a clause is an expression-building step. It does not assert an additional proposition. An uninterpreted wrapper is introduced before its recognized contents; local lambda scopes never become outer facts.
- Exact object IDs connect introductions, applications, and comparisons. Types, constant universe arguments, operator instances, and bound-variable identities participate in identity. Similar printed labels do not establish equality.
- The cue plan has a display bound, with explicit omitted counts and source IDs. The underlying complete statement and its selected ancestry remain accessible. Bounded presentation is not reported as complete interpretation.

Each renderer receives the same typed relation and scope used by the static reader. Geometry is substituted only for an entire recognized clause. The guide does not promote a nested metric condition into the meaning of an unknown outer predicate.

The plan is included in version 3 workspace exports. It can be reused by an editor host or another presentation without moving Lean semantics into the renderer. The method follows the construction-first and persistent-identity principles documented in [the 3Blue1Brown research](visual-method.md); no Manim code or scene assets are copied.
