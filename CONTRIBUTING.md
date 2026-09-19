# Contributing

Keep the formal environment separate from the visual application. Do not add
axioms, `sorry`, project imports, executable input syntax, or changes to global
Lean settings to make a visualization work. Do not run dependency updates in a
user's formal project.

New geometric support must be recognized from Lean expressions and instances,
with an explicit unsupported path. Preserve quantifier scope and binder IDs.
Never label sampling, successful elaboration, or a candidate witness as proof.

Run the checks documented in the README. Add semantic regression tests when
changing recognizers, numeric operations, dimensions, boundary conditions, or
witness dependencies. Check the browser when changing interaction or layout.

Keep user-facing text concise. Record a limitation explicitly instead of
silently selecting an interpretation. Publish or push only when the maintainer
requests it.
