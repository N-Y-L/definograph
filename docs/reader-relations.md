# Reading relations and recorded outcomes

The source reader keeps expression structure, recorded typing outcomes and derived
readings separate. The ordered provenance and supply panels read the selected
prefix of the retained editor history. Selecting a row or changing a presentation
runs no Lean process. Explicit inspection actions start fresh captures.

| Relation or record | What the reader displays | What it does not establish |
| --- | --- | --- |
| Containment | An exact constructor position inside an earlier expression, with the binders entered along that path. | A new proof of that part or a specialization of the enclosing expression. |
| Type-of | The type inferred for a term at the captured universe levels. | Equality with a source ascription or the result of an enclosing application. |
| Projection | A named field of a recorded owner, its context, and the recorded projection checks. | A relationship to another owner with the same displayed name. |
| Conversion | The requested definition-head exposure or field projection conversion, with its own recorded outcome. | Arbitrary simplification or interchangeable source text. |
| Typing | The accepted, rejected or unknown outcome of one submitted declaration in the captured environment. | Truth of a proposition or certification of the drawing. |
| Formation | The proposition, type, sort of general level or ordinary term reading supported by the occurrence’s recorded formation evidence, or an explicit unestablished/conflicting status. | Independent confirmation from multiple receipts of the same checked judgement. |
| Supply | “is read as supplying a proof of” appears only for a term with accepted typing and an inferred type whose formation is established as a proposition. The same block lists the full context, ordered frames and recorded axioms. | A claim that any listed context entry is used, that a contained position has a separate proof, or that the declaration is independent of axioms. |

The supply panel always states: “Kernel acceptance is a typing outcome in the
captured environment, not a statement that the proposition is true.” Its conditions
include every recorded context entry, including auxiliary entries and local
definitions. Recorded declaration kinds determine the neutral auxiliary labels;
names do not. “Whether the term uses each listed entry is not read here.” The
statement is the inferred type at the captured universe levels, rather than a
source annotation.

The supply sentence explicitly includes the captured environment and its axioms.
The typing declaration's recorded axiom list, or its unavailable-audit reason,
follows immediately. Changing that audit does not change the supply reading.
Each type-of block identifies both occurrences by their first appearance and
incoming relation. Occurrence, relation, step and outcome numbers identify
different things. Links to the matching provenance entries only move reading
focus; they do not select another history or request a native check.

Each formation judgement lists its physical receipts once, preserving every
outcome. A receipt that serves both typing and formation is identified as one
receipt in two roles. The numbered outcome list also retains checks beyond the
selected prefix; those later checks are explicitly excluded from the prefix’s
reading.

Context positions count entries in the ordered home; constructor-path positions
count steps along a containment path. Entered-binder readings identify their
relation separately. Names identify displayed entries only together with these
coordinates. Anonymous
names and names with Lean macro scopes display as “unnamed binder” or “unnamed
context entry”; exact names remain in the expandable data. Ordinary recorded
identifiers keep their spelling. In a collision between an ordinary variable and
an auxiliary entry, the ordinary variable keeps its name. The complete structural
view retains both entries and their original references.

In a guided component view, **Names in scope** labels ordinary surrounding
entries. The full scope may include captured declarations and entries introduced
by selection or later focus. These lexical labels assign no logical role; the
ordered provenance and conditions retain the qualified binder readings. Local
definitions, function inputs, logical-root binders and recorded auxiliary entries
keep their separate labels. In the guided and structure views, recorded kinds apply
by position only while the leading context entries carry exactly the recorded
names, in order; otherwise every entry reads as a neutral context entry without a
role, and a note says that the recorded kinds could not be matched.

## Section navigation

Within a continuation attempt, **Section navigation** offers links to the
**Step reading**, **Ordered provenance**, **Supply reading** and **Attempt outcomes**
sections that are present. A return link before each section leads back to the
same outline. The outline and return links identify the displayed attempt and
step. These links only move reading focus within the drawer; they do not select
another attempt or step, open a disclosure, change the address or request a
native check.

Ordered provenance and the supply reading concern the prefix through the selected
step. **Attempt outcomes** contains every recorded outcome of the attempt,
including source extraction and any steps after the selected one; those later
checks remain outside the prefix's reading. Its navigation link reaches the
whole-attempt explanation even when the outcome list is collapsed. An attempt
without a recorded step has no Step reading link and is labelled accordingly.
An attempt whose checking is unavailable has no section navigation.

## Explicit inspections

**Inspect type** makes the inferred type of the displayed term the next term.
**Read logical structure of this term (one layer)** inspects that term only. To
inspect the logical structure of an inferred type, choose **Inspect type** first.
These actions are available on the original pair and on eligible completed derived
pairs, including the first definition exposure. Saved records and a busy editor
have no continuation actions. The host reports a refused request without inventing
another result.

The panels are derived for display and are not added to saved snapshot files.
Saved records retain an unverified origin; their recorded outcomes do not establish
that they describe the current buffer or environment. See the
[editor integration boundary](editor-integration.md) and
[exact source snapshot contract](editor-source-snapshots.md).
