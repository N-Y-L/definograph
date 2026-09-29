# Definition exposure, fields and continuations

After checking a chosen editor occurrence, select its **Term** or **Inferred type**
and use **Expose definition head**. The reader keeps the original expression and
shows the exposed result, exact trace and fresh check outcomes. The result uses the
same guided and structural readers as the original occurrence. No definition name
or fixture recognizer is registered to make this operation work.

## The step

The worker re-elaborates the trusted current buffer and matches the exact original
selection, prepared frame, universe parameters and selected dependent triple.
It looks up the original application's global head in that process's initial
environment. Only a safe definition is eligible. The worker substitutes its actual
universe arguments structurally, consumes only the body's original leading lambdas,
and reapplies any remaining original arguments. Substitution preserves scope and
does not simplify universe `max` or `imax` constructors.

This is one body exposure. Newly created redexes, nested definitions, local lets,
projections and recursors are not reduced. Recursive references in the exposed body
stay folded. Opaque declarations, theorems, axioms, constructors, recursors, local
heads, unsafe/partial definitions and unsupported metadata receive an explicit
refusal. A safe definition with an opaque *reducibility hint* is eligible; it is
different from an opaque declaration. Hints do not control this explicit operation.

The retained trace contains the actual definition, formal and actual universe
parameters, body, type, original ordered arguments and consumed-lambda count.
The browser independently reconstructs the exact syntactic result. This checks
record consistency; a saved JSON declaration does not authenticate membership in
a Lean environment.

## Meaning of the checks

Let the selected triple be context Γ, term t and inferred type A. Exposing the term
checks the result against A. Exposing the type first infers A's type in Γ and
requires a literal `Sort ℓ`; the result is checked against that `Sort ℓ`. The latter
display therefore labels it **Carrier annotation**, rather than treating A's own
type as the original term's inferred type. The context, including owned lets and
their flags, is preserved exactly.

The fresh process retains source, root and selected context/component outcomes
(six checks), then result context, result component and conversion (three more).
The conversion theorem uses `Eq.refl` with the exact before/after pair and carrier,
closed in Γ. Acceptance establishes kernel convertibility, including Lean's proof
irrelevance; independent trace replay is what verifies the specified syntactic step.
It does not establish understanding of the definition or certify the surrounding
source file. A rejected root remains visible even when later local checks accept.

Ordinary rejection or an unknown result does not erase earlier checks or stop later
ones. A callback error retains its genuine receipt prefix and candidate when the
receipt, audit and environment chain is coherent. If that chain is inconsistent,
or the output exceeds its limit, the complete checking record is explicitly omitted.

## Freshness and limits

The webview requests only the retained capture ID and term/type target. The host
supplies its immutable original snapshot and occurrence, checks the current source,
selection, document revision, trusted project and engine identity, and launches a
fresh process. Original and fresh captures remain separate. Edits, changed
selection, configuration changes, dirty imports and cancellation invalidate the
request. Saved exports carry both bundles as unverified records and cannot launch
live exposure actions. Definitions are never opened automatically.

Each standalone construction is bounded to 20,000 expression-plus-level constructor
occurrences, depth 96 and 128 KiB of accumulated UTF-8 payload text. Inserted argument
copies count again, and are charged before allocation. The existing context limit
is 128 entries. A single-head request is at most 768 KiB and its complete exposure
attachment at most 1 MiB. The combined native response is at most 4 MiB; JSON nesting
is limited to 120. The process deadline is 45 seconds, with 400,000 enclosing Lean
heartbeats and 200,000 per check. Limits produce a stated boundary rather than an
unbounded normalization attempt.

## Continue inside a result

After an exposure completes, choose a part of its **After exposure** expression
in Guided reading or Structure, then press **Check chosen part**. The new step
retains that part's complete surrounding context and a separately inferred type.
You can inspect the checked term or its inferred type, then explicitly expose
that target's definition head. A completed pair can also be inspected for direct fields, exposed again or focused again. Changing
tabs, selecting a source position, or opening a fold never runs Lean.

Only expression positions within the preceding result term can be chosen.
Its carrier annotation and surrounding context remain available for inspection.
Choosing the whole result is allowed, and its newly inferred type is retained
even when its syntax differs from the previous annotation. A focused part is a
separate result: this operation does not replace that part throughout an enclosing
dependent expression.

Each action re-elaborates the current trusted buffer once and recomputes the exact
chosen prefix. Earlier expression pairs and definition traces must match before
the new action begins. A changed or incomplete step stays inspectable but cannot
be continued. Rejected or unknown check verdicts remain separate from whether an
operation completed. Earlier completed matching steps can still be continued
after a later step stops.

The reader keeps the original occurrence and every retained continuation attempt.
Choosing an earlier completed step starts a new continuation without deleting the
previous suffix. The original can start an independent attempt too. Once an action
begins, even if its whole result record is omitted, the original selection stays
fixed; save and **Refresh** to start another source history. Saved revision 5
supports a history beginning directly at that occurrence; export uses revision 6
when any retained attempt uses the v3 schema, which supports type/logical
operations. Legacy v1/v2 records and one-head seeds remain supported in retained
histories. These saved-source exports
remain unverified data: there is no saved editor-snapshot importer, and neither the
separate packet reader nor raw-frame importer grants them current-source authority
or a native execution route.

A continuation has at most eight operations. The source path and all
focus paths together have at most 128 edges, each path at most 64. The maximum
completed receipt schedule is six base checks, three per exposure or projection,
two per focus or type inspection, and zero per field catalogue. Logical inspection
adds two root checks, plus two domain checks for a literal `forall`; interrupted
checking can retain fewer receipts. A v3 plan conservatively reserves four checks
per logical operation and refuses reservation totals above 30, even when a
particular result would need only two. V2 attempts also retain at most 30 outcomes.
Legacy v1 records retain their strict exposure/focus alternation and 26-check cap.
Each native continuation request/record is limited to 2 MiB, within the
existing 4 MiB response and 45-second deadline. The editor keeps at most eight
continuation attempts and 16 MiB of aggregate source/history data, including room
for a bounded refusal and export metadata. Limits preserve earlier history rather
than silently evicting it.

## Inspect a type or one logical layer

**Inspect type** makes the pair's inferred type the next term, preserving its home
and recording the new pair's checks. **Read logical structure of this term (one
layer)** inspects the current term, without recursively unfolding unfamiliar
definitions. To inspect an inferred type's logical structure, choose **Inspect
type** first. These v3 operations preserve earlier attempts and selected prefixes.
Formation, typing, proof supply and visible meaning remain distinct; see
[reader relations](reader-relations.md) for the evidence, full conditions and axiom
audits attached to the derived readings.

## Inspect a record and check a field

Use **Inspect fields** on the original occurrence or a completed derived pair.
This lists at most 16 direct fields in constructor order. The owner pair is unchanged,
and no field typing checks are requested by listing metadata. **Check field**
explicitly selects one retained entry and starts a fresh replay. No expression or
catalogue supplied by the webview becomes executable input.

A catalogue requires a literal fully applied structure constant in the owner's
type. It uses the initial environment's safe, nonrecursive, single-constructor
structure and actual projector metadata. An embedded parent appears as a direct
subobject; parents are not flattened. Non-structures, type aliases and unsupported
metadata produce a retained refusal. Exposing the owner's type does not in general
recover an aliased record, because it produces a type-expression pair instead of
reannotating the owner.

The checked field is the named projector applied to its exact universe arguments,
type parameters and owner. The record also retains the primitive kernel projection,
the newly inferred field type and its literal sort. Three local checks concern the
unchanged context, the named component, and its conversion to the primitive
projection. The browser reconstructs both terms and all closed declarations. A
proof-valued field may have a theorem projector: its application is allowed, while
its proof body is never unfolded by field inspection. Conversion includes proof
irrelevance and does not establish identity of proof bodies.

A projected record can be inspected again. A projected law proof can have its type
head exposed, followed by positional focus under a binder and another exposure.
The law stays scoped to its owner and assumptions. This path supplies exact local
operations, not automatic logical classification or a global truth claim.

Catalogue metadata is compared during historical replay before the new projection
starts. A catalogue itself has no receipts. A failed projection callback can retain
zero, one, two or three local outcomes; a candidate's inferred type is not checked
component typing until a corresponding receipt exists. Display labels distinguish
retained **Owner type**, newly **Inferred type**, and exposure **Carrier annotation**.
The existing deadline, context and expression guards apply, with at most 65,536
metadata fields, 128 parameters/universes, and an explicit omitted-field count.

## Verification

`npm run test:source-head-exposure` exercises real fresh editor processes with
unfamiliar and renamed compositions, function-type and dependent aliases, a recursive
body, an owned local definition, refusals and stale/cancel gates. The validator and
replay suites independently check exact trace and receipt association, hostile input,
partial outcomes and term/type distinctions. Backend controls also exercise
under/overapplication, structural universe substitution, generated expansion limits,
initial-environment guards and deliberately invalid conversion candidates.

`npm run test:source-decomposition` exercises fresh processes for nested and renamed
wrappers, owned local definitions, dependent binders, distinct old and newly inferred
types, unsupported heads, and continuation from an earlier step while retaining its
old suffix. Backend controls cover eight-operation limits, partial focus receipts,
mixed check verdicts, replay mismatches and initial-environment guards. The browser
validators reconstruct each exposed result, focused context and closed check
declaration independently of the native implementation.

`npm run test:source-fields` exercises fresh v2 editor requests from original pairs,
nested and renamed law wrappers, dependent internal carriers, inherited subobjects,
owned local definitions, Prop-valued records, empty and bounded catalogues, aliases,
non-structures, backtracking, and a legacy v1 prefix continued in v2. Native controls
also cover interrupted callbacks, conversion rejection, altered metadata and
initial-environment guards. Validator and host controls reject changed field
identities, owners, projector applications, declaration receipts and stale ancestry.

Native process, mocked extension and browser checks have distinct scopes. Actual
VS Code GUI installation and use remain a separate validation requirement. See
[editor integration](editor-integration.md) and [current status](status.md).
