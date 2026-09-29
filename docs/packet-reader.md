# Exact composition packet client

The `/packet` route reads saved outputs of the Definograph composition checker.
It uses the existing guided sequence, logical overview and application/equality
figures. The ordinary Lean source reader and versioned editor adapter retain
their existing routes and execution contracts.

This is a client of the checking infrastructure. Importing JSON does not run
Lean, authenticate its producer, or certify any current document. The displayed
formation/evidence outcomes are **reported** outcomes. Two reported successful
operations and matching shared references do not establish joint certification.
Failed reference coherence does not establish mathematical inequality.

## Local use

For saved packets alone, Node.js 22.12+ is sufficient. From the repository root:

```sh
npm ci --ignore-scripts
npm run dev:web
```

Open [the packet reader](http://127.0.0.1:5173/packet), then
choose a saved packet file or paste its JSON. The Lean/mathlib setup in the
main README is needed for ordinary statement analysis, not packet import.
Import validation runs locally;
the packet is not sent to the analysis server. Select an operation and its
retained premises or derived consequence. Follow the reading steps and select
objects to inspect their exact source and scope. Selected uses retain their
original/chosen routes, owner-context arguments and certificate universe
information. Each selected function occurrence also shows its full enclosing
call and ordered application arguments. Selecting it opens that call's reading
step while the source inspector retains the exact selected head and shared
supplier identity; Next/Previous then resumes normal navigation.

Switch to **Source structure** to follow the exact expression's constructor
connections and binder regions at every nesting depth. Function and argument,
domain and body, let type/value/body, and projected value have distinct roles.
Declaration links retain identity even when names repeat. Marked folds state
how many nodes they hide and expand in finite chunks. Each node's attached
inspector exposes its exact name components, universes, annotations and source
position; escaped strings distinguish invisible Unicode characters.

Editing the import replaces the current reading. A failed import keeps the
original text available for correction; it cannot reuse an earlier success as
evidence for the changed input. Refused operations remain inspectable, including
when another operation has a usable record. Unknown/missing evidence is distinct
from a false mathematical statement.

## Boundaries between modules

| Module | Responsibility |
| --- | --- |
| `packets/packet.ts` | Exact JSON parsing, canonical hashes, schema and attachment consistency; no producer trust |
| `packets/natural.ts` | Versioned exact decimal natural values and checked narrowing of operational indices |
| `packets/syntax.ts` | Bounded constructor-preserving DAG resolution and simultaneous substitution |
| `packets/semantic.ts` | Per-record, scoped presentation with source associations; no legacy expression interning or mathematical checking |
| `packets/structure.ts` | Constructor drawing, explicit declaration homes and an independent reader reconstructing exact source from emitted fields and child roles |
| `packets/StructuralReading.tsx` | Visible ordered connections, binder regions, declaration references, recoverable folds and attached exact fields |
| `reading/` and `visual/` | Existing sequence, overview and diagrams; presentation does not add evidence |

Packet-backed presentation identities preserve exact constructors and lexical
bindings. Repeated spelling is not identity. Retained and derived supplier
binders are separate, and each operation retains its own supplier. A local
definition retains its value and `nondep` flag; it does not become a universal
choice. Subexpressions without a specialized guided diagram retain an explicit
boundary and can be examined structurally. An opaque part of a dependent type
prevents inference of a complete dependency signature in the guided view.

The guided adapter presents exact `forallE`, `lam` and `letE` introductions,
exact `And`/`Eq` applications, and generic applications with ordered arguments.
Nested unsupported constructors retain an explicit guided-reading boundary. It selects
a uniquely associated captured reading declaration when available; otherwise,
it can display the captured original source statement, disclosing that fallback.
Without a supported declaration association, only the exact stored source is
available. These implemented cases do not establish universal diagram coverage.

The structural view handles `bvar`, registered `fvar`, `sort`, `const`, `lit`,
`app`, `lam`, `forallE`, `letE` and `proj` uniformly at nested positions. It
reconstructs the input from the drawing's fields and ordered connections before
display. This checks structural preservation, independently of Lean typing or
evidence. Its reusable API also accepts exact original local declarations:
external free-variable identities and owned bound-variable positions remain
separate. Opaque local `nondep` values are retained as metadata, never granted
a defining equation.

Unfinished metavariables, metadata expression constructors, and opaque stored
values outside that drawing profile produce an explicit unsupported outcome;
that does not invalidate an otherwise admitted mathematical source. The complete
captured input remains inspectable. The constructor profile, versioned
transport and resource limits are implementation coverage boundaries, not a
definition of the project's completeness goal.

The browser accepts matched envelope/payload versions 1/1 and 2/2. Version 2
encodes every semantic natural as `["nat", "canonical ASCII decimal digits"]`,
including small values. Numeric names, natural literals, raw bound-variable and
projection indices, local declaration indices, selected-use IDs and heartbeat
bounds retain every digit, up to the 10,000-digit implementation limit. Scope
and collection indices are compared against their bounds before conversion.
Finite operational fields remain safe JSON integers.

Legacy safe-range version 1 imports keep their representation and identity;
large raw JSON integer tokens remain unsupported. Mixed encodings, duplicate
JSON keys, floating/exponential number tokens and unpaired Unicode surrogates
are rejected. Canonical object keys are sorted by Unicode code point. New
version 2 captures have new canonical identities and attachment hashes. No
automatic conversion inherits a producer receipt. The structural drawing
records its source version and independently reconstructs that exact wire
representation. Large natural values are displayed as decimal text without a
floating-point approximation or an inferred numerical interpretation.
Import size is limited to 16 MiB, with additional parser, serialization and
diagram traversal bounds. Structural traversal is capped at 100,000 data/work
nodes, depth 256, two million text characters, and 256 external declarations;
callers can lower these limits. Unsupported source remains inspectable without a
fabricated partial success. The diagram does not independently check Lean proofs.

Editor occurrence candidates use a separate positional drawing schema and build/read
API, described in [editor source snapshots](editor-source-snapshots.md). Their
context supplies ambient bound positions. A packet's named external registry still
supplies only free-variable identities and cannot make an otherwise unbound index
valid. Both formats share the constructor presentation and finite rendering bounds.
The exact presentation compiler also has a direct positional entry for the shared
guided reader. This occurrence mode uses neutral parameters and generic applications
with separate term/type targets. It does not fabricate a packet or reuse packet
proposition classifications; the existing packet route keeps its own contract.

## Lean integration

The existing trusted-project editor sidecar elaborates the real active buffer
and reads Lean's actual context, with request/version/selection invalidation.
Its legacy export substitutes local lets definitionally. That export cannot
stand in for an exact let-preserving component admission contract.

The composition backend provides the reusable `PacketCapture` Lean module,
which accepts typed represented components in the caller's actual environment
and captures exact checks with an explicit resource policy. The fixed CLI
fixtures are one caller. Connecting arbitrary editor selections to that module
requires connecting source/context admission to declared environment/version bindings;
the saved-packet client does not claim that connection is already implemented.
Neither path modifies Lean's kernel. See [editor integration](editor-integration.md)
for its execution and project-source boundary.

The backend's `SourceCapture` API now performs exact named source admission,
occurrence extraction and dependent map checks with isolated caller state. It
preserves supplied-source checks separately and in the aggregate extraction
outcomes. Its transport can explicitly decline unsupported retained metadata;
kernel admission and transport/display coverage are separate boundaries. The
editor's legacy export has not yet been replaced by this exact API.

## Checks

Run `npm run build`, `npm test`, and `npm run test:server` for portable checks.
Packet tests include independent canonicalization and malformed-input controls.
For additional real-worker fixtures, set `DEFINOGRAPH_PACKET_FIXTURES` to a
separate fixture directory containing `worker-packets/` and `import-controls/`.
Set `DEFINOGRAPH_V2_PACKET_FIXTURES` to the separate directory containing fresh
version 2 packet files and their `production.json` identity inventory to run the
additional full-pipeline controls. Private project packets are not bundled with the application or committed.

For actual source-capture roundtrips, run `scripts/structure-capture.lean` with
the backend's configured import directory on `LEAN_PATH`. Each
`STRUCTURAL_SOURCE=` output line contains one JSON record. Save those records as
a JSON array outside the repository and set `DEFINOGRAPH_SOURCE_CAPTURES` to its
path when running the tests. The controls include dependent external contexts,
same-spelled identities, opaque metadata, nested lets/projections, owned have,
universe expressions, string literals, adjacent large naturals, numeric names
and an independently specified long decimal literal. No source-capture data are bundled.

Browser interaction and actual VS Code host use are separate checks. Automated
transport, scope and rendering tests do not establish human comprehension.
