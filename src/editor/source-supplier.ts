/** Proof-supplier distinctions as a pure derivation over the accepted ordered
 * provenance.
 *
 * Reads the accepted chain for a chosen prefix and, per occurrence, exactly one
 * extra receipt: the typing receipt (term : type in the exact home) at the
 * position the module's span already names. Formation is taken from the
 * accepted module and never derived from typing. Every type-of edge receives
 * one status; a supplier reading exists only with an accepted typing receipt on
 * the source and an established proposition formation on the target, and it is
 * conditional on the source's whole ordered home, the binders entered and the
 * ordered frames above the source. The formation
 * receipts of a link target are listed once each and split by the exact
 * judgement they check, so receipts of different inferred types are never
 * presented as one judgement and equal ones never as independent confirmation.
 * Parts of a whole type are positional lineage, never specialized proofs. Nothing is read
 * beyond the chosen prefix; inconsistent input refuses by throwing. Every
 * structure created here is frozen in depth before it is returned; the
 * provenance arrives frozen from the accepted module. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { sourceSnapshotValidation as shared, type SnapshotAudit, type SnapshotReceipt } from './source-snapshot';
import type { SourceOccurrenceStep } from './source-occurrence';
import type { DecompositionHistory } from './source-decomposition';
import type { FormationKind } from './logical-inspection-reading';
import { occurrenceProvenance, type BinderRole, type ContainmentRole, type EnteredBinder, type OccurrenceProvenance, type ProvenanceOccurrence, type ReceiptOutcome, type ReceiptSpan } from './source-provenance';

const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;

/** The declaration audit the record holds for one receipt: the axioms the declaration was recorded to depend on, or the reason
 * no audit is available. It is recorded data, carried as it is and meant to be shown. It never gates a status: an accepted typing
 * check of a term that depends on an axiom, or on a lemma whose proof is a placeholder, is still an accepted typing check. */
export type ReceiptAudit = { tag: 'available'; axioms: JsonValue[] } | { tag: 'unavailable'; reason: string };
/** The typing receipt of an occurrence: `term : type` in the exact home, from the record the prefix was read from. */
export interface TypingReceipt {
  captureId: string; index: number; outcome: Exclude<ReceiptOutcome, 'missing'>;
  /** The recorded audit of this receipt: the entry of the same record at the same index, by value. */
  audit: ReceiptAudit;
  /** Receipt identity only: true when this physical receipt is also the occurrence's type-component formation receipt (an occurrence
   * created by typeComponent), whatever its outcome. One receipt, two roles; it establishes nothing unless accepted. */
  alsoFormation: boolean;
}
/** One physical formation receipt of a type-of target: local index 1 of the type-component step that created the target or of a
 * logical step on the target, in the record the prefix was read from. Listed once, whatever roles it serves, with its own outcome. */
export interface FormationReceipt {
  /** Position of this receipt's entry in the accepted module's `formations` of the target, where its kind and origin are read. */
  entry: number;
  source: 'logical' | 'typeComponent';
  /** The physical receipt: absolute index in the record read from (shown to a reader as index + 1). */
  captureId: string; index: number;
  /** The creating step's span, as the accepted module names it for this formation entry. */
  span: ReceiptSpan;
  outcome: Exclude<ReceiptOutcome, 'missing'>;
  /** The same physical receipt as the target's own typing receipt: one receipt serving typing and formation, never counted twice. */
  alsoTyping: boolean;
}
/** The receipts that check one exact judgement: the target's term in the target's home at this inferred type. Subject and home are
 * the target pair's for every formation receipt (shared validators and the accepted module), so two judgements of one target differ
 * exactly in the canonical inferred type. The comparison is syntactic, the one the accepted module uses for its own status: types
 * that are definitionally equal but written differently stay in different groups.
 *
 * Rules for any wording built on this: several receipts in one group are receipts of one checked judgement, never independent
 * confirmation, and that sentence is used only inside one group, never across groups and never for a conflicting target as a
 * whole; outcomes are worded per receipt; a group can hold accepted and non-accepted receipts of one judgement and is never called
 * confirmed, agreed or overridden; formation rests only on the accepted receipts of the established group; the type of a
 * non-accepted receipt is what was submitted for checking, never a classification; a receipt that is also the target's own typing
 * receipt is one receipt, never two. */
export interface FormationJudgement {
  inferredType: JsonValue;
  /** True only when the accepted module reports the target's formation as established at this inferred type. Copied from the
   * module's status, never derived here; a group can contain a rejected or unknown receipt beside the accepted one it rests on. */
  established: boolean;
  /** In the accepted module's order. */
  receipts: FormationReceipt[];
}
/** Ordered scope above an occurrence, read only from the chain's edges. */
export type Frame = { kind: 'containment'; edge: number; path: SourceOccurrenceStep[]; role: ContainmentRole | null; binders: EnteredBinder[] }
  | { kind: 'type-of' | 'projection-of' | 'conversion'; edge: number };
/** Where an entry of a home comes from. `context`: a declaration of the captured context, with the declaration kind the capture
 * recorded for it (for example `auxDecl` for the elaborator's auxiliary self-reference); classification never reads the name.
 * `selection`: entered inside the captured term on the way to the originally selected occurrence. `entered`: entered by a
 * containment edge of this chain, with the role the accepted module reads for that binder, which may be none. */
export type HomeOrigin = { kind: 'context'; declaration: number; declarationKind: string | null }
  | { kind: 'selection' } | { kind: 'entered'; edge: number; binder: number; role: BinderRole | null };
/** One entry of an occurrence's home, outermost first. The exact type and value of the entry stay in the occurrence's pair. No
 * entry is an assumption by being listed: a logical reading of an entry exists only as the role of an entered binder. */
export interface HomeEntry { position: number; kind: 'port' | 'let'; name: JsonValue; origin: HomeOrigin }
export type LinkStatus = 'supplier' | 'value-of-type' | 'not-established' | 'conflicting' | 'annotation-only';
/** One status per type-of edge k → m. */
export interface TypeOfLink {
  edge: number; from: number; to: number; status: LinkStatus;
  typing: TypingReceipt;
  /** Status and kind are the accepted module's. `judgements` lists every formation receipt of the target, whatever its outcome. */
  formation: { status: 'unestablished' | 'conflicting' | 'established'; kind: FormationKind | null; judgements: FormationJudgement[] };
  /** Conditions of a supplier reading: the source's whole ordered home, over which its typing receipt is checked, the entered
   * binders with the module's roles, and the ordered frames above the source. */
  conditions: { home: HomeEntry[]; binders: EnteredBinder[]; frames: Frame[] };
}
export type PartTier = 'within-supplied-law' | 'within-statement' | 'within-annotation' | 'within-expression';
/** An occurrence reached from its root by containment only. */
export interface Part {
  occurrence: number; root: number; supplier: number | null; tier: PartTier; path: SourceOccurrenceStep[]; frames: Frame[];
}
export interface SupplierReading {
  provenance: OccurrenceProvenance;
  occurrences: { index: number; typing: TypingReceipt; lineage: Frame[] }[];
  links: TypeOfLink[];
  parts: Part[];
}

function receiptAt(history: DecompositionHistory, captureId: string, index: number, at: RawPath): { receipt: SnapshotReceipt; audit: SnapshotAudit } {
  const record = captureId === history.occurrence.captureId ? history.occurrence
    : history.seed && captureId === history.seed.record.captureId ? history.seed.record
      : history.attempts.find(entry => entry.record.captureId === captureId)?.record;
  requireThat(record !== undefined && record.checking.status === 'captured', 'typing receipt names a record outside this history', at);
  const receipt = record.checking.checks[index], audit = record.checking.audits[index];
  requireThat(receipt !== undefined, 'typing receipt is missing from the record read from', at);
  requireThat(audit !== undefined && audit.checkId === receipt.id, 'typing receipt has no audit of its own in the record read from', at);
  return { receipt, audit };
}
function typingOf(history: DecompositionHistory, provenance: OccurrenceProvenance, index: number): TypingReceipt {
  const occurrence = provenance.occurrences[index], span = occurrence.receipts, at: RawPath = ['supplier', 'typing', index];
  // Occurrence 0 is the selected pair: base receipt 5 ("selected component"). Every created occurrence: local index 1 of its step span.
  const local = index === 0 ? 5 : 1;
  requireThat(local < span.count, 'typing receipt lies outside the occurrence span', at);
  const { receipt, audit } = receiptAt(history, span.captureId, span.start + local, at);
  const declaration = receipt.declaration as JsonObject;
  requireThat(receipt.label === 'component' && declaration.kind === 'defnDecl', 'typing receipt is not a component declaration', at);
  // The position is also guarded by the declaration's own name: the component of the selected pair for the first occurrence (never
  // the source or root component beside it), and the component of the producing operation for every other occurrence.
  const named: string[] = [];
  for (let node = declaration.name as JsonValue; Array.isArray(node) && node[0] === 'str' && named.length < 3; node = node[1]) named.unshift(String(node[2]));
  const relation = index === 0 ? null : provenance.edges[index - 1].relation.kind;
  const expected = relation === null ? ['extraction', 'selected', 'component']
    : [relation === 'containment' ? 'focus' : relation === 'type-of' ? 'typeComponent' : relation === 'projection-of' ? 'project' : 'result', 'component'];
  requireThat(expected.every((part, position) => named[named.length - expected.length + position] === part), 'typing receipt is not the component of this occurrence', at);
  const outcome = receipt.outcome.tag === 'accepted' ? 'accepted' : receipt.outcome.tag === 'rejected' ? 'rejected' : 'unknown';
  const alsoFormation = occurrence.formations.some(formation => formation.source === 'typeComponent'
    && formation.receipts.captureId === span.captureId && formation.receipts.start === span.start);
  // The audit is carried by value, detached from the record, exactly as recorded.
  const recorded: ReceiptAudit = audit.result.tag === 'available' ? { tag: 'available', axioms: audit.result.axioms.map(axiom => JSON.parse(JSON.stringify(axiom)) as JsonValue) }
    : { tag: 'unavailable', reason: audit.result.reason };
  return { captureId: span.captureId, index: span.start + local, outcome, audit: recorded, alsoFormation };
}
/** Split the target's formation receipts by exact checked judgement. Inconsistent input refuses; nothing is relabelled. */
function judgementsOf(target: ProvenanceOccurrence, own: TypingReceipt, canonical: (value: JsonValue) => string, at: RawPath): FormationJudgement[] {
  const formation = target.formation, established = formation.status === 'established' ? canonical(formation.inferredType) : null;
  const groups: { key: string; judgement: FormationJudgement }[] = [], seen = new Set<string>();
  target.formations.forEach((entry, position) => {
    const where: RawPath = [...at, 'formations', position];
    requireThat(entry.outcome !== 'missing' && entry.receipts.count > 1, 'formation receipt is missing from the record read from', where);
    const index = entry.receipts.start + 1, reference = `${entry.receipts.captureId}#${index}`;
    requireThat(!seen.has(reference), 'one physical receipt is cited twice as formation evidence', where);
    seen.add(reference);
    const alsoTyping = entry.receipts.captureId === own.captureId && index === own.index;
    // One physical receipt read along two paths, as typing of the target and as its type-component formation entry: same
    // outcome, and the same checked type (the target's own type), compared here and not assumed.
    requireThat(alsoTyping === (entry.source === 'typeComponent')
      && (!alsoTyping || (entry.outcome === own.outcome && canonical(entry.inferredType) === canonical(target.pair.type as JsonValue))),
      'the type-component receipt reads differently as typing and as formation', where);
    const key = canonical(entry.inferredType);
    let group = groups.find(item => item.key === key);
    if (!group) groups.push(group = { key, judgement: { inferredType: entry.inferredType, established: key === established, receipts: [] } });
    group.judgement.receipts.push({ entry: position, source: entry.source, captureId: entry.receipts.captureId, index, span: entry.receipts, outcome: entry.outcome, alsoTyping });
  });
  // A type-of target is created by exactly one type-component step, whose component receipt is the target's own typing receipt.
  requireThat(own.alsoFormation && groups.flatMap(group => group.judgement.receipts).filter(receipt => receipt.alsoTyping).length === 1,
    'type-of target lacks its own type-component receipt', at);
  // The status is the accepted module's alone and is not recomputed here; its agreement with the groups is a test invariant.
  return groups.map(group => group.judgement);
}
/** The ordered home of an occurrence: the captured context, then what the original selection entered, then what the chain entered. */
function homeOf(history: DecompositionHistory, provenance: OccurrenceProvenance, index: number, canonical: (value: JsonValue) => string, at: RawPath): HomeEntry[] {
  const home = provenance.occurrences[index].pair.home, nodes: JsonValue[][] = [];
  for (let node = home.telescope as JsonValue[]; Array.isArray(node) && node[0] !== 'nil'; node = node[1] as JsonValue[]) nodes.unshift(node);
  requireThat(nodes.every(node => node[0] === 'port' || node[0] === 'letE'), 'home has an entry that is neither a port nor a let entry', at);
  requireThat(nodes.length === home.arity, 'home departs from its recorded arity', at);
  // The original occurrence of a validated history is always captured, and its binding carries the captured context with the
  // recorded declaration kinds; the parent snapshot's own check record may be unavailable without affecting the chain.
  const checking = history.occurrence.checking;
  requireThat(checking.status === 'captured', 'the captured context is unavailable', at);
  const context = checking.binding.context, base = provenance.occurrences[0].pair.home.arity;
  const entered = provenance.edges.slice(0, index).flatMap((edge, position) => edge.relation.kind === 'containment'
    ? edge.relation.binders.map((binder, order) => ({ edge: position, order, binder })) : []);
  requireThat(context.arity === context.originalDeclarations.length && context.arity <= base && base + entered.length === nodes.length,
    'home does not extend the captured context by the binders entered', at);
  // The captured context is the outermost part of every home of the chain, entry for entry.
  const innermost = context.arity > 0 ? nodes[context.arity - 1] : nodes.length > 0 ? nodes[0][1] : home.telescope as JsonValue;
  requireThat(canonical(innermost) === canonical(context.telescope), 'home does not begin with the captured context', at);
  return nodes.map((node, position) => {
    // As the accepted module reads a telescope: a port carries its name in its binder record, a let entry (constructor letE) carries it directly.
    const kind: 'port' | 'let' = node[0] === 'port' ? 'port' : 'let', name = kind === 'port' ? (node[2] as JsonObject).name : node[2], where: RawPath = [...at, 'home', position];
    if (position < context.arity) {
      const declaration = context.originalDeclarations[position];
      requireThat(canonical(declaration.userName) === canonical(name), 'captured declaration departs from its context entry', where);
      return { position, kind, name, origin: { kind: 'context' as const, declaration: position, declarationKind: typeof declaration.kind === 'string' ? declaration.kind : null } };
    }
    if (position < base) return { position, kind, name, origin: { kind: 'selection' as const } };
    const item = entered[position - base];
    requireThat(item.binder.kind === kind && canonical(item.binder.name) === canonical(name), 'entered binder departs from its home entry', where);
    return { position, kind, name, origin: { kind: 'entered' as const, edge: item.edge, binder: item.order, role: item.binder.role } };
  });
}
function frameOf(provenance: OccurrenceProvenance, edge: number): Frame {
  const relation = provenance.edges[edge].relation;
  return relation.kind === 'containment' ? { kind: 'containment', edge, path: relation.path, role: relation.role, binders: relation.binders } : { kind: relation.kind, edge };
}

/** Derive typing, type-of link statuses and parts for the chosen prefix. */
export function supplierReading(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number): SupplierReading {
  const provenance = occurrenceProvenance(history, previousCaptureId, parentStepIndex);
  // One bounded canonicalization session per derivation, the comparison the accepted module uses for its own status.
  const tools = createExactJsonTools(), canonical = (value: JsonValue) => tools.canonical(value);
  const edges = provenance.edges;
  edges.forEach((edge, i) => requireThat(edge.from === i && edge.to === i + 1, 'provenance chain is not linear', ['supplier', 'edges', i]));
  const occurrences = provenance.occurrences.map(occurrence => ({ index: occurrence.index, typing: typingOf(history, provenance, occurrence.index),
    lineage: edges.slice(0, occurrence.index).map((_, edge) => frameOf(provenance, edge)) }));
  const links: TypeOfLink[] = [];
  edges.forEach((edge, i) => {
    if (edge.relation.kind !== 'type-of') return;
    const source = provenance.occurrences[edge.from], target = provenance.occurrences[edge.to];
    requireThat(JSON.stringify(target.pair.home) === JSON.stringify(source.pair.home) && JSON.stringify(target.pair.term) === JSON.stringify(source.pair.type),
      'type-of edge does not relate the source type to the target term', ['supplier', 'links', i]);
    const typing = occurrences[edge.from].typing, formation = target.formation;
    const status: LinkStatus = typing.outcome !== 'accepted' ? 'annotation-only'
      : formation.status === 'conflicting' ? 'conflicting'
        : formation.status === 'established' && formation.kind === 'proposition' ? 'supplier'
          : formation.status === 'established' && formation.kind === 'type' ? 'value-of-type' : 'not-established';
    const lineage = occurrences[edge.from].lineage;
    links.push({ edge: i, from: edge.from, to: edge.to, status, typing,
      formation: { status: formation.status, kind: formation.status === 'established' ? formation.kind : null,
        judgements: judgementsOf(target, occurrences[edge.to].typing, canonical, ['supplier', 'links', i]) },
      conditions: { home: homeOf(history, provenance, edge.from, canonical, ['supplier', 'links', i]),
        binders: lineage.flatMap(frame => frame.kind === 'containment' ? frame.binders : []), frames: lineage } });
  });
  const parts: Part[] = [];
  provenance.occurrences.forEach(occurrence => {
    const j = occurrence.index;
    if (j === 0 || edges[j - 1].relation.kind !== 'containment') return;
    let root = j;
    while (root > 0 && edges[root - 1].relation.kind === 'containment') root--;
    const link = links.find(link => link.to === root), rootFormation = provenance.occurrences[root].formation;
    // A root that is a type-of target without a supplier reading is a recorded annotation or typed value; its parts are positions within it.
    const tier: PartTier = link?.status === 'supplier' ? 'within-supplied-law' : link !== undefined ? 'within-annotation'
      : rootFormation.status === 'established' && rootFormation.kind === 'proposition' ? 'within-statement' : 'within-expression';
    const frames = edges.slice(root, j).map((_, offset) => frameOf(provenance, root + offset));
    parts.push({ occurrence: j, root, supplier: link?.status === 'supplier' ? link.from : null, tier,
      path: frames.flatMap(frame => frame.kind === 'containment' ? frame.path : []), frames });
  });
  tools.freeze(occurrences); tools.freeze(links); tools.freeze(parts);
  return Object.freeze({ provenance, occurrences, links, parts });
}
