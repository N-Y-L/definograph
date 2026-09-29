/** Ordered occurrence provenance for one chosen retained prefix.
 *
 * Pure derivation over an already validated decomposition history. It reads
 * exact retained steps and receipts and returns frozen plain data. It creates
 * no kernel assumption, witness, proof application or beta-reduction. Inherited
 * occurrence identity follows the actual previousCaptureId/parentStepIndex
 * links at the same step position and never checkpoint equality; fresh receipt
 * spans always belong to the record the prefix was read from. Neutral outcomes
 * are explicit nulls; inconsistent or tampered input refuses by throwing. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import type { PositionalStructuralInput } from '../packets/structure';
import { sourceSnapshotValidation as shared } from './source-snapshot';
import type { SourceOccurrenceStep } from './source-occurrence';
import type { HeadExposureTarget } from './source-head-exposure';
import { DECOMPOSITION_MAX_ATTEMPTS, decompositionParent, isValidatedSourceDecomposition, type DecompositionHistory, type DecompositionStep,
  type SourceDecomposition } from './source-decomposition';
import { logicalInspectionReading, typeComponentFormation, type FormationKind, type LogicalForm } from './logical-inspection-reading';

/** Inherited identity: the retained record and position where an occurrence first appeared. */
export type OccurrenceOrigin = { kind: 'original'; captureId: string } | { kind: 'seed'; captureId: string }
  | { kind: 'step'; captureId: string; stepIndex: number };
/** Fresh receipts of the record the prefix was read from; never an identity. */
export interface ReceiptSpan { captureId: string; start: number; count: number }
export type ReceiptOutcome = 'accepted' | 'rejected' | 'unknown' | 'missing';
/** One formation receipt on an occurrence's term, kept visible whatever its outcome. */
export interface OccurrenceFormation {
  source: 'logical' | 'typeComponent'; kind: FormationKind; inferredType: JsonValue; outcome: ReceiptOutcome;
  origin: OccurrenceOrigin; receipts: ReceiptSpan;
}
/** Established only when every accepted receipt on the subject agrees canonically on the inferred type. */
export type EvidenceStatus = { status: 'unestablished' } | { status: 'conflicting' }
  | { status: 'established'; kind: Exclude<FormationKind, 'unestablished'>; inferredType: JsonValue };
export interface OccurrenceInspection {
  origin: OccurrenceOrigin; receipts: ReceiptSpan; shape: 'forall' | 'standard' | 'unexpanded';
  formation: FormationKind; rootOutcome: ReceiptOutcome; inferredType: JsonValue;
  domain: { formation: FormationKind; inferredType: JsonValue; outcome: ReceiptOutcome } | null;
  /** Syntactic interpretation candidate from the shape and trusted descriptor; never a reading by itself. */
  candidate: LogicalForm;
  /** Null unless the occurrence formation is an established proposition. */
  form: LogicalForm | null;
  /** Established proposition plus the occurrence's domain evidence established at literal Sort zero. */
  proofBinder: boolean; bodyUsesBinder: boolean | null;
  operands: { role: string; path: SourceOccurrenceStep[] }[];
}
export interface OccurrenceCatalogue { origin: OccurrenceOrigin; receipts: ReceiptSpan; fields: number; omittedFields: number }
export interface ProvenanceOccurrence {
  index: number; origin: OccurrenceOrigin; pair: PositionalStructuralInput; receipts: ReceiptSpan;
  /** Term formation over every accepted formation receipt (logical root or typeComponent). */
  formation: EvidenceStatus;
  /** Literal-forall domain formation over every accepted logical domain receipt; typeComponent never contributes. */
  domain: EvidenceStatus;
  formations: OccurrenceFormation[]; inspections: OccurrenceInspection[]; catalogues: OccurrenceCatalogue[];
}
export type BinderRole = 'universal' | 'proof' | 'candidate';
export interface EnteredBinder {
  position: number; step: 'piBody' | 'lamBody' | 'letBody'; name: JsonValue; kind: 'port' | 'let'; role: BinderRole | null;
}
export interface ContainmentRole {
  form: LogicalForm; operand: string; operandPath: SourceOccurrenceStep[]; remainder: SourceOccurrenceStep[]; inspection: number;
}
export type ProvenanceRelation = { kind: 'containment'; path: SourceOccurrenceStep[]; binders: EnteredBinder[]; role: ContainmentRole | null }
  | { kind: 'type-of' } | { kind: 'conversion'; target: HeadExposureTarget; head: JsonValue }
  | { kind: 'projection-of'; index: number; field: JsonValue };
export interface ProvenanceEdge { from: number; to: number; origin: OccurrenceOrigin; receipts: ReceiptSpan; relation: ProvenanceRelation }
export interface OccurrenceProvenance {
  original: { captureId: string; path: SourceOccurrenceStep[] };
  prefix: { previousCaptureId: string; parentStepIndex: number; route: 'original' | 'seed' | 'attempt' };
  occurrences: ProvenanceOccurrence[]; edges: ProvenanceEdge[];
  /** Steps of the chosen record after the chosen prefix. They stay in history and are never read here. */
  excluded: { captureId: string; stepIndices: number[] } | null;
}

type Same = (a: unknown, b: unknown) => boolean;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const json = (value: unknown) => value as JsonValue;
const edges: Record<string, Partial<Record<SourceOccurrenceStep, number>>> = {
  app: { appFun: 1, appArg: 2 }, lam: { lamDomain: 2, lamBody: 3 }, forallE: { piDomain: 2, piBody: 3 },
  letE: { letType: 2, letValue: 3, letBody: 4 }, proj: { projValue: 3 },
};
const entering = new Set<SourceOccurrenceStep>(['piBody', 'lamBody', 'letBody']);
const outcomeOf = (receipt: { outcome: { tag: string } } | undefined): ReceiptOutcome =>
  receipt === undefined ? 'missing' : receipt.outcome.tag === 'accepted' ? 'accepted' : receipt.outcome.tag === 'rejected' ? 'rejected' : 'unknown';

/** Telescope entries oldest first, names only; types stay in the exact pair. */
function entries(telescope: JsonValue): { name: JsonValue; kind: 'port' | 'let' }[] {
  const reversed: { name: JsonValue; kind: 'port' | 'let' }[] = []; let tel = telescope as JsonValue[];
  while (tel[0] !== 'nil') {
    reversed.push(tel[0] === 'port' ? { name: (tel[2] as JsonObject).name, kind: 'port' } : { name: tel[2], kind: 'let' });
    tel = tel[1] as JsonValue[];
  }
  return reversed.reverse();
}
function tail(telescope: JsonValue, drop: number): JsonValue {
  let tel = telescope as JsonValue[];
  for (let i = 0; i < drop; i++) { requireThat(tel[0] !== 'nil', 'focus result home is shorter than its binder steps', ['provenance']); tel = tel[1] as JsonValue[]; }
  return tel;
}
function nodeAt(term: JsonValue, path: SourceOccurrenceStep[]): JsonValue[] | undefined {
  let node = term as JsonValue[];
  for (const step of path) {
    const index = edges[String(node[0])]?.[step];
    if (index === undefined) return undefined;
    node = node[index] as JsonValue[];
  }
  return node;
}
function attempt(history: DecompositionHistory, captureId: string): SourceDecomposition | undefined {
  return history.attempts.find(entry => entry.record.captureId === captureId)?.record;
}
function replayedCount(history: DecompositionHistory, record: SourceDecomposition): number {
  return record.previousCaptureId === history.occurrence.captureId ? 0 : record.parentStepIndex + 1;
}
/** Inherited identity of step `index` of `record`: recurse through the actual
 * parent link at the same position while the step lies in the replayed prefix. */
function originOf(history: DecompositionHistory, record: SourceDecomposition, index: number, depth = 0): OccurrenceOrigin {
  const path: RawPath = ['provenance', 'origin', record.captureId, index];
  requireThat(depth <= DECOMPOSITION_MAX_ATTEMPTS, 'origin recovery exceeds the retained attempt bound', path);
  requireThat(record.checking.status === 'captured' && index < record.checking.steps.length, 'origin recovery addresses a missing step', path);
  const step = record.checking.steps[index];
  if (index >= replayedCount(history, record)) {
    requireThat(step.replay === 'new', 'a step beyond the replayed prefix must be new', path);
    return { kind: 'step', captureId: record.captureId, stepIndex: index };
  }
  requireThat(step.replay === 'matched', 'a replayed step without a matched replay has no inherited identity', path);
  if (history.seed && record.previousCaptureId === history.seed.record.captureId) {
    requireThat(index === 0 && step.operation.kind === 'expose', 'a legacy seed contributes only its exposure', path);
    return { kind: 'seed', captureId: history.seed.record.captureId };
  }
  const parent = attempt(history, record.previousCaptureId);
  requireThat(parent !== undefined, 'origin recovery is unavailable: the parent record is not retained', path);
  return originOf(history, parent, index, depth + 1);
}
/** Evidence over accepted receipts: unestablished, established when all agree, conflicting otherwise. */
function evidence(receipts: { kind: FormationKind; inferredType: JsonValue; outcome: ReceiptOutcome }[], same: Same): EvidenceStatus {
  const accepted = receipts.filter(receipt => receipt.outcome === 'accepted' && receipt.kind !== 'unestablished');
  if (accepted.length === 0) return { status: 'unestablished' };
  return accepted.every(receipt => same(receipt.inferredType, accepted[0].inferredType))
    ? { status: 'established', kind: accepted[0].kind as Exclude<FormationKind, 'unestablished'>, inferredType: accepted[0].inferredType }
    : { status: 'conflicting' };
}
/** Recompute the occurrence's formation and domain evidence from every accepted
 * receipt, then the dependent reading of each inspection on that occurrence. */
function refresh(occurrence: ProvenanceOccurrence, same: Same) {
  occurrence.formation = evidence(occurrence.formations, same);
  occurrence.domain = evidence(occurrence.inspections.flatMap(inspection => inspection.domain
    ? [{ kind: inspection.domain.formation, inferredType: inspection.domain.inferredType, outcome: inspection.domain.outcome }] : []), same);
  const proposition = occurrence.formation.status === 'established' && occurrence.formation.kind === 'proposition';
  const proofDomain = occurrence.domain.status === 'established' && occurrence.domain.kind === 'proposition';
  for (const inspection of occurrence.inspections) {
    inspection.proofBinder = proposition && proofDomain;
    inspection.form = !proposition ? null
      : inspection.shape === 'forall' ? inspection.proofBinder && inspection.bodyUsesBinder === false ? 'implies' : 'forall' : inspection.candidate;
  }
}
function containment(source: ProvenanceOccurrence, path: SourceOccurrenceStep[], result: PositionalStructuralInput, same: Same, at: RawPath): ProvenanceRelation {
  const base = entries(source.pair.home.telescope), grown = entries(result.home.telescope);
  const steps = path.map((step, position) => ({ step, position })).filter(({ step }) => entering.has(step));
  requireThat(grown.length === base.length + steps.length && same(tail(result.home.telescope, steps.length), source.pair.home.telescope),
    'focus result home does not extend the source home by exactly its binder steps', at);
  const binders: EnteredBinder[] = steps.map(({ step, position }, i) => {
    const entry = grown[base.length + i];
    return { position, step: step as EnteredBinder['step'], name: entry.name, kind: entry.kind, role: null };
  });
  let role: ContainmentRole | null = null;
  const proposition = source.formation.status === 'established' && source.formation.kind === 'proposition';
  let inspection = -1;
  for (let i = source.inspections.length - 1; i >= 0; i--) if (source.inspections[i].form !== null) { inspection = i; break; }
  const established = proposition && inspection >= 0 ? source.inspections[inspection] : undefined;
  const operand = established?.operands.find(candidate => candidate.path.length <= path.length && candidate.path.every((step, i) => path[i] === step));
  if (established && established.form !== null && operand) {
    role = { form: established.form, operand: operand.role, operandPath: operand.path, remainder: path.slice(operand.path.length), inspection };
    const binderAt = (position: number, assigned: BinderRole | null) => {
      const binder = binders.find(candidate => candidate.position === position);
      if (binder) binder.role = assigned;
    };
    if ((established.form === 'forall' || established.form === 'implies') && operand.role === 'body') {
      // Binder reading needs the occurrence's logical domain evidence; the operand role comes from formation alone.
      // A general sort keeps the neutral binder reading: a level parameter could instantiate to Prop.
      binderAt(operand.path.length - 1, source.domain.status !== 'established' ? null
        : established.proofBinder ? 'proof' : source.domain.kind === 'type' ? 'universal' : null);
    } else if (established.form === 'exists' && operand.role === 'predicate' && path[operand.path.length] === 'lamBody'
      && nodeAt(source.pair.term, operand.path)?.[0] === 'lam') {
      binderAt(operand.path.length, 'candidate');
    }
  }
  return { kind: 'containment', path, binders, role };
}

/** Derive the ordered chain for the retained prefix ending at `parentStepIndex`
 * of `previousCaptureId`. The same eligibility rule as continuation applies:
 * only completed, matched or new candidates are readable, so a stopped or
 * mismatched step and everything after it refuse. Each call uses its own
 * bounded canonicalization session, so repeated derivations never accumulate. */
export function occurrenceProvenance(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number): OccurrenceProvenance {
  // Uniform precondition: only records registered by validateDecompositionHistory are read, whatever the prefix kind.
  history.attempts.forEach((entry, i) => requireThat(isValidatedSourceDecomposition(entry.record),
    'history must be the validated object returned by validateDecompositionHistory', ['provenance', 'history', 'attempts', i]));
  decompositionParent(history, previousCaptureId, parentStepIndex, 3);
  const tools = createExactJsonTools();
  const canonical = (value: unknown) => tools.canonical(json(value));
  const same: Same = (a, b) => canonical(a) === canonical(b);
  const original = history.occurrence, check = original.checking;
  requireThat(check.status === 'captured' && check.selected !== null, 'history has no original selected pair', ['provenance']);
  const occurrences: ProvenanceOccurrence[] = [], edgeList: ProvenanceEdge[] = [];
  const push = (origin: OccurrenceOrigin, pair: PositionalStructuralInput, receipts: ReceiptSpan) => {
    occurrences.push({ index: occurrences.length, origin, pair, receipts, formation: { status: 'unestablished' }, domain: { status: 'unestablished' },
      formations: [], inspections: [], catalogues: [] });
    return occurrences.length - 1;
  };
  const originIdentity: OccurrenceOrigin = { kind: 'original', captureId: original.captureId };
  let route: OccurrenceProvenance['prefix']['route'], excluded: OccurrenceProvenance['excluded'] = null;
  if (previousCaptureId === original.captureId) {
    route = 'original';
    push(originIdentity, check.selected, { captureId: original.captureId, start: 0, count: check.checks.length });
  } else if (history.seed && previousCaptureId === history.seed.record.captureId) {
    route = 'seed';
    const seed = history.seed.record, seedCheck = seed.checking;
    requireThat(seedCheck.status === 'captured' && seedCheck.selected !== null && seedCheck.exposure?.status === 'candidate'
      && seedCheck.checks.length >= 6, 'seed has no completed exposure', ['provenance']);
    push(originIdentity, seedCheck.selected, { captureId: seed.captureId, start: 0, count: 6 });
    const origin: OccurrenceOrigin = { kind: 'seed', captureId: seed.captureId };
    const receipts = { captureId: seed.captureId, start: 6, count: seedCheck.checks.length - 6 };
    const to = push(origin, seedCheck.exposure.result, receipts);
    edgeList.push({ from: 0, to, origin, receipts, relation: { kind: 'conversion', target: seed.target, head: seedCheck.exposure.definition.name } });
  } else {
    route = 'attempt';
    const record = attempt(history, previousCaptureId);
    requireThat(record !== undefined && record.checking.status === 'captured', 'unknown retained operation', ['provenance']);
    const recordCheck = record.checking, selected = recordCheck.selected;
    requireThat(selected !== null, 'unknown retained operation', ['provenance']);
    push(originIdentity, selected, { captureId: record.captureId, start: 0, count: 6 });
    recordCheck.steps.slice(0, parentStepIndex + 1).forEach((step, index) => apply(history, record, step, index));
    const rest = recordCheck.steps.slice(parentStepIndex + 1).map(step => step.index);
    excluded = rest.length ? { captureId: record.captureId, stepIndices: rest } : null;
  }
  function apply(history: DecompositionHistory, record: SourceDecomposition, step: DecompositionStep, index: number) {
    const at: RawPath = ['provenance', 'steps', index];
    const current = occurrences[occurrences.length - 1], output = step.output, operation = step.operation;
    requireThat(same(step.input, current.pair), 'step input departs from the current occurrence', at);
    requireThat(output.status === 'candidate' && output.checking.status === 'completed', 'only completed candidates carry provenance', at);
    const origin = originOf(history, record, index);
    const receipts: ReceiptSpan = { captureId: record.captureId, start: step.receiptStart, count: step.receiptCount };
    if (operation.kind === 'fields') {
      requireThat('catalogue' in output, 'field catalogue is missing', at);
      current.catalogues.push({ origin, receipts, fields: output.catalogue.fields.length, omittedFields: output.catalogue.omittedFields });
    } else if (operation.kind === 'logical') {
      requireThat('formation' in output && 'shape' in output, 'logical candidate is missing its shape', at);
      const reading = logicalInspectionReading(record, index);
      requireThat(reading !== undefined, 'logical step has no validated reading', at);
      const shape = output.shape as unknown as { kind: 'forall' | 'standard' | 'unexpanded'; form?: LogicalForm; operands: { role: string; path: SourceOccurrenceStep[] }[] };
      const candidate: LogicalForm | undefined = shape.kind === 'forall' ? 'forall' : shape.kind === 'standard' ? shape.form : 'unexpanded';
      requireThat(candidate !== undefined, 'standard logical shape is missing its form', at);
      current.formations.push({ source: 'logical', kind: reading.formation, inferredType: reading.inferredType, outcome: outcomeOf(reading.rootReceipt), origin, receipts });
      current.inspections.push({ origin, receipts, shape: shape.kind, formation: reading.formation, rootOutcome: outcomeOf(reading.rootReceipt), inferredType: reading.inferredType,
        domain: reading.domain ? { formation: reading.domain.formation, inferredType: reading.domain.inferredType, outcome: outcomeOf(reading.domain.receipt) } : null,
        candidate, form: null, proofBinder: false, bodyUsesBinder: reading.bodyUsesBinder ?? null, operands: shape.operands });
      refresh(current, same);
    } else {
      let relation: ProvenanceRelation;
      if (operation.kind === 'focus') relation = containment(current, operation.path, output.result, same, at);
      else if (operation.kind === 'typeComponent') relation = { kind: 'type-of' };
      else if (operation.kind === 'expose') {
        requireThat('definition' in output, 'exposure candidate is missing its definition', at);
        relation = { kind: 'conversion', target: operation.target, head: output.definition.name };
      } else {
        requireThat('field' in output, 'projection candidate is missing its field', at);
        relation = { kind: 'projection-of', index: operation.index, field: output.field.name };
      }
      const to = push(origin, output.result, receipts);
      edgeList.push({ from: current.index, to, origin, receipts, relation });
      if (operation.kind === 'typeComponent') {
        const formation = typeComponentFormation(record, index);
        requireThat(formation !== undefined, 'type component has no validated formation reading', at);
        occurrences[to].formations.push({ source: 'typeComponent', kind: formation.formation, inferredType: formation.inferredType,
          outcome: outcomeOf(formation.receipt), origin, receipts });
        refresh(occurrences[to], same);
      }
    }
  }
  const value: OccurrenceProvenance = { original: { captureId: original.captureId, path: original.path },
    prefix: { previousCaptureId, parentStepIndex, route }, occurrences, edges: edgeList, excluded };
  const detached = tools.parse(canonical(value)) as unknown as OccurrenceProvenance;
  tools.freeze(json(detached));
  return detached;
}
