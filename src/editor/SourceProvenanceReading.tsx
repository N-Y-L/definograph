/** Read-only presentation of the accepted ordered occurrence provenance.
 *
 * `ProvenancePanel` renders a frozen OccurrenceProvenance value as data and
 * maps it to labels; it derives nothing: no parent-link walking, no receipt
 * reading, no checkpoint comparison, no logical interpretation. The one
 * comparison it makes is between two receipt spans the module supplies, to say
 * when an occurrence's own outcomes are also listed as its formation outcome.
 * Neutral entries
 * stay visible as neutral, inherited identity and recorded outcomes are
 * separate lines, and a refused prefix is an explicit notice beside the
 * still-visible step outcomes. `deriveProvenance` is the single call site of
 * the accepted module for the reader. */
import { Fragment, useState } from 'react';
import { StructuralFieldValue } from '../packets/StructuralReading';
import { nameText } from '../packets/syntax';
import { recordedName } from '../packets/recorded-name';
import type { JsonValue } from '../packets/packet';
import type { PositionalLogicalRoot } from '../packets/semantic';
import type { DecompositionHistory } from './source-decomposition';
import type { FormationKind, LogicalForm } from './logical-inspection-reading';
import { occurrenceProvenance, type ContainmentRole, type EnteredBinder, type EvidenceStatus, type OccurrenceFormation, type OccurrenceInspection,
  type OccurrenceOrigin, type OccurrenceProvenance, type ProvenanceOccurrence, type ProvenanceRelation, type ReceiptOutcome, type ReceiptSpan } from './source-provenance';
import { continuationPathTitle } from './ContinuationChoice';

export type DerivedProvenance = { value: OccurrenceProvenance; refusal?: undefined } | { value?: undefined; refusal: string };
/** The reader's only call of the accepted module. A refusal is data, not an error. */
export function deriveProvenance(history: DecompositionHistory | undefined, previousCaptureId: string, parentStepIndex: number): DerivedProvenance | undefined {
  if (!history) return undefined;
  try { return { value: occurrenceProvenance(history, previousCaptureId, parentStepIndex) }; }
  catch (error) { return { refusal: error instanceof Error ? error.message : String(error) }; }
}
/** The guided reading's logical root is the module's last inspection of the
 * displayed occurrence, or none; it is never read from the step's own receipts
 * separately, so the guided sentence and the panel cannot disagree. */
export function guidedLogicalRoot(derived: DerivedProvenance | undefined): PositionalLogicalRoot | null {
  const occurrence = derived?.value?.occurrences.at(-1);
  const inspection = occurrence ? [...occurrence.inspections].reverse().find(candidate => candidate.form !== null) : undefined;
  if (!inspection || inspection.form === null) return null;
  return { form: inspection.form, proofBinder: inspection.proofBinder, ...(inspection.bodyUsesBinder === null ? {} : { bodyUsesBinder: inspection.bodyUsesBinder }) };
}

const safeName = (value: JsonValue): string => { try { return nameText(value as never); } catch { return 'unnamed'; } };
const kindTitles: Record<FormationKind, string> = {
  proposition: 'a proposition', type: 'a type above Prop', 'general-sort': 'a sort of general level', term: 'an ordinary term', unestablished: 'not established',
};
const formTitles: Record<LogicalForm, string> = {
  forall: 'universal statement', implies: 'implication', eq: 'equality', and: 'conjunction', or: 'disjunction of alternatives', iff: 'equivalence',
  not: 'negation', exists: 'existential statement', true: 'the constant True proposition', false: 'the constant False proposition', unexpanded: 'unexpanded proposition',
};
/** Head constants the standard-core descriptor recognizes, shown as identifiers in code. They name the syntax of a candidate
 * when no logical form is read, and the constant inside the title of a read constant proposition. */
const candidateHeads: Partial<Record<LogicalForm, string>> = { eq: 'Eq', and: 'And', or: 'Or', iff: 'Iff', not: 'Not', exists: 'Exists', true: 'True', false: 'False' };
const operandTitles: Record<string, string> = {
  carrier: 'carrier', left: 'left side', right: 'right side', 'required-left': 'required condition (not supplied)', 'required-right': 'required condition (not supplied)',
  'alternative-left': 'alternative (no case assumed)', 'alternative-right': 'alternative (no case assumed)', 'equivalent-left': 'equivalent side', 'equivalent-right': 'equivalent side',
  negated: 'negated condition (no hypothesis inserted)', predicate: 'predicate', domain: 'binder domain', body: 'body',
};
const outcomeTitles: Record<ReceiptOutcome, string> = { accepted: 'accepted', rejected: 'rejected', unknown: 'unknown', missing: 'not recorded' };

/** Pure label functions; tests and the theory oracle target this one vocabulary. */
export const provenanceWording = Object.freeze({
  /** Visible labels always carry the exact 8-character capture id beside the ordinal. */
  recordTitle(history: DecompositionHistory, captureId: string): string {
    const id = captureId.slice(0, 8);
    if (captureId === history.occurrence.captureId) return `the original selected occurrence (${id})`;
    if (history.seed && captureId === history.seed.record.captureId) return `the first exposure (${id})`;
    const index = history.attempts.findIndex(entry => entry.record.captureId === captureId);
    return index >= 0 ? `attempt ${index + 1} (${id})` : `record ${id}`;
  },
  introTitle: 'Each entry names where it first appeared, following the recorded parent links, and separately which recorded outcomes of the selected record concern it. Any logical-root reading in the term view above comes from the last inspection of the displayed occurrence that reads a logical form. Nothing is re-checked, reduced or assumed here.',
  /** Which outcomes the formation statuses are read from, and what an occurrence's own line lists. */
  evidenceTitle: 'Formation is read only from accepted logical-root and type-component outcomes, listed under the occurrence; accepted outcomes that disagree give no reading. An inferred type of literal Sort zero reads as a proposition, a literal successor level as a type above Prop, any other level as a sort of general level, and any other inferred type as an ordinary term. Binder-domain formation is a separate field, read from logical-domain outcomes. An occurrence\u2019s own line lists the checks the selected record made to produce it, which include its typing check; the relation that produced it lists the same recorded outcomes. For an occurrence produced by a type-component step these are also listed as its type-component formation outcome: the same recorded outcomes, not a second check. Checks made by selection, focus, projection or exposure are not read as formation under the current rule.',
  /** An occurrence's own line lists the checks the record read from made to produce the occurrence, which for an inherited
   * occurrence are that record's replay and not the checks of the record it first appeared in. When a formation entry names the
   * same span, the line says so: one set of recorded outcomes in two places, never a second check. The comparison is between
   * two spans the module supplies; no receipt is read here. */
  occurrenceReceiptTitle(history: DecompositionHistory, occurrence: { receipts: ReceiptSpan; formations: { receipts: ReceiptSpan }[] }): string {
    const span = occurrence.receipts, title = provenanceWording.receiptTitle(history, span);
    if (span.count === 0) return title;
    const listed = occurrence.formations.some(formation => formation.receipts.captureId === span.captureId && formation.receipts.start === span.start && formation.receipts.count === span.count);
    return `${title} · the checks that record made to produce this occurrence${listed ? ', also listed below as a formation outcome: the same recorded outcomes, not a second check' : ''}`;
  },
  originTitle(history: DecompositionHistory, origin: OccurrenceOrigin): string {
    if (origin.kind === 'step') return `${provenanceWording.recordTitle(history, origin.captureId)}, step ${origin.stepIndex + 1}`;
    return provenanceWording.recordTitle(history, origin.captureId);
  },
  receiptTitle(history: DecompositionHistory, span: ReceiptSpan): string {
    const where = provenanceWording.recordTitle(history, span.captureId);
    if (span.count === 0) return `No kernel outcomes recorded by ${where} for this entry`;
    if (span.count === 1) return `Outcome ${span.start + 1} recorded by ${where}`;
    return `Outcomes ${span.start + 1}–${span.start + span.count} recorded by ${where}`;
  },
  statusTitle(status: EvidenceStatus): string {
    if (status.status === 'established') return `established as ${kindTitles[status.kind]}`;
    return status.status === 'conflicting' ? 'conflicting: accepted outcomes disagree, so none is read' : 'not established';
  },
  kindTitle: (kind: FormationKind): string => kindTitles[kind],
  outcomeTitle: (outcome: ReceiptOutcome): string => outcomeTitles[outcome],
  formTitle: (form: LogicalForm | null): string => form === null ? 'no logical form is read' : formTitles[form],
  operandTitle: (operand: string): string => operandTitles[operand] ?? operand,
  /** Wording of a relation without its Lean identifier; identifiers render separately as code. */
  relationLabel(relation: ProvenanceRelation): string {
    switch (relation.kind) {
      case 'containment': return `Contained part · ${continuationPathTitle(relation.path)}`;
      case 'type-of': return 'Type of the previous occurrence';
      case 'conversion': return `Definition-head conversion of ${relation.target}`;
      case 'projection-of': return `Projected field ${relation.index + 1}`;
    }
  },
  relationName: (relation: ProvenanceRelation): string | null =>
    relation.kind === 'conversion' ? safeName(relation.head) : relation.kind === 'projection-of' ? safeName(relation.field) : null,
  relationTitle(relation: ProvenanceRelation): string {
    const identifier = provenanceWording.relationName(relation);
    return identifier === null ? provenanceWording.relationLabel(relation) : `${provenanceWording.relationLabel(relation)} · ${identifier}`;
  },
  roleTitle(role: ContainmentRole): string {
    const outer = `${formTitles[role.form]} · ${provenanceWording.operandTitle(role.operand)}`;
    return role.remainder.length ? `${outer} · then ${continuationPathTitle(role.remainder)}, read as ordinary containment` : outer;
  },
  /** Generic universal wording applies to the binder a forall body operand enters when no binder role is read. */
  isBodyBinder: (binder: EnteredBinder, role: ContainmentRole | null): boolean =>
    role !== null && (role.form === 'forall' || role.form === 'implies') && role.operand === 'body' && binder.position === role.operandPath.length - 1,
  /** Wording around the binder's Lean identifier, which renders separately as code. */
  binderParts(binder: EnteredBinder, role: ContainmentRole | null): [string, string] {
    if (binder.role === 'candidate') return ['Candidate ', ' within the existential statement, read as allowed dependence only'];
    if (binder.role === 'proof') return ['Assuming ', ', a proof binder'];
    if (binder.role === 'universal') return ['For every ', ''];
    if (provenanceWording.isBodyBinder(binder, role)) return ['For all ', ', without a binder classification'];
    return ['Bound name ', ' entered here; lexical only, no logical role'];
  },
  binderTitle(binder: EnteredBinder, role: ContainmentRole | null): string {
    const [before, after] = provenanceWording.binderParts(binder, role);
    return `${before}${recordedName(binder.name, 'binder')}${after}`;
  },
  formationTitle(formation: OccurrenceFormation): string {
    return `${formation.source === 'logical' ? 'Logical root' : 'Type-component'} outcome ${outcomeTitles[formation.outcome]} · ${kindTitles[formation.kind]}`;
  },
  /** Several accepted outcomes that agree are receipts of one judgement in one capture, never independent confirmation. */
  agreementTitle(occurrence: { formation: EvidenceStatus; formations: OccurrenceFormation[] }): string | null {
    const accepted = occurrence.formations.filter(formation => formation.outcome === 'accepted').length;
    return occurrence.formation.status === 'established' && accepted > 1
      ? `These ${accepted} accepted outcomes are receipts of one checked judgement in this capture, not independent confirmation.` : null;
  },
  /** Syntax of a candidate when no logical form is read: the shape token forall, or the head constant of a standard shape as an
   * identifier. Never a logical reading title: a forall candidate can be an ordinary function type. An unexpanded shape records
   * no candidate at all (any term that is neither a forall nor a recognized standard application), so none is named. */
  candidateParts(candidate: LogicalForm): [string, string | null] | null {
    if (candidate === 'unexpanded') return null;
    const head = candidateHeads[candidate];
    return head !== undefined ? ['head constant ', head] : ['forall', null];
  },
  /** Wording around a Lean constant, which renders separately as code: a candidate's head constant when no form is read, or
   * the constant of a read constant proposition. */
  inspectionParts(inspection: OccurrenceInspection): [string, string | null, string] {
    const domain = inspection.domain ? ` · binder domain ${kindTitles[inspection.domain.formation]}, outcome ${outcomeTitles[inspection.domain.outcome]}` : '';
    const start = `Logical inspection · shape ${inspection.shape} · root outcome ${outcomeTitles[inspection.rootOutcome]} · `, end = `${domain}${inspection.proofBinder ? ' · proof binder, read from the occurrence’s formation and binder-domain formation' : ''}`;
    if (inspection.form === null) {
      const candidate = provenanceWording.candidateParts(inspection.candidate);
      return candidate === null ? [`${start}no logical form is read${end}`, null, '']
        : [`${start}no logical form is read (syntactic candidate ${candidate[0]}`, candidate[1], `, not a reading)${end}`];
    }
    const title = formTitles[inspection.form], attribution = inspection.rootOutcome === 'accepted' ? '' : ', read from the occurrence formation, not from this root outcome';
    // The title of a read constant proposition contains its Lean constant; that word goes to the code slot. The one title table stays the only source.
    const constant = inspection.form === 'true' || inspection.form === 'false' ? candidateHeads[inspection.form] ?? null : null, at = constant === null ? -1 : title.indexOf(constant);
    return constant === null || at < 0 ? [`${start}${title}${attribution}${end}`, null, '']
      : [`${start}${title.slice(0, at)}`, constant, `${title.slice(at + constant.length)}${attribution}${end}`];
  },
  inspectionTitle(inspection: OccurrenceInspection): string {
    const [before, head, after] = provenanceWording.inspectionParts(inspection);
    return `${before}${head ?? ''}${after}`;
  },
  excludedTitle(history: DecompositionHistory, excluded: NonNullable<OccurrenceProvenance['excluded']>): string {
    const steps = excluded.stepIndices.map(index => index + 1).join(', '), single = excluded.stepIndices.length === 1;
    return `${single ? 'Step' : 'Steps'} ${steps} of ${provenanceWording.recordTitle(history, excluded.captureId)} ${single ? 'is' : 'are'} outside this prefix and not read.`;
  },
  routeTitle(provenance: OccurrenceProvenance): string {
    return provenance.prefix.route === 'attempt' ? `through step ${provenance.prefix.parentStepIndex + 1} of this attempt`
      : provenance.prefix.route === 'seed' ? 'through the first exposure' : 'of the original selected occurrence';
  },
  authorityTitle: (currentOrigin: boolean): string => currentOrigin
    ? 'Read from the validated history of this capture. It lists retained records only and adds no kernel outcome, logical claim or reduction.'
    : 'Read from a saved history whose origin is unconfirmed. Outcomes are as recorded and nothing is re-checked here; no action is available.',
});

function Exact({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={event => setOpen(event.currentTarget.open)}><summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}
function originAttributes(origin: OccurrenceOrigin, receipts: ReceiptSpan) {
  return { 'data-origin-kind': origin.kind, 'data-origin-capture': origin.captureId, 'data-origin-step': origin.kind === 'step' ? origin.stepIndex : undefined,
    'data-receipt-capture': receipts.captureId, 'data-receipt-start': receipts.start, 'data-receipt-count': receipts.count };
}

/** The caller supplies a unique panel-instance prefix shared with its passive references. */
export function provenanceOccurrenceAnchor(prefix: string, occurrence: Pick<ProvenanceOccurrence, 'index' | 'origin'>): string {
  const { origin } = occurrence;
  return `${prefix}-${origin.kind}-${origin.captureId}${origin.kind === 'step' ? `-${origin.stepIndex}` : ''}-occurrence-${occurrence.index}`;
}

/** Pure render model: a frozen provenance value (or refusal) to markup. Exported as the injection seam for controls. */
export function ProvenancePanel({ history, derived, currentOrigin, occurrenceAnchorPrefix }: { history?: DecompositionHistory; derived?: DerivedProvenance; currentOrigin: boolean; occurrenceAnchorPrefix?: string }) {
  if (!history || !derived) return <p className="snapshot-context" data-provenance-absent="">Ordered provenance is shown only for the validated history retained by the editor host; none is retained for this record.</p>;
  if (derived.refusal !== undefined) return <section className="source-provenance" aria-label="Ordered occurrence provenance" data-provenance-refused="">
    <h4>Ordered provenance</h4>
    <p className="snapshot-unavailable" role="status">Provenance unavailable for this step: {derived.refusal}. The step outcomes above remain available; no other prefix is shown.</p>
  </section>;
  const provenance = derived.value, w = provenanceWording;
  return <section className="source-provenance" aria-label="Ordered occurrence provenance" data-provenance-route={provenance.prefix.route}
    data-provenance-prefix={provenance.prefix.previousCaptureId} data-provenance-step={provenance.prefix.parentStepIndex}>
    <h4>Ordered provenance · {w.routeTitle(provenance)}</h4>
    <p>{w.authorityTitle(currentOrigin)}</p>
    <p className="snapshot-context">{w.introTitle}</p>
    <p className="snapshot-context" data-provenance-evidence="">{w.evidenceTitle}</p>
    <ol className="snapshot-checks" aria-label="Occurrences and relations in prefix order">{provenance.occurrences.map(occurrence => <Fragment key={occurrence.index}>
      {provenance.edges.filter(edge => edge.to === occurrence.index).map(edge => {
        const relation = edge.relation, role = relation.kind === 'containment' ? relation.role : null, binders = relation.kind === 'containment' ? relation.binders : [];
        return <li key={`${edge.from}-${edge.to}`} data-provenance-edge={`${edge.from}-${edge.to}`} data-relation-kind={relation.kind} {...originAttributes(edge.origin, edge.receipts)}>
          <strong>{w.relationLabel(relation)}{w.relationName(relation) !== null && <> · <code>{w.relationName(relation)}</code></>}</strong>
          <p>First appeared in {w.originTitle(history, edge.origin)}</p>
          <p>{w.receiptTitle(history, edge.receipts)}</p>
          {relation.kind === 'containment' && <>
            <p data-containment-role={role ? role.operand : 'none'}>{role ? `Role: ${w.roleTitle(role)}` : 'Role: none read; ordinary containment'}</p>
            {binders.length > 0 && <ol aria-label="Binders entered">{binders.map(binder => <li key={binder.position} data-binder-position={binder.position} data-binder-role={binder.role ?? 'none'}>{w.binderParts(binder, role)[0]}<code>{recordedName(binder.name, 'binder')}</code>{w.binderParts(binder, role)[1]} · constructor-path position {binder.position + 1}</li>)}</ol>}
          </>}
        </li>;
      })}
      <li data-provenance-occurrence={occurrence.index} id={occurrenceAnchorPrefix ? provenanceOccurrenceAnchor(occurrenceAnchorPrefix, occurrence) : undefined}
        tabIndex={occurrenceAnchorPrefix ? -1 : undefined} {...originAttributes(occurrence.origin, occurrence.receipts)}>
        <strong>Occurrence {occurrence.index + 1}</strong>
        <p>First appeared in {w.originTitle(history, occurrence.origin)}</p>
        <p data-provenance-own-outcomes="">{w.occurrenceReceiptTitle(history, occurrence)}</p>
        <p data-formation-status={occurrence.formation.status} data-domain-status={occurrence.domain.status}>Formation: {w.statusTitle(occurrence.formation)} · Binder-domain formation: {w.statusTitle(occurrence.domain)}</p>
        {occurrence.formations.length > 0 && <ol aria-label="Formation outcomes">{occurrence.formations.map((formation, i) => <li key={i} data-formation-outcome={formation.outcome}>{w.formationTitle(formation)} · first appeared in {w.originTitle(history, formation.origin)} · {w.receiptTitle(history, formation.receipts).toLowerCase()}</li>)}</ol>}
        {w.agreementTitle(occurrence) !== null && <p data-formation-agreement="">{w.agreementTitle(occurrence)}</p>}
        {occurrence.inspections.length > 0 && <ol aria-label="Logical inspections">{occurrence.inspections.map((inspection, i) => <li key={i} data-inspection-form={inspection.form ?? 'none'}>{w.inspectionParts(inspection)[0]}{w.inspectionParts(inspection)[1] !== null && <code>{w.inspectionParts(inspection)[1]}</code>}{w.inspectionParts(inspection)[2]} · first appeared in {w.originTitle(history, inspection.origin)} · {w.receiptTitle(history, inspection.receipts).toLowerCase()}</li>)}</ol>}
        {occurrence.catalogues.length > 0 && <ol aria-label="Field catalogues">{occurrence.catalogues.map((catalogue, i) => <li key={i} data-provenance-catalogue={i} {...originAttributes(catalogue.origin, catalogue.receipts)}>Direct fields listed: {catalogue.fields}{catalogue.omittedFields ? `, ${catalogue.omittedFields} omitted` : ''} · first appeared in {w.originTitle(history, catalogue.origin)} · {w.receiptTitle(history, catalogue.receipts).toLowerCase()}</li>)}</ol>}
        <Exact title="Exact context, term and type of this occurrence" value={occurrence.pair}/>
      </li>
    </Fragment>)}</ol>
    {provenance.excluded && <p className="snapshot-context" data-provenance-excluded={provenance.excluded.stepIndices.join(',')}>{w.excludedTitle(history, provenance.excluded)}</p>}
  </section>;
}

/** Convenience wrapper deriving for one (record, step); the reader's attempt view derives once and passes the value down. */
export function SourceProvenanceReading({ history, previousCaptureId, parentStepIndex, currentOrigin }: {
  history?: DecompositionHistory; previousCaptureId: string; parentStepIndex: number; currentOrigin: boolean;
}) {
  return <ProvenancePanel history={history} derived={deriveProvenance(history, previousCaptureId, parentStepIndex)} currentOrigin={currentOrigin}/>;
}
