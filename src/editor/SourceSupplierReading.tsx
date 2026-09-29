/** Presentation of the accepted supplier model. No source term, saved record or
 * kernel receipt is interpreted here; the panel labels the model's fields. */
import { Fragment, useState } from 'react';
import { StructuralFieldValue } from '../packets/StructuralReading';
import { nameText } from '../packets/syntax';
import type { DecompositionHistory } from './source-decomposition';
import type { EvidenceStatus } from './source-provenance';
import { supplierReading, type SupplierReading, type TypeOfLink, type Frame, type Part, type HomeEntry } from './source-supplier';
import { provenanceWording as p, provenanceOccurrenceAnchor } from './SourceProvenanceReading';
import { recordedName } from '../packets/recorded-name';
import { continuationPathTitle } from './ContinuationChoice';
import { counted } from '../core/counted';

export type DerivedSupplier = { value: SupplierReading; refusal?: undefined } | { value?: undefined; refusal: string };
export function deriveSupplier(history: DecompositionHistory | undefined, previousCaptureId: string, parentStepIndex: number): DerivedSupplier | undefined {
  if (!history) return undefined;
  try { return { value: supplierReading(history, previousCaptureId, parentStepIndex) }; }
  catch (error) { return { refusal: error instanceof Error ? error.message : String(error) }; }
}
/** Join only the module's indices; no raw term or provenance walk is needed. */
export function joinPartsToLinks(reading: SupplierReading): { part: Part; link: TypeOfLink | null }[] {
  return reading.parts.map(part => ({ part, link: reading.links.find(link => link.to === part.root) ?? null }));
}
const reference = (receipt: { captureId: string; index: number }) => `${receipt.captureId}#${receipt.index}`;
const restsOn = (link: TypeOfLink) => link.formation.judgements.filter(group => group.established).flatMap(group => group.receipts.filter(receipt => receipt.outcome === 'accepted'));

export const supplierWording = Object.freeze({
  supplyPhrase: 'is read as supplying a proof of',
  environment: 'Kernel acceptance is a typing outcome in the captured environment, not a statement that the proposition is true.',
  usage: 'Whether the term uses each listed entry is not read here.',
  inferredStatement: 'The statement is the type inferred for this term at the captured universe levels, not read from a source ascription or an enclosing application.',
  nothing: 'Nothing is read about supply.',
  noTypeOf: 'This prefix contains no type-of step, so no supply reading is made.',
  noSupply: 'The recorded type-of links give no supply reading in this prefix.',
  linkTitle(link: TypeOfLink, formation: EvidenceStatus): string {
    if (link.status === 'supplier') return `Relative to the captured environment, including its axioms, and the ${counted(link.conditions.home.length, 'entry', 'entries')} and ${counted(link.conditions.frames.length, 'frame')} listed, occurrence ${link.from + 1} ${supplierWording.supplyPhrase} the statement at occurrence ${link.to + 1}.`;
    return `Occurrence ${link.from + 1} has a recorded typing outcome ${p.outcomeTitle(link.typing.outcome)}. Formation of its type at occurrence ${link.to + 1}: ${p.statusTitle(formation)}. ${supplierWording.nothing}`;
  },
  homeTitle(entry: HomeEntry): string {
    const origin = entry.origin;
    if (origin.kind === 'context') return `${origin.declarationKind === 'auxDecl' ? 'Auxiliary entry' : 'Context entry'}, recorded kind ${origin.declarationKind ?? 'not recorded'}`;
    return origin.kind === 'selection' ? 'Entry entered by the original selection' : `Entry entered at relation ${origin.edge + 1}, binder ${origin.binder + 1}`;
  },
  frameTitle(frame: Frame): string {
    if (frame.kind === 'containment') return `Relation ${frame.edge + 1}: ${continuationPathTitle(frame.path)} · ${frame.role ? p.roleTitle(frame.role) : 'ordinary containment; no logical role read'}`;
    return `Relation ${frame.edge + 1}: ${frame.kind === 'type-of' ? 'type-of' : frame.kind === 'projection-of' ? 'projection' : 'conversion'}`;
  },
  partTitle(part: Part, link: TypeOfLink | null): string {
    if (part.tier === 'within-supplied-law') return `Occurrence ${part.occurrence + 1} is a position inside the statement at occurrence ${part.root + 1}. Nothing is read about this part by itself.`;
    if (part.tier === 'within-statement') return `Occurrence ${part.occurrence + 1} is a position inside the statement at occurrence ${part.root + 1}. This prefix relates no term to that statement by a type-of step, so nothing is read about supply.`;
    if (part.tier === 'within-annotation') return `Occurrence ${part.occurrence + 1} is a position inside the ${link?.status === 'value-of-type' ? 'type' : 'type annotation'} at occurrence ${part.root + 1}. Nothing is read about supply for this part by itself.`;
    return `Occurrence ${part.occurrence + 1} is a position inside the expression at occurrence ${part.root + 1}. Nothing is read about supply for this part by itself.`;
  },
});
function Exact({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={event => setOpen(event.currentTarget.open)}><summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}
function Frames({ frames }: { frames: Frame[] }) {
  return <ol aria-label="Ordered frames">{frames.map((frame, index) => <li key={index} data-frame-index={index} data-frame-kind={frame.kind} data-frame-edge={frame.edge}
    data-frame-path={frame.kind === 'containment' ? JSON.stringify(frame.path) : undefined}>{supplierWording.frameTitle(frame)}</li>)}</ol>;
}
function Conditions({ link }: { link: TypeOfLink }) {
  const { home, binders, frames } = link.conditions;
  const binderFrames = frames.flatMap(frame => frame.kind === 'containment' ? frame.binders.map(() => frame) : []);
  return <div data-supplier-conditions="" data-home-count={home.length} data-binder-count={binders.length} data-frame-count={frames.length}>
    <p>Conditions: {counted(home.length, 'ordered entry', 'ordered entries')}, {counted(binders.length, 'entered binder')} and {counted(frames.length, 'frame')}.</p>
    <ol aria-label="Full ordered context" data-supplier-home="">{home.map(entry => <li key={entry.position} data-home-position={entry.position} data-home-kind={entry.kind}
      data-home-origin={entry.origin.kind} data-home-declaration={entry.origin.kind === 'context' ? entry.origin.declaration : undefined}
      data-home-declaration-kind={entry.origin.kind === 'context' ? entry.origin.declarationKind ?? 'none' : undefined}
      data-home-edge={entry.origin.kind === 'entered' ? entry.origin.edge : undefined} data-home-binder={entry.origin.kind === 'entered' ? entry.origin.binder : undefined}
      data-home-role={entry.origin.kind === 'entered' ? entry.origin.role ?? 'none' : undefined}>
      Context position {entry.position + 1} · {supplierWording.homeTitle(entry)}{entry.kind === 'let' && ' · local definition'} · <code>{recordedName(entry.name, 'context entry')}</code>
    </li>)}</ol>
    <ol aria-label="Entered binder readings">{binders.map((binder, index) => { const parts = p.binderParts(binder, binderFrames[index]?.role ?? null); return <li key={index} data-supplier-binder={index} data-binder-position={binder.position} data-binder-role={binder.role ?? 'none'}>
      {parts[0]}<code>{recordedName(binder.name, 'binder')}</code>{parts[1]}{binderFrames[index] && <> · relation {binderFrames[index].edge + 1}</>} · constructor-path position {binder.position + 1}
    </li>; })}</ol>
    <Frames frames={frames}/>
    <Exact title="Exact condition entries, names and frames" value={link.conditions}/>
  </div>;
}

/** Identify an endpoint by the model's occurrence and incoming relation, never by its typing receipt or a step ordinal. */
function OccurrenceReference({ history, reading, index, anchorPrefix }: { history: DecompositionHistory; reading: SupplierReading; index: number; anchorPrefix?: string }) {
  const occurrence = reading.provenance.occurrences[index];
  const relationIndex = reading.provenance.edges.findIndex(edge => edge.to === occurrence.index);
  const incoming = reading.provenance.edges[relationIndex], relation = incoming?.relation;
  const anchor = anchorPrefix ? provenanceOccurrenceAnchor(anchorPrefix, occurrence) : undefined;
  return <p data-supplier-occurrence-reference={occurrence.index}>
    {anchor ? <a href={`#${anchor}`} onClick={event => {
      event.preventDefault();
      const target = event.currentTarget.ownerDocument.getElementById(anchor);
      if (target) { target.focus({ preventScroll: true }); target.scrollIntoView({ block: 'start' }); }
    }}>Occurrence {occurrence.index + 1}</a> : <>Occurrence {occurrence.index + 1}</>}
    {' · First appeared in '}{p.originTitle(history, occurrence.origin)}
    {relation && <> · Relation {relationIndex + 1} from occurrence {incoming.from + 1} · {p.relationLabel(relation)}{p.relationName(relation) !== null && <> · <code>{p.relationName(relation)}</code></>}</>}
  </p>;
}

export function SupplierPanel({ history, derived, currentOrigin, occurrenceAnchorPrefix }: { history?: DecompositionHistory; derived?: DerivedSupplier; currentOrigin: boolean; occurrenceAnchorPrefix?: string }) {
  if (!history || !derived) return <p className="snapshot-context" data-supplier-state="no-history">Supply reading is shown only for the validated history retained by the editor host; none is retained for this record.</p>;
  if (derived.refusal !== undefined) return <section className="source-supplier" aria-label="Supply reading" data-supplier-state="refused"><h4>Supply reading</h4>
    <p className="snapshot-unavailable" role="status">Supply reading unavailable for this step: {derived.refusal}. The step outcomes and ordered provenance remain available; no other prefix is shown.</p></section>;
  const reading = derived.value, provenance = reading.provenance, w = supplierWording;
  const joined = joinPartsToLinks(reading), roots = [...new Set(joined.map(item => item.part.root))];
  const receiptTitle = (receipt: { captureId: string; index: number; outcome: 'accepted' | 'rejected' | 'unknown' }) => `Outcome ${receipt.index + 1} recorded by ${p.recordTitle(history, receipt.captureId)}: ${p.outcomeTitle(receipt.outcome)}`;
  return <section className="source-supplier" aria-label="Supply reading" data-supplier-state={!reading.links.length ? 'no-type-of' : reading.links.some(link => link.status === 'supplier') ? 'reading' : 'no-supply'}
    data-supplier-route={provenance.prefix.route} data-supplier-prefix={provenance.prefix.previousCaptureId} data-supplier-step={provenance.prefix.parentStepIndex}>
    <h4>Supply reading · {p.routeTitle(provenance)}</h4>
    <p>{p.authorityTitle(currentOrigin)}</p><p data-supplier-environment="">{w.environment}</p>
    {!reading.links.length ? <p>{w.noTypeOf}</p> : !reading.links.some(link => link.status === 'supplier') && <p>{w.noSupply}</p>}
    <ol className="snapshot-checks" aria-label="Type-of readings">{reading.links.map(link => <li key={link.edge} data-supplier-link={link.edge} data-supplier-status={link.status}
      data-link-from={link.from} data-link-to={link.to} data-typing-capture={link.typing.captureId} data-typing-index={link.typing.index} data-typing-outcome={link.typing.outcome}
      data-supplier-rests-on={link.status === 'supplier' ? restsOn(link).map(reference).join(',') : ''}>
      <p data-supplier-sentence="">{w.linkTitle(link, provenance.occurrences[link.to].formation)}</p>
      <p data-supplier-axioms={link.typing.audit.tag}>Recorded axioms of the typing declaration: {link.typing.audit.tag === 'available'
        ? link.typing.audit.axioms.length ? link.typing.audit.axioms.map((axiom, index) => <Fragment key={index}>{index > 0 ? ', ' : ''}<code>{nameText(axiom as never)}</code></Fragment>) : 'none recorded'
        : `unavailable: ${link.typing.audit.reason}`}.</p>
      <OccurrenceReference history={history} reading={reading} index={link.from} anchorPrefix={occurrenceAnchorPrefix}/>
      <OccurrenceReference history={history} reading={reading} index={link.to} anchorPrefix={occurrenceAnchorPrefix}/>
      <p>{receiptTitle(link.typing)} · typing of occurrence {link.from + 1}{link.typing.alsoFormation ? '; one receipt also serving formation' : ''}.</p>
      <p>Formation of occurrence {link.to + 1}: {p.statusTitle(provenance.occurrences[link.to].formation)}.</p>
      {link.status === 'supplier' && <><p data-supplier-usage="">{w.usage}</p><p data-supplier-inferred="">{w.inferredStatement}</p>
        <p>Formation rests on {restsOn(link).map(receipt => receiptTitle(receipt)).join('; ')}.</p></>}
      <Conditions link={link}/>
      <ol aria-label="Formation judgement groups">{link.formation.judgements.map((group, index) => <li key={index} data-judgement={index} data-established={String(group.established)}>
        <p>Judgement group {index + 1}{group.established ? ' · formation read from its accepted outcomes' : ''}.</p>
        {group.receipts.length > 1 && <p>These receipts concern one checked judgement in this capture, not independent confirmation. Each keeps its recorded outcome.</p>}
        <ol>{group.receipts.map(receipt => <li key={reference(receipt)} data-formation-capture={receipt.captureId} data-formation-index={receipt.index} data-formation-outcome={receipt.outcome} data-formation-also-typing={String(receipt.alsoTyping)}>
          {receiptTitle(receipt)} · {receipt.source === 'logical' ? 'logical root' : 'type component'}{receipt.alsoTyping ? ' · the same receipt also serves the target’s typing, one receipt in two roles' : ''}
        </li>)}</ol><Exact title="Exact submitted inferred type for this judgement" value={group.inferredType}/>
      </li>)}</ol>
    </li>)}</ol>
    <h5>Typing outcomes by occurrence</h5><ol aria-label="Occurrence typing outcomes">{reading.occurrences.map(item => <li key={item.index} data-supplier-typing={item.index} data-typing-capture={item.typing.captureId} data-typing-index={item.typing.index} data-typing-outcome={item.typing.outcome}>
      Occurrence {item.index + 1} · {receiptTitle(item.typing)}{item.typing.alsoFormation ? ' · one receipt also serving formation' : ''}
    </li>)}</ol>
    <h5>Contained positions</h5>{reading.parts.length === 0 && <p>No contained positions are recorded in this prefix.</p>}{roots.map(root => <div key={root} data-part-group={root}><p>Root occurrence {root + 1}</p><ol>{joined.filter(item => item.part.root === root).map(({ part, link }) => <li key={part.occurrence}
      data-supplier-part={part.occurrence} data-part-root={part.root} data-part-tier={part.tier} data-part-link={link?.edge ?? 'none'} data-part-supplier={part.supplier ?? 'none'} data-part-path={JSON.stringify(part.path)}>
      <p>{w.partTitle(part, link)}</p><p>Position: {continuationPathTitle(part.path)}</p><Frames frames={part.frames}/>
    </li>)}</ol></div>)}
    {provenance.excluded && <p className="snapshot-context" data-supplier-excluded={provenance.excluded.stepIndices.join(',')}>{p.excludedTitle(history, provenance.excluded)}</p>}
  </section>;
}
