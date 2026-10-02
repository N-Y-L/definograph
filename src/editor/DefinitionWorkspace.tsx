import { useMemo, useState } from 'react';
import { definitionOccurrences, scopedExpressionLabel, type DefinitionOccurrence } from './definition-occurrences';
import type { DefinitionWorkspaceState } from './definition-workspace';
import { decompositionReading } from './source-decomposition-reading';
import { PositionalReadingPane } from './SourceOccurrenceGuidedReading';
import { operationOutcomeLabel } from './source-outcome-labels';
import type { HeadExposureCandidate } from './source-head-exposure';
import { nameText } from '../packets/syntax';
import { counted } from '../core/counted';
import { SourceResultPresentation } from './SourceResultPresentation';
import './definition-workspace.css';

export function DefinitionWorkspace({ state, onInspect, onReturn, onDetails }: {
  state: DefinitionWorkspaceState;
  onInspect: (occurrence: DefinitionOccurrence) => void;
  onReturn: () => void;
  onDetails: () => void;
}) {
  const [filter, setFilter] = useState('');
  const catalogue = useMemo(() => state.catalogue && definitionOccurrences(state.catalogue, {filter}), [state.catalogue,filter]);
  const search = filter.trim().toLocaleLowerCase();
  const candidates = catalogue?.status === 'available' ? [...catalogue.occurrences].sort((a,b) =>
    Number(b.headName.toLocaleLowerCase() === search) - Number(a.headName.toLocaleLowerCase() === search)) : [];
  const record = state.result, index = state.resultStep;
  const step = record?.checking.status === 'captured' && index !== undefined ? record.checking.steps[index] : undefined;
  const output = step?.output.status === 'candidate' ? step.output : undefined;
  const outcomes = record?.checking.status === 'captured' && step ? record.checking.checks.slice(step.receiptStart, step.receiptStart + step.receiptCount) : [];
  const accepted = outcomes.length > 0 && outcomes.every(check => check.outcome.tag === 'accepted');
  const resultReading = useMemo(() => { try { return record && index !== undefined ? decompositionReading(record, index, 'term', null) : undefined; } catch { return undefined; } }, [record, index]);
  const resultLabel = useMemo(() => { if(!output)return undefined;try{return {text:scopedExpressionLabel(output.result)};}catch{return {unavailable:'The readable expression exceeds the display limit. Its exact result and scope are retained below.'};} }, [output]);
  return <aside className="definition-workspace" aria-label="Definition workspace">
    <header><div><span className="eyebrow">DEFINITION INSPECTION</span><h2>Keep the clause in view</h2></div><button type="button" className="quiet-button" disabled={['preparing','focusing','exposing'].includes(state.phase)} onClick={onReturn}>Return to reading</button></header>
    <section className="definition-original" aria-label="Original reading clause"><h3>Original clause</h3><code>{state.anchor.clause}</code><p>Its ordered context remains in the reading. Inspecting an expression does not assert it separately.</p></section>
    <p role="status" aria-live="polite">{state.message}</p>
    {state.phase === 'choosing' && <>
      <p>Applications come from the whole selected statement. Each occurrence retains its own arguments and scope.</p>
      <label className="field-label">Find an application<input type="search" value={filter} onChange={event => setFilter(event.target.value)} placeholder="Definition or expression"/></label>
      <ul className="definition-candidates">{candidates.map(item => <li key={item.id}><button type="button" onClick={() => onInspect(item)}><strong>{item.headName}</strong><code>{item.label}</code>{item.labelUnavailable&&<small>Readable label unavailable: {item.labelUnavailable}</small>}<small>In scope: {item.scope.map(entry => entry.label).join(', ') || 'no local binders'}</small><span>Inspect this occurrence →</span></button></li>)}</ul>
      {!candidates.length && <p>No matching application is available in the searched positions.</p>}
      {catalogue?.status === 'available' && catalogue.omittedCount > 0 && <p>{counted(catalogue.omittedCount, 'application position')} {catalogue.omittedCount === 1 ? 'is' : 'are'} outside the displayed or searched bounds. The complete source remains available in Source data.</p>}
      <p className="small muted">A listed head may be opaque or unavailable. Inspection reports the actual outcome.</p>
    </>}
    {state.chosen && <section className="definition-comparison"><h3>Chosen application</h3><code>{state.chosen.label}</code>{state.chosen.labelUnavailable&&<p>Readable label unavailable: {state.chosen.labelUnavailable}. The exact chosen source remains in the operation details.</p>}
      <details><summary>Exact surrounding scope ({counted(state.chosen.scope.length, 'entry', 'entries')}, oldest first)</summary><ol>{state.chosen.scope.map(entry => <li key={entry.position}>{entry.label}</li>)}</ol><p>These are lexical binders. Other conjuncts, such as a required positivity condition, remain in the original logical frame.</p></details>
    </section>}
    {state.phase === 'complete' && output && <section className="definition-comparison" aria-label="Inspected definition result">
      <h3>Recorded result of inspecting {'definition' in output ? nameText((output as HeadExposureCandidate).definition.name) : 'the definition'}</h3>
      <SourceResultPresentation record={record!} stepIndex={index!} presentation={state.resultPresentation}/>
      <p>This recorded definition result retains the application’s surrounding scope. Binders introduced inside it remain local.</p>
      <p>{accepted?'All recorded checks for this exposure were accepted.':'Not all checks for this candidate were accepted. Read the individual outcomes before relying on it.'}</p><ul aria-label="Definition check outcomes">{outcomes.map((check,index)=><li key={check.id}>{operationOutcomeLabel('expose',check.label,index)}: <strong>{check.outcome.tag}</strong></li>)}</ul>
      <details><summary>Exact result and surrounding scope</summary><code>{resultLabel?.text}</code>{resultLabel?.unavailable&&<p role="status">{resultLabel.unavailable}</p>}<pre>{JSON.stringify(output.result,null,2)}</pre></details>
      <details><summary>Read the result and its context</summary><PositionalReadingPane model={resultReading} title="Inspected definition"/></details>
    </section>}
    <footer><button type="button" className="quiet-button" onClick={onDetails}>Source, operations and check details ↗</button><p className="small muted">The original reading and new inspection records are retained separately. A source or selection change closes this workspace.</p></footer>
  </aside>;
}
