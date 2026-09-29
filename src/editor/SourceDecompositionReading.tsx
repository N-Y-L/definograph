import { useId, useMemo, useState } from 'react';
import { StructuralFieldValue, StructuralReading } from '../packets/StructuralReading';
import { nameText } from '../packets/syntax';
import type { DecompositionHistory, SourceDecomposition, SourceDecompositionBundle, DecompositionOperation } from './source-decomposition';
import { ProvenancePanel, deriveProvenance, guidedLogicalRoot } from './SourceProvenanceReading';
import { SupplierPanel, deriveSupplier } from './SourceSupplierReading';
import { operationOutcomeLabel } from './source-outcome-labels';
import type { LogicalCandidate } from './logical-inspection-replay';
import type { PositionalLogicalRoot } from '../packets/semantic';
import { decompositionReading, decompositionDrawing, decompositionResultPath } from './source-decomposition-reading';
import { recordedContextEntries } from './source-snapshot';
import type { DirectFieldCatalogue, DirectFieldEntry } from './field-inspection-replay';
import type { HeadExposureCandidate } from './source-head-exposure';
import type { SourceOccurrenceStep } from './source-occurrence';
import { PositionalReadingPane } from './SourceOccurrenceGuidedReading';
import { ContinuationChoice, continuationPathTitle } from './ContinuationChoice';
import { OutlineLanding, SourceReaderOutline, outlineDestinations, outlineNamespace, type OutlineAttempt, type OutlineSection } from './SourceReaderOutline';
import { counted } from '../core/counted';

export type ContinueSource = (previousCaptureId: string, parentStepIndex: number, operation: DecompositionOperation) => void;

function Exact({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={event => setOpen(event.currentTarget.open)}><summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}
export function canContinueDecompositionStep(record: SourceDecomposition, index: number): boolean {
  const checking = record.checking;
  return checking.status === 'captured' && checking.action.status === 'completed' && Number.isSafeInteger(index) && index >= 0 && index < 7
    && !!checking.steps[index] && checking.steps.slice(0, index + 1).every(step => step.output.status === 'candidate'
      && step.output.checking.status === 'completed' && (step.replay === 'matched' || step.replay === 'new'));
}
function operationTitle(operation: DecompositionOperation): string {
  switch (operation.kind) {
    case 'expose': return `Expose ${operation.target}`;
    case 'focus': return `Check part · ${continuationPathTitle(operation.path)}`;
    case 'fields': return 'Inspect fields';
    case 'typeComponent': return 'Inspect type';
    case 'logical': return 'Read logical structure';
    case 'project': return `Check field ${operation.index + 1}`;
  }
}

function StepReading({ record, index, logicalRoot, onContinue }: { record: SourceDecomposition; index: number; logicalRoot: PositionalLogicalRoot | null; onContinue?: ContinueSource }) {
  const [target, setTarget] = useState<'term' | 'type'>('term');
  const [view, setView] = useState<'guided' | 'structure'>('guided');
  const [chosenPath, setChosenPath] = useState<SourceOccurrenceStep[] | null>(null);
  const reading = useMemo(() => decompositionReading(record, index, target, logicalRoot), [record, index, target, logicalRoot]);
  const drawing = useMemo(() => decompositionDrawing(record, index), [record, index]);
  if (record.checking.status !== 'captured') return null;
  const step = record.checking.steps[index];
  if (!step) return null;
  const output = step.output, focus = step.operation.kind === 'focus';
  const candidate = output.status === 'candidate' ? output : undefined;
  const exposure = candidate && 'definition' in candidate ? candidate as HeadExposureCandidate : undefined;
  const catalogue = candidate && 'catalogue' in candidate ? candidate.catalogue as DirectFieldCatalogue : undefined;
  const field = candidate && 'field' in candidate ? candidate.field as DirectFieldEntry : undefined;
  const logical = step.operation.kind === 'logical' && candidate ? candidate as LogicalCandidate : undefined;
  const unrecordedLogical = logical ? ['Logical root context', 'Logical root component', ...(logical.domain ? ['Binder-domain context', 'Binder-domain component'] : [])].slice(step.receiptCount) : [];
  const eligible = onContinue && canContinueDecompositionStep(record, index);
  const termTitle = field ? `Field ${nameText(field.name)}` : catalogue ? 'Record owner' : focus ? 'Checked part' : step.operation.kind === 'typeComponent' ? 'Type component' : step.operation.kind === 'logical' ? 'Inspected term' : `Exposed ${step.operation.kind === 'expose' ? step.operation.target : 'term'}`;
  const typeTitle = exposure ? 'Carrier annotation' : catalogue ? 'Owner type' : 'Inferred type';
  const title = target === 'term' ? termTitle : exposure ? 'Carrier annotation of exposed result' : catalogue ? 'Retained owner type' : `Inferred type of ${field ? 'field' : 'checked part'}`;
  const choose = (path: (string | number)[]) => setChosenPath(decompositionResultPath(record, index, path) ?? null);
  return <section className="continuation-step" aria-label={`Continuation step ${index + 1}`} data-decomposition-step={index}>
    <h4>Step {index + 1} · {operationTitle(step.operation)}</h4>
    <p>{step.replay === 'matched' ? 'This step reproduced the earlier expression.' : step.replay === 'new' ? 'This is the newly requested step.' : step.replay === 'mismatch' ? 'This result changed since the step was recorded. Inspect it below; choose an earlier step to continue.' : 'This step did not finish.'}</p>
    {output.status === 'unavailable' && <p className="snapshot-unavailable" role="status">Unavailable during {output.phase}: {output.reason}</p>}
    {candidate && <>
      {candidate.checking.status === 'error' && <p className="snapshot-unavailable" role="status">Checking stopped: {candidate.checking.reason}</p>}
      {catalogue ? <div className="direct-fields">
        <p>Metadata inspection completed. No field typing checks were requested. Choose a field to check its named projection in this owner’s context.</p>
        <p>Record: <code>{nameText(catalogue.structure.name)}</code>.</p>
        <ol className="snapshot-checks" aria-label="Direct fields">{catalogue.fields.map(entry => <li key={entry.index}>
          <strong>{nameText(entry.name)}</strong>{entry.parent && <span> · embedded parent {nameText(entry.parent)}</span>}
          {eligible && <button type="button" className="toolbar-button" onClick={() => onContinue!(record.captureId, index, { kind: 'project', index: entry.index })}>Check field {nameText(entry.name)}</button>}
          <Exact title={`Field metadata: ${nameText(entry.name)}`} value={entry}/>
        </li>)}</ol>
        {!catalogue.fields.length && <p>This record has no direct fields.</p>}
        {catalogue.omittedFields > 0 && <p>{counted(catalogue.omittedFields, 'further direct field')} omitted from this bounded list.</p>}
        <Exact title="Exact structure, constructor and direct-field catalogue" value={catalogue}/>
      </div> : <p>Check results are shown separately below.</p>}
      {field && <><p>The field is a new term in the exact owner’s context. Its inferred type is retained below, together with the check outcomes that completed.</p><Exact title="Named field, primitive projection and inferred carrier sort" value={candidate}/></>}
      <div className="snapshot-tabs" role="tablist" aria-label="Checked part target">{(['term', 'type'] as const).map(item => <button type="button" role="tab" aria-selected={target === item} key={item} onClick={() => setTarget(item)}>{item === 'term' ? termTitle : typeTitle}</button>)}</div>
      {eligible && <div className="head-exposure-action">
        <p>Continue from this pair. Each explicit action recomputes the steps through step {index + 1} from your current source.</p>
        <button type="button" className="toolbar-button" onClick={() => onContinue!(record.captureId, index, { kind: 'expose', target })}>Expose definition head of {target}</button>
        <button type="button" className="toolbar-button" onClick={() => onContinue!(record.captureId, index, { kind: 'fields' })}>Inspect fields</button>
        <button type="button" className="toolbar-button" onClick={() => onContinue!(record.captureId, index, { kind: 'typeComponent' })}>Inspect type of this term</button>
        {target === 'term' ? <button type="button" className="toolbar-button" onClick={() => onContinue!(record.captureId, index, { kind: 'logical' })}>Read logical structure of this term (one layer)</button>
          : <p>To read the logical structure of this type, choose Inspect type first.</p>}
        {target === 'term' && <ContinuationChoice path={chosenPath} onChooseRoot={() => setChosenPath([])} onCheck={path => onContinue!(record.captureId, index, { kind: 'focus', path })}/>}
      </div>}
      {!eligible && onContinue && <p className="snapshot-context">This step cannot be continued. Choose an earlier completed matching step, or Save and Refresh.</p>}
      <div className="snapshot-tabs" role="tablist" aria-label="Continuation presentation">{(['guided', 'structure'] as const).map(item => <button type="button" role="tab" aria-selected={view === item} key={item} onClick={() => setView(item)}>{item === 'guided' ? 'Guided reading' : 'Structure'}</button>)}</div>
      <div role="tabpanel" aria-label={title}>
        {view === 'guided' ? <PositionalReadingPane key={`${record.captureId}:${index}:${target}`} model={reading} title={title} inspectorLabel="Exact continuation source" onSourcePathSelect={target === 'term' && eligible ? choose : undefined}/>
          : drawing?.ok ? <><p>The complete context, expression and type annotation are shown here.</p><StructuralReading drawing={drawing.value} onSourceSelect={eligible ? choose : undefined} positionalRootTitles={{ term: termTitle, type: typeTitle }}
            recordedContext={recordedContextEntries(record.checking.binding)}/></>
            : <p className="snapshot-unavailable">Structure unavailable: {drawing?.error.message ?? 'No drawing was produced.'} Exact data and outcomes remain available.</p>}
      </div>
      {exposure && <><p>Definition: <code>{nameText(exposure.definition.name)}</code>.</p><Exact title="Definition and exposure trace" value={candidate}/></>}
      <Exact title="Exact result context, term and type annotation" value={candidate.result}/>
    </>}
    <ol className="snapshot-checks" aria-label={`Step ${index + 1} outcomes`}>{record.checking.checks.slice(step.receiptStart, step.receiptStart + step.receiptCount).map((check, local) => <li key={check.id}>
      <strong>Outcome {step.receiptStart + local + 1} · {operationOutcomeLabel(step.operation.kind, check.label, local)}</strong> <span>{check.outcome.tag}</span>
      <Exact title="Exact declaration, outcome and resource bound" value={check}/><Exact title="Declaration axiom audit" value={record.checking.status === 'captured' ? record.checking.audits[step.receiptStart + local] : undefined}/>
    </li>)}</ol>
    {unrecordedLogical.length > 0 && <p data-unrecorded-logical-outcomes="">Not recorded for this logical inspection: {unrecordedLogical.join('; ')}.</p>}
    {step.receiptCount === 0 && !catalogue && <p>No kernel outcomes were retained for this operation.</p>}
    <Exact title="Exact input pair" value={step.input}/>
  </section>;
}

function AttemptReading({ bundle, parentTitle, history, currentOrigin, onContinue, attempt, current }: { bundle: SourceDecompositionBundle; parentTitle: string; history?: DecompositionHistory; currentOrigin: boolean; onContinue?: ContinueSource; attempt: number; current: boolean }) {
  const { record } = bundle, checking = record.checking;
  const panelId = useId();
  const [selected, setSelected] = useState(checking.status === 'captured' ? Math.max(0, checking.steps.length - 1) : 0);
  // One derivation per selected step feeds both the guided reading's logical root and the provenance panel.
  // Identity guard: only the retained record object of this history may show a chain; a substituted record gets an explicit refusal.
  const derived = useMemo(() => history && history.attempts.find(entry => entry.record.captureId === record.captureId)?.record !== record
    ? { refusal: 'the displayed record is not the retained record of this history' } : deriveProvenance(history, record.captureId, selected), [history, record, selected]);
  const logicalRoot = useMemo(() => history ? guidedLogicalRoot(derived) : null, [history, derived]);
  const supply = useMemo(() => history && history.attempts.find(entry => entry.record.captureId === record.captureId)?.record !== record
    ? { refusal: 'the displayed record is not the retained record of this history' } : deriveSupplier(history, record.captureId, selected), [history, record, selected]);
  const occurrenceAnchorPrefix = derived?.value ? `${panelId}-${record.captureId}-${selected}` : undefined;
  // Section navigation names this attempt and its selected step. A destination exists only where the
  // corresponding section below is rendered; the conditions are those of the sections themselves.
  const step = checking.status === 'captured' ? checking.steps[selected] : undefined;
  const outline: OutlineAttempt = { current, attempt, step: step ? { number: step.index + 1, title: operationTitle(step.operation) } : null,
    outcomesAfterStep: !!step && checking.status === 'captured' && checking.checks.length > step.receiptStart + step.receiptCount };
  const outlineId = outlineNamespace(panelId, record.captureId, step ? step.index : null);
  const sections = outlineDestinations({ step: !!step, provenance: !!history && !!derived, supply: !!history && !!supply, outcomes: checking.status === 'captured' });
  const landing = (section: OutlineSection) => sections.includes(section) && <OutlineLanding namespace={outlineId} attempt={outline} section={section}/>;
  return <div data-decomposition-capture={record.captureId}>
    <p>Continues {parentTitle}. The expressions and checks below were recomputed for this attempt.</p>
    {checking.status === 'unavailable' ? <><p className="snapshot-unavailable" role="status">Continuation unavailable during {checking.phase}: {checking.reason}</p><p>{checking.attempted ? 'The capture call began; retained checking outcomes are unavailable.' : 'The continuation capture call did not begin.'}</p></> : <>
      <p>{counted(checking.checks.length, 'fresh kernel outcome')} retained across {counted(checking.steps.length, 'executed operation')}. The source extraction {checking.action.status === 'completed' ? 'completed' : 'reported an error'}.</p>
      {checking.action.status === 'error' && <p className="snapshot-unavailable">{checking.action.reason}</p>}
      {checking.stop && <p className="snapshot-unavailable" role="status">Stopped during {checking.stop.phase}: {checking.stop.reason}</p>}
      <ol className="continuation-steps" aria-label="Ordered continuation steps">{checking.steps.map(step => <li key={step.index}><button type="button" aria-pressed={selected === step.index} onClick={() => setSelected(step.index)}>Step {step.index + 1} · {operationTitle(step.operation)}<small>{step.replay} · {counted(step.receiptCount, 'outcome')}</small></button></li>)}</ol>
      <SourceReaderOutline namespace={outlineId} attempt={outline} sections={sections}/>
      {landing('step')}
      <StepReading key={`${record.captureId}:${selected}`} record={record} index={selected} logicalRoot={logicalRoot} onContinue={onContinue}/>
      {landing('provenance')}
      <ProvenancePanel key={`provenance:${record.captureId}:${selected}`} history={history} derived={derived} currentOrigin={currentOrigin} occurrenceAnchorPrefix={occurrenceAnchorPrefix}/>
      {landing('supply')}
      <SupplierPanel key={`supply:${record.captureId}:${selected}`} history={history} derived={supply} currentOrigin={currentOrigin} occurrenceAnchorPrefix={occurrenceAnchorPrefix}/>
      {landing('outcomes')}
      <details className="snapshot-exact" open><summary>Recorded outcomes in this attempt ({checking.checks.length})</summary><ol className="snapshot-checks" aria-label="All numbered outcomes of this attempt">{checking.checks.map((check, i) => {
        const step = checking.steps.find(candidate => i >= candidate.receiptStart && i < candidate.receiptStart + candidate.receiptCount);
        const label = step ? `Step ${step.index + 1} · ${operationOutcomeLabel(step.operation.kind, check.label, i - step.receiptStart)}`
          : ['Source context', 'Source component', 'Root context', 'Root component', 'Selected context', 'Selected component'][i] ?? `Recorded ${check.label}`;
        return <li key={check.id} data-numbered-outcome={i + 1}><strong>Outcome {i + 1} · {label}</strong> <span>{check.outcome.tag}</span><Exact title="Exact declaration and outcome" value={check}/><Exact title="Declaration axiom audit" value={checking.audits[i]}/></li>;
      })}</ol></details>
      {checking.checks.length === 0 && <p>No retained kernel checks establish acceptance.</p>}
      <Exact title="Fresh original selected pair" value={checking.selected}/><Exact title="Exact continuation binding" value={checking.binding}/>
    </>}
    <Exact title="Complete continuation record" value={record}/><Exact title="Fresh source snapshot" value={bundle.snapshot}/><Exact title="Fresh process and input identity" value={bundle.origin}/>
  </div>;
}

export function SourceDecompositionReading({ attempts, history, currentOrigin = false, onContinue }: {
  attempts: SourceDecompositionBundle[]; history?: DecompositionHistory; currentOrigin?: boolean; onContinue?: ContinueSource;
}) {
  const [selectedCapture, setSelectedCapture] = useState(attempts.at(-1)?.record.captureId);
  const selected = attempts.find(item => item.record.captureId === selectedCapture) ?? attempts.at(-1);
  if (!selected) return null;
  const current = selected === attempts.at(-1);
  const parentIndex = attempts.findIndex(item => item.record.captureId === selected.record.previousCaptureId);
  const parentTitle = selected.record.previousCaptureId === selected.record.parentCaptureId ? 'the original selected occurrence' : parentIndex < 0 ? 'the first exposure' : `attempt ${parentIndex + 1}, step ${selected.record.parentStepIndex + 1}`;
  return <section className="source-decomposition" aria-label="Continuation history">
    <h3 data-source-result="attempt" tabIndex={-1}>{current ? 'Current continuation' : 'Earlier continuation'} · attempt {attempts.indexOf(selected) + 1}</h3>
    <p>{currentOrigin ? 'Each attempt followed an explicit action on your source.' : 'This saved history has an unverified origin.'} Earlier continuations stay available. Selecting a row only inspects it.</p>
    <details className="snapshot-exact"><summary>Earlier continuations and current attempt ({attempts.length})</summary><div className="continuation-attempts">{attempts.map((item, i) => <button type="button" key={item.record.captureId} aria-pressed={item === selected} onClick={() => setSelectedCapture(item.record.captureId)}>Attempt {i + 1}{i === attempts.length - 1 ? ' · current' : ''}<small>{counted(item.record.operations.length, 'requested step')}</small></button>)}</div></details>
    <AttemptReading key={selected.record.captureId} bundle={selected} parentTitle={parentTitle} history={history} currentOrigin={currentOrigin} onContinue={currentOrigin ? onContinue : undefined}
      attempt={attempts.indexOf(selected) + 1} current={current}/>
  </section>;
}
