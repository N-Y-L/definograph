import { useMemo, useState } from 'react';
import { StructuralFieldValue, StructuralReading } from '../packets/StructuralReading';
import { nameText } from '../packets/syntax';
import type { HeadExposureBundle } from './host';
import type { SourceOccurrence, SourceOccurrenceStep } from './source-occurrence';
import { sourceOccurrenceReading } from './source-occurrence-reading';
import { sourceOccurrenceDrawing } from './source-occurrence-structure';
import { recordedContextEntries } from './source-snapshot';
import { PositionalReadingPane } from './SourceOccurrenceGuidedReading';
import { headExposureDrawing, headExposureReading } from './source-head-exposure-reading';
import { positionalResultPath } from './source-decomposition-reading';
import { ContinuationChoice } from './ContinuationChoice';
import type { ContinueSource } from './SourceDecompositionReading';
import { counted } from '../core/counted';

function Exact({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={event => setOpen(event.currentTarget.open)}>
    <summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}

export function SourceHeadExposureReading({ bundle, original, currentOrigin = false, initialSide = 'after', initialView = 'guided', onFocusExposedPart, onContinue }: {
  bundle: HeadExposureBundle; original: SourceOccurrence; currentOrigin?: boolean; initialSide?: 'before' | 'after'; initialView?: 'guided' | 'structure'; onFocusExposedPart?: (path: SourceOccurrenceStep[]) => void;
  onContinue?: ContinueSource;
}) {
  const { record } = bundle, checking = record.checking;
  const [side, setSide] = useState(initialSide), [view, setView] = useState(initialView);
  const [chosenPath, setChosenPath] = useState<SourceOccurrenceStep[] | null>(null);
  const before = useMemo(() => sourceOccurrenceReading(original, record.target), [original, record.target]);
  const after = useMemo(() => headExposureReading(record), [record]);
  const originalDrawing = useMemo(() => sourceOccurrenceDrawing(original), [original]);
  const resultDrawing = useMemo(() => headExposureDrawing(record), [record]);
  const candidate = checking.status === 'captured' && checking.exposure?.status === 'candidate' ? checking.exposure : undefined;
  const eligible = candidate?.checking.status === 'completed' && checking.status === 'captured' && checking.action.status === 'completed' && onFocusExposedPart;
  const choose = (path: (string | number)[]) => setChosenPath(candidate ? positionalResultPath(candidate.result, ['checking', 'exposure', 'result'], path) ?? null : null);
  const structure = side === 'after' ? resultDrawing : originalDrawing;
  const title = side === 'after' ? `Exposed ${record.target}` : record.target === 'term' ? 'Original selected term' : 'Original inferred type';
  const stages = ['Fresh source context', 'Fresh source component', 'Fresh inferred root context', 'Fresh inferred root component',
    'Fresh selected context', 'Fresh selected component', 'Result context', 'Result component', 'Conversion'];
  return <section className="source-head-exposure" aria-label="Definition-head exposure" data-head-exposure-target={record.target}>
    <h3 data-source-result="head-exposure" tabIndex={-1}>Definition-head exposure · {record.target}</h3>
    <p>{currentOrigin ? 'This separate record comes from a fresh Lean process.' : 'This saved exposure record has unverified process provenance.'} The original occurrence and its outcomes remain above. No further definition is opened automatically.</p>
    {checking.status === 'unavailable' ? <>
      <p className="snapshot-unavailable" role="status">Exposure record unavailable during {checking.phase}: {checking.reason}</p>
      <p>{checking.attempted ? 'The capture call began; this record does not establish how many checks ran.' : 'The exposure capture call did not begin.'}</p>
    </> : <>
      <p>{counted(checking.checks.length, 'fresh kernel outcome')} retained. The base extraction {checking.action.status === 'completed' ? 'completed' : 'reported an error'}.</p>
      {checking.action.status === 'error' && <p className="snapshot-unavailable" role="status">{checking.action.reason}</p>}
      {checking.checks.length === 0 && <p>No retained kernel checks establish acceptance.</p>}
      {checking.exposure?.status === 'unavailable' && <p className="snapshot-unavailable" role="status">Head exposure unavailable during {checking.exposure.phase}: {checking.exposure.reason}</p>}
      {candidate && <>
        <p>A candidate exposes the retained body of <code>{nameText(candidate.definition.name)}</code> with {candidate.betaApplications} original leading lambda {candidate.betaApplications === 1 ? 'input consumed' : 'inputs consumed'}. Candidate availability does not mean that any check accepted.</p>
        {candidate.checking.status === 'error' && <p className="snapshot-unavailable" role="status">Candidate checks reported an error: {candidate.checking.reason}</p>}
        <p>The browser reconstructed the recorded syntactic step. This does not authenticate the definition's environment membership. Conversion acceptance, when recorded below, concerns kernel convertibility and can include proof irrelevance; it does not certify this reduction policy or assert a proposition.</p>
      </>}
      <ol className="snapshot-checks" aria-label="Fresh exposure outcomes">{checking.checks.map((check, index) => <li key={index}>
        <strong>{stages[index]}</strong> <span>{check.outcome.tag}</span>
        <Exact title="Exact declaration, outcome and resource bound" value={check}/>
        <Exact title="Declaration axiom audit" value={checking.audits[index]}/>
      </li>)}</ol>
      {candidate && <>
        <div className="snapshot-tabs" role="tablist" aria-label="Exposure comparison side">{(['before', 'after'] as const).map(value =>
          <button type="button" role="tab" key={value} aria-selected={side === value} onClick={() => { setSide(value); setChosenPath(null); }}>{value === 'before' ? 'Before exposure' : 'After exposure'}</button>)}</div>
        <div className="snapshot-tabs" role="tablist" aria-label="Exposure presentation">{(['guided', 'structure'] as const).map(value =>
          <button type="button" role="tab" key={value} aria-selected={view === value} onClick={() => setView(value)}>{value === 'guided' ? 'Guided reading' : 'Structure'}</button>)}</div>
        {side === 'after' && eligible && <ContinuationChoice path={chosenPath} onChooseRoot={() => setChosenPath([])} onCheck={onFocusExposedPart!}/>}
        {side === 'after' && currentOrigin && onContinue && candidate.checking.status === 'completed' && checking.action.status === 'completed' && <div className="head-exposure-action">
          <button type="button" className="toolbar-button" onClick={() => onContinue(record.captureId, 0, { kind: 'typeComponent' })}>Inspect type of exposed term</button>
          <button type="button" className="toolbar-button" onClick={() => onContinue(record.captureId, 0, { kind: 'logical' })}>Read logical structure of exposed term (one layer)</button>
        </div>}
        {onFocusExposedPart && !eligible && <p className="snapshot-context">This seed operation did not complete. Its candidate remains inspectable; Refresh to start another source/exposure history.</p>}
        <div role="tabpanel" aria-label={title} data-head-exposure-side={side}>
          {view === 'guided' ? <PositionalReadingPane key={`${record.captureId}:${record.target}:${side}`} model={side === 'before' ? before : after}
            title={title} onSourcePathSelect={side === 'after' && eligible ? choose : undefined} inspectorLabel={side === 'before' ? 'Exact original occurrence source' : 'Exact exposed source'}/>
            : structure?.ok ? <><h4>{title}</h4><p>{side === 'after' ? 'The result pair contains the exposed expression and its carrier annotation in the unchanged surrounding context.' : 'The original selected term and inferred type remain paired in their surrounding context.'}</p><StructuralReading key={`${record.captureId}:${side}`} drawing={structure.value} onSourceSelect={side === 'after' && eligible ? choose : undefined} positionalRootTitles={side === 'after' ? { term: title, type: 'Carrier annotation' } : undefined}
              recordedContext={side === 'after' ? recordedContextEntries(checking.binding) : original.checking.status === 'captured' ? recordedContextEntries(original.checking.binding) : undefined}/></>
              : <p className="snapshot-unavailable">Structure unavailable: {structure?.error.message ?? 'No drawing was produced.'} Exact data remain available.</p>}
        </div>
        <Exact title="Exact before expression" value={candidate.before}/>
        <Exact title="Exact result context, expression and carrier" value={candidate.result}/>
        <Exact title="Definition and exposure trace" value={{ definition: candidate.definition, actualLevels: candidate.actualLevels,
          arguments: candidate.arguments, betaApplications: candidate.betaApplications, carrierSort: candidate.carrierSort }}/>
      </>}
      <Exact title="Freshly extracted selected triple" value={checking.selected}/>
      <Exact title="Exact exposure binding" value={checking.binding}/>
    </>}
    <Exact title="Fresh source snapshot" value={bundle.snapshot}/>
    <Exact title="Exposure policy and parent association" value={{ policy: record.policy, path: record.path, target: record.target, parentCaptureId: record.parentCaptureId, captureId: record.captureId }}/>
    <Exact title="Fresh process and input identity" value={bundle.origin}/>
  </section>;
}
