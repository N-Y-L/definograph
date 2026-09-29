import { useMemo, useState } from 'react';
import { RawSourceReading } from '../packets/RawSourceReading';
import { StructuralFieldValue, StructuralReading } from '../packets/StructuralReading';
import { recordedContextEntries, sourceSnapshotDrawings, type SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import { sourceOccurrencePath, type SourceOccurrence, type SourceOccurrenceStep } from './source-occurrence';
import { sourceOccurrenceDrawing } from './source-occurrence-structure';
import { SourceOccurrenceGuidedReading } from './SourceOccurrenceGuidedReading';
import { SourceHeadExposureReading } from './SourceHeadExposureReading';
import { assertSourceHistoryLimit, retainedDecompositionHistory, type HeadExposureBundle } from './host';
import type { SourceDecompositionBundle } from './source-decomposition';
import { SourceDecompositionReading, type ContinueSource } from './SourceDecompositionReading';
import type { HeadExposureTarget } from './source-head-exposure';
import './source-snapshot.css';
import { counted } from '../core/counted';

type Tab = 'original' | 'prepared' | 'expectedType' | 'checking';
const titles: Record<Tab, string> = { original: 'Original data', prepared: 'Checker input', expectedType: 'Expected type', checking: 'Check outcomes' };

function ExactDetails({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={e => setOpen(e.currentTarget.open)}><summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}

const stepTitles: Record<SourceOccurrenceStep, string> = {
  appFun: 'Function', appArg: 'Argument', lamDomain: 'Lambda domain', lamBody: 'Lambda body',
  piDomain: 'Product domain', piBody: 'Product body', letType: 'Let type', letValue: 'Let value',
  letBody: 'Let body', projValue: 'Projection value',
};
function occurrenceTitle(path: SourceOccurrenceStep[]): string {
  return path.length ? path.map(step => stepTitles[step]).join(' → ') : 'Whole prepared term';
}

export function SourceOccurrenceReading({ value, initialView = 'guided', onExposeDefinitionHead }: { value: SourceOccurrence; initialView?: 'guided' | 'structure'; onExposeDefinitionHead?: (target: HeadExposureTarget) => void }) {
  const checking = value.checking;
  const [view, setView] = useState(initialView);
  const structure = useMemo(() => sourceOccurrenceDrawing(value), [value]);
  const stages = ['Source context', 'Source component', 'Inferred root context', 'Inferred root component', 'Selected context', 'Selected component'];
  return <section className="source-occurrence" aria-label="Chosen occurrence checks">
    <h3 data-source-result="occurrence" tabIndex={-1}>Chosen occurrence checks</h3>
    <p className="occurrence-path">{occurrenceTitle(value.path)}</p>
    <p>Each request uses a fresh Lean process. Extraction begins only when the prepared source matches the parent capture. Earlier check results are not carried forward.</p>
    {checking.status === 'unavailable' ? <>
      <p className="snapshot-unavailable" role="status">Occurrence record unavailable during {checking.phase}: {checking.reason}</p>
      <p>{checking.attempted ? 'An occurrence capture call was attempted. Its kernel outcomes are unavailable.' : 'The occurrence capture call did not begin.'}</p>
    </> : <>
      <p>{checking.checks.length} kernel {checking.checks.length === 1 ? 'outcome' : 'outcomes'} retained. The action {checking.action.status === 'completed' ? 'completed' : 'reported an error'}. Typing outcomes do not assert a proposition or certify the drawing.</p>
      {checking.action.status === 'error' && <p className="snapshot-unavailable">{checking.action.reason}</p>}
      {checking.checks.length === 0 && <p>No retained kernel checks establish acceptance.</p>}
      {checking.selected && <div className="occurrence-home">
        <p>The chosen term has {checking.selected.home.arity} surrounding {checking.selected.home.arity === 1 ? 'declaration' : 'declarations'}. Bound references use positional indices; enclosing binders and this context determine what they refer to. Binder names may repeat.</p>
        <ExactDetails title="Exact dependent context" value={checking.selected.home}/>
        <ExactDetails title="Exact selected term" value={checking.selected.term}/>
        <ExactDetails title="Inferred selected type" value={checking.selected.type}/>
      </div>}
      <ol className="snapshot-checks">{checking.checks.map((check, index) => <li key={index}>
        <strong>{stages[index]}</strong> <span>{check.outcome.tag}</span>
        <ExactDetails title="Exact declaration, outcome and resource bound" value={check}/>
        <ExactDetails title="Declaration axiom audit" value={checking.audits[index]}/>
      </li>)}</ol>
      {checking.selected && <>
        <div className="snapshot-tabs" role="tablist" aria-label="Occurrence presentation">
          <button type="button" role="tab" aria-selected={view === 'guided'} onClick={() => setView('guided')}>Guided reading</button>
          <button type="button" role="tab" aria-selected={view === 'structure'} onClick={() => setView('structure')}>Structure</button>
        </div>
        {structure?.ok && <p className="occurrence-readback">The Structure view reconstructs the exact selected term, inferred type and complete surrounding context. This comparison does not establish typing or verify the record's origin. Guided reading presents supported parts of that syntax.</p>}
        <div role="tabpanel" aria-label={view === 'guided' ? 'Occurrence guided reading' : 'Occurrence structure'}>
          {view === 'guided' ? <SourceOccurrenceGuidedReading key={`${value.captureId}:${JSON.stringify(value.path)}`} value={value} onExposeDefinitionHead={onExposeDefinitionHead}/>
            : structure?.ok ? <StructuralReading drawing={structure.value} recordedContext={recordedContextEntries(checking.binding)}/>
              : <p className="snapshot-unavailable" role="status">Selected structure unavailable ({structure?.error.code ?? 'unavailable'}): {structure?.error.message ?? 'No drawing was produced.'} The retained source data and check outcomes remain available.</p>}
        </div>
      </>}
      <ExactDetails title="Exact occurrence binding" value={checking.binding}/>
    </>}
    <ExactDetails title="Occurrence path, policy and process association" value={{ path: value.path, policy: value.policy, parentCaptureId: value.parentCaptureId, captureId: value.captureId }}/>
  </section>;
}

/** Only the editor host supplies origin here. Importing or reading saved JSON
 * cannot construct a current editor session or re-run the recorded checks. */
export function savedSourceSnapshot(snapshot: SourceSnapshot, origin?: SourceSnapshotOrigin, occurrence?: SourceOccurrence,
  headExposure?: HeadExposureBundle, headExposureUnavailable?: string, decompositions?: SourceDecompositionBundle[], decompositionUnavailable?: string) {
  const saved = { format: 'definograph.saved-source-snapshot', version: decompositions?.some(item => item.record.schema === 'definograph.source-decomposition.v3') ? 6 : decompositions?.some(item => item.record.schema === 'definograph.source-decomposition.v2') || (!headExposure && (decompositions !== undefined || decompositionUnavailable !== undefined)) ? 5 : decompositions !== undefined || decompositionUnavailable !== undefined ? 4 : headExposure || headExposureUnavailable !== undefined ? 3 : occurrence ? 2 : 1,
    provenance: 'unverified-saved-record', snapshot, recordedOrigin: origin ?? null,
    ...(occurrence ? { occurrence } : {}), ...(headExposure ? { headExposure } : {}),
    ...(headExposureUnavailable !== undefined ? { headExposureUnavailable } : {}),
    ...(decompositions !== undefined ? { decompositions } : {}), ...(decompositionUnavailable !== undefined ? { decompositionUnavailable } : {}) };
  assertSourceHistoryLimit(saved);
  return saved;
}

export function SourceSnapshotReading({ snapshot, origin, initialTab, occurrence, occurrenceUnavailable, onCheckOccurrence,
  headExposure, headExposureUnavailable, onExposeDefinitionHead, decompositions, decompositionUnavailable, onContinue }: {
  snapshot: SourceSnapshot; origin?: SourceSnapshotOrigin; initialTab?: Tab;
  occurrence?: SourceOccurrence; occurrenceUnavailable?: string; onCheckOccurrence?: (path: SourceOccurrenceStep[]) => void;
  headExposure?: HeadExposureBundle; headExposureUnavailable?: string; onExposeDefinitionHead?: (target: HeadExposureTarget) => void;
  decompositions?: SourceDecompositionBundle[]; decompositionUnavailable?: string; onContinue?: ContinueSource;
}) {
  const [tab, setTab] = useState<Tab>(initialTab ?? (occurrence || occurrenceUnavailable ? 'prepared' : 'original'));
  const [chosenPath, setChosenPath] = useState<SourceOccurrenceStep[] | null>(occurrence?.path ?? null);
  const drawings = useMemo(() => sourceSnapshotDrawings(snapshot), [snapshot]);
  // Only the host-validated history object carries ordered provenance; nothing is rebuilt or re-validated here.
  const history = decompositions ? retainedDecompositionHistory(decompositions) : undefined;
  const section = snapshot[tab];
  const continueAction = origin && (decompositions?.length ?? 0) < 8 ? onContinue : undefined;
  const checkSource = headExposure || decompositions !== undefined ? undefined : onCheckOccurrence;
  const originalReady = occurrence?.checking.status === 'captured' && occurrence.checking.action.status === 'completed' && occurrence.checking.selected;
  const exposeOriginal = continueAction && originalReady ? (target: HeadExposureTarget) => continueAction(occurrence!.captureId, 0, { kind: 'expose', target }) : origin && !headExposure && decompositions === undefined ? onExposeDefinitionHead : undefined;
  function download() {
    const text = JSON.stringify(savedSourceSnapshot(snapshot, origin, occurrence, headExposure, headExposureUnavailable, decompositions, decompositionUnavailable));
    const url = URL.createObjectURL(new Blob([text], { type: 'application/json' }));
    const link = document.createElement('a'); link.href = url; link.download = 'definograph-source-snapshot.json'; link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }
  return <section className="source-snapshot" aria-label="Selected source snapshot">
    <header><h2>Selected source data</h2><button className="toolbar-button" onClick={download}>Save source snapshot</button></header>
    <p>{origin ? 'Captured from your Lean buffer by the local reader process.' : 'Saved source snapshot. Its origin is unverified.'} Raw data and kernel outcomes are separate records.</p>
    <p className="snapshot-context">Selected bytes {snapshot.selection.startByte}–{snapshot.selection.endByte}{origin?.document ? ` · buffer v${origin.document.version}` : ''}. Imported libraries describe that process’s environment; their later changes are not tracked by this snapshot.</p>
    <div className="snapshot-tabs" role="tablist" aria-label="Source snapshot sections">{(Object.keys(titles) as Tab[]).map(key => <button key={key} role="tab" aria-selected={tab === key} onClick={() => setTab(key)}>{titles[key]}</button>)}</div>
    <div role="tabpanel" aria-label={titles[tab]}>
      {tab === 'original' && <p>The exact selected expression and local declarations before preparation, with a type inferred in the captured context. This may retain assigned metavariables, metadata and local definitions.</p>}
      {tab === 'prepared' && <p>The input supplied to the source checker after Lean’s <code>instantiateMVars</code> operation. It may instantiate assigned metavariables and perform associated beta reduction. Ignored stored values remain unchanged. This records the preparation; it does not prove equivalence of the two frames.</p>}
      {tab === 'prepared' && checkSource && snapshot.prepared.status === 'available' && <div className="occurrence-choice">
        <p>Choose a constructor inside the prepared term, then check it with its surrounding declarations. This reruns the current Lean buffer.</p>
        <p className="occurrence-path">{chosenPath === null ? 'No occurrence chosen.' : occurrenceTitle(chosenPath)}</p>
        <button type="button" className="toolbar-button" disabled={chosenPath === null} onClick={() => { if (chosenPath) checkSource!([...chosenPath]); }}>Check chosen occurrence</button>
      </div>}
      {tab === 'prepared' && occurrence && <SourceOccurrenceReading key={`${occurrence.captureId}:${JSON.stringify(occurrence.path)}`} value={occurrence} onExposeDefinitionHead={exposeOriginal}/>}
      {tab === 'prepared' && originalReady && continueAction && <div className="head-exposure-action"><p>Continue from the original selected pair. To read the logical structure of its type, choose Inspect type first.</p>
        <button type="button" className="toolbar-button" onClick={() => continueAction(occurrence!.captureId, 0, { kind: 'typeComponent' })}>Inspect type of original selected term</button>
        <button type="button" className="toolbar-button" onClick={() => continueAction(occurrence!.captureId, 0, { kind: 'logical' })}>Read logical structure of original selected term (one layer)</button>
        <button type="button" className="toolbar-button" onClick={() => continueAction(occurrence!.captureId, 0, { kind: 'fields' })}>Inspect fields of original occurrence</button><button type="button" className="toolbar-button" onClick={() => continueAction(occurrence!.captureId, 0, { kind: 'focus', path: [] })}>Check whole selected term</button></div>}
      {tab === 'prepared' && headExposure && occurrence && <SourceHeadExposureReading key={headExposure.record.captureId} bundle={headExposure} original={occurrence} currentOrigin={!!origin} onContinue={continueAction} onFocusExposedPart={continueAction ? path => continueAction(headExposure.record.captureId, 0, { kind: 'focus', path }) : undefined}/>}
      {tab === 'prepared' && headExposure && origin && <p className="snapshot-context">This history keeps the original selection and earlier attempts. Save the history and Refresh to start another source/exposure history.</p>}
      {tab === 'prepared' && decompositions && <SourceDecompositionReading key={decompositions.at(-1)?.record.captureId ?? 'empty'} attempts={decompositions} history={history} currentOrigin={!!origin} onContinue={continueAction}/>}
      {tab === 'prepared' && (decompositions?.length ?? 0) >= 8 && <p className="snapshot-unavailable" role="status">Eight continuation attempts are retained. Save this history and Refresh to start another. Earlier attempts remain available.</p>}
      {tab === 'prepared' && decompositionUnavailable !== undefined && <p className="snapshot-unavailable" role="status" data-source-result="continuation-unavailable" tabIndex={-1}>Continuation data unavailable: {decompositionUnavailable} Earlier retained history remains available.</p>}
      {tab === 'prepared' && headExposureUnavailable !== undefined && <p className="snapshot-unavailable" role="status" data-source-result="head-exposure-unavailable" tabIndex={-1}>Definition-head exposure data unavailable: {headExposureUnavailable} The original occurrence remains available.</p>}
      {tab === 'prepared' && occurrenceUnavailable && <p className="snapshot-unavailable" role="status" data-source-result="occurrence-unavailable" tabIndex={-1}>Occurrence data unavailable: {occurrenceUnavailable}</p>}
      {tab === 'expectedType' && <p>The elaborator’s recorded expectation, when present. It is kept separately from the inferred type used for checking.</p>}
      {tab !== 'checking' && (section.status === 'unavailable'
        ? <p className="snapshot-unavailable" role="status">Unavailable during {section.phase}: {section.reason}</p>
        : section.status === 'absent' ? <p>No expected type was recorded for this occurrence.</p>
        : drawings[tab] ? <RawSourceReading key={tab} drawing={drawings[tab]!} nodeAction={tab === 'prepared' && checkSource ? node => {
          const path = sourceOccurrencePath(snapshot, node.sourcePath);
          if (node.family !== 'expression' || !path) return undefined;
          return { label: 'Choose occurrence', selected: chosenPath !== null && JSON.stringify(chosenPath) === JSON.stringify(path), onClick: () => setChosenPath(path) };
        } : undefined}/> : <p>Raw drawing unavailable.</p>)}
      {tab === 'prepared' && snapshot.prepared.status === 'available' && <ExactDetails title="Exact checking universe parameters" value={snapshot.prepared.checkerUniverseParams}/>}
      {tab === 'checking' && (snapshot.checking.status === 'unavailable' ? <>
        <p className="snapshot-unavailable" role="status">Check record unavailable during {snapshot.checking.phase}: {snapshot.checking.reason}</p>
        <p>{snapshot.checking.attempted ? 'A source capture call was attempted. This record does not establish how many kernel checks ran or their outcomes.' : 'The source capture call did not begin.'}</p>
      </> : <>
        <p>{snapshot.checking.checks.length} kernel {snapshot.checking.checks.length === 1 ? 'outcome' : 'outcomes'} retained. The action {snapshot.checking.action.status === 'completed' ? 'completed' : 'reported an error'}. These checks concern the prepared context and term typing; they do not certify this visualization or assert the selected proposition.</p>
        {snapshot.checking.action.status === 'error' && <p className="snapshot-unavailable">{snapshot.checking.action.reason}</p>}
        {snapshot.checking.checks.length === 0 && <p>No retained kernel checks establish acceptance.</p>}
        <ol className="snapshot-checks">{snapshot.checking.checks.map((check, index) => <li key={index}>
          <strong>{String(check.displayLabel)}</strong> <span>{String((check.outcome as { tag: string }).tag)}</span>
          <ExactDetails title="Exact declaration, outcome and resource bound" value={check}/>
          {snapshot.checking.status === 'captured' && <ExactDetails title="Declaration axiom audit" value={snapshot.checking.audits[index]}/>}
        </li>)}</ol>
        <p>{counted(snapshot.checking.environmentSnapshotCount, 'process-local environment snapshot')} retained by the check sequence.</p>
        <ExactDetails title="Exact source binding" value={snapshot.checking.binding}/>
      </>)}
    </div>
    <ExactDetails title="Selection and checking policy" value={{ selection: snapshot.selection, policy: snapshot.policy }}/>
    {origin && <ExactDetails title="Captured process and input identity" value={origin}/>}
  </section>;
}
