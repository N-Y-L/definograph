import { useMemo, useState } from 'react';
import { compileReading } from '../reading/compiler';
import { StatementReadingView } from '../visual/StatementReadingView';
import { StructuralFieldValue } from '../packets/StructuralReading';
import { formatExpr } from '../packets/syntax';
import type { PacketSource, PositionalComponentReading } from '../packets/semantic';
import { UNMATCHED_RECORDED_KINDS } from '../core/context-entry';
import type { SourceOccurrence } from './source-occurrence';
import { sourceOccurrenceReading } from './source-occurrence-reading';
import type { HeadExposureTarget } from './source-head-exposure';
import { counted } from '../core/counted';

function ExactValue({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="snapshot-exact" onToggle={event => setOpen(event.currentTarget.open)}>
    <summary>{title}</summary>{open && <StructuralFieldValue value={value}/>}</details>;
}

/** A CTel introduction points at an actual snoc entry, not an invented Expr.
 * Its type and defining value instead point at their own expression fields. */
function isContextEntry(source: PacketSource): boolean {
  const telescope = source.path.indexOf('telescope');
  return telescope >= 0 && source.path.slice(telescope + 1).every(part => part === 1);
}

function OccurrenceSourceInspector({ model, selectedId, onSelect, label }: {
  model: PositionalComponentReading; selectedId: string; onSelect: (id: string) => void; label: string;
}) {
  const [limit, setLimit] = useState(50);
  const [boundaryLimit, setBoundaryLimit] = useState(30);
  const selected = model.sourceById[selectedId];
  const objects = model.document?.objects ?? [];
  const names = new Map(objects.flatMap(object => object.binder ? [[object.binder.id, object.binder.name] as const] : []));
  let text: string | undefined;
  if (selected && !isContextEntry(selected)) {
    try { text = formatExpr(selected.syntax, selected.scopeBinderIds.map(id => names.get(id) ?? id).reverse(), 2); }
    catch { /* The exact constructor remains available if readable formatting is unsupported. */ }
  }
  return <section className="occurrence-inspector" aria-label={label}>
    <h4>Inspect the selected source</h4>
    <p>Select an object or reading step to see its exact source and scope. The complete context and both expressions remain available in Structure.</p>
    {selected ? <div data-occurrence-source-path={JSON.stringify(selected.path)}>
      <strong>{isContextEntry(selected) ? 'Surrounding context entry' : 'Expression constructor'}</strong>
      {text && <p><code>{text}</code></p>}
      <p>Source path: <code>{JSON.stringify(selected.path)}</code></p>
      <ExactValue title="Exact source value" value={selected.syntax}/>
      <details className="snapshot-exact"><summary>Surrounding scope ({selected.scopeBinderIds.length} {selected.scopeBinderIds.length === 1 ? 'declaration' : 'declarations'}, oldest first)</summary>
        {selected.scopeBinderIds.length ? <ol>{selected.scopeBinderIds.map(id => <li key={id}><span>{names.get(id) ?? 'Declaration'}</span><br/><code>{id}</code></li>)}</ol> : <p>No surrounding declarations at this source position.</p>}
      </details>
    </div> : <p>No source selected.</p>}
    <details className="snapshot-exact"><summary>All objects and application inputs ({objects.length})</summary>
      <div className="occurrence-object-list">{objects.slice(0, limit).map(object => <button type="button" key={object.id} aria-pressed={selectedId === object.id} onClick={() => onSelect(object.id)}>
        {object.label}{object.type && <small>{object.type}</small>}
      </button>)}</div>
      {objects.length > limit && <button type="button" className="toolbar-button" onClick={() => setLimit(count => count + 50)}>Show next {counted(Math.min(50, objects.length - limit), 'object')}</button>}
    </details>
    {!!model.document?.opaqueRegions.length && <details className="snapshot-exact"><summary>Expressions without a specialized diagram ({model.document.opaqueRegions.length})</summary>
      <ul>{model.document.opaqueRegions.slice(0, boundaryLimit).map(region => <li key={region.id}><p>{region.reason}</p><button type="button" className="quiet-button" onClick={() => onSelect(region.id)}>Inspect {region.label}</button></li>)}</ul>
      {model.document.opaqueRegions.length > boundaryLimit && <button type="button" className="toolbar-button" onClick={() => setBoundaryLimit(count => count + 30)}>Show next {counted(Math.min(30, model.document.opaqueRegions.length - boundaryLimit), 'boundary', 'boundaries')}</button>}
    </details>}
    {!!model.document?.diagnostics.length && <details className="snapshot-exact"><summary>Scope and display notes</summary><ul>{model.document.diagnostics.map((note, index) => <li key={index}>{note}</li>)}</ul></details>}
  </section>;
}

function TargetReading({ value, target }: { value: SourceOccurrence; target: 'term' | 'type' }) {
  const model = useMemo(() => sourceOccurrenceReading(value, target), [value, target]);
  return <PositionalReadingPane model={model} title={target === 'term' ? 'Selected term' : 'Inferred type'}/>;
}

/** A record adapter supplies actual positional data and provenance. Display
 * titles never alter the compiler's target, source paths or expression pairing. */
export function PositionalReadingPane({ model, title, inspectorLabel = 'Exact occurrence source', onSourcePathSelect }: {
  model?: PositionalComponentReading; title: string; inspectorLabel?: string; onSourcePathSelect?: (path: (string | number)[]) => void;
}) {
  const [selectedNode, setSelectedNode] = useState('');
  const [selectedObject, setSelectedObject] = useState('');
  const [selectedSource, setSelectedSource] = useState('');
  const reading = useMemo(() => model?.document ? compileReading(model.document, { selectedNodeId: selectedNode || undefined }) : undefined, [model, selectedNode]);
  const currentSource = selectedSource || model?.targetNodeId || '';
  if (!model) return <p>No selected candidate is available for guided reading.</p>;
  if (!model.document || !reading) return <p className="snapshot-unavailable" role="status">Guided reading unavailable: {model.reason ?? 'No supported presentation was produced.'} The Structure view and exact data remain available.</p>;
  const selectSource = (id: string) => {
    setSelectedSource(id);
    const source = model.sourceById[id];
    if (source) onSourcePathSelect?.([...source.path]);
  };
  const selectNode = (id: string) => { setSelectedNode(id); selectSource(id); setSelectedObject(''); };
  return <div className="occurrence-guided-target" data-occurrence-target={model.target}>
    <h4>{title}</h4>
    <p>{model.document.presentation?.logicalRootNodeId
      ? 'The associated formation check identifies a proposition. This reading interprets its outer logical form under the recorded standard-core convention; it does not supply a proof. Nested expressions retain their ordinary positional structure.'
      : 'This reading shows context, binding and application structure. It does not classify the expression as a proposition or establish its mathematical meaning.'}</p>
    {model.recordedKindsUnmatched && <p className="snapshot-unavailable" data-recorded-kinds-unmatched="">{UNMATCHED_RECORDED_KINDS}</p>}
    <details className="snapshot-exact"><summary>Surrounding scope ({model.contextNodeIds.length} {model.contextNodeIds.length === 1 ? 'declaration' : 'declarations'})</summary>
      <p>These entries form the surrounding scope of the displayed term or type. They can include captured declarations and names or local definitions entered while selecting or focusing. This list does not assign them a logical role. Binders inside the displayed expression are shown separately.</p>
      <ol>{model.contextNodeIds.map(id => <li key={id}><button type="button" className="quiet-button" onClick={() => selectNode(id)}>{reading.nodes.find(node => node.id === id)?.phrase ?? 'Context entry'}</button></li>)}</ol>
      <button type="button" className="toolbar-button" onClick={() => { if (model.targetNodeId) selectNode(model.targetNodeId); }}>Inspect {title.toLowerCase()} root</button>
    </details>
    <StatementReadingView document={model.document} reading={reading} componentTitle={title} selectedObjectId={selectedObject || undefined}
      onObjectSelect={id => { setSelectedObject(id); selectSource(id); }} onNodeSelect={selectNode} onSourceSelect={selectSource}/>
    <OccurrenceSourceInspector model={model} selectedId={currentSource} label={inspectorLabel} onSelect={id => { selectSource(id); setSelectedObject(model.document!.objects.some(object => object.id === id) ? id : ''); }}/>
  </div>;
}

/** A target switch creates a fresh focus state without invoking the native host. */
export function SourceOccurrenceGuidedReading({ value, onExposeDefinitionHead }: { value: SourceOccurrence; onExposeDefinitionHead?: (target: HeadExposureTarget) => void }) {
  const [target, setTarget] = useState<'term' | 'type'>('term');
  return <section className="occurrence-guided" aria-label="Chosen occurrence guided reading">
    <div className="snapshot-tabs" role="tablist" aria-label="Occurrence reading target">{(['term', 'type'] as const).map(item => <button type="button" key={item} role="tab" aria-selected={target === item} onClick={() => setTarget(item)}>{item === 'term' ? 'Selected term' : 'Inferred type'}</button>)}</div>
    {onExposeDefinitionHead && <div className="head-exposure-action"><p>Expose one definition head of this {target === 'term' ? 'term' : 'type'}. This reruns the current Lean buffer; the original occurrence and its outcomes stay separate.</p><button type="button" className="toolbar-button" onClick={() => onExposeDefinitionHead(target)}>Expose definition head of {target}</button></div>}
    <div role="tabpanel" aria-label={target === 'term' ? 'Selected term reading' : 'Inferred type reading'}>
      <TargetReading key={`${value.captureId}:${JSON.stringify(value.path)}:${target}`} value={value} target={target}/>
    </div>
  </section>;
}
