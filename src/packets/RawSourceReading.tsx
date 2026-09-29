import { useMemo, useState, type ReactNode } from 'react';
import { readRawInspection, type RawInspectionDrawing, type RawNode } from './raw';
import { StructuralFieldValue } from './StructuralReading';
import './raw-source-reading.css';
import { counted } from '../core/counted';

const CHUNK = 40;
const labels: Record<string, string> = {
  expression: 'Expression', expressions: 'Ordered expressions', level: 'Universe level', literal: 'Literal', metadata: 'Metadata',
  dataValue: 'Metadata value', integer: 'Integer', syntax: 'Syntax', sourceInfo: 'Source information',
  substring: 'Raw substring', preresolved: 'Preresolution', localDeclaration: 'Original local declaration',
  frame: 'Source frame', levels: 'Ordered universe levels', syntaxList: 'Ordered syntax children',
  preresolutions: 'Ordered preresolutions', strings: 'Ordered strings', declarations: 'Original local declarations',
  metadataEntries: 'Ordered metadata entries', metadataEntry: 'Metadata entry', string: 'String',
};
function words(value: string): string { return value.replace(/([a-z])([A-Z])/g, '$1 $2').replace(/^./, first => first.toUpperCase()); }

/** Each expansion is bounded independently of the length of a collection. */
export function expandRawBranch(drawing: RawInspectionDrawing, visible: ReadonlySet<string>, rootId: string, limit = CHUNK): Set<string> {
  const nodes = new Map(drawing.nodes.map(node => [node.id, node]));
  const next = new Set(visible), pending = [rootId];
  let added = 0;
  while (pending.length && added < limit) {
    const id = pending.pop()!, node = nodes.get(id);
    if (!node) continue;
    if (!next.has(id)) { next.add(id); added++; }
    for (let i = node.children.length - 1; i >= 0; i--) pending.push(node.children[i].nodeId);
  }
  return next;
}

function Fields({ node }: { node: RawNode }) {
  const [open, setOpen] = useState(false);
  return <details className="struct-inspector" onToggle={event => setOpen(event.currentTarget.open)}>
    <summary>Exact fields and constructor path ({counted(node.fields.length, 'field')})</summary>
    {open && <><p>Strings use escaped Unicode spelling. Numeric references and byte positions are retained as data.</p>
      <dl>{node.fields.map(field => <div key={field.role}><dt>{words(field.role)}</dt><dd data-raw-field={field.role}><StructuralFieldValue value={field.value}/></dd></div>)}
        <div><dt>Constructor path</dt><dd><StructuralFieldValue value={node.sourcePath}/></dd></div></dl></>}
  </details>;
}

export interface RawNodeAction { label: string; selected: boolean; onClick(): void }

/** Raw constructor data has no declaration links, scopes or evidence outcomes.
 * A caller can select exact constructors without changing their interpretation. */
export function RawSourceReading({ drawing, nodeAction }: { drawing: RawInspectionDrawing; nodeAction?: (node: RawNode) => RawNodeAction | undefined }) {
  const checked = useMemo(() => readRawInspection(drawing), [drawing]);
  const initial = useMemo(() => checked.ok ? expandRawBranch(drawing, new Set(), drawing.rootId, 32) : new Set<string>(), [drawing, checked]);
  const [state, setState] = useState({ drawing, visible: initial, childLimits: new Map<string, number>() });
  const current = state.drawing === drawing ? state : { drawing, visible: initial, childLimits: new Map<string, number>() };
  const nodes = useMemo(() => new Map(drawing.nodes.map(node => [node.id, node])), [drawing]);
  if (!checked.ok) return <p className="packet-boundary" role="alert">Raw source data unavailable: {checked.error.message}</p>;
  function renderNode(id: string, depth: number): ReactNode {
    const node = nodes.get(id)!;
    if (!current.visible.has(id)) return <div className="struct-fold" data-raw-fold={id}>
      <strong>{labels[node.family]} · {node.tag}</strong><p>Folded constructor branch.</p>
      <button className="toolbar-button" type="button" onClick={() => setState({ ...current, visible: expandRawBranch(drawing, current.visible, id) })}>Show next constructors in this branch</button>
    </div>;
    const childLimit = current.childLimits.get(id) ?? CHUNK;
    const action = nodeAction?.(node);
    return <article className="struct-node" data-raw-family={node.family} data-raw-constructor={node.tag} data-deep={depth >= 4} data-raw-selected={action?.selected || undefined}>
      <header className="struct-node-heading"><strong>{labels[node.family] ?? words(node.family)}</strong><code>{node.tag}</code></header>
      <div className="struct-node-content">
        {action && <button type="button" className="toolbar-button raw-node-action" aria-pressed={action.selected} aria-label={`${action.label}: ${node.tag} at ${JSON.stringify(node.sourcePath)}`} onClick={action.onClick}>{action.selected ? 'Chosen occurrence' : action.label}</button>}
        {(node.tag === 'bvar' || node.tag === 'fvar' || node.tag === 'mvar') && <p>Stored reference identifier; no declaration is resolved in this view.</p>}
        {node.family === 'integer' && node.tag === 'negSucc' && <p>The stored natural n represents the negative integer −(n + 1).</p>}
        {node.family === 'substring' && <p>Complete backing string and original byte positions. Positions are not applied to the string.</p>}
        <Fields node={node}/>
        {node.children.length > 0 && <ol className="struct-ports">{node.children.slice(0, childLimit).map((edge, position) => <li className="struct-port" key={`${edge.role}:${position}`} data-raw-role={edge.role} data-raw-order={position}>
          <div className="struct-port-label"><span className="struct-port-number">{position + 1}</span>{words(edge.role)}{edge.ordinal !== undefined && <span> · index {edge.ordinal}</span>}</div>
          {renderNode(edge.nodeId, depth + 1)}
        </li>)}</ol>}
        {node.children.length > childLimit && <div className="struct-fold"><p>{counted(node.children.length - childLimit, 'further ordered child', 'further ordered children')} {node.children.length - childLimit === 1 ? 'is' : 'are'} folded.</p><button type="button" className="toolbar-button" onClick={() => {
          const childLimits = new Map(current.childLimits); childLimits.set(id, childLimit + CHUNK);
          setState({ ...current, childLimits });
        }}>Show next {counted(Math.min(CHUNK, node.children.length - childLimit), 'child position')}</button></div>}
        {!node.children.length && !node.fields.length && <p>No fields or children.</p>}
      </div>
    </article>;
  }
  return <section className="structural-reading raw-source-reading" aria-label="Raw source data" data-raw-schema={drawing.schema}>
    <header><div><h3>Raw source data</h3><p>Exact constructor readback checked. This view records data without checking scope, typing or mathematical validity.</p></div>
      <button type="button" className="quiet-button" onClick={() => setState({ drawing, visible: initial, childLimits: new Map() })}>Reset folds</button></header>
    <p className="raw-order-note">Child order and repeated entries are preserved. Each constructor is labelled by its data family.</p>
    <div className="struct-canvas">{renderNode(drawing.rootId, 0)}</div>
    <p className="struct-view-count">{counted(drawing.nodes.length, 'constructor node')} retained. Folded branches remain in the checked drawing.</p>
  </section>;
}
