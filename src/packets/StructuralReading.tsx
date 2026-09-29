import { useId, useMemo, useState, type ReactNode } from 'react';
import { createExactJsonTools, plainJsonData, type JsonValue } from './packet';
import { naturalText } from './natural';
import { nameText } from './syntax';
import type { ExternalStructuralDeclaration, PositionalStructuralDeclaration, PositionalStructuralDrawing,
  StructuralDeclaration, StructuralDrawing, StructuralEdge, StructuralLocalKind, StructuralNode, StructurePath } from './structure';
import { recordedEntryLabel, UNMATCHED_RECORDED_KINDS } from '../core/context-entry';
import './structural-reading.css';
import { counted } from '../core/counted';

const CHUNK_SIZE = 40;
const INITIAL_NODE_COUNT = 32;
export type StructuralReadingDrawing = StructuralDrawing | PositionalStructuralDrawing;
type ReadingDeclaration = StructuralDeclaration | PositionalStructuralDeclaration;

const constructorLabels: Record<string, string> = {
  bvar: 'Bound reference', fvar: 'Registered free reference', sort: 'Sort', const: 'Constant',
  lit: 'Literal', app: 'Application', lam: 'Lambda', forallE: 'Dependent product',
  letE: 'Let / have binding', proj: 'Projection',
};
const roleLabels: Record<string, string> = {
  function: 'Function', argument: 'Argument', domain: 'Domain', body: 'Body',
  type: 'Declared type', value: 'Defining value', projectedValue: 'Projected value',
  definitionValue: 'Defining value', storedValue: 'Stored value (not a defining equation)',
};
const fieldLabels: Record<string, string> = {
  constructor: 'Constructor',
  name: 'Structured name', userName: 'Structured user name', fvarId: 'Registry identity',
  level: 'Universe', levels: 'Ordered universe instances', binderInfo: 'Binder annotation',
  index: 'Index', fieldIndex: 'Field index', nondep: 'Original nondependent flag',
  literalKind: 'Literal kind', literalValue: 'Exact literal value',
  owner: 'Structured projection owner', field: 'Field index', literal: 'Exact literal', localKind: 'Local declaration kind',
};

function words(value: string): string { return value.replace(/([a-z])([A-Z])/g, '$1 $2').replace(/^./, first => first.toUpperCase()); }
function exactName(value: unknown): string | undefined {
  try { return nameText(value as JsonValue); } catch { return undefined; }
}
function exactInscription(value: string | StructurePath): string {
  // Encode UTF-16 units without normalizing: invisible characters, combining
  // spellings and both halves of a non-BMP pair remain visibly distinguishable.
  return JSON.stringify(value).replace(/[\u007f-\uffff]/g, character => `\\u${character.charCodeAt(0).toString(16).padStart(4, '0')}`);
}
function readableInscription(value: string): string {
  // Keep ordinary RTL scripts readable; explicit direction controls must not
  // reorder even the text inside an isolated inscription.
  return value.replace(/[\u061c\u200e\u200f\u202a-\u202e\u2066-\u206f]/g,
    character => `\\u${character.charCodeAt(0).toString(16).padStart(4, '0')}`);
}

/** The inspector exposes scalar fields as labelled structure, including the
 * difference between numeric and string Name components and all universe roles. */
export function StructuralFieldValue({ value, depth = 0 }: { value: unknown; depth?: number }): ReactNode {
  if (value === null) return <code>null</code>;
  if (typeof value === 'string') return <code className="struct-exact-text">{exactInscription(value)}</code>;
  if (typeof value === 'number' || typeof value === 'boolean') return <code>{String(value)}</code>;
  if (Array.isArray(value)) {
    const constructor = typeof value[0] === 'string' ? value[0] : undefined;
    const forms: Record<string, { label: string; roles: string[] }> = {
      nat: { label: 'Exact natural number', roles: ['Decimal digits'] },
      anonymous: { label: 'Anonymous name root', roles: [] },
      str: { label: 'String name component', roles: ['Parent name', 'String component'] },
      num: { label: 'Numeric name component', roles: ['Parent name', 'Numeric component'] },
      zero: { label: 'Universe zero', roles: [] },
      succ: { label: 'Successor universe', roles: ['Predecessor'] },
      max: { label: 'Maximum universe', roles: ['First operand', 'Second operand'] },
      imax: { label: 'Impredicative maximum universe', roles: ['First operand', 'Second operand'] },
      param: { label: 'Named universe parameter', roles: ['Structured name'] },
      natVal: { label: 'Natural literal', roles: ['Exact value'] },
      strVal: { label: 'String literal', roles: ['Exact value'] },
    };
    const form = constructor ? forms[constructor] : undefined;
    if (form && value.length === form.roles.length + 1) return <div data-field-constructor={constructor} className={depth >= 4 ? 'struct-field-deep' : undefined}><span className="struct-field-tag">{form.label}</span>{form.roles.length > 0 && <div className="struct-field-children">{form.roles.map((role, index) => <div key={role}><span>{role}</span><StructuralFieldValue value={value[index + 1]} depth={depth + 1}/></div>)}</div>}</div>;
    return value.length ? <ol className="struct-fields" start={0}>{value.map((item, index) => <li key={index}><StructuralFieldValue value={item} depth={depth + 1}/></li>)}</ol> : <span className="struct-empty-list">Empty ordered list</span>;
  }
  if (typeof value === 'object') return <dl>{Object.entries(value).map(([key, item]) => <div key={key}><dt>{fieldLabels[key] ?? words(key)}</dt><dd><StructuralFieldValue value={item} depth={depth + 1}/></dd></div>)}</dl>;
  return <span>Unavailable</span>;
}

function nodeFields(node: StructuralNode): Record<string, unknown> {
  switch (node.kind) {
    case 'bvar': return { index: node.index };
    case 'fvar': return { fvarId: node.fvarId };
    case 'sort': return { level: node.level };
    case 'const': return { name: node.name, levels: node.levels };
    case 'lit': return { literal: node.literal };
    case 'lam': case 'forallE': return { name: node.name, binderInfo: node.binderInfo };
    case 'letE': return { name: node.name, nondep: node.nondep };
    case 'proj': return { owner: node.owner, field: node.field };
    case 'app': return {};
  }
}

/** The same attached field view is used in node inspectors and their tests. */
export function StructuralNodeFields({ node }: { node: StructuralNode }) {
  return <dl>{Object.entries(nodeFields(node)).map(([key, value]) => <div key={key}><dt>{fieldLabels[key] ?? words(key)}</dt><dd><StructuralFieldValue value={value}/></dd></div>)}</dl>;
}

function Inspector({ path, children, onSourceSelect }: { path: StructurePath; children: ReactNode; onSourceSelect?: (path: StructurePath) => void }) {
  const [open, setOpen] = useState(false);
  return <details className="struct-inspector" onToggle={event => setOpen(event.currentTarget.open)}><summary>Exact fields and source position</summary>{open && <><p>Escaped strings preserve invisible characters and exact Unicode spelling.</p>{children}<dl><dt>Constructor path</dt><dd><code>{exactInscription(path)}</code></dd></dl>{onSourceSelect && <button type="button" className="quiet-button" onClick={() => onSourceSelect([...path])}>Inspect this exact source position</button>}</>}</details>;
}

function roots(drawing: StructuralReadingDrawing): string[] {
  const declarations = new Map<string, ReadingDeclaration>(drawing.declarations.map(declaration => [declaration.id, declaration]));
  const contextIds = drawing.schema === 'definograph.structure.positional.v1' ? drawing.contextDeclarationIds : drawing.externalDeclarationIds;
  return [...contextIds.flatMap(id => {
    const declaration = declarations.get(id);
    return declaration?.kind === 'external' || declaration?.kind === 'positional' ? declaration.children.map(edge => edge.nodeId) : [];
  }), drawing.rootId, ...(drawing.schema === 'definograph.structure.positional.v1' ? [drawing.typeRootId] : [])];
}

/** Expand only this branch, in source child order. No unrelated folded branch
 * consumes its budget. Used both by the controls and deterministic fold checks. */
export function expandStructuralBranch(drawing: StructuralReadingDrawing, visible: ReadonlySet<string>, rootId: string, budget = CHUNK_SIZE): Set<string> {
  const byId = new Map(drawing.nodes.map(node => [node.id, node]));
  const next = new Set(visible), pending = [rootId];
  let added = 0;
  while (pending.length && added < budget) {
    const id = pending.pop()!, node = byId.get(id);
    if (!node) continue;
    if (!next.has(id)) { next.add(id); added++; }
    for (let index = node.children.length - 1; index >= 0; index--) pending.push(node.children[index].nodeId);
  }
  return next;
}

function initialVisibility(drawing: StructuralReadingDrawing, limit: number): Set<string> {
  let visible = new Set<string>();
  for (const rootId of roots(drawing)) visible = expandStructuralBranch(drawing, visible, rootId, Math.max(0, limit - visible.size));
  return visible;
}

export interface StructuralReadingProps {
  drawing: StructuralReadingDrawing;
  selectedPath?: readonly (string | number)[];
  onSourceSelect?: (path: StructurePath) => void;
  /** Initial presentation bound; later expansion always occurs in finite chunks. */
  initialNodeLimit?: number;
  /** Display labels only; term/type roots, paths and readback remain unchanged. */
  positionalRootTitles?: { term: string; type: string };
  /** The captured context's declarations, oldest first. Their recorded kinds label the leading positional context
   * entries; entries entered later by a selection or focus have none. */
  recordedContext?: readonly RecordedContextEntry[];
}
/** A captured declaration: its exact recorded name, used only to check alignment, and its recorded kind. */
export interface RecordedContextEntry { readonly name: JsonValue; readonly kind: StructuralLocalKind }

/** Headings chosen by recorded kind, one per positional context entry, or undefined where the constructor heading
 * stays (no record given, an ordinary kind, or an entry entered after the captured context). The kinds apply only
 * when the leading entries carry exactly the recorded names, in order; the names check alignment and never choose
 * a heading. Without that alignment no entry can be matched to its record, so every entry reads neutrally. */
export function recordedContextHeadings(drawing: PositionalStructuralDrawing, recorded?: readonly RecordedContextEntry[]): (string | undefined)[] | undefined {
  if (!recorded) return undefined;
  const aligned = recordedContextAligned(drawing, recorded);
  return drawing.contextDeclarationIds.map((_, position) => aligned ? recordedEntryLabel(recorded[position]?.kind) : 'Context entry');
}
/** Whether the leading context entries carry exactly the recorded names, in order. Each supplied name must be plain
 * JSON data before it is compared. */
export function recordedContextAligned(drawing: PositionalStructuralDrawing, recorded: readonly RecordedContextEntry[]): boolean {
  const declarations = new Map(drawing.declarations.map(declaration => [declaration.id, declaration]));
  const entries = drawing.contextDeclarationIds.map(id => declarations.get(id));
  if (recorded.length > entries.length) return false;
  try {
    const { canonical } = createExactJsonTools();
    return recorded.every((entry, position) => {
      const declaration = entries[position];
      return declaration?.kind === 'positional' && plainJsonData(entry.name) && canonical(declaration.name as JsonValue) === canonical(entry.name);
    });
  } catch { return false; }
}

/** Constructor structure only. A reference link records declaration identity;
 * neither that link nor the drawing asserts typing or mathematical evidence. */
export function StructuralReading({ drawing, selectedPath, onSourceSelect, initialNodeLimit = INITIAL_NODE_COUNT, positionalRootTitles, recordedContext }: StructuralReadingProps) {
  const prefix = useId();
  const initialLimit = Math.min(200, Math.max(1, Number.isSafeInteger(initialNodeLimit) ? initialNodeLimit : INITIAL_NODE_COUNT));
  const initial = useMemo(() => initialVisibility(drawing, initialLimit), [drawing, initialLimit]);
  const [state, setState] = useState({ drawing, visible: initial });
  const [focused, setFocused] = useState<{ drawing: StructuralReadingDrawing; id: string }>();
  const visible = state.drawing === drawing ? state.visible : initial;
  const index = useMemo(() => {
    const nodes = new Map(drawing.nodes.map(node => [node.id, node]));
    const declarations = new Map<string, ReadingDeclaration>(drawing.declarations.map(declaration => [declaration.id, declaration]));
    const numbers = new Map(drawing.declarations.map((declaration, position) => [declaration.id, position + 1]));
    const parents = new Map<string, string>();
    drawing.nodes.forEach(node => node.children.forEach(edge => parents.set(edge.nodeId, node.id)));
    const references = new Map<string, number>();
    drawing.nodes.forEach(node => { if (node.kind === 'bvar' || node.kind === 'fvar') references.set(node.declarationId, (references.get(node.declarationId) ?? 0) + 1); });
    const counts = new Map<string, number>();
    function count(id: string): number {
      const known = counts.get(id); if (known !== undefined) return known;
      const value = 1 + (nodes.get(id)?.children.reduce((total, edge) => total + count(edge.nodeId), 0) ?? 0);
      counts.set(id, value); return value;
    }
    roots(drawing).forEach(count);
    return { nodes, declarations, numbers, parents, counts, references };
  }, [drawing]);
  const contextHeadings = useMemo(() => drawing.schema === 'definograph.structure.positional.v1' ? recordedContextHeadings(drawing, recordedContext) : undefined, [drawing, recordedContext]);
  const contextUnmatched = drawing.schema === 'definograph.structure.positional.v1' && !!recordedContext && !!contextHeadings && !recordedContextAligned(drawing, recordedContext);
  function declarationLabel(declaration: ReadingDeclaration): ReactNode {
    const node = declaration.kind === 'binder' || declaration.kind === 'let' ? index.nodes.get(declaration.nodeId) : undefined;
    const name = declaration.kind === 'external' ? exactName(declaration.userName) : declaration.kind === 'positional'
      ? exactName(declaration.name) : node && 'name' in node ? exactName(node.name) : undefined;
    return <><bdi dir="auto">{readableInscription(name ?? '(name in exact fields)')}</bdi><span> · declaration {index.numbers.get(declaration.id)}</span></>;
  }
  function nodeLabel(node: StructuralNode): ReactNode {
    if ('name' in node) return <bdi dir="auto">{readableInscription(exactName(node.name) ?? '(name in exact fields)')}</bdi>;
    if (node.kind === 'proj') return <><bdi dir="auto">{readableInscription(exactName(node.owner) ?? '(owner in exact fields)')}</bdi><span> · field {naturalText(node.field)}</span></>;
    if (node.kind === 'lit') return <bdi dir="auto">{readableInscription(node.literal[0] === 'strVal' ? JSON.stringify(node.literal[1]) : naturalText(node.literal[1]))}</bdi>;
    if (node.kind === 'bvar' || node.kind === 'fvar') {
      const declaration = index.declarations.get(node.declarationId);
      return declaration ? declarationLabel(declaration) : 'Unresolved declaration';
    }
    return null;
  }
  function declarationDomId(id: string): string { return `${prefix}-declaration-${index.numbers.get(id)}`; }
  function selectNode(node: StructuralNode) {
    setFocused({ drawing, id: node.id }); onSourceSelect?.([...node.sourcePath]);
  }
  function revealDeclaration(declaration: ReadingDeclaration) {
    if (declaration.kind === 'external' || declaration.kind === 'positional') {
      setFocused({ drawing, id: declaration.id }); onSourceSelect?.([...declaration.sourcePath]);
    } else {
      const node = index.nodes.get(declaration.nodeId);
      if (!node) return;
      const next = new Set(visible);
      let cursor: string | undefined = node.id;
      while (cursor) { next.add(cursor); cursor = index.parents.get(cursor); }
      setState({ drawing, visible: next }); selectNode(node);
    }
    // Declaration cards are ancestors or surrounding-context cards, so already
    // mounted when their references are visible. The link never follows a name.
    document.getElementById(declarationDomId(declaration.id))?.scrollIntoView({ block: 'nearest' });
  }
  function selected(path: StructurePath, id: string): boolean {
    return selectedPath ? path.length === selectedPath.length && path.every((part, position) => part === selectedPath[position])
      : focused?.drawing === drawing && focused.id === id;
  }
  function reference(node: StructuralNode): ReactNode {
    if (node.kind !== 'bvar' && node.kind !== 'fvar') return null;
    const declaration = index.declarations.get(node.declarationId);
    return declaration ? <div className="struct-reference" data-reference-target={declaration.id}><span>Refers to</span><button type="button" aria-controls={declarationDomId(declaration.id)} onClick={() => revealDeclaration(declaration)}>{declarationLabel(declaration)}</button>{node.kind === 'bvar' && <span>Bound position {node.index}</span>}</div>
      : <p className="struct-reference-unavailable">The referenced declaration is unavailable.</p>;
  }
  function renderPorts(edges: StructuralEdge[], depth: number, binder?: ReadingDeclaration, owner?: StructuralNode) {
    return <ol className="struct-ports">{edges.map((edge, position) => {
      const body = edge.role === 'body' && binder;
      const label = owner?.kind === 'proj' && edge.role === 'value' ? 'Projected value' : owner?.kind === 'letE' && edge.role === 'value' ? 'Bound value' : roleLabels[edge.role] ?? words(edge.role);
      return <li className="struct-port" data-role={edge.role} data-parent-node={owner?.id} data-child-node={edge.nodeId} data-port-order={position + 1} key={edge.role}><div className="struct-port-label"><span className="struct-port-number">{position + 1}</span>{label}</div>{body ? <section className="struct-scope-region" data-body-home={binder.bodyHomeId}><p>Body scope includes {declarationLabel(binder)}.</p>{renderNode(edge.nodeId, depth + 1)}</section> : renderNode(edge.nodeId, depth + 1)}</li>;
    })}</ol>;
  }
  function renderNode(id: string, depth: number): ReactNode {
    const node = index.nodes.get(id);
    if (!node) return <p className="struct-error">The source structure is incomplete at this connection.</p>;
    if (!visible.has(id)) return <div className="struct-fold" data-fold-root={id} data-fold-count={index.counts.get(id)}><strong>{constructorLabels[node.kind]} — folded branch</strong><p>{index.counts.get(id)} constructor node{index.counts.get(id) === 1 ? '' : 's'} hidden in this exact scope.</p><button type="button" className="toolbar-button" onClick={() => setState({ drawing, visible: expandStructuralBranch(drawing, visible, id) })}>Show next {counted(Math.min(CHUNK_SIZE, index.counts.get(id) ?? 1), 'node')} in this branch</button></div>;
    const binder = node.kind === 'lam' || node.kind === 'forallE' || node.kind === 'letE' ? index.declarations.get(node.declarationId) : undefined;
    const inscription = nodeLabel(node);
    return <article className="struct-node" data-node-id={node.id} data-constructor={node.kind} data-home={node.homeId} data-selected={selected(node.sourcePath, node.id)} data-deep={depth >= 4} id={binder ? declarationDomId(binder.id) : undefined}>
      <header className="struct-node-heading"><strong>{constructorLabels[node.kind]}</strong>{inscription && <span className="struct-inscription">{inscription}</span>}{binder && <span className="struct-declaration">Declaration {index.numbers.get(binder.id)}</span>}<button type="button" className="quiet-button" onClick={() => selectNode(node)}>Select source</button></header>
      <div className="struct-node-content">{reference(node)}{binder && <p className="struct-scope-summary">{node.kind === 'letE' ? 'The type and value use the enclosing scope. This binding enters scope only in the body.' : 'The domain uses the enclosing scope. This binder enters scope only in the body.'}</p>}{node.children.length > 0 && renderPorts(node.children, depth, binder, node)}
        <Inspector path={node.sourcePath} onSourceSelect={onSourceSelect}><StructuralNodeFields node={node}/></Inspector>
      </div>
    </article>;
  }
  function external(declaration: ExternalStructuralDeclaration): ReactNode {
    const fields = { constructor: declaration.constructor, userName: declaration.userName, fvarId: declaration.fvarId, index: declaration.index, localKind: declaration.localKind,
      ...(declaration.constructor === 'cdecl' ? { binderInfo: declaration.binderInfo } : { nondep: declaration.nondep }) };
    return <article className="struct-node" id={declarationDomId(declaration.id)} data-external-declaration={declaration.id} data-selected={selected(declaration.sourcePath, declaration.id)} key={declaration.id}>
      <header className="struct-node-heading"><strong>{recordedEntryLabel(declaration.localKind) ?? (declaration.constructor === 'cdecl' ? 'Registered declaration' : declaration.nondep ? 'Registered opaque local' : 'Registered local definition')}</strong><span className="struct-inscription">{declarationLabel(declaration)}</span><button type="button" className="quiet-button" onClick={() => { setFocused({ drawing, id: declaration.id }); onSourceSelect?.([...declaration.sourcePath]); }}>Select source</button></header>
      <div className="struct-node-content"><p className="struct-scope-summary">{declaration.constructor === 'cdecl' ? 'Its type uses the earlier registered context.' : declaration.nondep ? 'Its type and stored value use the earlier registered context. The stored value is metadata, not a defining equation.' : 'Its type and defining value use the earlier registered context.'}</p>{renderPorts(declaration.children, 0)}<Inspector path={declaration.sourcePath} onSourceSelect={onSourceSelect}><StructuralFieldValue value={fields}/></Inspector></div>
    </article>;
  }
  function positional(declaration: PositionalStructuralDeclaration, position: number): ReactNode {
    return <article className="struct-node" id={declarationDomId(declaration.id)} data-context-declaration={declaration.id}
      data-context-position={position + 1} data-home={declaration.homeId} data-context-body-home={declaration.bodyHomeId}
      data-reference-count={index.references.get(declaration.id) ?? 0} data-selected={selected(declaration.sourcePath, declaration.id)} key={declaration.id}>
      <header className="struct-node-heading"><strong>{contextHeadings?.[position] ?? (declaration.constructor === 'port' ? 'Context parameter' : 'Context definition')}</strong><span className="struct-inscription">{declarationLabel(declaration)}</span><span className="struct-context-position">Context entry {position + 1}</span><button type="button" className="quiet-button" onClick={() => { setFocused({ drawing, id: declaration.id }); onSourceSelect?.([...declaration.sourcePath]); }}>Select source</button></header>
      <div className="struct-node-content"><p className="struct-scope-summary">{declaration.constructor === 'port' ? 'Its type uses only the preceding context.' : 'Its type and defining value use only the preceding context. This entry retains its defining equation.'}</p>{renderPorts(declaration.children, 0)}
        {!index.references.has(declaration.id) && <p className="struct-unused-context">No references to this entry in the drawing.</p>}
        <Inspector path={declaration.sourcePath} onSourceSelect={onSourceSelect}><PositionalDeclarationFields declaration={declaration}/></Inspector>
      </div>
    </article>;
  }
  const isPositional = drawing.schema === 'definograph.structure.positional.v1';
  return <section className="structural-reading" data-positional={isPositional || undefined} aria-label={isPositional ? positionalRootTitles ? 'Exact positional structure' : 'Exact selected structure' : 'Exact source structure'}><header><div><h3>{isPositional ? positionalRootTitles ? 'Positional expression structure' : 'Selected occurrence structure' : 'Source structure'}</h3><p>{isPositional ? positionalRootTitles ? 'Constructor roles in both expression roots and their shared context.' : 'Constructor roles in the selected term, its inferred type, and their shared context.' : 'Constructor roles and lexical scopes of the imported expression.'} This drawing does not assert typing or evidence.</p></div><button type="button" className="toolbar-button" onClick={() => { setState({ drawing, visible: initial }); setFocused(undefined); }}>Reset folds</button></header>
    <div className="struct-legend"><span><i/>Ordered constructor connection</span><span><i data-kind="reference"/>Declaration reference, not a mathematical arrow</span></div>
    <div className="struct-canvas">{drawing.schema === 'definograph.structure.positional.v1' ? <>
      <section className="struct-positional-context" aria-label="Surrounding context" data-complete-home={drawing.rootHomeId}><h4>Surrounding context, oldest first</h4><p>{drawing.contextDeclarationIds.length === 1 ? 'The 1 context entry is retained, even if it is unused.' : drawing.contextDeclarationIds.length ? `All ${drawing.contextDeclarationIds.length} context entries are retained, including unused entries.` : 'Empty surrounding context.'} {positionalRootTitles ? 'Both expression roots use this complete context.' : 'The selected term and inferred type use this complete context.'}</p>{contextUnmatched && <p className="struct-context-note" data-recorded-kinds-unmatched="">{UNMATCHED_RECORDED_KINDS}</p>}{drawing.contextDeclarationIds.map((id, position) => { const declaration = index.declarations.get(id); return declaration?.kind === 'positional' ? positional(declaration, position) : <p className="struct-error" key={id}>Context entry unavailable.</p>; })}</section>
      <div className="struct-positional-roots"><section className="struct-root-section" aria-label={positionalRootTitles?.term ?? 'Selected term'} data-structure-root="term" data-root-home={drawing.rootHomeId}><h4>{positionalRootTitles?.term ?? 'Selected term'}</h4>{renderNode(drawing.rootId, 0)}</section><section className="struct-root-section" aria-label={positionalRootTitles?.type ?? 'Inferred type'} data-structure-root="type" data-root-home={drawing.rootHomeId}><h4>{positionalRootTitles?.type ?? 'Inferred type'}</h4>{renderNode(drawing.typeRootId, 0)}</section></div>
    </> : <>{drawing.externalDeclarationIds.length > 0 && <section className="struct-registered-context" aria-label="Registered context"><h4>Registered context, oldest first</h4>{drawing.externalDeclarationIds.map(id => { const declaration = index.declarations.get(id); return declaration?.kind === 'external' ? external(declaration) : <p className="struct-error" key={id}>Registered declaration unavailable.</p>; })}</section>}{renderNode(drawing.rootId, 0)}</>}</div>
    <p className="struct-view-count">{visible.size} of {counted(drawing.nodes.length, 'constructor node')} shown. Folded branches retain their exact source positions and scopes.</p>
  </section>;
}

/** Exact context fields accompany the same cards targeted by bound references. */
export function PositionalDeclarationFields({ declaration }: { declaration: PositionalStructuralDeclaration }) {
  return <StructuralFieldValue value={{ constructor: declaration.constructor, name: declaration.name,
    ...(declaration.constructor === 'port' ? { binderInfo: declaration.binderInfo } : { nondep: declaration.nondep }) }}/>;
}
