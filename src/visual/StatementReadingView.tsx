import { useEffect, useLayoutEffect, useMemo, useRef, useState, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import type { ReadingBinder, ReadingDocument, ReadingNode, ReadingPanel, ReadingStep } from '../reading/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { compactLabel } from './layout';
import './statement-reading.css';

export interface StatementReadingViewProps {
  reading: ReadingDocument;
  document: SemanticDocument;
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
  onNodeSelect?: (id: string) => void;
  /** Return null when this clause has no faithful symbolic geometric rendering. */
  renderGeometry?: (panel: ReadingPanel) => ReactNode;
}

const palette = ['#497c72', '#927044', '#667da5', '#92759c', '#ad7063', '#6d8555', '#4c8197', '#977d5b'];
export function readingObjectColor(id: string): string {
  let hash = 0;
  for (let index = 0; index < id.length; index++) hash = (Math.imul(hash, 31) + id.charCodeAt(index)) | 0;
  return palette[(hash >>> 0) % palette.length];
}
const roleText: Record<ReadingBinder['role'], string> = { universal: 'For every', existential: 'There is', parameter: 'Given parameter', lambda: 'For input', assumption: 'Assuming' };
const roleSymbol: Record<ReadingBinder['role'], string> = { universal: '∀', existential: '∃', parameter: '↦', lambda: '↦', assumption: '⇒' };
type Maps = { objects: Map<string, SemanticObject>; relations: Map<string, SemanticRelation>; panels: Map<string, ReadingPanel> };
type RenderContext = StatementReadingViewProps & Maps & { visibleNodes: Set<string> };

function keyActivate(event: KeyboardEvent<SVGGElement>, action?: () => void) {
  if (action && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); action(); }
}

function FigureObject({ id, ctx, children, title }: { id?: string; ctx: RenderContext; children: ReactNode; title?: string }) {
  const object = id ? ctx.objects.get(id) : undefined;
  const actionable = Boolean(object && ctx.onObjectSelect);
  const color = id ? readingObjectColor(id) : '#82918f';
  return <g className={`sr-figure-object${id === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} style={{ '--object-color': color } as CSSProperties} data-reading-object={id} role={actionable ? 'button' : 'group'} tabIndex={actionable ? 0 : undefined} aria-label={object ? `${object.label}${object.type ? ` : ${object.type}` : ''}` : title} aria-pressed={actionable ? id === ctx.selectedObjectId : undefined} onClick={() => { if (id) ctx.onObjectSelect?.(id); }} onKeyDown={event => keyActivate(event, actionable && id ? () => ctx.onObjectSelect?.(id) : undefined)}>
    <title>{`${title ?? object?.label ?? ''}${object?.type ? ` : ${object.type}` : ''}`}</title>{children}
  </g>;
}

function ObjectName({ id, x, y, ctx, max = 24, anchor = 'middle' }: { id?: string; x: number; y: number; ctx: RenderContext; max?: number; anchor?: 'start' | 'middle' | 'end' }) {
  const object = id ? ctx.objects.get(id) : undefined;
  return <text x={x} y={y} textAnchor={anchor} className="sr-object-label">{compactLabel(object?.label ?? 'unspecified', max)}</text>;
}

function Region({ id, x, y, width, height, ctx, children, labelTop = true }: { id?: string; x: number; y: number; width: number; height: number; ctx: RenderContext; children?: ReactNode; labelTop?: boolean }) {
  return <><FigureObject id={id} ctx={ctx}><ellipse cx={x} cy={y} rx={width / 2} ry={height / 2} className="sr-set-outline"/><ObjectName id={id} x={x} y={labelTop ? y - height / 2 + 25 : y + height / 2 - 15} ctx={ctx} max={Math.min(24, Math.floor(width / 10))}/></FigureObject>{children}</>;
}

function NamedPoint({ id, x, y, ctx, labelY = 24 }: { id?: string; x: number; y: number; ctx: RenderContext; labelY?: number }) {
  return <FigureObject id={id} ctx={ctx}><circle cx={x} cy={y} r="6" className="sr-named-point"/><circle cx={x} cy={y} r="16" fill="transparent"/><ObjectName id={id} x={x} y={y + labelY} ctx={ctx} max={Math.min(30, Math.max(8, Math.floor(Math.min(x, 500 - x) * 2 / 9) - 2))}/></FigureObject>;
}

function FigureArrow({ from, to, bend = 0, label, ctx }: { from: [number, number]; to: [number, number]; bend?: number; label?: string; ctx: RenderContext }) {
  const mid = (from[0] + to[0]) / 2;
  const y = (from[1] + to[1]) / 2 + bend;
  const direction = to[0] >= from[0] ? 1 : -1;
  return <><path d={`M ${from[0]} ${from[1]} Q ${mid} ${y + bend} ${to[0]} ${to[1]}`} className="sr-map-arrow"/><path d={`M ${to[0] - direction * 7} ${to[1] - 4} L ${to[0]} ${to[1]} L ${to[0] - direction * 7} ${to[1] + 4}`} className="sr-map-arrow"/>{label && <FigureObject id={label} ctx={ctx}><ObjectName id={label} x={mid} y={y - 12} ctx={ctx} max={22}/></FigureObject>}</>;
}

function port(relation: SemanticRelation, role: string): string | undefined { return relation.ports.find(candidate => candidate.role === role)?.objectId; }
function producedBy(id: string | undefined, relations: readonly SemanticRelation[]) { return id ? relations.find(relation => relation.ports.some(p => ['output', 'result', 'region', 'distance'].includes(p.role) && p.objectId === id)) : undefined; }

/** Expand a bounded map path; unexpanded subexpressions remain explicit objects. */
export function expressionMapPath(objectId: string, relations: readonly SemanticRelation[], depth = 0): { inputs: string[]; maps: string[]; output: string; collapsed: boolean } {
  const application = producedBy(objectId, relations);
  const fallback = { inputs: [objectId], maps: [], output: objectId, collapsed: Boolean(application?.kind === 'application') };
  if (application?.kind !== 'application' || depth >= 3) return fallback;
  const fn = port(application, 'function');
  const inputs = application.ports.filter(p => p.role.startsWith('input')).map(p => p.objectId);
  if (!fn || !inputs.length || inputs.length > 3) return fallback;
  if (inputs.length > 1) return { inputs, maps: [fn], output: objectId, collapsed: inputs.some(id => producedBy(id, relations)?.kind === 'application') };
  const inner = expressionMapPath(inputs[0], relations, depth + 1);
  return { inputs: inner.inputs, maps: [...inner.maps, fn], output: objectId, collapsed: inner.collapsed };
}

function ExpressionPath({ objectId, relations, y, ctx }: { objectId: string; relations: readonly SemanticRelation[]; y: number; ctx: RenderContext }) {
  const path = expressionMapPath(objectId, relations);
  if (!path.maps.length) return <FigureObject id={objectId} ctx={ctx}><rect x="62" y={y - 28} width="357" height="56" rx="13" className="sr-expression-box"/><ObjectName id={objectId} x={240} y={y + 6} ctx={ctx} max={41}/></FigureObject>;
  const positions = path.maps.map((_, index) => 170 + index * 174 / Math.max(1, path.maps.length - 1));
  const lastMap = positions.at(-1)!;
  return <g className="sr-expression-path" data-expression-output={objectId}>
    {path.inputs.length === 1 ? <NamedPoint id={path.inputs[0]} x={62} y={y} ctx={ctx} labelY={24}/> : <>{path.inputs.map((input, index) => <FigureObject key={`${input}:${index}`} id={input} ctx={ctx}><text x="14" y={y - 15 * (path.inputs.length - 1) + index * 30 + 6} className="sr-input-index">{index + 1}</text><ObjectName id={input} x={76} y={y - 15 * (path.inputs.length - 1) + index * 30 + 6} ctx={ctx} max={12}/></FigureObject>)}</>}
    <FigureArrow from={[path.inputs.length === 1 ? 80 : 120, y]} to={[positions[0] - 32, y]} ctx={ctx}/>
    {path.maps.map((fn, index) => <g key={`${fn}:${index}`} data-map-function={fn} data-map-stage={index}><FigureObject id={fn} ctx={ctx}><rect x={positions[index] - 31} y={y - 25} width="62" height="50" rx="10" className="sr-function-box"/><ObjectName id={fn} x={positions[index]} y={y + 6} ctx={ctx} max={8}/></FigureObject>{index < path.maps.length - 1 && <FigureArrow from={[positions[index] + 34, y]} to={[positions[index + 1] - 34, y]} ctx={ctx}/>}</g>)}
    <FigureArrow from={[lastMap + 34, y]} to={[426, y]} ctx={ctx}/><NamedPoint id={objectId} x={442} y={y} ctx={ctx} labelY={24}/>
  </g>;
}

function RelationFigure({ relation, relations, ctx }: { relation: SemanticRelation; relations: readonly SemanticRelation[]; ctx: RenderContext }) {
  let body: ReactNode;
  let caption = relation.label;
  let mapPaths = false;
  if (relation.kind === 'membership') {
    const element = port(relation, 'element'), set = port(relation, 'set');
    const application = producedBy(element, relations);
    if (application?.kind === 'application' && application.ports.filter(p => p.role.startsWith('input')).length === 1 && port(application, 'input 1')) {
      body = <><Region id={set} x={336} y={100} width={235} height={155} ctx={ctx}/><NamedPoint id={port(application, 'input 1')} x={78} y={110} ctx={ctx}/><FigureArrow from={[94, 107]} to={[318, 107]} label={port(application, 'function')} ctx={ctx}/><NamedPoint id={element} x={337} y={110} ctx={ctx}/></>;
    } else body = <Region id={set} x={250} y={100} width={312} height={160} ctx={ctx}><NamedPoint id={element} x={250} y={110} ctx={ctx}/></Region>;
    caption = 'Membership condition · the named element belongs to the region';
  } else if (relation.kind === 'subset') {
    const subset = port(relation, 'subset'), superset = port(relation, 'superset');
    const image = producedBy(subset, relations);
    if (image?.kind === 'image') {
      body = <><Region id={port(image, 'set')} x={84} y={105} width={140} height={135} ctx={ctx}/><Region id={superset} x={350} y={103} width={255} height={173} ctx={ctx}/><Region id={subset} x={354} y={120} width={163} height={97} ctx={ctx} labelTop={false}/><FigureArrow from={[160, 99]} to={[273, 112]} bend={-18} label={port(image, 'function')} ctx={ctx}/></>;
    } else body = <><Region id={superset} x={250} y={102} width={360} height={180} ctx={ctx}/><Region id={subset} x={250} y={120} width={223} height={103} ctx={ctx}/></>;
    caption = 'Every element of the inner set belongs to the outer set. The sets may be equal; spacing does not express proper inclusion.';
  } else if (relation.kind === 'image' || relation.kind === 'preimage') {
    const source = port(relation, 'set'), result = port(relation, 'result');
    body = <><Region id={source} x={113} y={106} width={175} height={153} ctx={ctx}/><Region id={result} x={387} y={106} width={175} height={153} ctx={ctx}/><FigureArrow from={relation.kind === 'image' ? [206, 110] : [294, 110]} to={relation.kind === 'image' ? [292, 110] : [208, 110]} bend={-12} label={port(relation, 'function')} ctx={ctx}/><text x="113" y="203" className="sr-role-label" textAnchor="middle">given set</text><text x="387" y="203" className="sr-role-label" textAnchor="middle">{relation.kind === 'image' ? 'image' : 'preimage'}</text></>;
    caption = relation.kind === 'image' ? 'The image collects outputs of the map on the given set' : 'The preimage collects inputs whose outputs lie in the given set';
  } else if (relation.kind === 'application') {
    const inputs = relation.ports.filter(p => p.role.startsWith('input'));
    body = <>{inputs.slice(0, 3).map((input, index) => <g key={input.role}><NamedPoint id={input.objectId} x={78} y={inputs.length > 1 ? 53 + index * 62 : 110} ctx={ctx} labelY={22}/><FigureArrow from={[94, inputs.length > 1 ? 53 + index * 62 : 108]} to={[236, 108]} ctx={ctx}/></g>)}<FigureObject id={port(relation, 'function')} ctx={ctx}><rect x="230" y="76" width="106" height="67" rx="13" className="sr-function-box"/><ObjectName id={port(relation, 'function')} x={283} y={115} ctx={ctx} max={16}/></FigureObject><FigureArrow from={[338, 108]} to={[420, 108]} ctx={ctx}/><NamedPoint id={port(relation, 'output')} x={439} y={110} ctx={ctx}/>{inputs.length > 3 && <text x="80" y="214" className="sr-role-label" textAnchor="middle">+ {inputs.length - 3} inputs</text>}</>;
    caption = 'Application · the map sends its inputs to this output';
  } else if (relation.kind === 'equality' || relation.kind === 'inequality') {
    const left = port(relation, 'left'), right = port(relation, 'right');
    mapPaths = relation.kind === 'equality' && Boolean(left && right && (expressionMapPath(left, relations).maps.length || expressionMapPath(right, relations).maps.length));
    if (mapPaths && left && right) {
      body = <><ExpressionPath objectId={left} relations={relations} y={58} ctx={ctx}/><ExpressionPath objectId={right} relations={relations} y={179} ctx={ctx}/><path d="M442 87 V103 M442 140 V149" className="sr-role-connection"/><text x="442" y="130" textAnchor="middle" className="sr-comparison-symbol">{relation.label}</text></>;
      const collapsed = expressionMapPath(left, relations).collapsed || expressionMapPath(right, relations).collapsed;
      caption = `Compare the outputs of these map paths${relation.label === '≠' ? ': they are required to differ' : ': they are required to agree'}.${collapsed ? ' Further nested inputs retain their expression labels.' : ''}`;
    } else {
      body = <><FigureObject id={left} ctx={ctx}><rect x="42" y="63" width="175" height="95" rx="23" className="sr-expression-box"/><ObjectName id={left} x={129} y={116} ctx={ctx} max={24}/></FigureObject><text x="250" y="120" textAnchor="middle" className="sr-comparison-symbol">{relation.label}</text><FigureObject id={right} ctx={ctx}><rect x="283" y="63" width="175" height="95" rx="23" className="sr-expression-box"/><ObjectName id={right} x={370} y={116} ctx={ctx} max={24}/></FigureObject></>;
      caption = relation.kind === 'equality' ? 'The displayed expressions are required to satisfy this relation' : 'Order condition on the displayed expressions';
    }
  } else if (relation.kind === 'distance') {
    body = <><NamedPoint id={port(relation, 'from')} x={89} y={110} ctx={ctx}/><NamedPoint id={port(relation, 'to')} x={411} y={110} ctx={ctx}/><path d="M109 109 H391 M110 101 V117 M390 101 V117" className="sr-distance-bracket"/><FigureObject id={port(relation, 'distance')} ctx={ctx}><ObjectName id={port(relation, 'distance')} x={250} y={88} ctx={ctx}/></FigureObject><text x="250" y="178" textAnchor="middle" className="sr-role-label">symbolic distance · no scale assigned</text></>;
    caption = 'Distance in the stated metric';
  } else if (relation.kind === 'metric-region') {
    body = <><NamedPoint id={port(relation, 'center')} x={99} y={62} ctx={ctx}/><FigureObject id={port(relation, 'radius')} ctx={ctx}><rect x="49" y="123" width="100" height="57" rx="11" className="sr-expression-box"/><ObjectName id={port(relation, 'radius')} x={99} y={158} ctx={ctx}/></FigureObject><FigureArrow from={[154, 64]} to={[280, 100]} ctx={ctx}/><FigureArrow from={[154, 150]} to={[280, 123]} ctx={ctx}/><FigureObject id={port(relation, 'region')} ctx={ctx}><rect x="288" y="66" width="184" height="91" rx="14" className="sr-expression-box"/><ObjectName id={port(relation, 'region')} x={380} y={116} ctx={ctx} max={24}/></FigureObject></>;
    caption = 'Region defined by its center, radius, and metric. No nonemptiness or membership of the center is assumed.';
  } else {
    const slots = relation.ports.slice(0, 4);
    const centerId = port(relation, 'function') ?? port(relation, 'relation') ?? port(relation, 'symbol');
    const others = slots.filter(p => p.objectId !== centerId);
    body = <><FigureObject id={centerId} ctx={ctx} title={relation.label}><rect x="160" y="65" width="180" height="79" rx="17" className="sr-expression-box"/>{centerId ? <ObjectName id={centerId} x={250} y={110} ctx={ctx} max={24}/> : <text x="250" y="110" textAnchor="middle" className="sr-object-label">{compactLabel(relation.label, 24)}</text>}</FigureObject>{others.map((p, index) => { const x = (index + 1) * 500 / (others.length + 1); return <g key={`${p.role}:${index}`}><path d={`M250 145 L${x} 178`} className="sr-role-connection"/><NamedPoint id={p.objectId} x={x} y={184} ctx={ctx} labelY={23}/></g>; })}{relation.kind === 'function-property' && <text x="250" y="171" className="sr-property-name" textAnchor="middle">{relation.label}</text>}</>;
    caption = relation.fidelity === 'structural' ? 'Argument structure only · this predicate has no interpreted geometric meaning' : `${relation.label} · a property required of the displayed object`;
  }
  const comparison = !mapPaths && (relation.kind === 'equality' || relation.kind === 'inequality');
  return <figure className={`sr-relation-figure sr-figure-${relation.kind}${mapPaths ? ' sr-has-map-paths' : ''}`}><svg viewBox={comparison ? '0 45 500 130' : '0 0 500 230'} role="group" aria-label={`${relation.label}: schematic relation`}><title>{relation.label}</title>{body}</svg><figcaption>{caption}</figcaption></figure>;
}

function BinderStrip({ nodes, ctx }: { nodes: readonly ReadingNode[]; ctx: RenderContext }) {
  return <div className="sr-binder-strip" aria-label="Quantifiers and parameters in statement order">{nodes.map((node, index) => {
    const binder = node.binder!;
    return <div key={node.id} className={`sr-binder sr-binder-${binder.role}`}>
      {index > 0 && <span className="sr-choice-next" aria-hidden="true">›</span>}
      <span className="sr-binder-role"><b>{roleSymbol[binder.role]}</b>{roleText[binder.role]}</span>
      <button type="button" className={`sr-binder-name${binder.objectId === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} style={{ '--object-color': readingObjectColor(binder.objectId ?? binder.binderId) } as CSSProperties} data-reading-object={binder.objectId} onClick={() => binder.objectId ? ctx.onObjectSelect?.(binder.objectId) : ctx.onNodeSelect?.(node.id)} aria-pressed={binder.objectId === ctx.selectedObjectId} title={`${binder.name} : ${binder.type}`}><strong>{binder.name}</strong><span>{compactLabel(binder.type, 42)}</span></button>
      {binder.role === 'existential' && <span className="sr-binder-dependency">{binder.dependsOn.length ? `may use ${binder.dependsOn.map(id => ctx.objects.get(id)?.label ?? id).join(', ')}` : 'independent of later choices'}</span>}
    </div>;
  })}</div>;
}

function SourceButton({ node, ctx, children }: { node: ReadingNode; ctx: RenderContext; children: ReactNode }) {
  return <button type="button" className="sr-source-button" onClick={() => ctx.onNodeSelect?.(node.id)} title={node.lean} aria-label={`Inspect ${node.phrase || node.lean}`}>{children}</button>;
}

function Clause({ node, ctx }: { node: ReadingNode; ctx: RenderContext }) {
  const [showAllRelations, setShowAllRelations] = useState(false);
  const panel = node.panelId ? ctx.panels.get(node.panelId) : undefined;
  const groups = panel?.groups.filter(group => group.role === 'clause') ?? [];
  const relationIds = groups.length ? groups.flatMap(group => group.rootRelationIds) : panel?.rootRelationIds ?? node.relationIds;
  const relationScopeIds = new Set(groups.map(group => group.scopeId));
  const relations = (panel?.relationIds ?? node.relationIds).flatMap(id => ctx.relations.has(id) ? [ctx.relations.get(id)!] : []).filter(relation => !relationScopeIds.size || relationScopeIds.has(relation.scopeId));
  const roots = [...new Set(relationIds)].flatMap(id => ctx.relations.has(id) ? [ctx.relations.get(id)!] : []);
  const geometry = panel && ctx.renderGeometry?.(panel);
  const selected = node.id === ctx.reading.selection.nodeId;
  return <section className={`sr-clause${selected ? ' sr-clause-selected' : ''}`} data-reading-node={node.id} aria-label={node.phrase || 'Statement condition'}>
    <div className="sr-clause-heading"><SourceButton node={node} ctx={ctx}>{node.phrase || 'Condition'} <span aria-hidden="true">↗</span></SourceButton>{panel?.coverage === 'partial' && <span className="sr-coverage-note">partly interpreted</span>}</div>
    {geometry || (roots.length > 0 ? <div className={`sr-clause-figures${roots.length > 1 ? ' sr-multiple-roots' : ''}`}>{(showAllRelations ? roots : roots.slice(0, 3)).map(relation => <RelationFigure key={relation.id} relation={relation} relations={relations} ctx={ctx}/>)}{roots.length > 3 && !showAllRelations && <button type="button" className="sr-show-more" onClick={() => setShowAllRelations(true)}>Show {roots.length - 3} further relations in this clause</button>}</div> : <div className="sr-symbolic-clause"><span className="sr-symbolic-mark" aria-hidden="true">◇</span><code>{node.lean}</code><p>This clause is retained symbolically; no geometric interpretation is assigned.</p></div>)}
    {panel?.groups.some(group => group.role === 'local-expression') && <p className="sr-local-note">This expression contains locally bound structure. Inspect the fragment for its inner scopes.</p>}
  </section>;
}

const connectiveTitles: Record<string, string> = { implies: 'Given the assumption, require the conclusion', and: 'These conditions are required together', or: 'At least one alternative is required', iff: 'The two conditions imply each other', not: 'Negate the enclosed condition' };
const logicSymbols: Record<string, string> = { forall: '∀', exists: '∃', parameter: '↦', implies: '→', and: '∧', or: '∨', iff: '↔', not: '¬', predicate: '·' };

function StepContext({ step, ctx }: { step: ReadingStep; ctx: RenderContext }) {
  const positions = step.branchPath.filter(position => !['body', 'result'].includes(position.edge.role));
  return positions.length ? <div className="sr-step-context" aria-label="Enclosing logical context">{positions.map((position, index) => {
    const { edge } = position;
    const label = edge.role === 'assumption' ? 'Given' : edge.role === 'conclusion' ? 'Conclusion' : edge.role === 'conjunct' ? `Required condition ${edge.index + 1}` : edge.role === 'alternative' ? `Alternative ${edge.index + 1} · at least one` : edge.role === 'negated' ? 'Under negation' : edge.role === 'equivalence-left' ? 'First equivalent condition' : 'Second equivalent condition';
    return <button key={`${position.nodeId}:${index}`} type="button" className={`sr-step-context-${edge.role}`} onClick={() => ctx.onNodeSelect?.(position.nodeId)}>{label}</button>;
  })}</div> : null;
}

function VisualSequence({ ctx }: { ctx: RenderContext }) {
  const nodes = new Map(ctx.reading.nodes.map(node => [node.id, node]));
  const groups = new Map(ctx.reading.quantifierGroups.map(group => [group.nodeIds[0], group]));
  const consumed = new Set<string>();
  const steps = ctx.reading.sequence.filter(step => ctx.visibleNodes.has(step.nodeId)).flatMap(step => {
    if (consumed.has(step.nodeId)) return [];
    const group = groups.get(step.nodeId);
    const binders = group?.nodeIds.filter(id => ctx.visibleNodes.has(id)).flatMap(id => nodes.has(id) ? [nodes.get(id)!] : []) ?? [];
    binders.forEach(node => consumed.add(node.id));
    return [{ step, node: nodes.get(step.nodeId)!, binders }];
  });
  return <ol className="sr-visual-sequence" aria-label="Ordered visual reading of the statement">{steps.map(({ step, node, binders }, index) => <li key={step.id} className={`sr-sequence-step sr-sequence-${step.kind}${node.id === ctx.reading.selection.nodeId ? ' sr-step-focused' : ''}`} data-reading-step={node.id}>
    <span className="sr-step-number">{index + 1}</span><div className="sr-step-content"><StepContext step={step} ctx={ctx}/>
    {step.kind === 'binder' ? <div className="sr-sequence-binders"><div className="sr-sequence-binder-title">{node.kind === 'forall' ? 'Start with arbitrary objects' : node.kind === 'exists' ? 'A witness is required' : 'Parameters of the definition'}</div><BinderStrip nodes={binders.length ? binders : [node]} ctx={ctx}/></div> : step.kind === 'connective' ? <div className={`sr-sequence-connective sr-sequence-logic-${node.kind}`}><span className="sr-sequence-logic-symbol" aria-hidden="true">{logicSymbols[node.kind]}</span><div><SourceButton node={node} ctx={ctx}>{connectiveTitles[node.kind] ?? node.phrase}</SourceButton>{node.kind === 'or' && <p>The alternatives remain separate; either or both may hold.</p>}{node.kind === 'not' && <p>The following condition is the one being negated.</p>}{node.kind === 'iff' && <div className="sr-sequence-directions">{node.directions?.map(direction => <button type="button" key={direction.id} onClick={() => ctx.onNodeSelect?.(direction.conclusionNodeId)}>{direction.label}</button>)}</div>}</div></div> : <Clause node={node} ctx={ctx}/>}
    </div></li>)}</ol>;
}

function LogicOverview({ node, ctx, depth = 0 }: { node: ReadingNode; ctx: RenderContext; depth?: number }) {
  if (depth > 18 || !ctx.visibleNodes.has(node.id)) return <button type="button" className="sr-overview-more" onClick={() => ctx.onNodeSelect?.(node.id)}>Further structure…</button>;
  return <div className={`sr-overview-node sr-overview-${node.kind}`}><button type="button" className={node.id === ctx.reading.selection.nodeId ? 'sr-overview-selected' : ''} onClick={() => ctx.onNodeSelect?.(node.id)} title={node.lean}><span aria-hidden="true">{logicSymbols[node.kind]}</span><span>{node.binder && node.kind !== 'implies' ? `${roleText[node.binder.role]} ${node.binder.name}` : node.kind === 'implies' ? 'Given → conclusion' : node.kind === 'and' ? 'All conditions' : node.kind === 'or' ? 'At least one alternative' : node.kind === 'iff' ? 'Both directions' : node.kind === 'not' ? 'Not' : compactLabel(node.phrase || node.lean, 54)}</span></button>{node.children.length > 0 && <div className="sr-overview-children">{node.children.map(child => <div key={child.id}>{child.edgeFromParent && !['body', 'result'].includes(child.edgeFromParent.role) && <span className="sr-overview-edge-label">{child.edgeFromParent.role === 'assumption' ? 'Given' : child.edgeFromParent.role === 'conclusion' ? 'Conclusion' : child.edgeFromParent.label}</span>}<LogicOverview node={child} ctx={ctx} depth={depth + 1}/></div>)}</div>}</div>;
}

export function StatementReadingView(props: StatementReadingViewProps) {
  const { reading, document: semantic, selectedObjectId } = props;
  const surface = useRef<HTMLDivElement>(null);
  const [nodeLimit, setNodeLimit] = useState(100);
  const previousSelection = useRef(reading.selection.nodeId);
  const [traces, setTraces] = useState<{ id: string; path: string }[]>([]);
  const maps = useMemo<Maps>(() => ({ objects: new Map(semantic.objects.map(object => [object.id, object])), relations: new Map(semantic.relations.map(relation => [relation.id, relation])), panels: new Map(reading.panels.map(panel => [panel.id, panel])) }), [semantic, reading]);
  const shared = useMemo(() => {
    const counts = new Map<string, number>();
    reading.panels.forEach(panel => [...new Set(panel.objectIds)].forEach(id => counts.set(id, (counts.get(id) ?? 0) + 1)));
    return [...counts.entries()].filter(([id, count]) => count > 1 && maps.objects.has(id) && maps.objects.get(id)!.binder?.role !== 'assumption' && !['literal', 'expression', 'type'].includes(maps.objects.get(id)!.kind)).sort((a, b) => b[1] - a[1]).slice(0, 8);
  }, [reading, maps]);
  const traceObjectId = selectedObjectId ?? shared[0]?.[0];
  useLayoutEffect(() => {
    const root = surface.current;
    if (!root || !traceObjectId) { setTraces([]); return; }
    const update = () => {
      const box = root.getBoundingClientRect();
      const nodes = [...root.querySelectorAll<HTMLElement>('[data-reading-object]')].filter(element => element.getAttribute('data-reading-object') === traceObjectId);
      const points = nodes.slice(0, 16).map(element => { const r = element.getBoundingClientRect(); return { x: r.x - box.x + r.width / 2, y: r.y - box.y + r.height / 2 }; });
      setTraces(points.slice(1).map((point, index) => { const prior = points[index]; const midY = (prior.y + point.y) / 2; return { id: `${traceObjectId}:${index}`, path: `M${prior.x} ${prior.y} C${prior.x} ${midY},${point.x} ${midY},${point.x} ${point.y}` }; }));
    };
    update();
    const observer = new ResizeObserver(update);
    observer.observe(root);
    return () => observer.disconnect();
  }, [reading, traceObjectId]);
  useEffect(() => {
    const selected = reading.selection.nodeId;
    if (previousSelection.current === selected) return;
    previousSelection.current = selected;
    const group = reading.quantifierGroups.find(candidate => candidate.nodeIds.includes(selected));
    const stepId = group?.nodeIds[0] ?? selected;
    const target = [...(surface.current?.querySelectorAll<HTMLElement>('[data-reading-step]') ?? [])].find(element => element.getAttribute('data-reading-step') === stepId);
    const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
    target?.scrollIntoView({ behavior: reducedMotion ? 'auto' : 'smooth', block: 'start', inline: 'nearest' });
  }, [reading.selection.nodeId, reading.quantifierGroups]);
  const prioritized = reading.selection.nodeId === reading.root.id ? [] : [reading.selection.nodeId, ...reading.selection.ancestorNodeIds, ...reading.selection.assumptionNodeIds, ...reading.selection.descendantNodeIds].slice(0, 80);
  const visibleNodes = new Set([...new Set([...prioritized, ...reading.nodes.map(node => node.id)])].slice(0, nodeLimit));
  const ctx: RenderContext = { ...props, ...maps, visibleNodes };
  return <div className="statement-reading-view"><div className="sr-reading-intro"><span className="sr-reading-label">Follow the statement</span><span className="sr-schematic-label">Symbolic schematics · no numerical choices</span></div><div className="sr-sequence-layout"><div ref={surface} className="sr-reading-surface"><svg className="sr-identity-traces" aria-hidden="true"><g style={{ stroke: traceObjectId ? readingObjectColor(traceObjectId) : undefined }}>{traces.map(trace => <path key={trace.id} d={trace.path}/>)}</g></svg><div className="sr-reading-content"><VisualSequence ctx={ctx}/></div></div><aside className="sr-overview"><div className="sr-overview-heading">Whole statement</div><LogicOverview node={reading.root} ctx={ctx}/><p>Reading order is not proof order. Each branch keeps its own logical role.</p></aside></div>
    {shared.length > 0 && <div className="sr-shared-objects"><span>Same objects throughout</span>{shared.map(([id, count]) => <button type="button" key={id} className={selectedObjectId === id ? 'sr-object-selected' : ''} style={{ '--object-color': readingObjectColor(id) } as CSSProperties} onClick={() => props.onObjectSelect?.(id)} aria-pressed={selectedObjectId === id} title={`${maps.objects.get(id)!.label} occurs in ${count} clauses`}><i aria-hidden="true"/>{compactLabel(maps.objects.get(id)!.label, 22)}<small>{count} clauses</small></button>)}</div>}
    {reading.nodes.length > visibleNodes.size && <div className="sr-limit">Showing {visibleNodes.size} of {reading.nodes.length} logical nodes with the selected fragment in context. <button type="button" className="sr-show-more" onClick={() => setNodeLimit(limit => limit + 100)}>Show the next {Math.min(100, reading.nodes.length - visibleNodes.size)} nodes</button></div>}
    <p className="sr-reading-note">Each diagram depicts the condition at its place in the statement. “Given,” alternatives, and negation determine how it is used. Region shapes are schematic; only named elements are drawn.</p>
  </div>;
}
