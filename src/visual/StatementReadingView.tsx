import { useEffect, useLayoutEffect, useMemo, useRef, useState, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import type { ReadingBinder, ReadingDocument, ReadingNode, ReadingPanel } from '../reading/types';
import { planReadingPresentation, visibleReadingNodes, type ReadingPresentation, type ReadingRegion } from '../reading/presentation';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { TypedConstructionFigure } from '../constructions';
import { compileGraphConstraint, GraphConstraintFigure } from '../graphs';
import { compileRestrictedMap, RestrictedMapFigure } from '../restricted';
import { compileStructuralObject } from '../decomposition/compiler';
import { StructuralObjectFigure } from '../decomposition/StructuralObjectFigure';
import type { StructuralField } from '../decomposition/types';
import { compileReading } from '../reading/compiler';
import { compileSetConstruction, SetConstructionFigure } from '../set-constructions';
import { compactLabel } from './layout';
import { applicationFlow } from '../semantic/application-flow';
import './statement-reading.css';
import { compileReadingCues, type ReadingCue } from '../reading/cues';
import { GuidedReading } from './GuidedReading';

export interface StatementReadingViewProps {
  reading: ReadingDocument;
  document: SemanticDocument;
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
  onNodeSelect?: (id: string) => void;
  /** Return null when this clause has no faithful symbolic geometric rendering. */
  renderGeometry?: (panel: ReadingPanel) => ReactNode;
}

import { readingObjectColor } from './object-identity';
export { readingObjectColor } from './object-identity';
const roleText: Record<ReadingBinder['role'], string> = { universal: 'For every', existential: 'There is', parameter: 'Given parameter', lambda: 'For input', assumption: 'Assuming' };
const roleSymbol: Record<ReadingBinder['role'], string> = { universal: '∀', existential: '∃', parameter: '↦', lambda: '↦', assumption: '⇒' };
type Maps = { objects: Map<string, SemanticObject>; relations: Map<string, SemanticRelation>; panels: Map<string, ReadingPanel> };
type RenderContext = StatementReadingViewProps & Maps & { visibleNodes: Set<string>; presentation: ReadingPresentation; focusObjectIds?: ReadonlySet<string> };

function keyActivate(event: KeyboardEvent<SVGGElement>, action?: () => void) {
  if (action && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); action(); }
}

function FigureObject({ id, ctx, children, title }: { id?: string; ctx: RenderContext; children: ReactNode; title?: string }) {
  const object = id ? ctx.objects.get(id) : undefined;
  const actionable = Boolean(object && ctx.onObjectSelect);
  const color = id ? readingObjectColor(id) : '#82918f';
  return <g className={`sr-figure-object${id && ctx.focusObjectIds?.has(id) ? ' sr-cue-object' : ''}${id === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} style={{ '--object-color': color } as CSSProperties} data-reading-object={id} role={actionable ? 'button' : 'group'} tabIndex={actionable ? 0 : undefined} aria-label={object ? `${object.label}${object.type ? ` : ${object.type}` : ''}` : title} aria-pressed={actionable ? id === ctx.selectedObjectId : undefined} onClick={() => { if (id) ctx.onObjectSelect?.(id); }} onKeyDown={event => keyActivate(event, actionable && id ? () => ctx.onObjectSelect?.(id) : undefined)}>
    <title>{`${title ?? object?.label ?? ''}${object?.type ? ` : ${object.type}` : ''}`}</title>{children}
  </g>;
}

function ObjectName({ id, x, y, ctx, max = 24, anchor = 'middle', suffix = '', fieldOnly = false }: { id?: string; x: number; y: number; ctx: RenderContext; max?: number; anchor?: 'start' | 'middle' | 'end'; suffix?: string; fieldOnly?: boolean }) {
  const object = id ? ctx.objects.get(id) : undefined;
  const label = fieldOnly && object?.provenance.some(source => source.expressionPath.startsWith('binder.structure.')) ? object.label.slice(object.label.lastIndexOf('.') + 1) : object?.label ?? 'unspecified';
  return <text x={x} y={y} textAnchor={anchor} className="sr-object-label">{compactLabel(label, max) + suffix}</text>;
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
function producedBy(id: string | undefined, relations: readonly SemanticRelation[]) { return id ? relations.find(relation => relation.ports.some(p => ['output', 'result', 'region', 'distance', 'color', 'target vertex'].includes(p.role) && p.objectId === id)) : undefined; }

/** Expand a bounded map path; unexpanded subexpressions remain explicit objects. */
export function expressionMapPath(objectId: string, relations: readonly SemanticRelation[], depth = 0): { inputs: string[]; maps: string[]; directions: ('forward' | 'inverse')[]; output: string; collapsed: boolean } {
  const application = producedBy(objectId, relations);
  const flow = applicationFlow(application);
  const fallback = { inputs: [objectId], maps: [], directions: [], output: objectId, collapsed: Boolean(flow) };
  if (!flow || !application || depth >= 3 || flow.inputIds.length > 3) return fallback;
  const scoped = relations.filter(relation => relation.nodeId === application.nodeId && relation.scopeId === application.scopeId);
  if (flow.inputIds.length > 1) return { inputs: [...flow.inputIds], maps: [flow.functionId], directions: [flow.direction], output: objectId, collapsed: flow.inputIds.some(id => Boolean(applicationFlow(producedBy(id, scoped)))) };
  const inner = expressionMapPath(flow.inputIds[0]!, scoped, depth + 1);
  return { inputs: inner.inputs, maps: [...inner.maps, flow.functionId], directions: [...inner.directions, flow.direction], output: objectId, collapsed: inner.collapsed };
}

function ExpressionPath({ objectId, relations, y, ctx }: { objectId: string; relations: readonly SemanticRelation[]; y: number; ctx: RenderContext }) {
  const path = expressionMapPath(objectId, relations);
  if (!path.maps.length) return <FigureObject id={objectId} ctx={ctx}><rect x="62" y={y - 28} width="357" height="56" rx="13" className="sr-expression-box"/><ObjectName id={objectId} x={240} y={y + 6} ctx={ctx} max={41}/></FigureObject>;
  const positions = path.maps.map((_, index) => 170 + index * 174 / Math.max(1, path.maps.length - 1));
  const lastMap = positions.at(-1)!;
  return <g className="sr-expression-path" data-expression-output={objectId}>
    {path.inputs.length === 1 ? <NamedPoint id={path.inputs[0]} x={62} y={y} ctx={ctx} labelY={24}/> : <>{path.inputs.map((input, index) => <FigureObject key={`${input}:${index}`} id={input} ctx={ctx}><text x="14" y={y - 15 * (path.inputs.length - 1) + index * 30 + 6} className="sr-input-index">{index + 1}</text><ObjectName id={input} x={76} y={y - 15 * (path.inputs.length - 1) + index * 30 + 6} ctx={ctx} max={12}/></FigureObject>)}</>}
    <FigureArrow from={[path.inputs.length === 1 ? 80 : 120, y]} to={[positions[0] - 32, y]} ctx={ctx}/>
    {path.maps.map((fn, index) => <g key={`${fn}:${index}`} data-map-function={fn} data-map-stage={index} data-map-direction={path.directions[index]}><FigureObject id={fn} ctx={ctx}><rect x={positions[index] - 31} y={y - 25} width="62" height="50" rx="10" className="sr-function-box"/><ObjectName id={fn} x={positions[index]} y={y + 6} ctx={ctx} max={8} fieldOnly suffix={path.directions[index] === 'inverse' ? '⁻¹' : ''}/></FigureObject>{index < path.maps.length - 1 && <FigureArrow from={[positions[index] + 34, y]} to={[positions[index + 1] - 34, y]} ctx={ctx}/>}</g>)}
    <FigureArrow from={[lastMap + 34, y]} to={[426, y]} ctx={ctx}/><NamedPoint id={objectId} x={442} y={y} ctx={ctx} labelY={24}/>
  </g>;
}

function RelationFigure({ relation, relations, ctx }: { relation: SemanticRelation; relations: readonly SemanticRelation[]; ctx: RenderContext }) {
  if (compileRestrictedMap(ctx.document, relation, relations)) return <RestrictedMapFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
  if (compileGraphConstraint(ctx.document, relation, relations)) return <GraphConstraintFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
  if (!['image', 'preimage'].includes(relation.kind) && compileSetConstruction(ctx.document, relation, relations)) return <SetConstructionFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
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
  return <div className="sr-binder-strip" aria-label="Quantifiers and parameters in statement order">{nodes.map(node => {
    const binder = node.binder!;
    return <div key={node.id} className={`sr-binder sr-binder-${binder.role}`}>
      <button type="button" className={`sr-binder-name${binder.objectId === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} style={{ '--object-color': readingObjectColor(binder.objectId ?? binder.binderId) } as CSSProperties} data-reading-object={binder.objectId} onClick={() => binder.objectId ? ctx.onObjectSelect?.(binder.objectId) : ctx.onNodeSelect?.(node.id)} aria-pressed={binder.objectId === ctx.selectedObjectId} title={`${binder.name} : ${binder.type}`}><strong>{binder.name}</strong><span className="sr-binder-colon">:</span><span>{binder.type}</span></button>
      {binder.role === 'existential' && <span className="sr-binder-dependency">{binder.dependsOn.length ? `may use ${binder.dependsOn.map(id => ctx.objects.get(id)?.label ?? id).join(', ')}` : 'independent of later choices'}</span>}
    </div>;
  })}</div>;
}

function SourceButton({ node, ctx, children }: { node: ReadingNode; ctx: RenderContext; children: ReactNode }) {
  return <button type="button" className="sr-source-button" onClick={() => ctx.onNodeSelect?.(node.id)} title={node.lean} aria-label={`Focus ${node.phrase || node.lean}`}>{children}</button>;
}

function InlineObject({ id, ctx }: { id: string; ctx: RenderContext }) {
  const object = ctx.objects.get(id);
  return <button type="button" className={`sr-inline-object${id === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} data-reading-object={id} style={{ '--object-color': readingObjectColor(id) } as CSSProperties} onClick={() => ctx.onObjectSelect?.(id)} title={object?.type} aria-label={`${object?.label ?? id}${object?.type ? ` : ${object.type}` : ''}`}>{object?.label ?? id}</button>;
}

function ContainedExpressions({ panel, ctx }: { panel: ReadingPanel; ctx: RenderContext }) {
  const [limit, setLimit] = useState(3);
  const roots = new Set(panel.rootRelationIds);
  const groups = panel.groups.map(group => ({ ...group, relations: group.relationIds.flatMap(id => !roots.has(id) && ctx.relations.has(id) ? [ctx.relations.get(id)!] : []) })).filter(group => group.relations.length);
  const count = groups.reduce((sum, group) => sum + group.relations.length, 0);
  if (!count) return null;
  let preceding = 0;
  return <details className="sr-contained-expressions"><summary>Inside this expression <span>{count} {count === 1 ? 'relation' : 'relations'}</span></summary><p className="sr-contained-note">These are parts of the expression, not separate assertions.</p>{groups.map(group => {
    const visible = group.relations.slice(0, Math.max(0, limit - preceding));
    preceding += group.relations.length;
    if (!visible.length) return null;
    const scopeRelations = group.relationIds.flatMap(id => ctx.relations.has(id) ? [ctx.relations.get(id)!] : []);
    return <section className="sr-contained-group" key={group.id} data-expression-scope={group.scopeId} aria-label={group.role === 'local-expression' ? 'Inside a local expression scope' : 'Inside this clause expression'}>{group.role === 'local-expression' && <p className="sr-local-note">Local binders apply only within this expression.</p>}{visible.map(relation => <RelationFigure key={relation.id} relation={relation} relations={scopeRelations} ctx={ctx}/>)}</section>;
  })}{count > limit && <button type="button" className="sr-show-more" onClick={() => setLimit(current => current + 3)}>Show {Math.min(3, count - limit)} more contained relations</button>}</details>;
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
  const root = roots[0];
  const left = root && port(root, 'left'), right = root && port(root, 'right');
  const simpleConstraint = !geometry && !(root && compileSetConstruction(ctx.document, root, relations)) && roots.length === 1 && ['equality', 'inequality'].includes(root.kind) && left && right && !(root.kind === 'equality' && (expressionMapPath(left, relations).maps.length || expressionMapPath(right, relations).maps.length));
  const contained = panel && (panel.coverage === 'partial' || roots.some(relation => relation.fidelity === 'structural' || ['predicate', 'equality', 'inequality'].includes(relation.kind)) || panel.groups.some(group => group.role === 'local-expression')) ? <ContainedExpressions panel={panel} ctx={ctx}/> : null;
  if (simpleConstraint && left && right) return <><div className="sr-inline-constraint" data-reading-node={node.id} aria-label={node.phrase}><span className="sr-constraint-math"><InlineObject id={left} ctx={ctx}/><span className="sr-inline-relation">{root.label}</span><InlineObject id={right} ctx={ctx}/></span><SourceButton node={node} ctx={ctx}><span className="sr-source-glyph" aria-hidden="true">↗</span></SourceButton></div>{contained}</>;
  return <section className="sr-clause" data-reading-node={node.id} aria-label={node.phrase || 'Statement condition'}>
    <div className="sr-clause-heading"><SourceButton node={node} ctx={ctx}>{node.phrase || 'Condition'} <span aria-hidden="true">↗</span></SourceButton>{panel?.coverage === 'partial' && <span className="sr-coverage-note">partly interpreted</span>}</div>
    {geometry || (roots.length > 0 ? <div className={`sr-clause-figures${roots.length > 1 ? ' sr-multiple-roots' : ''}`}>{(showAllRelations ? roots : roots.slice(0, 3)).map(relation => <RelationFigure key={relation.id} relation={relation} relations={relations} ctx={ctx}/>)}{roots.length > 3 && !showAllRelations && <button type="button" className="sr-show-more" onClick={() => setShowAllRelations(true)}>Show {roots.length - 3} further relations in this clause</button>}</div> : <div className="sr-symbolic-clause"><code>{node.lean}</code><p>This clause is retained symbolically; no geometric interpretation is assigned.</p></div>)}
    {contained}
    {panel?.groups.some(group => group.role === 'local-expression') && <p className="sr-local-note">This expression contains local binders. Inspect the fragment to follow their scopes.</p>}
  </section>;
}

function FieldLawReading({ field, ctx }: { field: StructuralField; ctx: RenderContext }) {
  const [nodeId, setNodeId] = useState(field.lawReading?.selection.nodeId);
  const [objectId, setObjectId] = useState<string>();
  const document = field.lawDocument;
  const reading = useMemo(() => document ? compileReading(document, { selectedNodeId: nodeId }) : undefined, [document, nodeId]);
  if (!document || !reading) return <code>{field.type}</code>;
  return <StatementReadingView document={document} reading={reading} selectedObjectId={objectId ?? ctx.selectedObjectId}
    onNodeSelect={setNodeId} onObjectSelect={id => { setObjectId(id); if (ctx.objects.has(id)) ctx.onObjectSelect?.(id); }}/>;
}

function StructuralBinderFigure({ object, ctx }: { object: SemanticObject; ctx: RenderContext }) {
  const model = useMemo(() => compileStructuralObject(ctx.document, object), [ctx.document, object]);
  return model ? <StructuralObjectFigure model={model} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}
    renderLaw={field => <FieldLawReading key={field.projection} field={field} ctx={ctx}/>}/> : object.binder?.structureOmission ? <p className="sd-remaining">{object.binder.structureOmission}</p> : null;
}

function HypothesisStructures({ nodeIds, ctx }: { nodeIds: readonly string[]; ctx: RenderContext }) {
  const owners = nodeIds.flatMap(id => {
    const binder = ctx.reading.nodes.find(node => node.id === id)?.binder;
    const owner = binder?.role === 'assumption' && binder.objectId ? ctx.objects.get(binder.objectId) : undefined;
    return owner?.binder?.structure ? [owner] : [];
  });
  return owners.length ? <div className="sd-hypotheses"><p>Under these hypotheses, the following laws are available in the conclusion.</p>{owners.map(owner => <StructuralBinderFigure key={owner.id} object={owner} ctx={ctx}/>)}</div> : null;
}

function BinderFigures({ nodes, ctx }: { nodes: readonly ReadingNode[]; ctx: RenderContext }) {
  const relations = nodes.flatMap(node => ctx.document.relations.filter(relation => relation.nodeId === node.id && relation.provenance.expressionPath === 'binder.type' && relation.scopeId === `scope:${node.id}`));
  const recognized = relations.filter(relation => compileGraphConstraint(ctx.document, relation) || compileRestrictedMap(ctx.document, relation));
  const figures: ReactNode[] = [];
  let run: ReadingNode[] = [];
  const flush = () => { if (run.length) { figures.push(<TypedConstructionFigure key={`types:${run[0]!.id}`} document={ctx.document} binders={run.map(node => node.binder!)} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>); run = []; } };
  for (const node of nodes) {
    const bundled = recognized.filter(relation => relation.nodeId === node.id);
    const object = node.binder?.objectId ? ctx.objects.get(node.binder.objectId) : undefined;
    const structure = object?.binder?.structure || object?.binder?.structureOmission;
    if (!bundled.length && !structure) { run.push(node); continue; }
    flush();
    bundled.forEach(relation => figures.push(<RelationFigure key={relation.id} relation={relation} relations={relations} ctx={ctx}/>));
    if (structure && object) {
      const figure = <StructuralBinderFigure object={object} ctx={ctx}/>;
      figures.push(bundled.length ? <details className="sd-generic-detail" key={`structure:${node.id}`}><summary>Read the underlying fields and laws</summary>{figure}</details> : <div key={`structure:${node.id}`}>{figure}</div>);
    }
  }
  flush();
  return <>{figures}</>;
}

function RegionHeader({ region, title, symbol, ctx, detail, lead }: { region: ReadingRegion; title: string; symbol?: string; ctx: RenderContext; detail?: string; lead?: string }) {
  return <header className="sr-region-heading"><SourceButton node={region.node} ctx={ctx}>{lead && <span className="sr-heading-lead">{lead}</span>}{symbol && <span className="sr-region-symbol" aria-hidden="true">{symbol}</span>}<span>{title}</span></SourceButton>{detail && <p>{detail}</p>}</header>;
}

function AtlasRegion({ region, ctx, depth = 0, lead }: { region: ReadingRegion; ctx: RenderContext; depth?: number; lead?: string }): ReactNode {
  if (!region.sourceNodeIds.some(id => ctx.visibleNodes.has(id))) return <div className="sr-folded-region"><button type="button" onClick={() => ctx.onNodeSelect?.(region.id)}>Continue with {compactLabel(region.node.phrase || region.node.lean, 70)} <span aria-hidden="true">↗</span></button></div>;
  const focused = region.sourceNodeIds.includes(ctx.reading.selection.nodeId) && ctx.reading.selection.nodeId !== ctx.reading.root.id;
  let body: ReactNode;
  if (region.kind === 'binders') {
    const binders = region.binders.filter(node => ctx.visibleNodes.has(node.id));
    const role = region.node.binder!.role;
    body = <><div className="sr-object-introduction"><RegionHeader region={region} ctx={ctx} lead={lead} symbol={roleSymbol[role]} title={role === 'universal' ? 'For every' : role === 'existential' ? 'A witness is required' : 'Parameters'}/><BinderStrip nodes={binders} ctx={ctx}/><BinderFigures nodes={binders} ctx={ctx}/>{binders.length < region.binders.length && <button type="button" className="sr-show-more" onClick={() => ctx.onNodeSelect?.(region.binders[binders.length].id)}>Read the next {region.binders.length - binders.length} binders</button>}</div>{region.body && <AtlasRegion region={region.body} ctx={ctx} depth={depth + 1}/>}</>;
  } else if (region.kind === 'implication') {
    body = <div className="sr-implication-regions"><section className="sr-given-region" aria-label="Given assumptions"><h3 className="sr-role-heading">Given</h3><div className="sr-region-stack">{region.assumptions.map(assumption => <AtlasRegion key={assumption.id} region={assumption} ctx={ctx} depth={depth + 1}/>)}</div><HypothesisStructures nodeIds={region.sourceNodeIds} ctx={ctx}/></section><section className="sr-then-region" aria-label="Then the conclusion is required">{region.conclusion.kind !== 'binders' && <h3 className="sr-role-heading"><span aria-hidden="true">→</span> Then</h3>}<AtlasRegion region={region.conclusion} ctx={ctx} depth={depth + 1} lead={region.conclusion.kind === 'binders' ? 'Then' : undefined}/></section></div>;
  } else if (region.kind === 'all') {
    body = <><RegionHeader region={region} ctx={ctx} symbol="∧" title="Together" detail="Every condition below is required."/><div className="sr-conjuncts">{region.children.map(child => <AtlasRegion key={child.id} region={child} ctx={ctx} depth={depth + 1}/>)}</div></>;
  } else if (region.kind === 'alternatives') {
    body = <><RegionHeader region={region} ctx={ctx} symbol="∨" title="At least one alternative" detail="Either or both may hold."/><div className="sr-alternatives">{region.children.map((child, index) => <section key={child.id} className="sr-alternative" aria-label={`Alternative ${index + 1}`}><h3 className="sr-branch-label">Alternative {index + 1}</h3><AtlasRegion region={child} ctx={ctx} depth={depth + 1}/></section>)}</div></>;
  } else if (region.kind === 'equivalence') {
    body = <><RegionHeader region={region} ctx={ctx} symbol="↔" title="Equivalent conditions" detail="Each condition implies the other."/><div className="sr-equivalent-conditions">{region.children.map((child, index) => <section key={child.id}><h3 className="sr-branch-label">{index === 0 ? 'First' : 'Second'} equivalent condition</h3><AtlasRegion region={child} ctx={ctx} depth={depth + 1}/></section>)}</div><div className="sr-equivalence-directions">{region.node.directions?.map(direction => <button type="button" key={direction.id} onClick={() => ctx.onNodeSelect?.(direction.conclusionNodeId)}>{direction.label}</button>)}</div></>;
  } else if (region.kind === 'negation') {
    body = <><RegionHeader region={region} ctx={ctx} symbol="¬" title="Not" detail="Negation applies to the entire enclosed condition."/><div className="sr-negated-body" aria-label="Under negation"><AtlasRegion region={region.body} ctx={ctx} depth={depth + 1}/></div></>;
  } else if (region.kind === 'structure') {
    body = <><RegionHeader region={region} ctx={ctx} title={region.node.phrase}/>{region.children.map(child => <AtlasRegion key={child.id} region={child} ctx={ctx} depth={depth + 1}/>)}</>;
  } else body = <Clause node={region.node} ctx={ctx}/>;
  return <section className={`sr-atlas-region sr-region-${region.kind}${focused ? ' sr-region-focused' : ''}${depth > 3 ? ' sr-deep-region' : ''}`} data-reading-step={region.id} data-reading-region={region.kind} data-source-nodes={region.sourceNodeIds.join(' ')}>{body}</section>;
}

function overviewTitle(region: ReadingRegion): string {
  if (region.kind === 'binders') return `${roleText[region.node.binder!.role]} ${region.binders.map(node => node.binder!.name).join(', ')}`;
  if (region.kind === 'implication') return 'Given → conclusion';
  if (region.kind === 'all') return 'All conditions';
  if (region.kind === 'alternatives') return 'At least one alternative';
  if (region.kind === 'equivalence') return 'Both directions';
  if (region.kind === 'negation') return 'Not';
  return compactLabel(region.node.phrase || region.node.lean, 70);
}

function LogicOverview({ region, ctx, depth = 0 }: { region: ReadingRegion; ctx: RenderContext; depth?: number }): ReactNode {
  if (!region.sourceNodeIds.some(id => ctx.visibleNodes.has(id))) return <button type="button" className="sr-overview-more" onClick={() => ctx.onNodeSelect?.(region.id)}>{compactLabel(overviewTitle(region), 44)}…</button>;
  const children: { region: ReadingRegion; role?: string }[] = region.kind === 'binders' ? region.body ? [{ region: region.body }] : [] : region.kind === 'implication' ? [...region.assumptions.map(assumption => ({ region: assumption, role: 'Given' })), { region: region.conclusion, role: 'Then' }] : region.kind === 'negation' ? [{ region: region.body, role: 'Negated' }] : region.kind === 'clause' ? [] : region.children.map((child, index) => ({ region: child, role: region.kind === 'alternatives' ? `Alternative ${index + 1}` : region.kind === 'equivalence' ? `${index === 0 ? 'First' : 'Second'} condition` : undefined }));
  return <div className={`sr-overview-node${depth > 3 ? ' sr-overview-deep' : ''}`}><button type="button" className={region.sourceNodeIds.includes(ctx.reading.selection.nodeId) ? 'sr-overview-selected' : ''} onClick={() => ctx.onNodeSelect?.(region.id)} title={region.node.lean}>{overviewTitle(region)}</button>{children.length > 0 && <div className="sr-overview-children">{children.map(child => <div key={child.region.id}>{child.role && <span className="sr-overview-edge-label">{child.role}</span>}<LogicOverview region={child.region} ctx={ctx} depth={depth + 1}/></div>)}</div>}</div>;
}

function CueFigure({ cue, ctx }: { cue: ReadingCue; ctx: RenderContext }) {
  const node = ctx.reading.nodes.find(candidate => candidate.id === cue.nodeId)!;
  const focused = { ...ctx, focusObjectIds: new Set(cue.focusObjectIds) };
  let body: ReactNode;
  if (cue.intent === 'introduce') {
    const nodes = cue.sourceNodeIds.flatMap(id => { const source = ctx.reading.nodes.find(candidate => candidate.id === id); return source?.binder ? [source] : []; });
    body = <><BinderStrip nodes={nodes} ctx={focused}/><BinderFigures nodes={nodes} ctx={focused}/></>;
  } else if (cue.stage.kind === 'clause') {
    body = <Clause node={node} ctx={focused}/>;
  } else if (cue.stage.relationId) {
    const relation = ctx.relations.get(cue.stage.relationId);
    const panel = cue.panelId ? ctx.panels.get(cue.panelId) : undefined;
    const group = panel?.groups.find(candidate => candidate.scopeId === cue.scopeId);
    const relations = group?.relationIds.flatMap(id => ctx.relations.has(id) ? [ctx.relations.get(id)!] : []) ?? [];
    const localContext = ctx.document.scopes.find(scope => scope.id === cue.scopeId)?.context ?? [];
    body = <>{cue.stage.kind === 'construction' && <p className="rg-construction-context">Constructing part of <span title={node.lean}>{compactLabel(node.phrase || node.lean, 180)}</span></p>}{cue.stage.kind === 'contained' && <p className="rg-local-binders">Part of <code>{node.lean}</code>. This inner relation is not asserted separately.{group?.role === 'local-expression' && <> Local context: {localContext.join(' · ') || 'binders apply only inside this expression'}.</>}</p>}{relation && <RelationFigure relation={relation} relations={relations} ctx={focused}/>}</>;
  } else if (cue.intent === 'logic') {
    const grouped = cue.sourceNodeIds.flatMap(id => { const source = ctx.reading.nodes.find(candidate => candidate.id === id); return source?.kind === 'implies' ? [source] : []; });
    const children = node.kind === 'implies' && grouped.length ? [...grouped.map(source => source.children[0]), grouped.at(-1)!.children[1]] : node.children;
    body = <><div className="rg-logic-children">{children.map((child, index) => <div className="rg-logic-child" key={child.id}><span>{node.kind === 'implies' ? index < children.length - 1 ? 'Given' : 'Then' : node.kind === 'or' ? `Alternative ${index + 1}` : node.kind === 'not' ? 'Negated condition' : node.kind === 'iff' ? `${index === 0 ? 'First' : 'Second'} condition` : `Condition ${index + 1}`}</span><button type="button" onClick={() => ctx.onNodeSelect?.(child.id)} title={child.lean}>{compactLabel(child.phrase || child.lean, 180)}</button></div>)}</div><HypothesisStructures nodeIds={cue.sourceNodeIds} ctx={focused}/></>;
  } else body = <Clause node={node} ctx={focused}/>;
  return <>{body}<details className="rg-source-context"><summary>Lean fragment and source context</summary><code>{node.lean}</code></details></>;
}

export function StatementReadingView(props: StatementReadingViewProps) {
  const { reading, document: semantic, selectedObjectId } = props;
  const surface = useRef<HTMLDivElement>(null);
  const complete = useRef<HTMLDetailsElement>(null);
  const [guideChoice, setGuideChoice] = useState<{ document: SemanticDocument; cueId: string; nodeId: string } | null>(null);
  const [nodeLimit, setNodeLimit] = useState(100);
  const previousSelection = useRef(reading.selection.nodeId);
  const [traces, setTraces] = useState<{ id: string; path: string }[]>([]);
  const maps = useMemo<Maps>(() => ({ objects: new Map(semantic.objects.map(object => [object.id, object])), relations: new Map(semantic.relations.map(relation => [relation.id, relation])), panels: new Map(reading.panels.map(panel => [panel.id, panel])) }), [semantic, reading]);
  const presentation = useMemo(() => planReadingPresentation(reading), [reading]);
  const cuePlan = useMemo(() => compileReadingCues(reading, semantic), [reading, semantic]);
  const activeCue = (guideChoice?.document === semantic && guideChoice.nodeId === reading.selection.nodeId ? cuePlan.cues.find(cue => cue.id === guideChoice.cueId) : undefined) ?? cuePlan.cues.find(cue => cue.sourceNodeIds.includes(reading.selection.nodeId)) ?? (reading.selection.nodeId === reading.root.id ? cuePlan.cues[0] : undefined);
  function chooseCue(cue: ReadingCue) { setGuideChoice({ document: semantic, cueId: cue.id, nodeId: cue.nodeId }); props.onNodeSelect?.(cue.nodeId); }
  function chooseNode(id: string) {
    const cue = cuePlan.cues.find(candidate => candidate.sourceNodeIds.includes(id));
    if (cue) setGuideChoice({ document: semantic, cueId: cue.id, nodeId: id });
    else if (complete.current) complete.current.open = true;
    props.onNodeSelect?.(id);
  }
  useLayoutEffect(() => {
    const root = surface.current;
    if (!root || !selectedObjectId) { setTraces([]); return; }
    const update = () => {
      const box = root.getBoundingClientRect();
      const nodes = [...root.querySelectorAll<HTMLElement>('[data-reading-object]')].filter(element => element.getAttribute('data-reading-object') === selectedObjectId);
      const points = nodes.map(element => element.getBoundingClientRect()).filter(r => r.width > 0 && r.height > 0).slice(0, 16).map(r => ({ x: r.x - box.x + r.width / 2, y: r.y - box.y + r.height / 2 }));
      setTraces(points.slice(1).map((point, index) => { const prior = points[index]; const midY = (prior.y + point.y) / 2; return { id: `${selectedObjectId}:${index}`, path: `M${prior.x} ${prior.y} C${prior.x} ${midY},${point.x} ${midY},${point.x} ${point.y}` }; }));
    };
    update();
    const observer = new ResizeObserver(update);
    observer.observe(root);
    return () => observer.disconnect();
  }, [reading, selectedObjectId, activeCue?.id]);
  useEffect(() => {
    const selected = reading.selection.nodeId;
    if (!activeCue && complete.current) complete.current.open = true;
    if (!complete.current?.open) { previousSelection.current = selected; return; }
    if (previousSelection.current === selected) return;
    previousSelection.current = selected;
    const regionId = presentation.nodeToRegionId[selected] ?? selected;
    const target = [...(surface.current?.querySelectorAll<HTMLElement>('[data-reading-step]') ?? [])].find(element => element.getAttribute('data-reading-step') === regionId);
    const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
    target?.scrollIntoView({ behavior: reducedMotion ? 'auto' : 'smooth', block: 'start', inline: 'nearest' });
  }, [reading.selection.nodeId, presentation, activeCue]);
  const visibleNodes = visibleReadingNodes(reading, nodeLimit);
  const ctx: RenderContext = { ...props, ...maps, onNodeSelect: chooseNode, visibleNodes, presentation };
  return <div className="statement-reading-view"><div className="sr-atlas-layout"><div className="sr-atlas-main"><div className="sr-reading-intro"><span className="sr-reading-label">Visual reading</span><span className="sr-schematic-label">Symbolic schematics · no numerical choices</span></div><div ref={surface} className="sr-reading-surface">{activeCue && <GuidedReading plan={cuePlan} cue={activeCue} reading={reading} document={semantic} onChoose={chooseCue} onObjectSelect={props.onObjectSelect}><CueFigure cue={activeCue} ctx={ctx}/></GuidedReading>}<details ref={complete} className="sr-complete-reading"><summary>Full visual statement</summary>{selectedObjectId && <svg className="sr-identity-traces" aria-hidden="true"><g style={{ stroke: readingObjectColor(selectedObjectId) }}>{traces.map(trace => <path key={trace.id} d={trace.path}/>)}</g></svg>}<div className="sr-reading-content" aria-label="Ordered visual reading of the statement"><AtlasRegion region={presentation.root} ctx={ctx}/></div></details></div>{reading.nodes.length > visibleNodes.size && <div className="sr-limit">Showing {visibleNodes.size} of {reading.nodes.length} logical nodes, with the complete selected scope. <button type="button" className="sr-show-more" onClick={() => setNodeLimit(limit => limit + 100)}>Show the next {Math.min(100, reading.nodes.length - visibleNodes.size)} nodes</button></div>}<p className="sr-reading-note">Schematics describe the conditions in their logical context. Shapes and spacing carry no unstated geometric meaning.</p></div><aside className="sr-overview"><div className="sr-overview-heading">Whole statement</div><LogicOverview region={presentation.root} ctx={ctx}/></aside></div></div>;
}
