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
import { FigureScroll, useFrameOverflow } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import { MathLabel } from '../components/MathLabel';
import { expressionDisplayNode, mathDisplay, sourceMathDisplay, type MathDisplay } from '../notation/math-display';
import { numericOperator } from '../core/expression';
import { relationObjectMathDisplay } from '../notation/relation-math-display';
import { layoutContainedRelation, layoutRelationComparison } from './relation-diagram-layout';
import { labelShape, layoutExpressionFlow, layoutRegionLink, stackShapes, type LabelShape } from './generic-relation-layout';
import { applicationFlow } from '../semantic/application-flow';
import { formatExpression } from '../semantic/expression';
import './statement-reading.css';
import { compileReadingCues, type ReadingCue } from '../reading/cues';
import { GuidedReading } from './GuidedReading';
import { contextEntryTitle } from '../core/context-entry';
import { counted } from '../core/counted';
import { createReadingCueSelection, notifyReadingCueSelection, resolveReadingCue, type ReadingCueSelection } from './reading-cue-selection';
import { compileScopedStatementGraph } from '../reading/scoped-graph';
import { ScopedStatementGraph } from './ScopedStatementGraph';
export type { ReadingCueSelection } from './reading-cue-selection';

export interface StatementReadingViewProps {
  reading: ReadingDocument;
  document: SemanticDocument;
  /** Display-only title for an actual component target, for example Exposed type. */
  componentTitle?: string;
  selectedObjectId?: string;
  /** Focus a particular relation when multiple applications share a clause.
   * Clear this controlled selection in onNodeSelect to resume step navigation. */
  selectedRelationId?: string;
  /** Retain an exact stage across remounts. Undefined uses local attention state;
   * null clears retained attention. The token belongs to its document reference. */
  selectedCue?: ReadingCueSelection | null;
  /** Called after the existing node/source callbacks for guided navigation. */
  onCueChange?: (selection: ReadingCueSelection | null) => void;
  onObjectSelect?: (id: string) => void;
  onNodeSelect?: (id: string) => void;
  /** A guided stage may focus an application inside its enclosing node. Called
   * after onNodeSelect with that source-bearing relation ID, or the node ID. */
  onSourceSelect?: (id: string) => void;
  /** Return null when this clause has no faithful symbolic geometric rendering. */
  renderGeometry?: (panel: ReadingPanel) => ReactNode;
}

import { readingObjectColor } from './object-identity';
export { readingObjectColor } from './object-identity';
const roleText: Record<ReadingBinder['role'], string> = { universal: 'For every', existential: 'There is', parameter: 'Given parameter', lambda: 'For input', assumption: 'Assuming', definition: 'Define', auxiliary: 'Recorded context entry' };
const roleSymbol: Record<ReadingBinder['role'], string> = { universal: '∀', existential: '∃', parameter: '↦', lambda: '↦', assumption: '⇒', definition: ':=', auxiliary: '·' };
const componentMode = (document: SemanticDocument): boolean => document.presentation?.kind === 'component';
const ambientNodes = (nodes: readonly ReadingNode[], document: SemanticDocument): boolean => nodes.every(node => document.presentation?.contextNodeIds?.includes(node.id));
function componentBinderTitle(nodes: readonly ReadingNode[], document: SemanticDocument): string {
  if (nodes[0]?.binder?.role === 'auxiliary') return 'Recorded context entries';
  if (nodes.some(node => node.id === document.presentation?.logicalRootNodeId))
    return nodes[0]?.binder?.role === 'existential' ? 'Candidate within the existential statement' : 'For every';
  return nodes[0]?.binder?.role === 'definition' ? ambientNodes(nodes, document) ? 'Context definitions' : 'Local definitions'
    : ambientNodes(nodes, document) ? 'Names in scope' : 'Function inputs';
}
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

function objectMathLabel(id: string | undefined, ctx: RenderContext, inverse = false, relations: readonly SemanticRelation[] = []): MathDisplay {
  const object = id ? ctx.objects.get(id) : undefined;
  if (!object) return sourceMathDisplay('unspecified');
  if (!inverse) return relationObjectMathDisplay(object, relations, ctx.objects);
  const base = expressionDisplayNode(object.expression);
  return base ? mathDisplay({ kind: 'script', base, superscript: { kind: 'literal', value: -1 } }, `(${object.label})⁻¹`)
    : sourceMathDisplay(`(${object.label})⁻¹`);
}

function ObjectName({ label, labelKey, x, y }: { label: MathDisplay; labelKey: string; x: number; y: number }) {
  return <MathLabel label={label} labelKey={labelKey} x={x} y={y} fontSize={18} className="sr-object-label"/>;
}

function FigureArrow({ from, to }: { from: [number, number]; to: [number, number] }) {
  const angle = Math.atan2(to[1] - from[1], to[0] - from[0]);
  const head = (offset: number): [number, number] => [to[0] - 8 * Math.cos(angle + offset), to[1] - 8 * Math.sin(angle + offset)];
  const a = head(.5), b = head(-.5);
  return <><path d={`M ${from[0]} ${from[1]} L ${to[0]} ${to[1]}`} className="sr-map-arrow"/><path d={`M ${a[0]} ${a[1]} L ${to[0]} ${to[1]} L ${b[0]} ${b[1]}`} className="sr-map-arrow"/></>;
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

/** Basic containment and comparison keep their glyphs inside the shapes that
 * carry their meaning. Full object labels remain on the interactive groups. */
function MeasuredRelationFigure({ relation, relations, ctx }: { relation: SemanticRelation; relations: readonly SemanticRelation[]; ctx: RenderContext }) {
  const text = useDiagramText();
  const nested = relation.kind === 'subset', comparison = relation.kind === 'equality' || relation.kind === 'inequality';
  const first = port(relation, comparison ? 'left' : nested ? 'superset' : 'set');
  const second = port(relation, comparison ? 'right' : nested ? 'subset' : 'element');
  const objectLabel = (id: string | undefined) => {
    const object = id ? ctx.objects.get(id) : undefined;
    return object ? relationObjectMathDisplay(object, relations, ctx.objects) : sourceMathDisplay('unspecified');
  };
  const firstLabel = objectLabel(first), secondLabel = objectLabel(second);
  const firstSize = text.size('first', firstLabel.source, 18), secondSize = text.size('second', secondLabel.source, 18);
  const name = (key: string, label: MathDisplay, x: number, y: number) => <MathLabel label={label} labelKey={key} className="sr-object-label" x={x} y={y} fontSize={18}/>;
  let body: ReactNode, width: number, height: number;
  if (comparison) {
    const operator = numericOperator(relation.expression);
    const symbol = operator === 'eq' || operator === 'ne' || operator === 'lt' || operator === 'le'
      ? mathDisplay({ kind: 'symbol', symbol: operator }, relation.label) : sourceMathDisplay(relation.label);
    const layout = layoutRelationComparison(firstSize, secondSize, text.size('symbol', symbol.source, 27));
    ({ width, height } = layout);
    const box = (id: string | undefined, label: MathDisplay, key: string, slot: typeof layout.left) => <FigureObject id={id} ctx={ctx}><rect x={slot.x} y={slot.y} width={slot.width} height={slot.height} rx="23" className="sr-expression-box"/>{name(key, label, slot.labelX, slot.labelY)}</FigureObject>;
    body = <>{box(first, firstLabel, 'first', layout.left)}<MathLabel label={symbol} labelKey="symbol" x={layout.symbolX} y={layout.symbolY} fontSize={27} className="sr-comparison-symbol"/>{box(second, secondLabel, 'second', layout.right)}</>;
  } else {
    const layout = layoutContainedRelation(firstSize, secondSize, nested);
    ({ width, height } = layout);
    body = <><FigureObject id={first} ctx={ctx}><ellipse cx={layout.outer.x} cy={layout.outer.y} rx={layout.outer.rx} ry={layout.outer.ry} className="sr-set-outline"/>{name('first', firstLabel, layout.outer.x, layout.outer.label.baseline)}</FigureObject><FigureObject id={second} ctx={ctx}>{nested ? <ellipse cx={layout.inner.x} cy={layout.inner.y} rx={layout.inner.rx} ry={layout.inner.ry} className="sr-set-outline"/> : <><circle cx={layout.inner.x} cy={layout.inner.y} r="6" className="sr-named-point"/><circle cx={layout.inner.x} cy={layout.inner.y} r="16" fill="transparent"/></>}{name('second', secondLabel, layout.inner.x, layout.inner.label.baseline)}</FigureObject></>;
  }
  const caption = comparison ? relation.kind === 'equality' ? 'The displayed expressions are required to satisfy this relation' : 'Order condition on the displayed expressions'
    : nested ? 'Every element of the inner set belongs to the outer set. The sets may be equal; spacing does not express proper inclusion.' : 'Membership condition · the named element belongs to the region';
  return <figure className={`sr-relation-figure sr-figure-${relation.kind}`}><FigureScroll label="Relation diagram; scroll to see all of it"><svg ref={text.ref} style={{ minWidth: width * .75, height: 'auto', aspectRatio: `${width} / ${height}` }} viewBox={`0 0 ${width} ${height}`} role="group" aria-label={`${relation.label}: schematic ${relation.fidelity === 'structural' ? 'expression' : 'relation'}`}><title>{relation.label}</title>{body}</svg></FigureScroll><figcaption>{caption}</figcaption></figure>;
}

function RelationFigure({ relation, relations, ctx }: { relation: SemanticRelation; relations: readonly SemanticRelation[]; ctx: RenderContext }) {
  if (compileRestrictedMap(ctx.document, relation, relations)) return <RestrictedMapFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
  if (compileGraphConstraint(ctx.document, relation, relations)) return <GraphConstraintFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
  if (!['image', 'preimage'].includes(relation.kind) && compileSetConstruction(ctx.document, relation, relations)) return <SetConstructionFigure document={ctx.document} relation={relation} relations={relations} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect}/>;
  if (relation.kind === 'membership') {
    const application = producedBy(port(relation, 'element'), relations);
    if (!(application?.kind === 'application' && application.ports.filter(p => p.role.startsWith('input')).length === 1 && port(application, 'input 1')))
      return <MeasuredRelationFigure relation={relation} relations={relations} ctx={ctx}/>;
  } else if (relation.kind === 'subset' && producedBy(port(relation, 'subset'), relations)?.kind !== 'image') {
    return <MeasuredRelationFigure relation={relation} relations={relations} ctx={ctx}/>;
  } else if (relation.kind === 'equality' || relation.kind === 'inequality') {
    const left = port(relation, 'left'), right = port(relation, 'right');
    if (!(relation.kind === 'equality' && left && right && (expressionMapPath(left, relations).maps.length || expressionMapPath(right, relations).maps.length)))
      return <MeasuredRelationFigure relation={relation} relations={relations} ctx={ctx}/>;
  }
  return <GenericRelationFigure relation={relation} relations={relations} ctx={ctx}/>;
}

/** Measured labels retain the existing schematic roles and source identities.
 * Each input/output column reserves its full label before arrows are placed. */
function GenericRelationFigure({ relation, relations, ctx }: { relation: SemanticRelation; relations: readonly SemanticRelation[]; ctx: RenderContext }) {
  const text = useDiagramText();
  const label = (id: string | undefined, inverse = false) => objectMathLabel(id, ctx, inverse, relations);
  const size = (key: string, value: MathDisplay) => text.size(key, value.source, 18);
  const name = (key: string, value: MathDisplay, x: number, y: number) => <ObjectName label={value} labelKey={key} x={x} y={y}/>;
  const shaped = (id: string | undefined, key: string, value: MathDisplay, shape: LabelShape, kind: 'box' | 'point' | 'ellipse', x = 0, y = 0, functionBox = false) => <g transform={`translate(${x} ${y})`}><FigureObject id={id} ctx={ctx}>
    {kind === 'point' ? <><circle cx={shape.width / 2} cy={shape.pointY} r="6" className="sr-named-point"/><circle cx={shape.width / 2} cy={shape.pointY} r="16" fill="transparent"/></>
      : kind === 'ellipse' ? <ellipse cx={shape.width / 2} cy={shape.height / 2} rx={shape.width / 2} ry={shape.height / 2} className="sr-set-outline"/>
        : <rect width={shape.width} height={shape.height} rx="13" className={functionBox ? 'sr-function-box' : 'sr-expression-box'}/>}
    {name(key, value, shape.width / 2, shape.label.baseline)}
  </FigureObject></g>;
  const flow = (path: ReturnType<typeof expressionMapPath>, prefix: string) => {
    const inputs = path.inputs.map(id => label(id)), maps = path.maps.map((id, i) => label(id, path.directions[i] === 'inverse')), output = label(path.output);
    const layout = layoutExpressionFlow(inputs.map((value, i) => size(`${prefix}:input:${i}`, value)), maps.map((value, i) => size(`${prefix}:map:${i}`, value)), size(`${prefix}:output`, output));
    const inputRight = Math.max(0, ...layout.inputs.map(item => item.x + item.width));
    const draw = () => <g className="sr-expression-path" data-expression-output={path.output}>
      {layout.inputs.map((item, i) => <g key={`input:${i}`} data-input-index={i + 1}>{shaped(path.inputs[i], `${prefix}:input:${i}`, inputs[i], item, 'point', item.x, item.y)}<path d={`M${item.x + item.width / 2 + 18} ${item.y + item.pointY!} H${inputRight}`} className="sr-map-arrow"/><FigureArrow from={[inputRight, item.y + item.pointY!]} to={[layout.maps[0].x - 6, layout.arrowY]}/></g>)}
      {layout.maps.map((item, i) => <g key={`map:${i}`} data-map-function={path.maps[i]} data-map-stage={i} data-map-direction={path.directions[i]}>{shaped(path.maps[i], `${prefix}:map:${i}`, maps[i], item, 'box', item.x, item.y, true)}<FigureArrow from={[item.x + item.width + 6, layout.arrowY]} to={i + 1 < layout.maps.length ? [layout.maps[i + 1].x - 6, layout.arrowY] : [layout.output.x + layout.output.width / 2 - 18, layout.arrowY]}/></g>)}
      {shaped(path.output, `${prefix}:output`, output, layout.output, path.maps.length ? 'point' : 'box', layout.output.x, layout.output.y)}
    </g>;
    return { ...layout, draw, outputX: layout.output.x + layout.output.width / 2 };
  };
  let body: ReactNode, width: number, height: number, caption = relation.label;
  const mapPaths = relation.kind === 'equality';
  if (relation.kind === 'application') {
    const inputs = relation.ports.filter(p => p.role.startsWith('input')).map(p => p.objectId);
    const path = { inputs, maps: [port(relation, 'function')!], directions: ['forward' as const], output: port(relation, 'output')!, collapsed: false };
    const layout = flow(path, 'application');
    ({ width, height } = layout); body = layout.draw();
    caption = componentMode(ctx.document) ? 'Application · ordered inputs and output expression' : 'Application · the map sends its inputs to this output';
  } else if (mapPaths) {
    const leftPath = expressionMapPath(port(relation, 'left')!, relations), rightPath = expressionMapPath(port(relation, 'right')!, relations);
    const left = flow(leftPath, 'left'), right = flow(rightPath, 'right');
    const operator = numericOperator(relation.expression), symbol = operator === 'eq' || operator === 'ne' ? mathDisplay({ kind: 'symbol', symbol: operator }, relation.label) : sourceMathDisplay(relation.label);
    const symbolSize = text.size('comparison', symbol.source, 27), outputX = Math.max(left.outputX, right.outputX);
    const rightY = left.height + symbolSize.height + 48;
    width = outputX + Math.max(left.width - left.outputX, right.width - right.outputX); height = rightY + right.height;
    body = <><g transform={`translate(${outputX - left.outputX} 0)`}>{left.draw()}</g><g transform={`translate(${outputX - right.outputX} ${rightY})`}>{right.draw()}</g><MathLabel label={symbol} labelKey="comparison" x={outputX} y={left.height + 24 + symbolSize.ascent} fontSize={27} className="sr-comparison-symbol"/><path d={`M${outputX} ${left.height - 4} V${left.height + 16} M${outputX} ${rightY - 16} V${rightY + 4}`} className="sr-role-connection"/></>;
    caption = `Compare the outputs of these map paths${relation.label === '≠' ? ': they are required to differ' : ': they are required to agree'}.${leftPath.collapsed || rightPath.collapsed ? ' Further nested inputs retain their expression labels.' : ''}`;
  } else if (['membership', 'subset', 'image', 'preimage'].includes(relation.kind)) {
    const membership = relation.kind === 'membership', nested = relation.kind === 'subset';
    const construction = membership ? producedBy(port(relation, 'element'), relations)! : nested ? producedBy(port(relation, 'subset'), relations)! : relation;
    const leftId = port(construction, membership ? 'input 1' : 'set'), rightId = port(relation, membership ? 'set' : nested ? 'superset' : 'result');
    const innerId = membership ? port(relation, 'element') : nested ? port(relation, 'subset') : undefined, mapId = port(construction, 'function');
    const leftLabel = label(leftId), rightLabel = label(rightId), innerLabel = label(innerId), mapLabel = label(mapId);
    const leftShape = labelShape(size('source', leftLabel), membership ? 'point' : 'ellipse');
    const contained = membership || nested ? layoutContainedRelation(size('target', rightLabel), size('inner', innerLabel), nested) : undefined;
    const rightShape = labelShape(size('target', rightLabel), 'ellipse');
    const target = contained ?? rightShape, layout = layoutRegionLink(leftShape, target, size('map', mapLabel), membership ? leftShape.pointY : leftShape.height / 2, contained?.inner.y);
    ({ width, height } = layout);
    const from: [number, number] = [layout.left.x + (membership ? leftShape.width / 2 + 18 : leftShape.width + 8), layout.arrowY], to: [number, number] = [layout.right.x + (membership && contained ? contained.inner.x - 18 : -8), layout.arrowY];
    // The point output remains inside its set. Region arrows join the boundary.
    body = <>{shaped(leftId, 'source', leftLabel, leftShape, membership ? 'point' : 'ellipse', layout.left.x, layout.left.y)}<g transform={`translate(${layout.right.x} ${layout.right.y})`}>{contained ? <><FigureObject id={rightId} ctx={ctx}><ellipse cx={contained.outer.x} cy={contained.outer.y} rx={contained.outer.rx} ry={contained.outer.ry} className="sr-set-outline"/>{name('target', rightLabel, contained.outer.x, contained.outer.label.baseline)}</FigureObject><FigureObject id={innerId} ctx={ctx}>{nested ? <ellipse cx={contained.inner.x} cy={contained.inner.y} rx={contained.inner.rx} ry={contained.inner.ry} className="sr-set-outline"/> : <circle cx={contained.inner.x} cy={contained.inner.y} r="6" className="sr-named-point"/>}{name('inner', innerLabel, contained.inner.x, contained.inner.label.baseline)}</FigureObject></> : shaped(rightId, 'target', rightLabel, rightShape, 'ellipse')}</g><FigureObject id={mapId} ctx={ctx}>{name('map', mapLabel, layout.map.x + layout.map.width / 2, layout.map.baseline)}</FigureObject><FigureArrow from={relation.kind === 'preimage' ? to : from} to={relation.kind === 'preimage' ? from : to}/>{!membership && !nested && <><text x={layout.left.x + leftShape.width / 2} y={height - 10} textAnchor="middle" className="sr-role-label">given set</text><text x={layout.right.x + rightShape.width / 2} y={height - 10} textAnchor="middle" className="sr-role-label">{relation.kind}</text></>}</>;
    caption = membership ? 'Membership condition · the named element belongs to the region' : nested ? 'Every element of the inner set belongs to the outer set. The sets may be equal; spacing does not express proper inclusion.' : relation.kind === 'image' ? 'The image collects outputs of the map on the given set' : 'The preimage collects inputs whose outputs lie in the given set';
  } else if (relation.kind === 'distance') {
    const fromId = port(relation, 'from'), toId = port(relation, 'to'), distanceId = port(relation, 'distance');
    const fromLabel = label(fromId), toLabel = label(toId), distanceLabel = label(distanceId);
    const from = labelShape(size('from', fromLabel), 'point'), to = labelShape(size('to', toLabel), 'point'), distance = size('distance', distanceLabel);
    width = Math.max(500, from.width + to.width + 100, distance.width + 40); const y = 24 + distance.height + 28;
    height = y + Math.max(from.height, to.height) + 48;
    const a = 20 + from.width / 2, b = width - 20 - to.width / 2;
    body = <>{shaped(fromId, 'from', fromLabel, from, 'point', 20, y)}{shaped(toId, 'to', toLabel, to, 'point', width - 20 - to.width, y)}<path d={`M${a + 18} ${y + 12} H${b - 18} M${a + 18} ${y + 4} V${y + 20} M${b - 18} ${y + 4} V${y + 20}`} className="sr-distance-bracket"/><FigureObject id={distanceId} ctx={ctx}>{name('distance', distanceLabel, width / 2, 20 + distance.ascent)}</FigureObject><text x={width / 2} y={height - 16} textAnchor="middle" className="sr-role-label">symbolic distance · no scale assigned</text></>;
    caption = 'Distance in the stated metric';
  } else if (relation.kind === 'metric-region') {
    const centerId = port(relation, 'center'), radiusId = port(relation, 'radius'), regionId = port(relation, 'region');
    const center = label(centerId), radius = label(radiusId), region = label(regionId);
    const stack = stackShapes([labelShape(size('center', center), 'point'), labelShape(size('radius', radius), 'box')], 32);
    const result = labelShape(size('region', region), 'box'), targetX = 20 + stack.width + 84;
    width = targetX + result.width + 20; height = Math.max(stack.height, result.height) + 32;
    const sourceY = (height - stack.height) / 2, resultY = (height - result.height) / 2;
    body = <>{stack.items.map((item, i) => <g key={i}>{shaped(i ? radiusId : centerId, i ? 'radius' : 'center', i ? radius : center, item, i ? 'box' : 'point', item.x + 20, item.y + sourceY)}<FigureArrow from={[20 + stack.width + 6, sourceY + item.y + (i ? item.height / 2 : item.pointY!)]} to={[targetX - 6, resultY + result.height * (i ? .7 : .3)]}/></g>)}{shaped(regionId, 'region', region, result, 'box', targetX, resultY)}</>;
    caption = 'Region defined by its center, radius, and metric. No nonemptiness or membership of the center is assumed.';
  } else {
    const headPort = relation.ports.find(port => port.role === 'function') ?? relation.ports.find(port => port.role === 'relation') ?? relation.ports.find(port => port.role === 'symbol');
    const centerId = headPort?.objectId;
    const center = centerId ? label(centerId) : sourceMathDisplay(relation.label), centerShape = labelShape(size('head', center), 'box');
    const others = relation.ports.filter(p => p !== headPort), labels = others.map(p => label(p.objectId));
    const shapes = labels.map((value, i) => labelShape(size(`argument:${i}`, value), 'point'));
    const rowWidth = shapes.reduce((sum, shape) => sum + shape.width, 0) + Math.max(0, shapes.length - 1) * 24;
    width = Math.max(500, centerShape.width + 40, rowWidth + 40);
    const rowY = centerShape.height + 64;
    height = rowY + Math.max(0, ...shapes.map(shape => shape.height)) + 20;
    let x = (width - rowWidth) / 2;
    body = <>{shaped(centerId, 'head', center, centerShape, 'box', (width - centerShape.width) / 2, 16)}{shapes.map((shape, i) => { const left = x; x += shape.width + 24; return <g key={`${others[i].role}:${i}`}><path d={`M${width / 2} ${16 + centerShape.height} L${left + shape.width / 2} ${rowY + shape.pointY! - 10}`} className="sr-role-connection"/>{shaped(others[i].objectId, `argument:${i}`, labels[i], shape, 'point', left, rowY)}</g>; })}</>;
    caption = componentMode(ctx.document) ? 'Argument structure of this expression' : relation.fidelity === 'structural' ? 'Argument structure only · this expression has no interpreted geometric meaning' : `${relation.label} · a property required of the displayed object`;
  }
  return <figure className={`sr-relation-figure sr-figure-${relation.kind}${mapPaths ? ' sr-has-map-paths' : ''}`}><FigureScroll label="Relation diagram; scroll to see all of it"><svg ref={text.ref} style={{ minWidth: width * .75, height: 'auto', aspectRatio: `${width} / ${height}` }} viewBox={`0 0 ${width} ${height}`} role="group" aria-label={`${relation.label}: schematic ${relation.fidelity === 'structural' ? 'expression' : 'relation'}`}><title>{relation.label}</title>{body}</svg></FigureScroll><figcaption>{caption}</figcaption></figure>;
}

function BinderStrip({ nodes, ctx }: { nodes: readonly ReadingNode[]; ctx: RenderContext }) {
  return <div className="sr-binder-strip" aria-label={componentMode(ctx.document) ? "Parameters and definitions in source order" : "Binders and definitions in statement order"}>{nodes.map(node => {
    const binder = node.binder!;
    return <div key={node.id} className={`sr-binder sr-binder-${binder.role}`}>
      {binder.role === 'auxiliary' && <span className="sr-binder-dependency">{contextEntryTitle(binder)}</span>}
      <button type="button" className={`sr-binder-name${binder.objectId === ctx.selectedObjectId ? ' sr-object-selected' : ''}`} style={{ '--object-color': readingObjectColor(binder.objectId ?? binder.binderId) } as CSSProperties} data-reading-object={binder.objectId} onClick={() => binder.objectId ? ctx.onObjectSelect?.(binder.objectId) : ctx.onNodeSelect?.(node.id)} aria-pressed={binder.objectId === ctx.selectedObjectId} title={`${binder.name} : ${binder.type}`}><strong>{binder.name}</strong><span className="sr-binder-colon">:</span><span>{binder.type}</span></button>
      {binder.definition && <span className="sr-definition-value">:= <code>{formatExpression(binder.definition.value)}</code></span>}
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
  return <details className="sr-contained-expressions"><summary>Inside this expression <span>{count} {count === 1 ? 'relation' : 'relations'}</span></summary><p className="sr-contained-note">{componentMode(ctx.document) ? 'These parts retain their positions within the enclosing expression.' : 'These are parts of the expression, not separate assertions.'}</p>{groups.map(group => {
    const visible = group.relations.slice(0, Math.max(0, limit - preceding));
    preceding += group.relations.length;
    if (!visible.length) return null;
    const scopeRelations = group.relationIds.flatMap(id => ctx.relations.has(id) ? [ctx.relations.get(id)!] : []);
    return <section className="sr-contained-group" key={group.id} data-expression-scope={group.scopeId} aria-label={group.role === 'local-expression' ? 'Inside a local expression scope' : componentMode(ctx.document) ? 'Inside this expression' : 'Inside this clause expression'}>{group.role === 'local-expression' && <p className="sr-local-note">Local binders apply only within this expression.</p>}{visible.map(relation => <RelationFigure key={relation.id} relation={relation} relations={scopeRelations} ctx={ctx}/>)}</section>;
  })}{count > limit && <button type="button" className="sr-show-more" onClick={() => setLimit(current => current + 3)}>Show {counted(Math.min(3, count - limit), 'more contained relation')}</button>}</details>;
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
  return <section className="sr-clause" data-reading-node={node.id} aria-label={node.phrase || (componentMode(ctx.document) ? 'Selected expression' : 'Statement condition')}>
    <div className="sr-clause-heading"><SourceButton node={node} ctx={ctx}>{node.phrase || (componentMode(ctx.document) ? 'Expression' : 'Condition')} <span aria-hidden="true">↗</span></SourceButton>{panel?.coverage === 'partial' && <span className="sr-coverage-note">partly interpreted</span>}</div>
    {geometry || (roots.length > 0 ? <div className={`sr-clause-figures${roots.length > 1 ? ' sr-multiple-roots' : ''}`}>{(showAllRelations ? roots : roots.slice(0, 3)).map(relation => <RelationFigure key={relation.id} relation={relation} relations={relations} ctx={ctx}/>)}{roots.length > 3 && !showAllRelations && <button type="button" className="sr-show-more" onClick={() => setShowAllRelations(true)}>Show {counted(roots.length - 3, 'further relation')} in this {componentMode(ctx.document) ? 'expression' : 'clause'}</button>}</div> : <div className="sr-symbolic-clause"><code>{node.lean}</code><p>{componentMode(ctx.document) ? 'This expression is retained symbolically; no further interpretation is assigned.' : 'This clause is retained symbolically; no geometric interpretation is assigned.'}</p></div>)}
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

function StructuralBinderFigure({ object, ctx, enclosed }: { object: SemanticObject; ctx: RenderContext; enclosed?: boolean }) {
  const model = useMemo(() => compileStructuralObject(ctx.document, object), [ctx.document, object]);
  return model ? <StructuralObjectFigure model={model} selectedObjectId={ctx.selectedObjectId} onObjectSelect={ctx.onObjectSelect} enclosed={enclosed}
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
    if (node.binder?.role === 'auxiliary') { flush(); continue; }
    const bundled = recognized.filter(relation => relation.nodeId === node.id);
    const object = node.binder?.objectId ? ctx.objects.get(node.binder.objectId) : undefined;
    const structure = object?.binder?.structure || object?.binder?.structureOmission;
    if (!bundled.length && !structure) { run.push(node); continue; }
    flush();
    bundled.forEach(relation => figures.push(<RelationFigure key={relation.id} relation={relation} relations={relations} ctx={ctx}/>));
    if (structure && object) {
      const figure = <StructuralBinderFigure object={object} ctx={ctx} enclosed={bundled.length > 0}/>;
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
    body = <><div className="sr-object-introduction"><RegionHeader region={region} ctx={ctx} lead={lead} symbol={roleSymbol[role]} title={role === 'auxiliary' ? 'Recorded context entries' : componentMode(ctx.document) ? componentBinderTitle(binders, ctx.document) : role === 'universal' ? 'For every' : role === 'existential' ? 'A witness is required' : role === 'definition' ? 'Local definitions' : 'Parameters'}/><BinderStrip nodes={binders} ctx={ctx}/><BinderFigures nodes={binders} ctx={ctx}/>{binders.length < region.binders.length && <button type="button" className="sr-show-more" onClick={() => ctx.onNodeSelect?.(region.binders[binders.length].id)}>Read the next {counted(region.binders.length - binders.length, 'binder')}</button>}</div>{region.body && <AtlasRegion region={region.body} ctx={ctx} depth={depth + 1}/>}</>;
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
  return <section className={`sr-atlas-region sr-region-${region.kind}${focused ? ' sr-region-focused' : ''}${depth > 3 ? ' sr-deep-region' : ''}`} data-reading-step={region.id} data-reading-region={region.kind} data-source-nodes={region.sourceNodeIds.join(' ')} data-component-region={componentMode(ctx.document) ? ambientNodes([region.node], ctx.document) ? 'context' : 'expression' : undefined}>{componentMode(ctx.document) && region.sourceNodeIds.includes(ctx.document.presentation!.targetNodeId!) && <p className="sr-heading-lead" data-component-target={ctx.document.presentation!.target}>{ctx.componentTitle ?? (ctx.document.presentation!.target === 'type' ? 'Inferred type' : 'Selected term')} begins here.</p>}{body}</section>;
}

function overviewTitle(region: ReadingRegion, document: SemanticDocument): string {
  if (region.kind === 'binders' && region.node.binder?.role === 'auxiliary') return region.binders.map(node => contextEntryTitle(node.binder!)).join('; ');
  if (componentMode(document) && region.kind === 'binders') return `${componentBinderTitle(region.binders, document)}: ${region.binders.map(node => node.binder!.name).join(', ')}`;
  if (region.kind === 'binders') return `${roleText[region.node.binder!.role]} ${region.binders.map(node => node.binder!.name).join(', ')}`;
  if (region.kind === 'implication') return 'Given → conclusion';
  if (region.kind === 'all') return 'All conditions';
  if (region.kind === 'alternatives') return 'At least one alternative';
  if (region.kind === 'equivalence') return 'Both directions';
  if (region.kind === 'negation') return 'Not';
  return compactLabel(region.node.phrase || region.node.lean, 70);
}

function LogicOverview({ region, ctx, depth = 0 }: { region: ReadingRegion; ctx: RenderContext; depth?: number }): ReactNode {
  if (!region.sourceNodeIds.some(id => ctx.visibleNodes.has(id))) return <button type="button" className="sr-overview-more" onClick={() => ctx.onNodeSelect?.(region.id)}>{compactLabel(overviewTitle(region, ctx.document), 44)}…</button>;
  const children: { region: ReadingRegion; role?: string }[] = region.kind === 'binders' ? region.body ? [{ region: region.body }] : [] : region.kind === 'implication' ? [...region.assumptions.map(assumption => ({ region: assumption, role: 'Given' })), { region: region.conclusion, role: 'Then' }] : region.kind === 'negation' ? [{ region: region.body, role: 'Negated' }] : region.kind === 'clause' ? [] : region.children.map((child, index) => ({ region: child, role: region.kind === 'alternatives' ? `Alternative ${index + 1}` : region.kind === 'equivalence' ? `${index === 0 ? 'First' : 'Second'} condition` : undefined }));
  return <div className={`sr-overview-node${depth > 3 ? ' sr-overview-deep' : ''}`}><button type="button" className={region.sourceNodeIds.includes(ctx.reading.selection.nodeId) ? 'sr-overview-selected' : ''} onClick={() => ctx.onNodeSelect?.(region.id)} title={region.node.lean}>{overviewTitle(region, ctx.document)}</button>{children.length > 0 && <div className="sr-overview-children">{children.map(child => <div key={child.region.id}>{child.role && <span className="sr-overview-edge-label">{child.role}</span>}<LogicOverview region={child.region} ctx={ctx} depth={depth + 1}/></div>)}</div>}</div>;
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
    body = <>{cue.stage.kind === 'construction' && <p className="rg-construction-context">Constructing part of <span title={node.lean}>{compactLabel(node.phrase || node.lean, 180)}</span></p>}{cue.stage.kind === 'contained' && <p className="rg-local-binders">Part of <code>{node.lean}</code>.{componentMode(ctx.document) || relation?.fidelity === 'structural' ? ' This part retains its expression scope.' : ' This inner relation is not asserted separately.'}{group?.role === 'local-expression' && <> Local context: {localContext.join(' · ') || 'binders apply only inside this expression'}.</>}</p>}{relation && <RelationFigure relation={relation} relations={relations} ctx={focused}/>}</>;
  } else if (cue.intent === 'logic') {
    const grouped = cue.sourceNodeIds.flatMap(id => { const source = ctx.reading.nodes.find(candidate => candidate.id === id); return source?.kind === 'implies' ? [source] : []; });
    const children = node.kind === 'implies' && grouped.length ? [...grouped.map(source => source.children[0]), grouped.at(-1)!.children[1]] : node.children;
    body = <><div className="rg-logic-children">{children.map((child, index) => <div className="rg-logic-child" key={child.id}><span>{node.kind === 'implies' ? index < children.length - 1 ? 'Given' : 'Then' : node.kind === 'or' ? `Alternative ${index + 1}` : node.kind === 'not' ? 'Negated condition' : node.kind === 'iff' ? `${index === 0 ? 'First' : 'Second'} condition` : `Condition ${index + 1}`}</span><button type="button" onClick={() => ctx.onNodeSelect?.(child.id)} title={child.lean}>{compactLabel(child.phrase || child.lean, 180)}</button></div>)}</div><HypothesisStructures nodeIds={cue.sourceNodeIds} ctx={focused}/></>;
  } else body = <Clause node={node} ctx={focused}/>;
  return <>{body}<details className="rg-source-context"><summary>Lean fragment and source context</summary><code>{node.lean}</code></details></>;
}

/** The whole-statement overview scrolls within its own height: always named (a complementary landmark), and a Tab stop
 * only while it overflows (FigureScroll rule). Its own component, so an overflow change re-renders only the aside. */
function Overview({ name, children }: { name: string; children: ReactNode }) {
  const [overview, overflow] = useFrameOverflow<HTMLElement>(true);
  return <aside ref={overview} className="sr-overview" aria-label={name} tabIndex={overflow ? 0 : undefined}>{children}</aside>;
}

export function StatementReadingView(props: StatementReadingViewProps) {
  const { reading, document: semantic, selectedObjectId, selectedRelationId } = props;
  const surface = useRef<HTMLDivElement>(null);
  const complete = useRef<HTMLDetailsElement>(null);
  const [guideChoice, setGuideChoice] = useState<ReadingCueSelection | null>(null);
  const [readingMode, setReadingMode] = useState<'graph' | 'guided'>('guided');
  const [nodeLimit, setNodeLimit] = useState(100);
  const previousSelection = useRef(reading.selection.nodeId);
  const [traces, setTraces] = useState<{ id: string; path: string }[]>([]);
  const maps = useMemo<Maps>(() => ({ objects: new Map(semantic.objects.map(object => [object.id, object])), relations: new Map(semantic.relations.map(relation => [relation.id, relation])), panels: new Map(reading.panels.map(panel => [panel.id, panel])) }), [semantic, reading]);
  const presentation = useMemo(() => planReadingPresentation(reading, { boundaryNodeIds: componentMode(semantic) && semantic.presentation?.targetNodeId ? [semantic.presentation.targetNodeId] : [] }), [reading, semantic]);
  const cuePlan = useMemo(() => compileReadingCues(reading, semantic), [reading, semantic]);
  const scopedGraph = useMemo(() => cuePlan.truncated ? undefined : compileScopedStatementGraph(semantic, reading), [semantic, reading, cuePlan]);
  const activeCue = resolveReadingCue({ plan: cuePlan, document: semantic, selectedNodeId: reading.selection.nodeId,
    rootNodeId: reading.root.id, selectedRelationId, selection: props.selectedCue === undefined ? guideChoice : props.selectedCue });
  function chooseCue(cue: ReadingCue) {
    const selection = createReadingCueSelection(semantic, cue);
    if (props.selectedCue === undefined) setGuideChoice(selection);
    notifyReadingCueSelection(selection, props);
  }
  function chooseNode(id: string) {
    const cue = cuePlan.cues.find(candidate => candidate.sourceNodeIds.includes(id) && candidate.stage.kind === 'clause')
      ?? cuePlan.cues.find(candidate => candidate.sourceNodeIds.includes(id));
    const selection = cue ? createReadingCueSelection(semantic, cue, id) : null;
    if (props.selectedCue === undefined) setGuideChoice(selection);
    if (!cue && complete.current) complete.current.open = true;
    props.onNodeSelect?.(id);
    props.onCueChange?.(selection);
  }
  const graphNodeId = activeCue && scopedGraph?.clauses.some(clause => clause.node.id === activeCue.nodeId) ? activeCue.nodeId : undefined;
  const showGraph = readingMode === 'graph' && Boolean(scopedGraph);
  function chooseGraphClause(id: string) {
    const cue = cuePlan.cues.find(cue => cue.nodeId === id && cue.stage.kind === 'clause');
    if (cue) { setReadingMode('graph'); chooseCue(cue); }
  }
  useLayoutEffect(() => {
    const root = surface.current;
    if (!root || !selectedObjectId) { setTraces([]); return; }
    const update = () => {
      const box = root.getBoundingClientRect();
      // Chrome still reports layout boxes for the content of a closed <details>; exclude it explicitly.
      const nodes = [...root.querySelectorAll<HTMLElement>('[data-reading-object]')].filter(element => element.getAttribute('data-reading-object') === selectedObjectId && !element.closest('details:not([open]) > :not(summary)'));
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
  const guided = activeCue && <GuidedReading plan={cuePlan} cue={activeCue} reading={reading} document={semantic} onChoose={chooseCue} onObjectSelect={props.onObjectSelect}><CueFigure cue={activeCue} ctx={ctx}/></GuidedReading>;
  const graphical = showGraph && scopedGraph && <ScopedStatementGraph model={scopedGraph} document={semantic} reading={reading} focusedNodeId={graphNodeId} selectedObjectId={selectedObjectId} selectedRelationId={selectedRelationId}
    onObjectSelect={props.onObjectSelect} onNodeSelect={chooseGraphClause} onSourceSelect={props.onSourceSelect} onRelationSelect={id => {
      const cue = cuePlan.cues.find(candidate => candidate.stage.relationId === id);
      if (cue) chooseCue(cue);
      else { const relation = maps.relations.get(id); if (relation) { chooseNode(relation.nodeId); props.onSourceSelect?.(id); } }
    }}/>;
  return <div className="statement-reading-view"><div className="sr-atlas-layout"><div className="sr-atlas-main"><div className="sr-reading-intro"><span className="sr-reading-label">Visual reading</span><span className="sr-schematic-label">Symbolic schematics · no numerical choices</span></div><div ref={surface} className="sr-reading-surface">{scopedGraph && <nav className="ssg-mode" aria-label="Reading presentation"><button type="button" aria-pressed={showGraph} onClick={() => setReadingMode('graph')}>Construction graph</button><button type="button" aria-pressed={!showGraph} onClick={() => setReadingMode('guided')}>Guided reading</button></nav>}{showGraph ? graphical : guided}<details ref={complete} className="sr-complete-reading"><summary>{componentMode(semantic) ? 'Full visual reading' : 'Full visual statement'}</summary>{selectedObjectId && <svg className="sr-identity-traces" aria-hidden="true"><g style={{ '--trace-color': readingObjectColor(selectedObjectId) } as CSSProperties}>{traces.map(trace => <path key={trace.id} d={trace.path}/>)}</g></svg>}<div className="sr-reading-content" aria-label={componentMode(semantic) ? 'Ordered visual reading of the expression' : 'Ordered visual reading of the statement'}><AtlasRegion region={presentation.root} ctx={ctx}/></div></details></div>{reading.nodes.length > visibleNodes.size && <div className="sr-limit">Showing {visibleNodes.size} of {counted(reading.nodes.length, componentMode(semantic) ? 'expression node' : 'logical node')}, with the complete selected scope. <button type="button" className="sr-show-more" onClick={() => setNodeLimit(limit => limit + 100)}>Show the next {counted(Math.min(100, reading.nodes.length - visibleNodes.size), 'node')}</button></div>}<p className="sr-reading-note">{componentMode(semantic) ? 'Schematics follow expression structure and its context. Shapes and spacing carry no additional meaning.' : 'Schematics describe the conditions in their logical context. Shapes and spacing carry no unstated geometric meaning.'}</p></div><Overview name={componentMode(semantic) ? 'Expression and context' : 'Whole statement'}><div className="sr-overview-heading">{componentMode(semantic) ? 'Expression and context' : 'Whole statement'}</div><LogicOverview region={presentation.root} ctx={ctx}/></Overview></div></div>;
}
