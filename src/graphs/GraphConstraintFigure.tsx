import { useId, useMemo, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import { FigureScroll } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import { MathLabel } from '../components/MathLabel';
import { expressionDisplayNode, expressionMathDisplay, identifierMathDisplay, mathDisplay, sourceMathDisplay, withMathProse, type MathDisplay, type MathDisplayNode } from '../notation/math-display';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { readingObjectColor } from '../visual/object-identity';
import { compileGraphConstraint, type GraphConstraintModel, type GraphEndpoint, type GraphPalette } from './model';
import { layoutGraphAdjacency, layoutGraphRule, type GraphLabelPlacement } from './graph-constraint-layout';
import './graphs.css';

export interface GraphConstraintFigureProps {
  document: SemanticDocument;
  relation: SemanticRelation;
  relations?: readonly SemanticRelation[];
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
}
type Interaction = Pick<GraphConstraintFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
const short = (value: string, length = 48) => value.length > length ? `${value.slice(0, length - 1)}…` : value;
const swatches = ['#4b86a0', '#cb9951', '#8e73b2', '#62a08d', '#b97986', '#869548', '#bf8d72', '#7687b5'];

function ObjectControl({ object, ...interaction }: Interaction & { object: SemanticObject }) {
  return <button type="button" className={`gc-object${interaction.selectedObjectId === object.id ? ' gc-selected' : ''}`} data-reading-object={object.id} style={{ '--gc-object': readingObjectColor(object.id) } as CSSProperties} aria-label={`${object.label}${object.type ? ` : ${object.type}` : ''}`} title={`${object.label}${object.type ? ` : ${object.type}` : ''}`} aria-pressed={interaction.selectedObjectId === object.id} onClick={() => interaction.onObjectSelect?.(object.id)}>{short(object.label, 72)}</button>;
}
function SvgIdentity({ object, children, ...interaction }: Interaction & { object?: SemanticObject; children: ReactNode }) {
  const actionable = object && interaction.onObjectSelect;
  const activate = (event: KeyboardEvent<SVGGElement>) => { if (actionable && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); interaction.onObjectSelect!(object.id); } };
  return <g className={`gc-svg-object${object && interaction.selectedObjectId === object.id ? ' gc-selected' : ''}`} data-reading-object={object?.id} style={object ? { '--gc-object': readingObjectColor(object.id) } as CSSProperties : undefined} role={actionable ? 'button' : 'group'} aria-label={object?.label} aria-pressed={actionable ? interaction.selectedObjectId === object.id : undefined} tabIndex={actionable ? 0 : undefined} onKeyDown={activate} onClick={() => object && interaction.onObjectSelect?.(object.id)}>{object && <title>{`${object.label}${object.type ? ` : ${object.type}` : ''}`}</title>}{children}</g>;
}
function DiagramLabel({ id, placement, className, fontSize = 14, children }: { id: string; placement: GraphLabelPlacement; className?: string; fontSize?: number; children: string | MathDisplay }) {
  return typeof children === 'string'
    ? <text data-diagram-label={id} x={placement.x} y={placement.y} textAnchor="middle" className={className}>{children}</text>
    : <MathLabel label={children} labelKey={id} x={placement.x} y={placement.y} fontSize={fontSize} textAnchor="middle" className={className}/>;
}
// These slots are the existing schematic inputs, never semantic object IDs.
const slotNode = (index: number): MathDisplayNode => ({ kind: 'script', base: { kind: 'identifier', name: 'v' }, subscript: { kind: 'literal', value: index + 1 } });
const endpointMath = (endpoint: GraphEndpoint, index: number) => endpoint.object
  ? expressionMathDisplay(endpoint.object.expression, endpoint.label) : mathDisplay(slotNode(index), endpoint.label);

function Endpoint({ endpoint, index, x, y, label, ...interaction }: Interaction & { endpoint: GraphEndpoint; index: number; x: number; y: number; label: GraphLabelPlacement }) {
  return <SvgIdentity object={endpoint.object} {...interaction}><g data-graph-endpoint={endpoint.id} data-endpoint-role={endpoint.role}><circle cx={x} cy={y} r="19" className={`gc-vertex${endpoint.role === 'arbitrary-slot' ? ' gc-slot' : ''}`}/><DiagramLabel id={`endpoint:${index}`} placement={label} className="gc-endpoint-label">{endpointMath(endpoint, index)}</DiagramLabel></g></SvgIdentity>;
}

function Adjacency({ model, ...interaction }: Interaction & { model: GraphConstraintModel }) {
  const text = useDiagramText();
  const [left, right] = model.endpoints;
  const annotation = model.sameEndpoint ? 'the same vertex occurs at both endpoints' : 'adjacency required by this condition';
  const layout = layoutGraphAdjacency([text.size('endpoint:0', endpointMath(left, 0).source, 14), text.size('endpoint:1', endpointMath(right, 1).source, 14)], text.size('adjacency', annotation, 11.5), model.sameEndpoint);
  return <FigureScroll label="Graph condition diagram; scroll to see all of it"><svg ref={text.ref} style={{ minWidth: Math.ceil(layout.width * 10 / 11.5) }} viewBox={`0 0 ${layout.width} ${layout.height}`} role="group" aria-label="Named adjacency condition; this is not a complete graph drawing">
    {model.sameEndpoint ? <path className="gc-edge gc-conditional" d={`M${layout.center - 13} ${layout.vertexY - 11} C${layout.center - 61} ${layout.vertexY - 66} ${layout.center + 61} ${layout.vertexY - 66} ${layout.center + 13} ${layout.vertexY - 11}`}/> : <path className="gc-edge gc-conditional" d={`M${layout.x[0] + 19} ${layout.vertexY} H${layout.x[1] - 19}`}/>}
    <Endpoint endpoint={left} index={0} x={layout.x[0]} y={layout.vertexY} label={layout.labels[0]} {...interaction}/>
    {!model.sameEndpoint && <Endpoint endpoint={right} index={1} x={layout.x[1]} y={layout.vertexY} label={layout.labels[1]} {...interaction}/>}
    <DiagramLabel id="adjacency" placement={layout.annotation} className="gc-annotation">{annotation}</DiagramLabel>
  </svg></FigureScroll>;
}

function GraphRule({ model, marker, ...interaction }: Interaction & { model: GraphConstraintModel; marker: string }) {
  const text = useDiagramText();
  const kind = model.kind === 'map' ? 'map' : 'coloring';
  const operation = model.map ?? model.coloring, name = operation?.label ?? 'color';
  const operationLabel = operation ? expressionMathDisplay(operation.expression, name) : identifierMathDisplay(name);
  const operationNode = operation ? expressionDisplayNode(operation.expression) : { kind: 'identifier' as const, name };
  const sourceAnnotation = kind === 'map' ? 'adjacency in the source graph' : 'if these endpoints are adjacent';
  const applyAnnotation = withMathProse(operationLabel, kind === 'map' ? `${model.mapKind === 'embedding' ? 'if and only if' : 'requires'} · apply ` : 'apply ');
  const resultAnnotation = kind === 'map' ? 'adjacency in the target graph' : 'different labels, for every edge';
  const outputs = [0, 1].map(index => {
    const source = `${name}(${index === 0 ? 'v₁' : 'v₂'})`;
    return operationNode ? mathDisplay({ kind: 'application', fn: operationNode, args: [slotNode(index)] }, source) : sourceMathDisplay(source);
  });
  const inequality = mathDisplay({ kind: 'symbol', symbol: 'ne' });
  const layout = layoutGraphRule(kind, {
    endpoints: [text.size('endpoint:0', endpointMath(model.endpoints[0], 0).source, 14), text.size('endpoint:1', endpointMath(model.endpoints[1], 1).source, 14)],
    outputs: [text.size('output:0', outputs[0].source, 14), text.size('output:1', outputs[1].source, 14)],
    sourceAnnotation: text.size('source-annotation', sourceAnnotation, 11.5), applyAnnotation: text.size('apply-annotation', applyAnnotation.source, 11.5),
    resultAnnotation: text.size('result-annotation', resultAnnotation, 11.5), inequality: text.size('inequality', '≠', 30),
  });
  const description = kind === 'coloring' ? 'For any adjacent endpoint pair, a proper coloring assigns unequal labels' : model.mapKind === 'embedding' ? 'A graph embedding preserves and reflects adjacency' : 'This graph map sends every edge to an edge';
  return <FigureScroll label="Graph condition diagram; scroll to see all of it"><svg ref={text.ref} style={{ minWidth: Math.ceil(layout.width * 10 / 11.5) }} viewBox={`0 0 ${layout.width} ${layout.height}`} role="group" aria-label={description}>
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    <path className="gc-edge gc-conditional" d={`M${layout.x[0] + 19} ${layout.vertexY} H${layout.x[1] - 19}`}/>
    <DiagramLabel id="source-annotation" placement={layout.sourceAnnotation} className="gc-annotation">{sourceAnnotation}</DiagramLabel>
    {model.endpoints.map((endpoint, index) => <Endpoint key={endpoint.id} endpoint={endpoint} index={index} x={layout.x[index]} y={layout.vertexY} label={layout.endpoints[index]} {...interaction}/>)}
    <SvgIdentity object={model.coloring ?? model.map} {...interaction}>
      {layout.x.map((x, index) => <path key={index} className="gc-map-arrow" d={`M${x} ${layout.arrowTop} V${layout.arrowBottom}`} markerEnd={`url(#${marker})`}/>)}
      <DiagramLabel id="apply-annotation" placement={layout.applyAnnotation} className="gc-annotation" fontSize={11.5}>{applyAnnotation}</DiagramLabel>
    </SvgIdentity>
    {kind === 'map' && <path className="gc-edge gc-conditional" d={`M${layout.x[0] + 19} ${layout.outputY} H${layout.x[1] - 19}`}/>}
    {outputs.map((output, index) => <g key={index} className={kind === 'coloring' ? 'gc-color-expression' : undefined} data-endpoint-role={kind === 'map' ? 'arbitrary-image-slot' : undefined}>
      {kind === 'coloring' ? <rect {...layout.boxes[index]} rx="8"/> : <circle className="gc-vertex gc-slot" cx={layout.x[index]} cy={layout.outputY} r="19"/>}
      <DiagramLabel id={`output:${index}`} placement={layout.outputs[index]} className={kind === 'map' ? 'gc-endpoint-label' : undefined}>{output}</DiagramLabel>
    </g>)}
    {kind === 'coloring' && <DiagramLabel id="inequality" placement={layout.inequality} className="gc-inequality" fontSize={30}>{inequality}</DiagramLabel>}
    <DiagramLabel id="result-annotation" placement={layout.resultAnnotation} className="gc-annotation">{resultAnnotation}</DiagramLabel>
  </svg></FigureScroll>;
}

function Palette({ palette, ...interaction }: Interaction & { palette: GraphPalette }) {
  return <div className="gc-palette" data-palette-kind={palette.kind} data-color-count={palette.count}>
    <div className="gc-palette-heading"><span>{palette.kind === 'finite' ? `${palette.count} available color ${palette.count === '1' ? 'label' : 'labels'}` : 'Color type or bound'}</span><ObjectControl object={palette.object} {...interaction}/></div>
    {palette.kind === 'finite' ? <>{palette.labels.length > 0 && <div className="gc-palette-labels" aria-label="Available labels; no vertex assignment is chosen">{palette.labels.map((label, index) => <span key={label} data-palette-label={label} style={{ '--gc-swatch': swatches[index] } as CSSProperties}><i aria-hidden="true"/>{label}</span>)}{palette.omittedCount && <span className="gc-palette-more">+ {palette.omittedCount} further labels</span>}</div>}<p>{palette.count === '0' ? 'The palette is empty.' : 'These are available labels, not colors assigned to the displayed endpoint slots. A coloring may use fewer labels.'}</p></> : <p>This type or bound is retained symbolically; no finite palette or cardinality is inferred.</p>}
  </div>;
}

/** A symbolic constraint grammar, not a layout of a fabricated example graph. */
export function GraphConstraintFigure({ document, relation, relations, ...interaction }: GraphConstraintFigureProps) {
  const model = useMemo(() => compileGraphConstraint(document, relation, relations), [document, relation, relations]);
  const marker = `gc-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  if (!model) return null;
  const empty = model.palette?.count === '0';
  return <figure className={`graph-constraint gc-${model.kind}`} data-graph-relation={relation.id} data-graph-kind={model.kind} data-graph-scope={model.scopeId} aria-label={model.title}>
    <div className="gc-heading"><strong>{model.title}</strong><span>Symbolic graph structure</span></div>
    <div className="gc-objects"><span>{model.kind === 'map' ? 'From' : 'Graph'}</span><ObjectControl object={model.graph} {...interaction}/>{model.targetGraph && <><span>to</span><ObjectControl object={model.targetGraph} {...interaction}/></>}{model.coloring && <><span>using coloring</span><ObjectControl object={model.coloring} {...interaction}/></>}{model.map && <><span>using map</span><ObjectControl object={model.map} {...interaction}/></>}</div>
    {model.application && <div className="gc-application" aria-label="The application appearing in the source"><span className="gc-application-role">Input</span><ObjectControl object={model.application.vertex} {...interaction}/><span className="gc-application-role">apply</span><ObjectControl object={model.coloring ?? model.map!} {...interaction}/><span className="gc-application-arrow" aria-hidden="true">⟶</span><ObjectControl object={model.application.value} {...interaction}/><span className="gc-application-label">source application</span></div>}
    {model.kind === 'adjacency' ? <Adjacency model={model} {...interaction}/> : empty ? <div className="gc-empty-palette"><span aria-hidden="true">∅</span><strong>Empty vertex type required</strong><p>With no vertices there are no edges to check. No endpoint slots are instantiated.</p></div> : <GraphRule model={model} marker={marker} {...interaction}/>}
    <p className="gc-explanation">{model.explanation}</p>
    {model.palette && <Palette palette={model.palette} {...interaction}/>}
    {model.palette?.count === '1' && <p className="gc-one-color">With one available label, any adjacent pair would require an impossible inequality. A one-label coloring therefore requires no edges; it does not require a single vertex.</p>}
    <figcaption>{model.kind === 'adjacency' ? 'Positions encode endpoint roles, not distinctness or geometry. This condition does not specify the full graph.' : 'Endpoint slots stand for arbitrary inputs to the rule. They do not instantiate vertices, assert that an edge exists, or determine the graph’s size or shape.'} {model.kind === 'colorable' && 'Existence remains the statement’s condition; no witness is selected.'}</figcaption>
  </figure>;
}
