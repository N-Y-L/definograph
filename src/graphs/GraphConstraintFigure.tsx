import { useId, useMemo, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { readingObjectColor } from '../visual/object-identity';
import { compileGraphConstraint, type GraphConstraintModel, type GraphEndpoint, type GraphPalette } from './model';
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
function Endpoint({ endpoint, x, y, ...interaction }: Interaction & { endpoint: GraphEndpoint; x: number; y: number }) {
  return <SvgIdentity object={endpoint.object} {...interaction}><g data-graph-endpoint={endpoint.id} data-endpoint-role={endpoint.role}><circle cx={x} cy={y} r="19" className={`gc-vertex${endpoint.role === 'arbitrary-slot' ? ' gc-slot' : ''}`}/><text x={x} y={y + 43} textAnchor="middle" className="gc-endpoint-label">{short(endpoint.label, 22)}</text></g></SvgIdentity>;
}

function Adjacency({ model, ...interaction }: Interaction & { model: GraphConstraintModel }) {
  const [left, right] = model.endpoints;
  return <svg viewBox="0 0 560 164" role="group" aria-label="Named adjacency condition; this is not a complete graph drawing">
    {model.sameEndpoint ? <><path className="gc-edge gc-conditional" d="M267 64 C219 10 341 10 293 64"/><Endpoint endpoint={left} x={280} y={75} {...interaction}/><text x="280" y="145" textAnchor="middle" className="gc-annotation">the same vertex occurs at both endpoints</text></> : <><path className="gc-edge gc-conditional" d="M145 74 H415"/><text x="280" y="50" textAnchor="middle" className="gc-annotation">adjacency required by this condition</text><Endpoint endpoint={left} x={126} y={74} {...interaction}/><Endpoint endpoint={right} x={434} y={74} {...interaction}/></>}
  </svg>;
}

function ColorRule({ model, marker, ...interaction }: Interaction & { model: GraphConstraintModel; marker: string }) {
  const name = model.coloring ? short(model.coloring.label, 18) : 'color';
  return <svg viewBox="0 0 560 245" role="group" aria-label="For any adjacent endpoint pair, a proper coloring assigns unequal labels">
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    <path className="gc-edge gc-conditional" d="M145 55 H415"/><text x="280" y="30" textAnchor="middle" className="gc-annotation">if these endpoints are adjacent</text>
    <Endpoint endpoint={model.endpoints[0]} x={126} y={55} {...interaction}/><Endpoint endpoint={model.endpoints[1]} x={434} y={55} {...interaction}/>
    <SvgIdentity object={model.coloring} {...interaction}><path className="gc-map-arrow" d="M126 109 V156" markerEnd={`url(#${marker})`}/><path className="gc-map-arrow" d="M434 109 V156" markerEnd={`url(#${marker})`}/><text x="280" y="133" textAnchor="middle" className="gc-annotation">apply {name}</text></SvgIdentity>
    {[126, 434].map((x, index) => <g key={x} className="gc-color-expression"><rect x={x - 74} y="169" width="148" height="43" rx="8"/><text x={x} y="196" textAnchor="middle">{name}({index === 0 ? 'v₁' : 'v₂'})</text></g>)}
    <text x="280" y="198" textAnchor="middle" className="gc-inequality">≠</text><text x="280" y="235" textAnchor="middle" className="gc-annotation">different labels, for every edge</text>
  </svg>;
}

function MapRule({ model, marker, ...interaction }: Interaction & { model: GraphConstraintModel; marker: string }) {
  const name = short(model.map!.label, 18);
  return <svg viewBox="0 0 560 246" role="group" aria-label={model.mapKind === 'embedding' ? 'A graph embedding preserves and reflects adjacency' : 'This graph map sends every edge to an edge'}>
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    <path className="gc-edge gc-conditional" d="M145 50 H415"/><text x="280" y="24" textAnchor="middle" className="gc-annotation">adjacency in the source graph</text>
    <Endpoint endpoint={model.endpoints[0]} x={126} y={50} {...interaction}/><Endpoint endpoint={model.endpoints[1]} x={434} y={50} {...interaction}/>
    <SvgIdentity object={model.map} {...interaction}><path className="gc-map-arrow" d="M126 106 V158" markerEnd={`url(#${marker})`}/><path className="gc-map-arrow" d="M434 106 V158" markerEnd={`url(#${marker})`}/><text x="280" y="129" textAnchor="middle" className="gc-annotation">{model.mapKind === 'embedding' ? 'if and only if' : 'requires'} · apply {name}</text></SvgIdentity>
    <path className="gc-edge gc-conditional" d="M145 188 H415"/>{[126, 434].map((x, index) => <g key={x} data-endpoint-role="arbitrary-image-slot"><circle className="gc-vertex gc-slot" cx={x} cy="188" r="19"/><text x={x} y="228" textAnchor="middle" className="gc-endpoint-label">{name}({index === 0 ? 'v₁' : 'v₂'})</text></g>)}<text x="280" y="212" textAnchor="middle" className="gc-annotation">adjacency in the target graph</text>
  </svg>;
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
    {model.kind === 'adjacency' ? <Adjacency model={model} {...interaction}/> : empty ? <div className="gc-empty-palette"><span aria-hidden="true">∅</span><strong>Empty vertex type required</strong><p>With no vertices there are no edges to check. No endpoint slots are instantiated.</p></div> : model.kind === 'map' ? <MapRule model={model} marker={marker} {...interaction}/> : <ColorRule model={model} marker={marker} {...interaction}/>}
    <p className="gc-explanation">{model.explanation}</p>
    {model.palette && <Palette palette={model.palette} {...interaction}/>}
    {model.palette?.count === '1' && <p className="gc-one-color">With one available label, any adjacent pair would require an impossible inequality. A one-label coloring therefore requires no edges; it does not require a single vertex.</p>}
    <figcaption>{model.kind === 'adjacency' ? 'Positions encode endpoint roles, not distinctness or geometry. This condition does not specify the full graph.' : 'Endpoint slots stand for arbitrary inputs to the rule. They do not instantiate vertices, assert that an edge exists, or determine the graph’s size or shape.'} {model.kind === 'colorable' && 'Existence remains the statement’s condition; no witness is selected.'}</figcaption>
  </figure>;
}
