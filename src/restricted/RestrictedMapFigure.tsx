import { useId, useMemo, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import { FigureScroll } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import { MathLabel } from '../components/MathLabel';
import { expressionDisplayNode, expressionMathDisplay, mathDisplay, sourceMathDisplay, type MathDisplay } from '../notation/math-display';
import { layoutRestrictedMap, type RestrictedLabelBox, type RestrictedRegionLayout } from './restricted-map-layout';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { readingObjectColor } from '../visual/object-identity';
import { compileRestrictedMap, type RestrictedMapStructure, type RestrictedRegion } from './model';
import './restricted.css';

export interface RestrictedMapFigureProps {
  document: SemanticDocument;
  relation: SemanticRelation;
  relations?: readonly SemanticRelation[];
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
}
type Interaction = Pick<RestrictedMapFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
const short = (value: string, length = 40) => value.length > length ? `${value.slice(0, length - 1)}…` : value;

function ObjectControl({ object, ...interaction }: Interaction & { object: SemanticObject }) {
  return <button type="button" className={`rm-object${interaction.selectedObjectId === object.id ? ' rm-selected' : ''}`} data-reading-object={object.id}
    style={{ '--rm-object': readingObjectColor(object.id) } as CSSProperties}
    title={`${object.label}${object.type ? ` : ${object.type}` : ''}`} aria-label={`${object.label}${object.type ? ` : ${object.type}` : ''}`}
    aria-pressed={interaction.selectedObjectId === object.id} onClick={() => interaction.onObjectSelect?.(object.id)}>{short(object.label, 96)}</button>;
}

function SvgIdentity({ object, children, ...interaction }: Interaction & { object?: SemanticObject; children: ReactNode }) {
  const actionable = object && interaction.onObjectSelect;
  const activate = (event: KeyboardEvent<SVGGElement>) => {
    if (actionable && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); interaction.onObjectSelect!(object.id); }
  };
  return <g className={`rm-svg-object${object && interaction.selectedObjectId === object.id ? ' rm-selected' : ''}`} data-reading-object={object?.id}
    style={object ? { '--rm-object': readingObjectColor(object.id) } as CSSProperties : undefined}
    role={actionable ? 'button' : 'group'} aria-label={object?.label} aria-pressed={actionable ? interaction.selectedObjectId === object.id : undefined}
    tabIndex={actionable ? 0 : undefined} onKeyDown={activate} onClick={() => object && interaction.onObjectSelect?.(object.id)}>
    {object && <title>{`${object.label}${object.type ? ` : ${object.type}` : ''}`}</title>}{children}
  </g>;
}

function DiagramLabel({ label, box, name, className, fontSize = 14 }: { label: string | MathDisplay; box: RestrictedLabelBox; name: string; className: string; fontSize?: number }) {
  return typeof label === 'string'
    ? <text className={className} data-diagram-label={name} x={box.x + box.width / 2} y={box.baseline} textAnchor="middle">{label}</text>
    : <MathLabel label={label} labelKey={name} x={box.x + box.width / 2} y={box.baseline} fontSize={fontSize} textAnchor="middle" className={className}/>;
}

const regionLabels = (region: RestrictedRegion, carrier: SemanticObject, open: boolean) => ({
  carrier: expressionMathDisplay(carrier.expression, carrier.label), carrierRole: `${region.role} carrier`, role: `${open ? 'open ' : ''}${region.role} region`,
  name: region.empty ? mathDisplay({ kind: 'symbol', symbol: 'empty' }) : region.object ? expressionMathDisplay(region.object.expression, region.label) : sourceMathDisplay(region.label), note: region.empty ? 'empty set' : 'possibly empty',
});

function Region({ region, carrier, layout, labels, selected, ...interaction }: Interaction & {
  region: RestrictedRegion; carrier: SemanticObject; layout: RestrictedRegionLayout;
  labels: ReturnType<typeof regionLabels>; selected: boolean;
}) {
  const label = (key: keyof typeof labels, className: string) => <DiagramLabel label={labels[key]} box={layout.labels[key]} name={`${region.role}-${key}`} className={className} fontSize={key === 'carrier' ? 20 : key === 'name' ? 17 : 14}/>;
  return <g data-restricted-region={region.role} data-region-evidence={region.object ? 'source-expression' : 'schematic'} data-region-selected={selected || undefined}>
    <SvgIdentity object={carrier} {...interaction}>
      <rect className="rm-carrier" {...layout.carrier} rx="11"/>
      {label('carrier', 'rm-carrier-label')}{label('carrierRole', 'rm-annotation')}
    </SvgIdentity>
    <SvgIdentity object={region.object} {...interaction}>
      {!region.object && <title>{region.label}</title>}
      <rect className={`rm-region${selected ? ' rm-region-focused' : ''}`} {...layout.region} rx="6"/>
      {label('role', 'rm-region-role')}{label('name', 'rm-region-name')}{label('note', 'rm-annotation')}
    </SvgIdentity>
  </g>;
}

export interface RestrictedRegionDiagramProps extends Interaction {
  structure: RestrictedMapStructure;
  selectedRegion?: 'source' | 'target';
  applicationDirection?: 'forward' | 'inverse';
}

/** A reusable diagram composed from containment, maps, and guarded inverse laws. */
export function RestrictedRegionDiagram({ structure: model, selectedRegion, applicationDirection, ...interaction }: RestrictedRegionDiagramProps) {
  const marker = `rm-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const text = useDiagramText();
  const continuity = model.properties.forwardContinuousOnSource && model.properties.inverseContinuousOnTarget ? 'continuous on these regions'
    : model.properties.forwardContinuousOnSource ? 'forward continuous on source'
      : model.properties.inverseContinuousOnTarget ? 'inverse continuous on target' : 'inverse on these regions';
  const note = model.sameCarrier ? 'Two roles of the same carrier; the regions may overlap.' : 'Abstract containers; no geometry or coordinates are specified.';
  const sourceLabels = regionLabels(model.source, model.sourceCarrier, model.properties.sourceOpen);
  const targetLabels = regionLabels(model.target, model.targetCarrier, model.properties.targetOpen);
  const sizes = (role: string, labels: ReturnType<typeof regionLabels>) => ({
    carrier: text.size(`${role}-carrier`, labels.carrier.source, 20), carrierRole: text.size(`${role}-carrierRole`, labels.carrierRole, 10.5),
    role: text.size(`${role}-role`, labels.role, 11), name: text.size(`${role}-name`, labels.name.source, 17), note: text.size(`${role}-note`, labels.note, 10.5),
  });
  const forward = expressionMathDisplay(model.map.expression, model.map.label), mapNode = expressionDisplayNode(model.map.expression);
  const inverseSource = `${model.map.label}⁻¹`;
  const inverse = mapNode ? mathDisplay({ kind: 'script', base: mapNode, superscript: { kind: 'literal', value: -1 } }, inverseSource) : sourceMathDisplay(inverseSource);
  const layout = layoutRestrictedMap(sizes('source', sourceLabels), sizes('target', targetLabels),
    text.size('forward', forward.source, 17), text.size('inverse', inverse.source, 17), text.size('continuity', continuity, 10.5), text.size('note', note, 10.5));
  const arrow = (direction: 'forward' | 'inverse') => {
    const { from, to } = layout.arrows[direction];
    return <path data-restricted-arrow={direction} className={`rm-map-arrow${applicationDirection === direction ? ' rm-arrow-focused' : ''}`}
      d={`M${from.x} ${from.y} H${to.x}`} markerEnd={`url(#${marker})`}/>;
  };
  return <FigureScroll className="rm-scroll" label="Restricted map diagram; scroll to see all of it"><svg ref={text.ref} className="rm-diagram"
    style={{ minWidth: Math.ceil(layout.width * 10 / 10.5) }} viewBox={`0 0 ${layout.width} ${layout.height}`} role="group" aria-label="Two abstract carrier spaces with valid source and target regions, linked by mutually inverse restricted maps">
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    <Region region={model.source} carrier={model.sourceCarrier} layout={layout.source} labels={sourceLabels} selected={selectedRegion === 'source'} {...interaction}/>
    <Region region={model.target} carrier={model.targetCarrier} layout={layout.target} labels={targetLabels} selected={selectedRegion === 'target'} {...interaction}/>
    <SvgIdentity object={model.map} {...interaction}>
      {arrow('forward')}<DiagramLabel label={forward} box={layout.forward} name="forward" className="rm-map-name" fontSize={17}/>
      {arrow('inverse')}<DiagramLabel label={inverse} box={layout.inverse} name="inverse" className="rm-map-name" fontSize={17}/>
    </SvgIdentity>
    <DiagramLabel label={continuity} box={layout.continuity} name="continuity" className="rm-annotation"/>
    <DiagramLabel label={note} box={layout.note} name="note" className="rm-annotation"/>
  </svg></FigureScroll>;
}

function RoundTrip({ model, role }: { model: RestrictedMapStructure; role: 'source' | 'target' }) {
  const source = role === 'source', region = source ? model.source : model.target, map = short(model.map.label, 28);
  return <div className="rm-law" data-restricted-law={role}>
    <div className="rm-law-condition">{region.empty ? 'Vacuous when this region is empty' : `For every element in the ${role} region`}</div>
    <div className="rm-law-flow" aria-label={source ? 'Forward then inverse returns the original source element' : 'Inverse then forward returns the original target element'}>
      <span className="rm-law-slot">{source ? 'x' : 'y'}</span><span className="rm-law-step"><b>{source ? map : `${map}⁻¹`}</b><span aria-hidden="true">⟶</span></span>
      <span className="rm-law-slot">{source ? `${map}(x)` : `${map}⁻¹(y)`}</span><span className="rm-law-step"><b>{source ? `${map}⁻¹` : map}</b><span aria-hidden="true">⟶</span></span>
      <span className="rm-law-slot rm-return">{source ? 'x' : 'y'}</span>
    </div>
    <span className="rm-law-caption">{source ? 'Back to the same source element' : 'Back to the same target element'}</span>
  </div>;
}

export function RestrictedRoundTrips({ structure }: { structure: RestrictedMapStructure }) {
  return <div className="rm-laws"><RoundTrip model={structure} role="source"/><RoundTrip model={structure} role="target"/></div>;
}

/** Regions encode type-provided laws, not coordinates, points, or chosen examples. */
export function RestrictedMapFigure({ document, relation, relations, ...interaction }: RestrictedMapFigureProps) {
  const model = useMemo(() => compileRestrictedMap(document, relation, relations), [document, relation, relations]);
  if (!model) return null;
  return <figure className={`restricted-map rm-${model.kind}`} data-restricted-relation={relation.id} data-restricted-kind={model.kind}
    data-restricted-scope={model.scopeId} data-restricted-direction={model.direction} data-restricted-map-kind={model.mapKind} aria-label={model.title}>
    <div className="rm-heading"><strong>{model.title}</strong><span>Abstract regions and maps</span></div>
    <div className="rm-objects"><span>Map</span><ObjectControl object={model.map} {...interaction}/><span>between</span><ObjectControl object={model.sourceCarrier} {...interaction}/><span>and</span><ObjectControl object={model.targetCarrier} {...interaction}/></div>
    {model.application && <div className="rm-application" data-restricted-application={model.direction}>
      <span className="rm-application-label">Source expression</span><ObjectControl object={model.application.input} {...interaction}/>
      <span className="rm-application-operation">{model.direction === 'inverse' ? 'inverse map' : 'forward map'} <span aria-hidden="true">⟶</span></span>
      <ObjectControl object={model.application.output} {...interaction}/><p>Region membership must come from the surrounding statement.</p>
    </div>}
    <RestrictedRegionDiagram structure={model} selectedRegion={model.selectedRegion} applicationDirection={model.application ? model.direction : undefined} {...interaction}/>
    <RestrictedRoundTrips structure={model}/>
    <p className="rm-explanation">{model.explanation}</p>
    <figcaption>The letters in the round trips are schematic bound variables, not chosen points. Region frames indicate containment, not shape, size, dimension, connectedness, or a proper subset. The inverse laws apply on the specified regions; no inverse law is asserted on the whole carriers.</figcaption>
  </figure>;
}
