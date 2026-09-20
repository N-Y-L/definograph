import { useId, useMemo, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
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

function Region({ region, carrier, x, open, selected, ...interaction }: Interaction & { region: RestrictedRegion; carrier: SemanticObject; x: number; open: boolean; selected: boolean }) {
  return <g data-restricted-region={region.role} data-region-evidence={region.object ? 'source-expression' : 'schematic'} data-region-selected={selected || undefined}>
    <SvgIdentity object={carrier} {...interaction}>
      <rect className="rm-carrier" x={x} y="26" width="204" height="215" rx="11"/>
      <text className="rm-carrier-label" x={x + 102} y="58" textAnchor="middle">{short(carrier.label, 19)}</text>
      <text className="rm-annotation" x={x + 102} y="79" textAnchor="middle">{region.role === 'source' ? 'source' : 'target'} carrier</text>
    </SvgIdentity>
    <SvgIdentity object={region.object} {...interaction}>
      <rect className={`rm-region${selected ? ' rm-region-focused' : ''}`} x={x + 18} y="104" width="168" height="111" rx="6"/>
      <text className="rm-region-role" x={x + 102} y="129" textAnchor="middle">{open ? 'open ' : ''}{region.role} region</text>
      <text className="rm-region-name" x={x + 102} y="161" textAnchor="middle"><title>{region.label}</title>{region.empty ? '∅' : short(region.label, 18)}</text>
      <text className="rm-annotation" x={x + 102} y="188" textAnchor="middle">{region.empty ? 'empty set' : 'possibly empty'}</text>
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
  const continuity = model.properties.forwardContinuousOnSource && model.properties.inverseContinuousOnTarget ? 'continuous on these regions'
    : model.properties.forwardContinuousOnSource ? 'forward continuous on source'
      : model.properties.inverseContinuousOnTarget ? 'inverse continuous on target' : 'inverse on these regions';
  return <svg className="rm-diagram" viewBox="0 0 680 270" role="group" aria-label="Two abstract carrier spaces with valid source and target regions, linked by mutually inverse restricted maps">
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    <Region region={model.source} carrier={model.sourceCarrier} x={10} open={model.properties.sourceOpen} selected={selectedRegion === 'source'} {...interaction}/>
    <Region region={model.target} carrier={model.targetCarrier} x={466} open={model.properties.targetOpen} selected={selectedRegion === 'target'} {...interaction}/>
    <SvgIdentity object={model.map} {...interaction}>
      <path data-restricted-arrow="forward" className={`rm-map-arrow${applicationDirection === 'forward' ? ' rm-arrow-focused' : ''}`} d="M202 139 H474" markerEnd={`url(#${marker})`}/>
      <text className="rm-map-name" x="340" y="119" textAnchor="middle"><title>{model.map.label}</title>{short(model.map.label, 19)}</text>
      <path data-restricted-arrow="inverse" className={`rm-map-arrow${applicationDirection === 'inverse' ? ' rm-arrow-focused' : ''}`} d="M478 183 H206" markerEnd={`url(#${marker})`}/>
      <text className="rm-map-name" x="340" y="209" textAnchor="middle"><title>{`${model.map.label}⁻¹`}</title>{short(model.map.label, 18)}⁻¹</text>
    </SvgIdentity>
    <text className="rm-annotation" x="340" y="163" textAnchor="middle">{continuity}</text>
    <text className="rm-annotation" x="340" y="262" textAnchor="middle">{model.sameCarrier ? 'Two roles of the same carrier; the regions may overlap.' : 'Abstract containers; no geometry or coordinates are specified.'}</text>
  </svg>;
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
