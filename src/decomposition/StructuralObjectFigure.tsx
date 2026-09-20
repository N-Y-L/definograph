import { useId, useState, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import type { SemanticObject } from '../semantic/types';
import type { ConstructionMap, ConstructionType, TypedConstruction } from '../constructions/model';
import { readingObjectColor } from '../visual/object-identity';
import type { StructuralField, StructuralObjectModel } from './types';
import './decomposition.css';

export interface StructuralObjectFigureProps {
  model: StructuralObjectModel;
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
  /** The caller supplies the ordinary logical reader, avoiding a renderer cycle. */
  renderLaw?: (field: StructuralField) => ReactNode;
}
type Interaction = Pick<StructuralObjectFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
const short = (value: string, limit = 44) => value.length > limit ? `${value.slice(0, limit - 1)}…` : value;

function ObjectControl({ id, label, title, ...interaction }: Interaction & { id?: string; label: string; title?: string }) {
  return id ? <button className={`sd-object${interaction.selectedObjectId === id ? ' sd-selected' : ''}`} type="button" data-reading-object={id}
    style={{ '--sd-object': readingObjectColor(id) } as CSSProperties} title={title ?? label} aria-label={title ?? label} aria-pressed={interaction.selectedObjectId === id}
    onClick={() => interaction.onObjectSelect?.(id)}>{short(label, 96)}</button> : <span className="sd-type-label" title={title ?? label}>{short(label, 72)}</span>;
}

function SvgObject({ id, label, children, ...interaction }: Interaction & { id?: string; label: string; children: ReactNode }) {
  const actionable = id && interaction.onObjectSelect;
  const activate = (event: KeyboardEvent<SVGGElement>) => { if (actionable && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); interaction.onObjectSelect!(id); } };
  return <g className={`sd-svg-object${id && interaction.selectedObjectId === id ? ' sd-selected' : ''}`} data-reading-object={id}
    style={id ? { '--sd-object': readingObjectColor(id) } as CSSProperties : undefined} role={actionable ? 'button' : 'group'} tabIndex={actionable ? 0 : undefined}
    aria-label={label} aria-pressed={actionable ? interaction.selectedObjectId === id : undefined} onKeyDown={activate} onClick={() => id && interaction.onObjectSelect?.(id)}><title>{label}</title>{children}</g>;
}

function MapRow({ map, construction, ...interaction }: Interaction & { map: ConstructionMap; construction: TypedConstruction }) {
  const domain = construction.types.find(type => type.id === map.domainId)!, codomain = construction.types.find(type => type.id === map.codomainId)!;
  return <div className="sd-map-row" data-structural-map={map.objectId}>
    <ObjectControl id={domain.objectId} label={domain.label} title={`Input type: ${domain.label}`} {...interaction}/>
    <div className="sd-map-step"><ObjectControl id={map.objectId} label={map.name} title={`Field ${map.name} : ${map.type}`} {...interaction}/><span aria-hidden="true">⟶</span></div>
    <ObjectControl id={codomain.objectId} label={codomain.label} title={`Output type: ${codomain.label}`} {...interaction}/>
  </div>;
}

function Carrier({ type, construction, x, y, ...interaction }: Interaction & { type: ConstructionType; construction: TypedConstruction; x: number; y: number }) {
  const sets = construction.members.filter(member => member.typeId === type.id && member.kind === 'set');
  const elements = construction.members.filter(member => member.typeId === type.id && member.kind === 'element');
  const height = 74 + sets.length * 51 + elements.length * 29;
  return <g data-structural-carrier={type.id}>
    <SvgObject id={type.objectId} label={`Carrier type: ${type.label}`} {...interaction}><rect className="sd-carrier" x={x - 78} y={y} width="156" height={height} rx="10"/><text className="sd-carrier-name" x={x} y={y + 28} textAnchor="middle">{short(type.label, 17)}</text><text className="sd-svg-caption" x={x} y={y + 47} textAnchor="middle">carrier type</text></SvgObject>
    {sets.map((set, index) => <SvgObject key={set.objectId} id={set.objectId} label={`Set field ${set.name} in ${type.label}`} {...interaction}><g data-structural-region={set.objectId}><rect className="sd-set-region" x={x - 65} y={y + 60 + index * 51} width="130" height="41" rx="5"/><text className="sd-set-name" x={x} y={y + 85 + index * 51} textAnchor="middle">{short(set.name, 15)}</text></g></SvgObject>)}
    {elements.map((element, index) => <SvgObject key={element.objectId} id={element.objectId} label={`Field ${element.name} : ${type.label}`} {...interaction}><text className="sd-element-name" x={x} y={y + 78 + sets.length * 51 + index * 29} textAnchor="middle">{short(element.name, 17)}</text></SvgObject>)}
  </g>;
}

/** Generic arrows and containment come from typed primitive data, never field names. */
function DataDiagram({ construction, ...interaction }: Interaction & { construction: TypedConstruction }) {
  const marker = `sd-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const compact = construction.types.length > 0 && construction.types.length <= 3 && construction.maps.length <= 5;
  if (!compact) return <div className="sd-data-list">{construction.maps.map(map => <MapRow key={map.objectId} map={map} construction={construction} {...interaction}/>)}
    <div className="sd-types">{construction.types.map(type => <div className="sd-type" key={type.id}><ObjectControl id={type.objectId} label={type.label} {...interaction}/>{construction.members.filter(member => member.typeId === type.id).map(member => <div className="sd-member" key={member.objectId}><span>{member.kind === 'set' ? 'set field' : 'field'}</span><ObjectControl id={member.objectId} label={member.name} title={`${member.name} : ${member.type}`} {...interaction}/></div>)}</div>)}</div>
  </div>;
  const positions = new Map(construction.types.map((type, index) => [type.id, construction.types.length === 1 ? 330 : 95 + index * 470 / (construction.types.length - 1)]));
  const lanes = new Map<string, number>();
  const routes = construction.maps.map(map => {
    const from = positions.get(map.domainId)!, to = positions.get(map.codomainId)!, pair = [map.domainId, map.codomainId].sort().join(':');
    const lane = lanes.get(pair) ?? 0; lanes.set(pair, lane + 1);
    const base = 105, height = 45 + lane * 31;
    const path = from === to ? `M${from - 38} ${base} C${from - 102} ${base - height * 2},${from + 102} ${base - height * 2},${from + 38} ${base}`
      : `M${from} ${base} Q${(from + to) / 2} ${base - height * 2},${to} ${base}`;
    return { map, path, x: (from + to) / 2, y: base - height * (from === to ? 1.5 : 1) - 8 };
  });
  const top = Math.min(0, ...routes.map(route => route.y - 20));
  const bottom = 212 + Math.max(0, ...construction.types.map(type => construction.members.filter(member => member.typeId === type.id).reduce((height, member) => height + (member.kind === 'set' ? 51 : 29), 0)));
  return <svg className="sd-data-diagram" viewBox={`0 ${top} 660 ${bottom - top}`} role="group" aria-label="Data fields displayed using their declared carrier types, sets, and maps">
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    {routes.map(route => <SvgObject key={route.map.objectId} id={route.map.objectId} label={`Map field ${route.map.name} : ${route.map.type}`} {...interaction}><path data-structural-map={route.map.objectId} className="sd-map-arrow" d={route.path} markerEnd={`url(#${marker})`}/><text className="sd-map-name" x={route.x} y={route.y} textAnchor="middle">{short(route.map.name, 24)}</text></SvgObject>)}
    {construction.types.map(type => <Carrier key={type.id} type={type} construction={construction} x={positions.get(type.id)!} y={110} {...interaction}/>)}
  </svg>;
}

function SignatureFields({ construction, ...interaction }: Interaction & { construction: TypedConstruction }) {
  return <>{construction.signatures.map(signature => <div className="sd-signature" key={signature.objectId} data-structural-signature={signature.objectId}>
    <ObjectControl id={signature.objectId} label={signature.name} title={`Field ${signature.name} : ${signature.type}`} {...interaction}/><span className="sd-signature-kind">{signature.kind === 'relation' ? 'relation field' : signature.kind === 'family' ? 'type family field' : signature.kind === 'dependent-map' ? 'dependent map field' : 'map field'}</span>
    <div className="sd-signature-flow"><div className="sd-signature-inputs">{signature.inputs.map((input, index) => <div key={index}><small>Input {index + 1}</small><span title={`${input.name} : ${input.type}`}>{short(input.name, 24)} : {short(input.type, 62)}</span>{input.dependsOn.length > 0 && <em>Depends on input {input.dependsOn.map(index => index + 1).join(', ')}</em>}</div>)}</div><span className="sd-signature-arrow" aria-hidden="true">⟶</span><div className="sd-signature-result"><small>{signature.kind === 'relation' ? 'Proposition' : signature.kind === 'family' ? 'Type' : 'Result type'}</small><span title={signature.result}>{short(signature.result, 72)}</span>{signature.resultDependsOn.length > 0 && <em>Depends on input {signature.resultDependsOn.map(index => index + 1).join(', ')}</em>}</div></div>
    <p>{signature.explanation}</p>
  </div>)}</>;
}

function FieldList({ fields, ...interaction }: Interaction & { fields: readonly StructuralField[] }) {
  return <dl className="sd-field-list">{fields.map(field => <div key={field.projection}><dt><ObjectControl id={field.object.id} label={field.name} title={`${field.name} : ${field.type}`} {...interaction}/></dt><dd>{field.type}</dd></div>)}</dl>;
}

export function StructuralObjectFigure({ model, renderLaw, ...interaction }: StructuralObjectFigureProps) {
  const [selectedLaw, setSelectedLaw] = useState<string>();
  const data = model.fields.filter(field => field.kind === 'data'), laws = model.fields.filter(field => field.kind === 'law');
  const lawIndex = Math.max(0, laws.findIndex(field => field.projection === selectedLaw)), law = laws[lawIndex];
  const owner: SemanticObject = model.object;
  const hasDiagram = model.construction.types.length > 0 || model.construction.maps.length > 0;
  return <section className="structural-object" data-structural-object={owner.id} aria-label={`Inside ${owner.label}`}>
    <header className="sd-heading"><div><span className="sd-eyebrow">Object structure</span><h3>Inside <ObjectControl id={owner.id} label={owner.label} title={`${owner.label} : ${owner.type}`} {...interaction}/></h3><p className="sd-declared-type" title={owner.type}>{owner.type}</p></div><span className="sd-count">{data.length} data {data.length === 1 ? 'field' : 'fields'} · {laws.length} {laws.length === 1 ? 'law' : 'laws'}</span></header>
    <p className="sd-context">These fields belong to this object, within the statement’s current quantifiers and assumptions.</p>
    {data.length > 0 && <div className="sd-data"><h4>What it contains</h4>{hasDiagram && <DataDiagram construction={model.construction} {...interaction}/>}<SignatureFields construction={model.construction} {...interaction}/><details className="sd-data-source" open={!hasDiagram && model.construction.signatures.length === 0}><summary>Field names and declared types</summary><FieldList fields={data} {...interaction}/></details>{hasDiagram && <p className="sd-diagram-note">Arrows show function types. Set frames show membership domains, with no coordinates, shape, size, or chosen elements.</p>}</div>}
    {laws.length > 0 && <section className="sd-laws" aria-label={`Laws carried by ${owner.label}`}><div className="sd-law-heading"><div><h4>What its fields must satisfy</h4><p>Read each law in declaration order.</p></div><span>{lawIndex + 1} / {laws.length}</span></div>
      <div className="sd-law-choices" aria-label="Choose a field law">{laws.map((field, index) => <button key={field.projection} type="button" className={index === lawIndex ? 'sd-law-active' : ''} aria-pressed={index === lawIndex} title={field.type} onClick={() => setSelectedLaw(field.projection)}><span>{index + 1}</span>{short(field.name, 46)}</button>)}</div>
      {law && <div className="sd-law-body" key={law.projection} data-structural-law={law.projection}><div className="sd-law-name"><ObjectControl id={law.object.id} label={law.name} title={`${law.name} : ${law.type}`} {...interaction}/><span>Law of this object</span></div>{renderLaw?.(law) ?? <code className="sd-law-source">{law.type}</code>}</div>}
      <nav className="sd-law-navigation" aria-label="Field law sequence"><button type="button" disabled={lawIndex === 0} onClick={() => setSelectedLaw(laws[lawIndex - 1]!.projection)}>Previous law</button><button type="button" disabled={lawIndex === laws.length - 1} onClick={() => setSelectedLaw(laws[lawIndex + 1]!.projection)}>Next law <span aria-hidden="true">→</span></button></nav>
    </section>}
    {model.omittedFields > 0 && <p className="sd-remaining">{model.omittedFields} further {model.omittedFields === 1 ? 'field remains' : 'fields remain'} in the declared type.{model.stopReason ? ` ${model.stopReason}` : ''}</p>}
    {model.fields.length === 0 && <p className="sd-remaining">The declared object is retained without adding fields.{model.stopReason ? ` ${model.stopReason}` : ''}</p>}
  </section>;
}
