import { useId, useState, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import { FigureScroll } from '../components/FigureScroll';
import { layoutMapDiagram } from '../components/map-diagram-layout';
import { useDiagramText } from '../components/use-diagram-text';
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
  /** An enclosing disclosure already controls visibility, so the box renders open. */
  enclosed?: boolean;
}
type Interaction = Pick<StructuralObjectFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
const short = (value: string, limit = 44) => value.length > limit ? `${value.slice(0, limit - 1)}…` : value;

/** One count for the header and the closed summary, so the two cannot disagree. */
function FieldCounts({ model }: { model: StructuralObjectModel }) {
  const data = model.fields.filter(field => field.kind === 'data').length, laws = model.fields.length - data;
  return <>{data} data {data === 1 ? 'field' : 'fields'} · {laws} {laws === 1 ? 'law' : 'laws'}</>;
}

/** Kind-based, never name-based: a box starts closed only when Lean reflected every direct field,
 * none is a law (Prop-valued), and none is a parent subobject, whose own laws the box does not list.
 * Laws, omitted fields and stop reasons therefore stay in view. */
export function startsClosed(model: StructuralObjectModel): boolean {
  return model.fields.length > 0 && model.omittedFields === 0 && !model.stopReason
    && model.fields.every(field => field.kind === 'data' && field.parent === undefined);
}

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

function Carrier({ type, construction, x, y, width, ...interaction }: Interaction & { type: ConstructionType; construction: TypedConstruction; x: number; y: number; width: number }) {
  const sets = construction.members.filter(member => member.typeId === type.id && member.kind === 'set');
  const elements = construction.members.filter(member => member.typeId === type.id && member.kind === 'element');
  const height = 74 + sets.length * 51 + elements.length * 29;
  return <g data-structural-carrier={type.id}>
    <SvgObject id={type.objectId} label={`Carrier type: ${type.label}`} {...interaction}><rect className="sd-carrier" x={x - width / 2} y={y} width={width} height={height} rx="10"/><text data-diagram-label={`type:${type.id}`} className="sd-carrier-name" x={x} y={y + 28} textAnchor="middle">{short(type.label, 17)}</text><text className="sd-svg-caption" x={x} y={y + 47} textAnchor="middle">carrier type</text></SvgObject>
    {sets.map((set, index) => <SvgObject key={set.objectId} id={set.objectId} label={`Set field ${set.name} in ${type.label}`} {...interaction}><g data-structural-region={set.objectId}><rect className="sd-set-region" x={x - width / 2 + 13} y={y + 60 + index * 51} width={width - 26} height="41" rx="5"/><text data-diagram-label={`member:${set.objectId}`} className="sd-set-name" x={x} y={y + 85 + index * 51} textAnchor="middle">{short(set.name, 15)}</text></g></SvgObject>)}
    {elements.map((element, index) => <SvgObject key={element.objectId} id={element.objectId} label={`Field ${element.name} : ${type.label}`} {...interaction}><text data-diagram-label={`member:${element.objectId}`} className="sd-element-name" x={x} y={y + 78 + sets.length * 51 + index * 29} textAnchor="middle">{short(element.name, 17)}</text></SvgObject>)}
  </g>;
}

/** Generic arrows and containment come from typed primitive data, never field names. */
function DataDiagram({ construction, ...interaction }: Interaction & { construction: TypedConstruction }) {
  const compact = construction.types.length > 0 && construction.types.length <= 3 && construction.maps.length <= 5;
  if (!compact) return <div className="sd-data-list">{construction.maps.map(map => <MapRow key={map.objectId} map={map} construction={construction} {...interaction}/>)}
    <div className="sd-types">{construction.types.map(type => <div className="sd-type" key={type.id}><ObjectControl id={type.objectId} label={type.label} {...interaction}/>{construction.members.filter(member => member.typeId === type.id).map(member => <div className="sd-member" key={member.objectId}><span>{member.kind === 'set' ? 'set field' : 'field'}</span><ObjectControl id={member.objectId} label={member.name} title={`${member.name} : ${member.type}`} {...interaction}/></div>)}</div>)}</div>
  </div>;
  return <DataGraph construction={construction} {...interaction}/>;
}

function DataGraph({ construction, ...interaction }: Interaction & { construction: TypedConstruction }) {
  const marker = `sd-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const text = useDiagramText();
  const layout = layoutMapDiagram(construction.types.map(type => {
    const members = construction.members.filter(member => member.typeId === type.id);
    const width = Math.max(156, text.size(`type:${type.id}`, short(type.label, 17), 18).width + 24,
      ...members.map(member => text.size(`member:${member.objectId}`, short(member.name, member.kind === 'set' ? 15 : 17), 14).width + (member.kind === 'set' ? 50 : 24)));
    return { id: type.id, width, height: 74 + members.reduce((sum, member) => sum + (member.kind === 'set' ? 51 : 29), 0) };
  }), construction.maps.map(map => ({ id: map.objectId, from: map.domainId, to: map.codomainId, label: text.size(`map:${map.objectId}`, short(map.name, 24), 15) })));
  return <FigureScroll className="sd-data-scroll" label="Data fields diagram; scroll to see all of it"><svg ref={text.ref} className="sd-data-diagram" style={{ minWidth: layout.width }} viewBox={`0 0 ${layout.width} ${layout.height}`} role="group" aria-label="Data fields displayed using their declared carrier types, sets, and maps">
    <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    {construction.maps.map((map, index) => {
      const route = layout.edges[index];
      return <SvgObject key={map.objectId} id={map.objectId} label={`Map field ${map.name} : ${map.type}`} {...interaction}><path data-structural-map={map.objectId} className="sd-map-arrow" d={route.path} markerEnd={`url(#${marker})`}/><text data-diagram-label={`map:${map.objectId}`} className="sd-map-name" x={route.labelX} y={route.labelY} textAnchor="middle">{short(map.name, 24)}</text></SvgObject>;
    })}
    {construction.types.map((type, index) => <Carrier key={type.id} type={type} construction={construction} x={layout.nodes[index].x} y={layout.nodes[index].y} width={layout.nodes[index].width} {...interaction}/>)}
  </svg></FigureScroll>;
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

export function StructuralObjectFigure({ model, renderLaw, enclosed, ...interaction }: StructuralObjectFigureProps) {
  const [selectedLaw, setSelectedLaw] = useState<string>();
  const data = model.fields.filter(field => field.kind === 'data'), laws = model.fields.filter(field => field.kind === 'law');
  const lawIndex = Math.max(0, laws.findIndex(field => field.projection === selectedLaw)), law = laws[lawIndex];
  const owner: SemanticObject = model.object;
  const hasDiagram = model.construction.types.length > 0 || model.construction.maps.length > 0;
  const figure = <section className="structural-object" data-structural-object={owner.id} aria-label={`Inside ${owner.label}`}>
    <header className="sd-heading"><div><span className="sd-eyebrow">Object structure</span><h3>Inside <ObjectControl id={owner.id} label={owner.label} title={`${owner.label} : ${owner.type}`} {...interaction}/></h3><p className="sd-declared-type" title={owner.type}>{owner.type}</p></div><span className="sd-count"><FieldCounts model={model}/></span></header>
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
  // The closed box holds the same figure; nothing is removed, and opening it restores the original view.
  return !enclosed && startsClosed(model) ? <details className="sd-closed-structure"><summary>Inside {short(owner.label, 96)} · <FieldCounts model={model}/></summary>{figure}</details> : figure;
}
