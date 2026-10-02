import { useId, useMemo, type KeyboardEvent, type ReactNode, type CSSProperties } from 'react';
import { FigureScroll } from '../components/FigureScroll';
import { layoutMapDiagram } from '../components/map-diagram-layout';
import { useDiagramText } from '../components/use-diagram-text';
import type { ReadingBinder } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';
import { compileTypedConstruction, isUsefulConstruction, type ConstructionMap, type ConstructionSignature, type ConstructionType, type TypedConstruction } from './model';
import './constructions.css';
import { readingObjectColor } from '../visual/object-identity';

export interface TypedConstructionFigureProps {
  document: SemanticDocument;
  /** Exactly one contiguous, same-role quantifier or parameter group. */
  binders: readonly ReadingBinder[];
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
}

const short = (text: string, limit = 26) => text.length > limit ? `${text.slice(0, limit - 1)}…` : text;
const roles = { universal: 'For every', existential: 'There exists', parameter: 'Parameter', lambda: 'Input', assumption: 'Assumption', definition: 'Definition', auxiliary: 'Recorded context entry' };
type Interaction = Pick<TypedConstructionFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
type Presentation = Interaction & { component: boolean };
const annotationLabel = (role: keyof typeof roles, name: string, type: string, component: boolean) =>
  component ? `${roles[role]} ${name}; declared annotation: ${type}` : `${roles[role]} ${name} : ${type}`;
const typeLabel = (label: string, component: boolean) => `${component ? 'Declared type annotation' : 'Type'} ${label}`;

function declaredSignatureDescription(signature: ConstructionSignature): string {
  if (signature.kind === 'relation') return 'The displayed signature ends in Prop.';
  if (signature.kind === 'family') return `The displayed signature ends in ${signature.result}.`;
  if (signature.kind === 'dependent-map') return 'Later input annotations or the result annotation reference earlier inputs.';
  if (signature.kind === 'multi-input-map') return 'Input annotations follow the order of the displayed signature.';
  return 'The displayed annotation is incomplete; its available signature fields are retained.';
}

function ObjectControl({ id, label, children, selectedObjectId, onObjectSelect }: Interaction & { id?: string; label: string; children: ReactNode }) {
  return id ? <button type="button" className={`tc-object${selectedObjectId === id ? ' tc-selected' : ''}`} data-reading-object={id} style={id ? { '--object-color': readingObjectColor(id) } as CSSProperties : undefined} title={label} aria-label={label} aria-pressed={selectedObjectId === id} onClick={() => onObjectSelect?.(id)}>{children}</button> : <span className="tc-object tc-symbolic" title={label}>{children}</span>;
}

function SvgObject({ id, label, children, selectedObjectId, onObjectSelect }: Interaction & { id?: string; label: string; children: ReactNode }) {
  const actionable = !!id && !!onObjectSelect;
  const activate = (event: KeyboardEvent<SVGGElement>) => { if (actionable && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); onObjectSelect(id); } };
  return <g className={`tc-svg-object${selectedObjectId && selectedObjectId === id ? ' tc-selected' : ''}`} data-reading-object={id} style={id ? { '--object-color': readingObjectColor(id) } as CSSProperties : undefined} aria-label={label} role={actionable ? 'button' : 'group'} aria-pressed={actionable ? selectedObjectId === id : undefined} tabIndex={actionable ? 0 : undefined} onKeyDown={activate} onClick={() => { if (id) onObjectSelect?.(id); }}><title>{label}</title>{children}</g>;
}

function MemberLabels({ type, model, component, ...interaction }: Presentation & { type: ConstructionType; model: TypedConstruction }) {
  return <div className="tc-members">{model.members.filter(member => member.typeId === type.id).map(member => <ObjectControl key={member.objectId} id={member.objectId} label={annotationLabel(member.role, member.name, member.type, component)} {...interaction}><span className="tc-member-name">{member.name}</span><span className="tc-member-type">{component ? `annotation: ${member.type}` : member.kind === 'set' ? `set of ${type.label}` : `: ${type.label}`}</span></ObjectControl>)}</div>;
}

/** A small shared-carrier diagram; arrow endpoints come only from exact function types. */
function MapGraph({ model, component, ...interaction }: Presentation & { model: TypedConstruction }) {
  const marker = `tc-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const text = useDiagramText();
  const layout = layoutMapDiagram(model.types.map(type => ({ id: type.id, width: Math.max(68, text.size(`type:${type.id}`, short(type.label, 8), 21).width + 24), height: 40 })),
    model.maps.map(map => ({ id: map.objectId, from: map.domainId, to: map.codomainId, label: text.size(`map:${map.objectId}`, short(map.name, 16), 18) })));
  const minimumWidth = Math.ceil(layout.width * 10 / 18);
  return <FigureScroll className="tc-map-graph" label="Types and maps diagram; scroll to see all of it"><svg ref={text.ref} style={{ minWidth: minimumWidth }} viewBox={`0 0 ${layout.width} ${layout.height}`} role="group" aria-label={component ? 'Arrows between declared annotations' : 'Maps between the declared types'}><defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    {model.maps.map((map, index) => {
      const route = layout.edges[index];
      return <SvgObject key={map.objectId} id={map.objectId} label={annotationLabel(map.role, map.name, map.type, component)} {...interaction}><path className="tc-map-arrow" d={route.path} markerEnd={`url(#${marker})`}/><text data-diagram-label={`map:${map.objectId}`} className="tc-map-name" x={route.labelX} y={route.labelY} textAnchor="middle">{short(map.name, 16)}</text></SvgObject>;
    })}
    {model.types.map((type, index) => {
      const node = layout.nodes[index], label = text.size(`type:${type.id}`, short(type.label, 8), 21);
      return <SvgObject key={type.id} id={type.objectId} label={`${typeLabel(type.label, component)}${type.introduced ? ', introduced here' : ', in scope'}`} {...interaction}><rect className="tc-type-node" x={node.x - node.width / 2} y={node.y} width={node.width} height={node.height} rx="9"/><text data-diagram-label={`type:${type.id}`} className="tc-type-name" x={node.x} y={node.y + (node.height - label.height) / 2 + label.ascent} textAnchor="middle">{short(type.label, 8)}</text></SvgObject>;
    })}
  </svg><div className="tc-graph-members" style={{ minWidth: minimumWidth, columnGap: 0, gridTemplateColumns: `repeat(${model.types.length}, minmax(0, 1fr))` }}>{model.types.map(type => <MemberLabels key={type.id} type={type} model={model} component={component} {...interaction}/>)}</div></FigureScroll>;
}

function MapRow({ map, model, component, ...interaction }: Presentation & { map: ConstructionMap; model: TypedConstruction }) {
  const domain = model.types.find(type => type.id === map.domainId)!, codomain = model.types.find(type => type.id === map.codomainId)!;
  return <div className="tc-map-row"><ObjectControl id={domain.objectId} label={typeLabel(domain.label, component)} {...interaction}>{short(domain.label)}</ObjectControl><div className="tc-inline-arrow"><ObjectControl id={map.objectId} label={annotationLabel(map.role, map.name, map.type, component)} {...interaction}>{short(map.name)}</ObjectControl><span aria-hidden="true">⟶</span></div><ObjectControl id={codomain.objectId} label={typeLabel(codomain.label, component)} {...interaction}>{short(codomain.label)}</ObjectControl></div>;
}

export function TypedConstructionFigure({ document, binders, ...interaction }: TypedConstructionFigureProps) {
  const component = document.presentation?.kind === 'component';
  const model = useMemo(() => compileTypedConstruction(document, binders), [document, binders]);
  if (!isUsefulConstruction(model)) return null;
  const compactGraph = model.maps.length > 0 && model.types.length <= 4 && model.maps.length <= 4;
  return <figure className="typed-construction" data-construction-role={model.role} aria-label={component ? 'Declared types and signatures' : `${model.role ? roles[model.role] : ''}: typed objects and maps`}>
    <div className="tc-heading">{component ? 'Declared signatures' : 'Types and maps'}</div>
    {compactGraph ? <MapGraph model={model} component={component} {...interaction}/> : <>
      <div className="tc-type-grid">{model.types.map(type => <div className="tc-carrier" key={type.id}><ObjectControl id={type.objectId} label={typeLabel(type.label, component)} {...interaction}><span className="tc-carrier-label">{short(type.label, 32)}</span><span className="tc-type-kind">{component ? 'declared annotation' : 'type'}{type.objectId && !type.introduced ? ' · in scope' : ''}</span></ObjectControl><MemberLabels type={type} model={model} component={component} {...interaction}/></div>)}</div>
      {model.maps.map(map => <MapRow key={map.objectId} map={map} model={model} component={component} {...interaction}/>)}
    </>}
    {model.signatures.map(signature => <div className={`tc-signature tc-${signature.kind}`} key={signature.objectId}><div className="tc-signature-heading"><ObjectControl id={signature.objectId} label={annotationLabel(signature.role, signature.name, signature.type, component)} {...interaction}>{signature.name}</ObjectControl><span>{component ? 'Declared signature' : signature.kind === 'relation' ? 'relation' : signature.kind === 'family' ? 'type family' : signature.kind === 'dependent-map' ? 'dependent map' : 'function'}</span></div><div className="tc-signature-flow"><div className="tc-inputs">{signature.inputs.map((input, index) => <span key={index} className="tc-input" title={component ? `${input.name}; declared annotation: ${input.type}` : `${input.name} : ${input.type}`}><small>{component ? 'Input annotation' : 'input'} {index + 1}</small><span>{short(input.name, 12)} : {short(input.type, 36)}</span>{input.dependsOn.length > 0 && <em>{component ? 'references input' : 'depends on input'} {input.dependsOn.map(i => i + 1).join(', ')}</em>}</span>)}</div><span className="tc-signature-arrow" aria-hidden="true">⟶</span><span className="tc-result" title={component ? `Result annotation: ${signature.result}` : signature.result}><small>{component ? 'Result annotation' : signature.kind === 'relation' ? 'proposition' : signature.kind === 'family' ? 'type' : 'result type'}</small><span>{short(signature.result, 42)}</span>{signature.resultDependsOn.length > 0 && <em>{component ? 'references input' : 'depends on input'} {signature.resultDependsOn.map(i => i + 1).join(', ')}</em>}</span></div><p>{component ? declaredSignatureDescription(signature) : signature.explanation}</p></div>)}
    {model.unknowns.map(object => <div className="tc-unresolved" key={object.objectId}><ObjectControl id={object.objectId} label={`${object.name} : ${object.type}`} {...interaction}>{object.name} : {short(object.type, 60)}</ObjectControl><span>{object.reason}</span></div>)}
    <figcaption>{component ? 'Type, element, and signature labels show declared annotations. Arrows follow the displayed signatures; typing outcomes remain separate.' : 'Arrows show declared function types. Named elements retain their types; no coordinates, cardinalities, or additional properties are assigned.'}</figcaption>
  </figure>;
}
