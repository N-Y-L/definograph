import { useId, useMemo, type KeyboardEvent, type ReactNode } from 'react';
import type { ReadingBinder } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';
import { compileTypedConstruction, isUsefulConstruction, type ConstructionMap, type ConstructionType, type TypedConstruction } from './model';
import './constructions.css';

export interface TypedConstructionFigureProps {
  document: SemanticDocument;
  /** Exactly one contiguous, same-role quantifier or parameter group. */
  binders: readonly ReadingBinder[];
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
}

const short = (text: string, limit = 26) => text.length > limit ? `${text.slice(0, limit - 1)}…` : text;
const roles = { universal: 'For every', existential: 'There exists', parameter: 'Parameter', lambda: 'Input', assumption: 'Assumption' };
type Interaction = Pick<TypedConstructionFigureProps, 'selectedObjectId' | 'onObjectSelect'>;

function ObjectControl({ id, label, children, selectedObjectId, onObjectSelect }: Interaction & { id?: string; label: string; children: ReactNode }) {
  return id ? <button type="button" className={`tc-object${selectedObjectId === id ? ' tc-selected' : ''}`} data-reading-object={id} title={label} aria-label={label} aria-pressed={selectedObjectId === id} onClick={() => onObjectSelect?.(id)}>{children}</button> : <span className="tc-object tc-symbolic" title={label}>{children}</span>;
}

function SvgObject({ id, label, children, selectedObjectId, onObjectSelect }: Interaction & { id?: string; label: string; children: ReactNode }) {
  const actionable = !!id && !!onObjectSelect;
  const activate = (event: KeyboardEvent<SVGGElement>) => { if (actionable && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); onObjectSelect(id); } };
  return <g className={`tc-svg-object${selectedObjectId && selectedObjectId === id ? ' tc-selected' : ''}`} data-reading-object={id} aria-label={label} role={actionable ? 'button' : 'group'} aria-pressed={actionable ? selectedObjectId === id : undefined} tabIndex={actionable ? 0 : undefined} onKeyDown={activate} onClick={() => { if (id) onObjectSelect?.(id); }}><title>{label}</title>{children}</g>;
}

function MemberLabels({ type, model, ...interaction }: Interaction & { type: ConstructionType; model: TypedConstruction }) {
  return <div className="tc-members">{model.members.filter(member => member.typeId === type.id).map(member => <ObjectControl key={member.objectId} id={member.objectId} label={`${roles[member.role]} ${member.name} : ${member.type}`} {...interaction}><span className="tc-member-name">{member.name}</span><span className="tc-member-type">{member.kind === 'set' ? `set of ${type.label}` : `: ${type.label}`}</span></ObjectControl>)}</div>;
}

/** A small shared-carrier diagram; arrow endpoints come only from exact function types. */
function MapGraph({ model, ...interaction }: Interaction & { model: TypedConstruction }) {
  const marker = `tc-arrow-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const width = 660, y = 111;
  const positions = new Map(model.types.map((type, index) => [type.id, model.types.length === 1 ? width / 2 : 75 + index * (width - 150) / (model.types.length - 1)]));
  const indices = new Map(model.types.map((type, index) => [type.id, index]));
  const parallelCounts = new Map<string, number>();
  const routes = model.maps.map(map => {
      const start = positions.get(map.domainId)!, end = positions.get(map.codomainId)!;
      const pair = [map.domainId, map.codomainId].sort().join(':');
      const lane = parallelCounts.get(pair) ?? 0; parallelCounts.set(pair, lane + 1);
      const forward = end >= start, offset = forward ? 36 : -36;
      const hops = Math.abs(indices.get(map.domainId)! - indices.get(map.codomainId)!);
      // Adjacent maps form a clear baseline. Longer maps pass above it; further
      // parallel/reverse arrows use lower lanes rather than crossing that arc.
      const curve = lane > 0 ? -(30 + lane * 14) : hops === 1 ? 0 : 48 + Math.max(0, hops - 2) * 10;
      const d = start === end ? `M${start - 23} ${y - 19} C${start - 81} ${24 - lane * 9},${start + 81} ${24 - lane * 9},${start + 23} ${y - 19}` : `M${start + offset} ${y} Q${(start + end) / 2} ${y - curve * 2},${end - offset} ${y}`;
      return { map, start, end, lane, curve, d };
  });
  const height = Math.max(175, ...routes.map(route => route.start !== route.end && route.curve < 0 ? y - route.curve + 30 : 175));
  return <div className="tc-map-graph"><svg viewBox={`0 0 ${width} ${height}`} role="group" aria-label="Maps between the declared types"><defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M1 1 L7 4 L1 7"/></marker></defs>
    {routes.map(({ map, start, end, lane, curve, d }) => {
      return <SvgObject key={map.objectId} id={map.objectId} label={`${roles[map.role]} ${map.name} : ${map.type}`} {...interaction}><path className="tc-map-arrow" d={d} markerEnd={`url(#${marker})`}/><text className="tc-map-name" x={(start + end) / 2} y={start === end ? 35 - lane * 9 : y - curve - 10} textAnchor="middle">{short(map.name, 16)}</text></SvgObject>;
    })}
    {model.types.map(type => <SvgObject key={type.id} id={type.objectId} label={`Type ${type.label}${type.introduced ? ', introduced here' : ', in scope'}`} {...interaction}><rect className="tc-type-node" x={positions.get(type.id)! - 34} y={y - 20} width="68" height="40" rx="9"/><text className="tc-type-name" x={positions.get(type.id)} y={y + 7} textAnchor="middle">{short(type.label, 8)}</text></SvgObject>)}
  </svg><div className="tc-graph-members" style={{ gridTemplateColumns: `repeat(${model.types.length}, minmax(0, 1fr))` }}>{model.types.map(type => <MemberLabels key={type.id} type={type} model={model} {...interaction}/>)}</div></div>;
}

function MapRow({ map, model, ...interaction }: Interaction & { map: ConstructionMap; model: TypedConstruction }) {
  const domain = model.types.find(type => type.id === map.domainId)!, codomain = model.types.find(type => type.id === map.codomainId)!;
  return <div className="tc-map-row"><ObjectControl id={domain.objectId} label={`Type ${domain.label}`} {...interaction}>{short(domain.label)}</ObjectControl><div className="tc-inline-arrow"><ObjectControl id={map.objectId} label={`${roles[map.role]} ${map.name} : ${map.type}`} {...interaction}>{short(map.name)}</ObjectControl><span aria-hidden="true">⟶</span></div><ObjectControl id={codomain.objectId} label={`Type ${codomain.label}`} {...interaction}>{short(codomain.label)}</ObjectControl></div>;
}

export function TypedConstructionFigure({ document, binders, ...interaction }: TypedConstructionFigureProps) {
  const model = useMemo(() => compileTypedConstruction(document, binders), [document, binders]);
  if (!isUsefulConstruction(model)) return null;
  const compactGraph = model.maps.length > 0 && model.types.length <= 4 && model.maps.length <= 4;
  return <figure className="typed-construction" data-construction-role={model.role} aria-label={`${model.role ? roles[model.role] : ''}: typed objects and maps`}>
    <div className="tc-heading">Types and maps</div>
    {compactGraph ? <MapGraph model={model} {...interaction}/> : <>
      <div className="tc-type-grid">{model.types.map(type => <div className="tc-carrier" key={type.id}><ObjectControl id={type.objectId} label={`Type ${type.label}`} {...interaction}><span className="tc-carrier-label">{short(type.label, 32)}</span><span className="tc-type-kind">type{type.objectId && !type.introduced ? ' · in scope' : ''}</span></ObjectControl><MemberLabels type={type} model={model} {...interaction}/></div>)}</div>
      {model.maps.map(map => <MapRow key={map.objectId} map={map} model={model} {...interaction}/>)}
    </>}
    {model.signatures.map(signature => <div className={`tc-signature tc-${signature.kind}`} key={signature.objectId}><div className="tc-signature-heading"><ObjectControl id={signature.objectId} label={`${roles[signature.role]} ${signature.name} : ${signature.type}`} {...interaction}>{signature.name}</ObjectControl><span>{signature.kind === 'relation' ? 'relation' : signature.kind === 'family' ? 'type family' : signature.kind === 'dependent-map' ? 'dependent map' : 'function'}</span></div><div className="tc-signature-flow"><div className="tc-inputs">{signature.inputs.map((input, index) => <span key={index} className="tc-input" title={`${input.name} : ${input.type}`}><small>input {index + 1}</small><span>{short(input.name, 12)} : {short(input.type, 36)}</span>{input.dependsOn.length > 0 && <em>depends on input {input.dependsOn.map(i => i + 1).join(', ')}</em>}</span>)}</div><span className="tc-signature-arrow" aria-hidden="true">⟶</span><span className="tc-result" title={signature.result}><small>{signature.kind === 'relation' ? 'proposition' : signature.kind === 'family' ? 'type' : 'result type'}</small><span>{short(signature.result, 42)}</span>{signature.resultDependsOn.length > 0 && <em>depends on input {signature.resultDependsOn.map(i => i + 1).join(', ')}</em>}</span></div><p>{signature.explanation}</p></div>)}
    {model.unknowns.map(object => <div className="tc-unresolved" key={object.objectId}><ObjectControl id={object.objectId} label={`${object.name} : ${object.type}`} {...interaction}>{object.name} : {short(object.type, 60)}</ObjectControl><span>{object.reason}</span></div>)}
    <figcaption>Arrows show declared function types. Named elements retain their types; no coordinates, cardinalities, or additional properties are assigned.</figcaption>
  </figure>;
}
