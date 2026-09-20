import { useId, useMemo, useState, type CSSProperties, type ReactNode } from 'react';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { readingObjectColor } from '../visual/object-identity';
import { compileSetConstruction, type SetConstructionModel, type SetTerm } from './model';
import './set-constructions.css';

export interface SetConstructionFigureProps {
  document: SemanticDocument;
  relation: SemanticRelation;
  /** Relations from this clause; the model additionally enforces exact scope. */
  relations?: readonly SemanticRelation[];
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
}
type Interaction = Pick<SetConstructionFigureProps, 'selectedObjectId' | 'onObjectSelect'>;
const symbol = { union: '∪', intersection: '∩', difference: '∖', complement: 'ᶜ' };
const short = (value: string, limit = 42) => value.length > limit ? `${value.slice(0, limit - 1)}…` : value;
function ObjectLabel({ object, ...interaction }: Interaction & { object: SemanticObject }) {
  return <button type="button" className={`sc-object${interaction.selectedObjectId === object.id ? ' sc-selected' : ''}`} data-reading-object={object.id} style={{ '--sc-object': readingObjectColor(object.id) } as CSSProperties} title={`${object.label}${object.type ? ` : ${object.type}` : ''}`} aria-label={`${object.label}${object.type ? ` : ${object.type}` : ''}`} aria-pressed={interaction.selectedObjectId === object.id} onClick={() => interaction.onObjectSelect?.(object.id)}>{short(object.label, 80)}</button>;
}

function MembershipRegions({ model, ...interaction }: Interaction & { model: SetConstructionModel }) {
  const prefix = `sc-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const circles = model.atoms.length === 1 ? [{ x: 270, y: 160, r: 96 }] : model.atoms.length === 2 ? [{ x: 218, y: 160, r: 99 }, { x: 322, y: 160, r: 99 }] : [{ x: 218, y: 126, r: 85 }, { x: 322, y: 126, r: 85 }, { x: 270, y: 206, r: 85 }];
  const empty = model.mode === 'required-empty';
  return <div className={`sc-regions sc-regions-${model.mode}`}><svg viewBox="0 0 540 330" role="group" aria-label={empty ? 'Membership regions required to be empty by this condition' : model.mode === 'required-witness' ? 'A distinguishing element is required in the highlighted membership regions' : 'Membership regions included in this set expression'}>
    <defs><pattern id={`${prefix}-hatch`} patternUnits="userSpaceOnUse" width="7" height="7" patternTransform="rotate(40)"><path d="M0 0 V7" stroke="#917a66" strokeWidth="2"/></pattern>{circles.map((circle, index) => <clipPath id={`${prefix}-in-${index}`} key={index}><circle cx={circle.x} cy={circle.y} r={circle.r}/></clipPath>)}{model.regions!.filter(region => region.highlighted).map((region, index) => <mask id={`${prefix}-out-${index}`} key={index} maskUnits="userSpaceOnUse" x="25" y="22" width="490" height="287"><rect x="25" y="22" width="490" height="287" fill="white"/>{circles.map((circle, bit) => !region.bits[bit] && <circle key={bit} cx={circle.x} cy={circle.y} r={circle.r} fill="black"/>)}</mask>)}</defs>
    <rect x="25" y="22" width="490" height="287" rx="5" className="sc-universe"/>
    {model.regions!.filter(region => region.highlighted).map((region, index) => {
      let regionShape: ReactNode = <rect x="25" y="22" width="490" height="287" fill={empty ? `url(#${prefix}-hatch)` : '#649b9a'} fillOpacity={empty ? .52 : .22} mask={`url(#${prefix}-out-${index})`}/>;
      region.bits.forEach((inside, bit) => { if (inside) regionShape = <g clipPath={`url(#${prefix}-in-${bit})`}>{regionShape}</g>; });
      return <g key={index} data-membership-bits={region.bits.map(bit => bit ? '1' : '0').join('')} aria-label={model.atoms.map((atom, bit) => `${region.bits[bit] ? 'in' : 'outside'} ${atom.label}`).join(', ')}>{regionShape}</g>;
    })}
    {circles.map((circle, index) => <circle key={index} cx={circle.x} cy={circle.y} r={circle.r} fill="none" stroke={readingObjectColor(model.atoms[index].id)} strokeWidth="1.4" strokeDasharray="5 3"/>)}
    <text x="39" y="44" className="sc-universe-name">{model.ambientType ? `Type ${short(model.ambientType, 54)}` : 'Ambient type'}</text>
  </svg><div className="sc-region-key">{model.atoms.map((atom, index) => <div key={atom.id}><span className="sc-set-swatch" style={{ '--sc-object': readingObjectColor(atom.id) } as CSSProperties} aria-hidden="true"/><span className="sc-region-index">{model.atoms.length === 3 ? ['upper left', 'upper right', 'lower'][index] : model.atoms.length === 2 ? ['left', 'right'][index] : 'set'}</span><ObjectLabel object={atom} {...interaction}/></div>)}</div></div>;
}

function ConstructionStep({ term, objects, ...interaction }: Interaction & { term: SetTerm; objects: ReadonlyMap<string, SemanticObject> }) {
  const fn = term.functionObjectId && objects.get(term.functionObjectId);
  return <li data-set-construction={term.objectId} className="sc-construction-step"><span className="sc-step-expression">{term.kind === 'operation' ? <><ObjectLabel object={term.children[0].object} {...interaction}/><span className="sc-operator">{symbol[term.operation!]}</span>{term.children[1] && <ObjectLabel object={term.children[1].object} {...interaction}/>}</> : <>{fn && <ObjectLabel object={fn} {...interaction}/>}<span className="sc-operation-name">{term.kind === 'image' ? 'image of' : 'preimage of'}</span><ObjectLabel object={term.children[0].object} {...interaction}/></>}</span><span className="sc-step-arrow" aria-hidden="true">⟶</span><ObjectLabel object={term.object} {...interaction}/></li>;
}

export function SetConstructionFigure({ document, relation, relations, ...interaction }: SetConstructionFigureProps) {
  const model = useMemo(() => compileSetConstruction(document, relation, relations), [document, relation, relations]);
  const [stepLimit, setStepLimit] = useState(6);
  const objects = useMemo(() => new Map(document.objects.map(object => [object.id, object])), [document]);
  if (!model) return null;
  const selectedRegions = model.regions?.filter(region => region.highlighted).length;
  const requirement = model.mode === 'allowed-membership' ? selectedRegions === 0 ? 'No membership combination belongs to this set expression.' : 'The named element must belong somewhere in the highlighted region; no particular membership combination is chosen.' : model.mode === 'required-empty' ? selectedRegions === 0 ? 'This construction excludes no membership combination.' : 'The hatched membership regions must be empty for this condition to hold.' : model.mode === 'required-witness' ? selectedRegions === 0 ? 'This construction has no distinguishing membership region.' : 'At least one highlighted region must contain a distinguishing element; no witness is chosen.' : 'The highlighted membership regions define the constructed set.';
  return <figure className="set-construction-figure" data-set-relation={relation.id} aria-label="Compositional set interpretation">
    <div className="sc-condition">{model.element && <><ObjectLabel object={model.element} {...interaction}/><span className="sc-operator">∈</span></>}<ObjectLabel object={model.left.object} {...interaction}/>{model.right && <><span className="sc-operator">{relation.kind === 'subset' ? '⊆' : relation.label}</span><ObjectLabel object={model.right.object} {...interaction}/></>}</div>
    {model.regions ? <><MembershipRegions model={model} {...interaction}/><p className="sc-requirement">{requirement}</p></> : <p className="sc-requirement">This expression uses {model.atoms.length} distinct set operands. Its ordered construction is retained below without assigning shapes to their intersections.</p>}
    <details className="sc-construction-details" open={!model.regions}><summary>How this set is constructed <span>{model.steps.length} {model.steps.length === 1 ? 'step' : 'steps'}</span></summary><ol>{model.steps.slice(0, stepLimit).map(term => <ConstructionStep key={term.objectId} term={term} objects={objects} {...interaction}/>)}</ol>{model.steps.length > stepLimit && <button type="button" className="sc-show-more" onClick={() => setStepLimit(limit => limit + 6)}>Show {Math.min(6, model.steps.length - stepLimit)} more construction steps</button>}{model.collapsed && <p className="sc-note">Deeper subexpressions retain their exact object identities. Select an expression to inspect its source.</p>}</details>
    <figcaption>Regions encode membership combinations, not elements or sizes. Drawing a region does not assert that it contains an element.</figcaption>
  </figure>;
}
