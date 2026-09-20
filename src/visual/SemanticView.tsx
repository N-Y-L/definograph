import { useMemo, type KeyboardEvent, type ReactNode } from 'react';
import type { PlannedView, QuantifierChoice, RelationKind, SemanticDocument, SemanticObject, SemanticRelation, SemanticScope } from '../semantic/types';
import { compactLabel, layoutSemanticMap } from './layout';
import './semantic-views.css';

export interface SemanticViewProps {
  document: SemanticDocument;
  view: PlannedView;
  selectedObjectId?: string;
  onObjectSelect?: (id: string) => void;
  onNodeSelect?: (id: string) => void;
}

const objectGlyph: Record<SemanticObject['kind'], string> = { variable: 'x', scalar: 'a', point: '•', set: '{ }', function: '↦', type: 'T', literal: '#', expression: '⋯', symbol: 's' };
const relationName: Record<RelationKind, string> = { membership: 'Membership', subset: 'Set inclusion', equality: 'Equality', inequality: 'Comparison', application: 'Function application', image: 'Image of a set', preimage: 'Preimage of a set', 'function-property': 'Function property', 'set-construction': 'Set construction', 'metric-region': 'Metric region', distance: 'Distance', predicate: 'Symbolic relation' };
const choiceSymbol: Record<QuantifierChoice['role'], string> = { universal: '∀', existential: '∃', assumption: '⇒', lambda: '↦', parameter: '↦' };
const choiceName: Record<QuantifierChoice['role'], string> = { universal: 'Arbitrary choice', existential: 'Candidate witness', assumption: 'Assumption', lambda: 'Function input', parameter: 'Definition parameter' };

function activate(event: KeyboardEvent<SVGGElement>, action: (() => void) | undefined) {
  if (action && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); action(); }
}

function ScopeContext({ scope, onNodeSelect }: { scope?: SemanticScope; onNodeSelect?: (id: string) => void }) {
  if (!scope) return null;
  const contexts = [...new Set(scope.context)];
  return <div className="sv-context">
    {contexts.map((context, index) => <span key={`${context}:${index}`} className="sv-context-tag">{context}</span>)}
    {scope.assumptionNodeIds.length > 0 && <span className="sv-assumption-context">Under {scope.assumptionNodeIds.length} {scope.assumptionNodeIds.length === 1 ? 'assumption' : 'assumptions'}{onNodeSelect && <span className="sv-assumption-links">{scope.assumptionNodeIds.slice(0, 3).map((id, index) => <button type="button" key={id} onClick={() => onNodeSelect(id)} aria-label={`Inspect assumption ${index + 1}`}>{index + 1}</button>)}</span>}</span>}
  </div>;
}

function ObjectButton({ object, selectedObjectId, onObjectSelect, role, compact = false }: { object: SemanticObject; selectedObjectId?: string; onObjectSelect?: (id: string) => void; role?: string; compact?: boolean }) {
  return <button type="button" className={`sv-object-token sv-kind-${object.kind}${compact ? ' sv-compact-token' : ''}${selectedObjectId === object.id ? ' is-selected' : ''}`} onClick={() => onObjectSelect?.(object.id)} aria-pressed={selectedObjectId === object.id} aria-label={`${role ? `${role}: ` : ''}${object.label}, ${object.type || object.kind}`} title={`${object.label}${object.type ? ` : ${object.type}` : ''}`}>
    {role && <span className="sv-port-role">{role}</span>}
    <span className="sv-token-main"><span className="sv-object-glyph" aria-hidden="true">{objectGlyph[object.kind]}</span><span className="sv-object-name">{compactLabel(object.label, compact ? 28 : 42)}</span></span>
    {!compact && <span className="sv-object-type">{compactLabel(object.type || object.kind, 52)}</span>}
  </button>;
}

function SemanticMap(props: SemanticViewProps) {
  const { document, view, selectedObjectId, onObjectSelect, onNodeSelect } = props;
  const layout = useMemo(() => layoutSemanticMap(document, view, selectedObjectId), [document, view, selectedObjectId]);
  const connectedRelations = new Set(layout.edges.filter(edge => edge.objectId === selectedObjectId).map(edge => edge.relationId));
  const missingObjects = layout.totalObjects - layout.objects.length;
  const missingRelations = layout.totalRelations - layout.relations.length;
  const visibleScopes = [...new Set([...layout.objects.map(node => node.object.scopeId), ...layout.relations.map(node => node.relation.scopeId)])];
  const scopes = document.scopes.filter(scope => visibleScopes.includes(scope.id) && (scope.context.length > 0 || scope.assumptionNodeIds.length > 0));
  return <div className="sv-semantic-map">
    <div className="sv-view-intro"><p>Shared objects connect the parts of this statement. Select an object to trace its relations.</p><span className="sv-fidelity">Structural view</span></div>
    <div className="sv-map-scroll" tabIndex={0} aria-label="Objects and relations diagram; scroll to inspect all visible nodes">
      <svg className="sv-map" viewBox={`0 0 ${layout.width} ${layout.height}`} style={{ minWidth: 650 }} role="group" aria-label={`Semantic map with ${layout.objects.length} objects and ${layout.relations.length} relations`}>
        <text x="26" y="31" className="sv-column-label">OBJECTS <tspan className="sv-column-count">{layout.totalObjects}</tspan></text>
        <text x="484" y="31" className="sv-column-label">RELATIONS <tspan className="sv-column-count">{layout.totalRelations}</tspan></text>
        {layout.edges.map(edge => <path key={edge.id} className={`sv-edge${selectedObjectId ? edge.objectId === selectedObjectId ? ' is-active' : ' is-muted' : ''}`} d={edge.path}><title>{edge.role}</title></path>)}
        {layout.objects.map(node => <g key={node.object.id} className={`sv-map-object sv-kind-${node.object.kind}${node.object.id === selectedObjectId ? ' is-selected' : ''}`} transform={`translate(${node.x} ${node.y})`} role={onObjectSelect ? 'button' : 'group'} tabIndex={onObjectSelect ? 0 : undefined} aria-label={`${node.object.label}, ${node.object.type || node.object.kind}`} aria-pressed={onObjectSelect ? node.object.id === selectedObjectId : undefined} onClick={() => onObjectSelect?.(node.object.id)} onKeyDown={event => activate(event, onObjectSelect ? () => onObjectSelect(node.object.id) : undefined)}>
          <title>{node.object.label}{node.object.type ? ` : ${node.object.type}` : ''}</title><rect width={node.width} height={node.height} rx="12" className="sv-object-box"/><rect x="12" y="14" width="36" height="36" rx="9" className="sv-glyph-box"/><text x="30" y="38" className="sv-map-glyph" textAnchor="middle">{objectGlyph[node.object.kind]}</text><text x="61" y="28" className="sv-map-title">{compactLabel(node.object.label, 27)}</text><text x="61" y="47" className="sv-map-type">{compactLabel(node.object.type || node.object.kind, 35)}</text>
        </g>)}
        {layout.relations.map(node => <g key={node.relation.id} className={`sv-map-relation${connectedRelations.has(node.relation.id) ? ' is-connected' : ''}`} transform={`translate(${node.x} ${node.y})`} role={onNodeSelect ? 'button' : 'group'} tabIndex={onNodeSelect ? 0 : undefined} aria-label={`Inspect ${node.relation.label}`} onClick={() => onNodeSelect?.(node.relation.nodeId)} onKeyDown={event => activate(event, onNodeSelect ? () => onNodeSelect(node.relation.nodeId) : undefined)}>
          <title>{node.relation.label}</title><rect width={node.width} height={node.height} rx="12" className="sv-relation-box"/><text x="17" y="27" className="sv-map-title">{compactLabel(node.relation.label, 36)}</text><text x="17" y="47" className="sv-map-type">{relationName[node.relation.kind]}{node.omittedPorts ? ` · ${node.omittedPorts} hidden ports` : ''}</text>
          {node.relation.ports.map((port, index) => <circle key={`${port.objectId}:${index}`} cx="0" cy={12 + (index + 0.5) * 40 / Math.max(node.relation.ports.length, 1)} r="3" className="sv-port-dot"><title>{port.role}</title></circle>)}
        </g>)}
        {layout.objects.length === 0 && <text x="28" y="102" className="sv-map-empty">No explicit objects in this fragment.</text>}
        {layout.relations.length === 0 && layout.objects.length > 0 && <text x="483" y="105" className="sv-map-empty">No interpreted relations in this fragment.</text>}
      </svg>
    </div>
    {(missingObjects > 0 || missingRelations > 0) && <p className="sv-limit-note">Overview shows {layout.objects.length} of {layout.totalObjects} objects and {layout.relations.length} of {layout.totalRelations} relations. Select a smaller statement fragment to inspect the remaining structure.</p>}
    {scopes.length > 0 && <div className="sv-map-contexts"><span className="sv-small-label">Context carried by these fragments</span>{scopes.slice(0, 3).map(scope => <ScopeContext key={scope.id} scope={scope} onNodeSelect={onNodeSelect}/>)}{scopes.length > 3 && <span className="sv-small-label">{scopes.length - 3} further contexts; inspect an individual relation.</span>}</div>}
    <p className="sv-view-note">Connections show expression structure. A relation may occur inside an assumption, negation, or alternative; its presence is not a claim that it holds.</p>
  </div>;
}

function relationSymbol(relation: SemanticRelation): string {
  if (relation.kind === 'membership') return '∈';
  if (relation.kind === 'subset') return '⊆';
  if (relation.kind === 'equality') return relation.label.includes('≠') ? '≠' : '=';
  if (relation.kind === 'inequality') {
    const symbols = ['≤', '≥', '≠', '<', '>'];
    return symbols.find(symbol => relation.label.includes(symbol)) ?? '⋯';
  }
  if (relation.kind === 'image' || relation.kind === 'preimage' || relation.kind === 'application') return '↦';
  return '⋯';
}

function RelationDiagram({ relation, objects, selectedObjectId, onObjectSelect }: { relation: SemanticRelation; objects: Map<string, SemanticObject>; selectedObjectId?: string; onObjectSelect?: (id: string) => void }) {
  const token = (role: string, compact = false): ReactNode => {
    const port = relation.ports.find(candidate => candidate.role === role);
    const object = port && objects.get(port.objectId);
    return object ? <ObjectButton key={`${role}:${object.id}`} object={object} selectedObjectId={selectedObjectId} onObjectSelect={onObjectSelect} role={role} compact={compact}/> : null;
  };
  if (['membership', 'subset', 'equality', 'inequality'].includes(relation.kind)) {
    const roles = relation.kind === 'membership' ? ['element', 'set'] : relation.kind === 'subset' ? ['subset', 'superset'] : ['left', 'right'];
    if (roles.every(role => relation.ports.some(port => port.role === role))) return <div className={`sv-binary-diagram sv-relation-${relation.kind}`}>{token(roles[0])}<span className="sv-relation-symbol" aria-hidden="true">{relationSymbol(relation)}</span>{token(roles[1])}</div>;
  }
  if (['application', 'image', 'preimage'].includes(relation.kind)) {
    const inputPorts = relation.ports.filter(port => port.role.startsWith('input') || port.role === 'set');
    const outputRole = relation.kind === 'application' ? 'output' : 'result';
    return <div className="sv-mapping-diagram"><div className="sv-mapping-inputs">{inputPorts.slice(0, 4).map(port => token(port.role))}{inputPorts.length > 4 && <span className="sv-small-label">{inputPorts.length - 4} further inputs</span>}</div><div className="sv-mapping-transform">{token('function', true)}<span className="sv-mapping-arrow" aria-hidden="true">{relation.kind === 'preimage' ? '←' : '→'}</span>{relation.kind === 'preimage' && <span className="sv-small-label">inverse image</span>}</div><div className="sv-mapping-output">{token(outputRole)}</div></div>;
  }
  if (relation.kind === 'metric-region') return <div className="sv-region-diagram"><div className="sv-region-parameters">{token('center')}{token('radius')}</div><span className="sv-construction-link" aria-hidden="true">→</span><div className="sv-region-result">{token('region')}<span className="sv-small-label">Symbolic region · no coordinates assumed</span></div></div>;
  if (relation.kind === 'distance') return <div className="sv-distance-diagram"><div className="sv-distance-pair">{token('from')}<span className="sv-distance-line" aria-hidden="true"/>{token('to')}</div><div className="sv-distance-value">{token('distance', true)}</div></div>;
  return <div className="sv-generic-ports">{relation.ports.slice(0, 6).map((port, index) => { const object = objects.get(port.objectId); return object ? <ObjectButton key={`${port.role}:${index}`} object={object} selectedObjectId={selectedObjectId} onObjectSelect={onObjectSelect} role={port.role}/> : <span key={`${port.role}:${index}`} className="sv-small-label">{port.role}: unavailable</span>; })}{relation.ports.length > 6 && <span className="sv-small-label">{relation.ports.length - 6} further ports</span>}</div>;
}

function RelationMap(props: SemanticViewProps) {
  const { document, view, onNodeSelect } = props;
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const scopes = new Map(document.scopes.map(scope => [scope.id, scope]));
  const ids = new Set(view.relationIds);
  const relations = document.relations.filter(relation => ids.has(relation.id));
  const shown = relations.slice(0, 8);
  return <div className="sv-relation-map"><div className="sv-view-intro"><p>Read each relation through its objects and their roles. Repeated objects stay linked across views.</p><span className="sv-fidelity">{view.fidelity === 'structural' ? 'Structural' : 'Symbolic'} view</span></div>
    <div className="sv-relation-cards">{shown.map((relation, index) => <article key={relation.id} className={`sv-relation-card sv-relation-${relation.kind}`}>
      <div className="sv-relation-heading"><span className="sv-relation-index">{String(index + 1).padStart(2, '0')}</span><div><span className="sv-small-label">{relationName[relation.kind]}</span><h3>{relation.label}</h3></div>{onNodeSelect && <button type="button" className="sv-source-link" onClick={() => onNodeSelect(relation.nodeId)} aria-label={`Inspect source fragment for ${relation.label}`}>Inspect fragment <span aria-hidden="true">↗</span></button>}</div>
      <ScopeContext scope={scopes.get(relation.scopeId)} onNodeSelect={onNodeSelect}/>
      <RelationDiagram relation={relation} objects={objects} selectedObjectId={props.selectedObjectId} onObjectSelect={props.onObjectSelect}/>
      {relation.conditions.length > 0 && <div className="sv-conditions">{relation.conditions.map((condition, index) => <p key={`${condition}:${index}`}>{condition}</p>)}</div>}
    </article>)}</div>
    {relations.length === 0 && <p className="sv-empty">No interpreted relations in this fragment. Its typed objects remain available in the semantic map.</p>}
    {relations.length > shown.length && <p className="sv-limit-note">Showing {shown.length} of {relations.length} relations. Select a smaller statement fragment to inspect the remaining relations.</p>}
    <p className="sv-view-note">These are diagrams of mathematical roles. Relative position and distance carry no geometric meaning.</p>
  </div>;
}

function QuantifierFlow(props: SemanticViewProps) {
  const { document, view, selectedObjectId, onObjectSelect, onNodeSelect } = props;
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const scopes = new Map(document.scopes.map(scope => [scope.id, scope]));
  const objectIds = new Set(view.objectIds);
  const nodeIds = new Set(view.nodeIds);
  const choices = document.choices.filter(choice => objectIds.has(choice.objectId) || nodeIds.has(choice.nodeId));
  const shown = choices.slice(0, 12);
  return <div className="sv-quantifier-flow"><div className="sv-view-intro"><p>A witness can use earlier choices in its scope. It cannot depend on a variable chosen later.</p><span className="sv-fidelity">Scope and dependency</span></div>
    <div className="sv-choice-legend"><span><b>∀</b> a value from the full domain</span><span><b>∃</b> a candidate chosen at this stage</span></div>
    <ol className="sv-choices">{shown.map((choice, index) => {
      const object = objects.get(choice.objectId);
      const dependencies = choice.dependsOn.flatMap(id => objects.has(id) ? [objects.get(id)!] : []);
      const missingDependencies = choice.dependsOn.length - dependencies.length;
      return <li key={choice.id} className={`sv-choice sv-choice-${choice.role}${selectedObjectId === choice.objectId ? ' is-selected' : ''}`}><span className="sv-choice-step" aria-label={`Step ${index + 1}`}>{index + 1}</span><div className="sv-choice-card"><div className="sv-choice-heading"><span className="sv-choice-symbol" aria-hidden="true">{choiceSymbol[choice.role]}</span><div><span className="sv-small-label">{choiceName[choice.role]}</span>{object ? <button type="button" className="sv-choice-name" onClick={() => onObjectSelect?.(object.id)} aria-pressed={selectedObjectId === object.id}>{object.label} <span>: {object.type || object.kind}</span></button> : <span className="sv-choice-name">Symbolic choice</span>}</div>{onNodeSelect && <button type="button" className="sv-source-link" onClick={() => onNodeSelect(choice.nodeId)} aria-label={`Inspect binder ${object?.label ?? index + 1}`}>Binder <span aria-hidden="true">↗</span></button>}</div>
      <ScopeContext scope={scopes.get(choice.scopeId)} onNodeSelect={onNodeSelect}/>
      <p className="sv-choice-explanation">{choice.explanation}</p>
      {(dependencies.length > 0 || missingDependencies > 0) ? <div className="sv-choice-dependencies"><span className="sv-small-label">{choice.role === 'existential' ? 'May depend on' : 'Earlier choices in this scope'}</span><div className="sv-dependency-tokens">{dependencies.slice(0, 8).map(dependency => <ObjectButton key={dependency.id} object={dependency} selectedObjectId={selectedObjectId} onObjectSelect={onObjectSelect} compact/>)}{dependencies.length > 8 && <span className="sv-small-label">{dependencies.length - 8} further choices</span>}{missingDependencies > 0 && <span className="sv-small-label">{missingDependencies} additional scoped dependencies</span>}</div></div> : choice.role === 'existential' ? <p className="sv-fixed-choice">Chosen without earlier values. Later choices cannot change this witness.</p> : null}
      </div></li>;
    })}</ol>
    {choices.length === 0 && <p className="sv-empty">This fragment introduces no quantified choices.</p>}
    {choices.length > shown.length && <p className="sv-limit-note">Showing {shown.length} of {choices.length} choices. Select a smaller statement fragment to inspect the remaining binders.</p>}
    <p className="sv-view-note">Steps follow the statement’s reading order. Only the listed dependencies belong to the same scope; choices in separate logical branches are not combined.</p>
  </div>;
}

export function SemanticView(props: SemanticViewProps) {
  return <section className="semantic-view" aria-label={props.view.title}>{props.view.kind === 'quantifier-flow' ? <QuantifierFlow {...props}/> : props.view.kind === 'relation-map' ? <RelationMap {...props}/> : <SemanticMap {...props}/>}</section>;
}
