import { useId, useMemo, type CSSProperties, type KeyboardEvent, type ReactNode } from 'react';
import { MathLabel } from '../components/MathLabel';
import { scopedGraphMathDisplay } from './scoped-graph-math';
import { FigureScroll } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import type { ReadingDocument, ReadingNode } from '../reading/types';
import type { ReadingRegion } from '../reading/presentation';
import { binderDisambiguators, type ScopedClauseGraph, type ScopedStatementGraphModel } from '../reading/scoped-graph';
import type { SemanticDocument } from '../semantic/types';
import { readingObjectColor } from './object-identity';
import { layoutScopedGraph } from './scoped-graph-layout';
import './scoped-statement-graph.css';

interface Selection {
  focusedNodeId?: string;
  selectedObjectId?: string;
  selectedRelationId?: string;
  onObjectSelect?: (id: string) => void;
  onNodeSelect?: (id: string) => void;
  onSourceSelect?: (id: string) => void;
  onRelationSelect?: (id: string) => void;
}
const short = (text: string, length = 100) => [...text].length > length ? `${[...text].slice(0, length - 1).join('')}…` : text;
function activate(event: KeyboardEvent<SVGGElement>, action: () => void) {
  if (event.key === 'Enter' || event.key === ' ') { event.preventDefault(); action(); }
}

function ClauseDiagram({ graph, ...selection }: Selection & { graph: ScopedClauseGraph }) {
  const text = useDiagramText();
  const marker = `scoped-result-${useId().replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const labels = new Map(graph.nodes.map(node => [node.id, scopedGraphMathDisplay(node, graph)]));
  const sizes = Object.fromEntries(graph.nodes.map(node => [node.id, {
    note: node.referenceNote ? text.size(`${node.id}:note`, node.referenceNote, 11) : undefined,
    label: text.size(node.id, labels.get(node.id)?.source ?? node.label, node.kind === 'object' ? 16 : 14),
    ports: Object.fromEntries(node.ports.map(port => [port.id, text.size(port.id, port.role, 12)])),
  }]));
  const layout = layoutScopedGraph(graph, sizes);
  const objects = new Map(graph.nodes.map(node => [node.id, node]));
  return <FigureScroll className="ssg-scroll" label="Construction and relation graph; scroll to see every port">
    <svg ref={text.ref} viewBox={`${layout.x} 0 ${layout.width} ${layout.height}`} style={{ minWidth: Math.ceil(layout.width * 10 / 11) }} role="group" aria-label="Source-supplied operations connected through their exact objects" data-graph-scope={graph.scopeId}>
      <defs><marker id={marker} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1 L7 4 L1 7"/></marker></defs>
      {layout.edges.map(edge => <path key={edge.id} d={edge.path} className={`ssg-edge ssg-edge-${edge.kind}`} markerEnd={edge.kind === 'result' ? `url(#${marker})` : undefined}
        data-graph-edge={edge.id} data-graph-port={edge.portId} data-edge-role={edge.role} data-edge-kind={edge.kind} data-reading-object={edge.objectId}><title>{`${edge.role}: ${edge.objectId}`}</title></path>)}
      {layout.nodes.map(position => {
        const node = objects.get(position.id)!, object = node.object, relation = node.relation;
        const source = object ? `${object.label}${object.type ? ` : ${object.type}` : ''}${node.referenceNote ? `; ${node.referenceNote}` : ''}` : `${relation!.label}; ${relation!.fidelity === 'structural' ? 'symbolic application structure' : 'supplied relation'}`;
        const selected = object ? object.id === selection.selectedObjectId : relation?.id === selection.selectedRelationId;
        const action = () => {
          if (object) { selection.onObjectSelect?.(object.id); }
          else selection.onRelationSelect?.(relation!.id);
        };
        return <g key={node.id} className={`ssg-node ssg-node-${node.kind}${relation?.fidelity === 'structural' ? ' ssg-symbolic' : ''}${selected ? ' ssg-selected' : ''}`}
          data-graph-node={node.id} data-reading-object={object?.id} data-reading-relation={relation?.id} data-source-node={graph.nodeId}
          style={object ? { '--ssg-object': readingObjectColor(object.id) } as CSSProperties : undefined}
          role="button" tabIndex={0} aria-label={`Inspect ${source}`} aria-pressed={object ? selected : undefined} onClick={action} onKeyDown={event => activate(event, action)}>
          <title>{source}</title>
          <rect x={position.x} y={position.y} width={position.width} height={position.height} rx={object ? 18 : 7}/>
          <>{object ? <MathLabel label={labels.get(node.id)!} labelKey={node.id} fontSize={16} className="ssg-node-label" x={position.labelX} y={position.labelY}/> : <text data-diagram-label={node.id} className="ssg-node-label" x={position.labelX} y={position.labelY} textAnchor="middle">{node.label}</text>}{node.referenceNote && <text data-diagram-label={`${node.id}:note`} className="ssg-reference-note" x={position.labelX} y={position.labelY + sizes[node.id].label.height - sizes[node.id].label.ascent + 6 + sizes[node.id].note!.ascent} textAnchor="middle">{node.referenceNote}</text>}</>
          {position.ports.map(port => <g key={port.id} data-graph-port-label={port.id}>
            <circle cx={port.x} cy={port.y} r="3"/>
            <text data-diagram-label={port.id} className="ssg-port-label" x={port.labelX} y={port.labelY} textAnchor={port.output ? 'end' : 'start'}>{node.ports.find(candidate => candidate.id === port.id)!.role}</text>
          </g>)}
        </g>;
      })}
    </svg>
  </FigureScroll>;
}

const titles = { implication: '⇒  Conditional', all: '∧  Both conditions', alternatives: '∨  At least one alternative', equivalence: '↔  Each condition implies the other', negation: '¬  Not', structure: 'Expression structure' };
const symbols: Record<string, string> = { forall: '∀', exists: '∃', parameter: 'Parameter', definition: 'Define', auxiliary: 'Context entry' };

/** A focused drawing retains its logical container tree. Folds change attention
 * only: source nodes, relation ports, identities and callbacks remain unchanged. */
export function ScopedStatementGraph({ model, document, reading, ...selection }: Selection & { model: ScopedStatementGraphModel; document: SemanticDocument; reading: ReadingDocument }) {
  const focus = selection.focusedNodeId ?? reading.selection.nodeId;
  const clauses = useMemo(() => new Map(model.clauses.map(clause => [clause.node.id, clause])), [model]);
  const focusNode = clauses.get(focus)?.node;
  const selectNode = (id: string) => selection.onNodeSelect?.(id);
  const clausePicker = <label>Clause <select data-reading-focus="" aria-label="Choose graph clause" value={focusNode?.id ?? ''} onChange={event => selectNode(event.target.value)}><option value="" disabled>Choose a clause to draw</option>{model.clauses.map((clause, index) => <option key={clause.node.id} value={clause.node.id}>{index + 1}. {short(clause.node.lean, 85)}</option>)}</select></label>;
  if (!focusNode) return <section className="scoped-statement-graph" aria-label="Scoped construction graph"><nav className="ssg-navigation">{clausePicker}</nav><p className="ssg-description">Choose a clause to inspect its supplied operations and logical context.</p></section>;
  const path = new Set([focusNode.id]);
  const nodes = new Map(reading.nodes.map(node => [node.id, node]));
  let ancestor = focusNode.parentId;
  while (ancestor) { path.add(ancestor); ancestor = nodes.get(ancestor)?.parentId; }
  const declarations = binderDisambiguators(document);
  const sourceButton = (node: ReadingNode, label: string) => node.children.length ? <span className="ssg-frame-title" title={node.lean}>{label}</span> : <button type="button" className="ssg-source" data-reading-node={node.id} title={node.lean} onClick={() => selectNode(node.id)}>{label}</button>;
  function exactSource(node: ReadingNode) {
    return <details className="ssg-exact"><summary>Exact source and supplied relations</summary><code>{node.lean}</code>
      {(clauses.get(node.id)?.graphs ?? []).map(graph => <div key={graph.id} data-source-scope={graph.scopeId}>
        <p>{graph.groupRole === 'local-expression' ? 'Local expression scope' : 'Clause scope'}</p>
        <ul>{graph.relationIds.map(id => {
          const relation = document.relations.find(relation => relation.id === id);
          return relation && <li key={id}><button type="button" onClick={() => selection.onRelationSelect?.(id)}>{relation.label}</button> · {relation.fidelity === 'structural' ? 'symbolic structure' : relation.kind}<ul>{relation.ports.map((port, index) => <li key={index}>{port.role}: {document.objects.find(object => object.id === port.objectId)?.label ?? port.objectId}</li>)}</ul></li>;
        })}</ul>
      </div>)}
    </details>;
  }
  function clause(node: ReadingNode, detailed: boolean) {
    const item = clauses.get(node.id), groups = item?.graphs ?? [];
    if (!detailed) return <div className="ssg-clause-summary" data-clause-node={node.id}>{sourceButton(node, short(node.lean))}</div>;
    return <div className="ssg-clause" data-clause-node={node.id}>
      <header>{sourceButton(node, short(node.lean, 180))}</header>
      {groups.map(graph => graph.reason ? <p className="ssg-boundary" key={graph.id}>{graph.reason}</p>
        : graph.groupRole === 'local-expression' ? <details className="ssg-local" key={graph.id}><summary>Inside a local expression scope{graph.localBindings.length ? ` · ${graph.localBindings.map(binding => `${binding.role === 'lambda' ? 'λ' : binding.role === 'existential' ? '∃' : '∀'} ${declarations.get(binding.id) ?? binding.name} : ${binding.type}`).join(' · ')}` : ' · binder metadata unavailable'}</summary><p>{graph.localBindings.length ? 'The displayed local binders apply only to this expression body; these operations are not separate assertions.' : 'The supplied local scope has no recoverable binder declaration. Treat this as an unsupported scope boundary; inspect the exact expression below.'}</p><ClauseDiagram graph={graph} {...selection}/></details>
          : graph.nodes.length ? <ClauseDiagram key={graph.id} graph={graph} {...selection}/> : null)}
      {!groups.length && <p className="ssg-boundary">This clause is retained symbolically. No operation ports were supplied.</p>}
      <div className="ssg-key"><span><i className="ssg-argument-key"/> Argument port</span><span><i className="ssg-result-key"/> Supplied result</span><span>Rounded nodes: shared objects</span><span>Dashed boxes: uninterpreted applications</span></div>
      {exactSource(node)}
    </div>;
  }
  function render(region: ReadingRegion, unfolded = false): ReactNode {
    const active = region.sourceNodeIds.some(id => path.has(id));
    if (region.kind === 'clause') return clause(region.node, active || unfolded);
    const title = region.kind === 'binders' ? region.binders.map(node => `${symbols[node.kind] ?? 'With'} ${declarations.get(node.binder?.binderId ?? '') ?? node.binder?.name}`).join(' · ') : titles[region.kind];
    if (!active && !unfolded) return <details className="ssg-fold" data-fold-node={region.node.id} data-logic-kind={region.node.kind}><summary>{title}</summary>{render(region, true)}</details>;
    let children: ReactNode;
    if (region.kind === 'binders') children = <>{region.body && render(region.body)}</>;
    else if (region.kind === 'implication') children = <><div className="ssg-assumptions" data-logic-edge="assumption"><span className="ssg-role">IF · antecedent{region.assumptions.length > 1 ? 's' : ''}</span>{region.assumptions.map(child => <div key={child.id}>{render(child)}</div>)}</div><div className="ssg-conclusion" data-logic-edge="conclusion"><span className="ssg-role">THEN · conditional conclusion</span>{render(region.conclusion)}</div></>;
    else if (region.kind === 'negation') children = <div data-logic-edge="negated">{render(region.body)}</div>;
    else children = region.children.map((child, index) => <div key={child.id} className="ssg-branch" data-logic-edge={child.node.edgeFromParent?.role} data-child-index={child.node.edgeFromParent?.index}>
      <span className="ssg-role">{region.kind === 'all' ? `Required together · condition ${index + 1}` : region.kind === 'alternatives' ? `Alternative ${index + 1}` : region.kind === 'equivalence' ? `${index === 0 ? 'First' : 'Second'} condition` : `Part ${index + 1}`}</span>{render(child)}</div>);
    return <section className={`ssg-frame ssg-frame-${region.kind}${region.node.kind === 'exists' ? ' ssg-exists' : ''}`} data-frame-node={region.node.id} data-frame-source-nodes={region.sourceNodeIds.join(' ')} data-logic-kind={region.node.kind}>
      {region.kind !== 'implication' && <header className="ssg-frame-heading">{region.kind === 'binders' ? region.binders.map(node => <span key={node.id} className={`ssg-binder${node.binder?.objectId && node.binder.objectId === selection.selectedObjectId ? ' ssg-binder-selected' : ''}`} data-reading-object={node.binder?.objectId} data-binder-id={node.binder?.binderId}>
        {sourceButton(node, `${symbols[node.kind] ?? 'With'} ${declarations.get(node.binder?.binderId ?? '') ?? node.binder?.name}`)}
        <details className="ssg-type"><summary aria-label={`Type of ${node.binder?.name}`}>type</summary><code>{node.binder?.type}</code></details>
      </span>) : sourceButton(region.node, title)}</header>}{children}
    </section>;
  }
  const index = model.clauses.findIndex(clause => clause.node.id === focusNode.id);
  return <section className="scoped-statement-graph" aria-label="Scoped construction graph">
    <nav className="ssg-navigation" aria-label="Graph clause focus">{clausePicker}
      <button type="button" aria-label="Previous graph clause" disabled={index <= 0} onClick={() => selectNode(model.clauses[index - 1].node.id)}>←</button>
      <button type="button" aria-label="Next graph clause" disabled={index >= model.clauses.length - 1} onClick={() => selectNode(model.clauses[index + 1].node.id)}>→</button>
    </nav>
    <p className="ssg-description">Frames preserve quantifier order and logical branches. Port connections show supplied expressions, not witness dependence.</p>
    {render(model.root)}
  </section>;
}
