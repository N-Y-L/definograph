import type { Expr } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { planReadingPresentation, type ReadingRegion } from './presentation';
import type { ReadingDocument, ReadingNode, ReadingRelationGroup } from './types';

export interface ScopedGraphPort { readonly id: string; readonly role: string; readonly objectId: string; readonly output: boolean }
export interface ScopedGraphNode {
  readonly id: string;
  readonly kind: 'object' | 'relation';
  readonly label: string;
  readonly referenceNote?: string;
  readonly object?: SemanticObject;
  readonly relation?: SemanticRelation;
  readonly ports: readonly ScopedGraphPort[];
}
export interface ScopedGraphEdge {
  readonly id: string; readonly from: string; readonly to: string;
  readonly relationId: string; readonly portId: string; readonly objectId: string;
  readonly role: string; readonly kind: 'argument' | 'result';
}
export interface ScopedClauseGraph {
  readonly id: string; readonly nodeId: string; readonly scopeId: string;
  readonly groupRole: ReadingRelationGroup['role']; readonly nodes: readonly ScopedGraphNode[];
  readonly edges: readonly ScopedGraphEdge[]; readonly relationIds: readonly string[];
  readonly reason?: string;
  readonly localBindings: readonly { id: string; role: string; name: string; type: string }[];
}
export interface ScopedStatementGraphModel {
  readonly root: ReadingRegion;
  readonly clauses: readonly { readonly node: ReadingNode; readonly graphs: readonly ScopedClauseGraph[] }[];
}

// These are already supplied producer ports, not deductions from a function's
// name, printed expression, or the object table's first-occurrence scope.
const outputRoles = new Set(['output', 'result', 'region', 'distance', 'color', 'target vertex']);
const objectKey = (id: string) => `object:${id}`;
const relationKey = (id: string) => `relation:${id}`;
const maximumObjects = 40, maximumRelations = 20, maximumPorts = 100;

function clauseGraph(document: SemanticDocument, node: ReadingNode, group: ReadingRelationGroup): ScopedClauseGraph {
  const relations = new Map(document.relations.map(relation => [relation.id, relation]));
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const scope = document.scopes.find(scope => scope.id === group.scopeId);
  const localBindings: { id: string; role: string; name: string; type: string }[] = [];
  let localScope = scope;
  while (localScope && localScope.id !== node.scopeId) {
    for (const choice of document.choices.filter(choice => choice.scopeId === localScope!.id)) {
      const object = objects.get(choice.objectId);
      if (object) localBindings.unshift({ id: choice.binderId, role: choice.role, name: object.label, type: object.type });
    }
    localScope = document.scopes.find(candidate => candidate.id === localScope!.parentId);
  }
  const base = { localBindings, id: group.id, nodeId: node.id, scopeId: group.scopeId, groupRole: group.role, relationIds: group.relationIds };
  const reject = (reason: string): ScopedClauseGraph => ({ ...base, nodes: [], edges: [], reason });
  const members = group.relationIds.flatMap(id => relations.has(id) ? [relations.get(id)!] : []);
  if (!scope || scope.nodeId !== node.id || members.length !== group.relationIds.length || new Set(group.relationIds).size !== group.relationIds.length
    || members.some(relation => relation.nodeId !== node.id || relation.scopeId !== group.scopeId)) return reject('The relation group has an unavailable or inconsistent source scope. Its source is retained below.');
  const objectIds = [...new Set(members.flatMap(relation => relation.ports.map(port => port.objectId)))];
  if (objectIds.some(id => !objects.has(id))) return reject('Some relation ports have no supplied object. The source remains available.');
  if (objectIds.length > maximumObjects || members.length > maximumRelations || members.reduce((count, relation) => count + relation.ports.length, 0) > maximumPorts)
    return reject(`This group exceeds the diagram bound (${maximumObjects} objects, ${maximumRelations} operations, ${maximumPorts} ports). Inspect the complete source and relation list below.`);
  const declarations = binderDisambiguators(document);
  const nodes: ScopedGraphNode[] = objectIds.map(id => {
    const object = objects.get(id)!;
    const notes = expressionBinderIds(object.expression).flatMap(id => declarations.has(id) ? [declarations.get(id)!] : []);
    return { id: objectKey(id), kind: 'object', label: object.label, object, referenceNote: object.binder ? `from ${binderRoleSymbol(object.binder.role)} ${declarations.get(object.binder.id) ?? object.binder.name}` : notes.length ? notes.join('; ') : undefined, ports: [] };
  });
  const edges: ScopedGraphEdge[] = [];
  for (const relation of members) {
    const ports = relation.ports.map((port, index) => ({ ...port, id: `${relation.id}:port:${index}`, output: relation.fidelity !== 'structural' && relation.kind !== 'predicate' && outputRoles.has(port.role) }));
    nodes.push({ id: relationKey(relation.id), kind: 'relation', label: relation.kind === 'application' ? 'apply' : relation.label, relation, ports });
    for (const port of ports) edges.push({ id: port.id, relationId: relation.id, portId: port.id, objectId: port.objectId, role: port.role,
      from: port.output ? relationKey(relation.id) : objectKey(port.objectId), to: port.output ? objectKey(port.objectId) : relationKey(relation.id), kind: port.output ? 'result' : 'argument' });
  }
  return { ...base, nodes, edges };
}

/** Spatial composition of an existing reading only. No expression is matched,
 * unfolded, evaluated, or reclassified here. Each graph is one clause and one
 * expression scope; the source tree supplies all surrounding logical frames. */
export function compileScopedStatementGraph(document: SemanticDocument, reading: ReadingDocument): ScopedStatementGraphModel | undefined {
  // Positional components have a separate, explicitly associated interpretation
  // boundary. Keep that reader separate from this legacy semantic document view.
  if (document.presentation?.kind === 'component') return;
  const panels = new Map(reading.panels.map(panel => [panel.nodeId, panel]));
  const clauses = reading.nodes.filter(node => !node.children.length).map(node => ({ node, graphs: (panels.get(node.id)?.groups ?? []).map(group => clauseGraph(document, node, group)) }));
  const composed = clauses.filter(clause => clause.graphs.some(graph => !graph.reason && graph.edges.some(edge => edge.kind === 'result') && graph.nodes.filter(node => node.kind === 'relation').length > 1));
  if (!composed.length) return;
  return { root: planReadingPresentation(reading).root, clauses };
}

/** Reference annotations preserve binder identity when printed names collide. */
export function binderDisambiguators(document: SemanticDocument): Map<string, string> {
  const binders = [...new Map(document.objects.flatMap(object => object.binder ? [[object.binder.id, object.binder] as const] : [])).values()];
  const names = new Map<string, typeof binders>();
  for (const binder of binders) names.set(binder.name, [...(names.get(binder.name) ?? []), binder]);
  return new Map([...names.values()].filter(group => group.length > 1).flatMap(group => group.map((binder, index) => [binder.id, `${binder.name} [declaration ${index + 1}]`])));
}
function expressionBinderIds(expression: Expr): string[] {
  const ids = new Set<string>();
  const visit = (node: Expr) => {
    if (node.kind === 'var') ids.add(node.id);
    else if (node.kind === 'app') { visit(node.fn); node.args.forEach(visit); }
    else if (node.kind === 'forall' || node.kind === 'lambda') { ids.add(node.binder.id); visit(node.body); if (node.binderType) visit(node.binderType); }
  };
  visit(expression);
  return [...ids];
}

export const binderRoleSymbol = (role: string) => ({ universal: '∀', existential: '∃', lambda: 'λ', parameter: 'parameter', assumption: 'assumption', definition: 'definition', auxiliary: 'context' })[role] ?? role;
