import type { StatementNode } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation, SemanticScope } from '../semantic/types';
import { READING_DOCUMENT_VERSION } from './types';
import type { ReadingBinder, ReadingConnection, ReadingDocument, ReadingEdge, ReadingNode, ReadingOptions, ReadingPanel, ReadingQuantifierGroup, ReadingRelationGroup, ReadingStep } from './types';

const unique = <T>(values: readonly T[]): T[] => [...new Set(values)];
const producedRoles = new Set(['output', 'result', 'region', 'distance', 'color', 'target vertex']);

function edgeFor(parent: StatementNode, index: number): ReadingEdge {
  switch (parent.kind) {
    case 'implies': return index === 0 ? { role: 'assumption', label: 'If', index } : { role: 'conclusion', label: 'Then', index };
    case 'and': return { role: 'conjunct', label: index === 0 ? 'Both' : 'And', index };
    case 'or': return { role: 'alternative', label: index === 0 ? 'Either' : 'Or', index };
    case 'iff': return { role: index === 0 ? 'equivalence-left' : 'equivalence-right', label: index === 0 ? 'First condition' : 'Second condition', index };
    case 'not': return { role: 'negated', label: 'Not', index };
    case 'parameter': return { role: 'result', label: 'Result', index };
    default: return { role: 'body', label: parent.kind === 'exists' ? 'Such that' : 'The following holds', index };
  }
}

function relationPhrase(relation: SemanticRelation, objects: ReadonlyMap<string, SemanticObject>): string | undefined {
  const port = (role: string) => {
    const id = relation.ports.find(port => port.role === role)?.objectId;
    return id ? objects.get(id)?.label : undefined;
  };
  const left = port('left'), right = port('right');
  switch (relation.kind) {
    case 'membership': return port('element') && port('set') ? `${port('element')} belongs to ${port('set')}` : undefined;
    case 'subset': return port('subset') && port('superset') ? `${port('subset')} is contained in ${port('superset')}` : undefined;
    case 'equality': return left && right ? `${left} ${relation.label === '≠' ? 'is not equal to' : 'equals'} ${right}` : undefined;
    case 'inequality': return left && right ? `${left} ${relation.label === '≤' ? 'is at most' : relation.label === '<' ? 'is less than' : relation.label} ${right}` : undefined;
    case 'function-property': return port('function') ? `${port('function')} is ${relation.label}` : undefined;
    case 'metric-region': return port('center') && port('radius') ? `The ${relation.label} centered at ${port('center')} with radius ${port('radius')}` : undefined;
    case 'distance': return port('from') && port('to') ? `The distance from ${port('from')} to ${port('to')}` : undefined;
    case 'image': return port('function') && port('set') ? `The image of ${port('set')} under ${port('function')}` : undefined;
    case 'preimage': return port('function') && port('set') ? `The preimage of ${port('set')} under ${port('function')}` : undefined;
    case 'graph-adjacency': return `${port('left vertex')} is adjacent to ${port('right vertex')} in ${port('graph')}`;
    case 'graph-colorable': return `${port('graph')} admits a proper coloring with at most ${port('color bound')} colors`;
    case 'graph-coloring': return port('vertex') ? `${port('coloring')} assigns a color to ${port('vertex')}` : `${port('coloring')} is a proper coloring of ${port('graph')}`;
    case 'graph-map': return `${port('map')} preserves the stated graph relationships`;
    // An abstract predicate or application keeps its source expression. Calling it true would
    // invent semantics, and generic inputs need not be points or members of a finite model.
    default: return undefined;
  }
}

function phraseFor(node: StatementNode, rootRelation: SemanticRelation | undefined, objects: ReadonlyMap<string, SemanticObject>): string {
  const binder = node.binder;
  switch (node.kind) {
    case 'forall': return binder ? `For every ${binder.name} : ${binder.type}` : 'For every choice';
    case 'exists': return binder ? `There exists ${binder.name} : ${binder.type}` : 'There exists a choice';
    case 'parameter': return binder ? `With parameter ${binder.name} : ${binder.type}` : 'With these parameters';
    case 'implies': return 'If the assumption holds, then the conclusion holds';
    case 'and': return 'Both conditions hold';
    case 'or': return 'At least one of these alternatives holds';
    case 'iff': return 'Each condition implies the other';
    case 'not': return 'The following condition does not hold';
    case 'predicate': return rootRelation && rootRelation.fidelity !== 'structural' ? relationPhrase(rootRelation, objects) ?? node.lean : node.lean;
  }
}

/** Connections express shared terms within an atomic clause, never logical entailment. */
function connectionsFor(relations: readonly SemanticRelation[]): ReadingConnection[] {
  const uses = new Map<string, { relation: SemanticRelation; produces: boolean; consumes: boolean }[]>();
  for (const relation of relations) {
    const objectIds = unique(relation.ports.map(port => port.objectId));
    for (const objectId of objectIds) {
      const ports = relation.ports.filter(port => port.objectId === objectId);
      const usage = uses.get(objectId) ?? [];
      usage.push({ relation, produces: ports.some(port => producedRoles.has(port.role)), consumes: ports.some(port => !producedRoles.has(port.role)) });
      uses.set(objectId, usage);
    }
  }
  const connections: ReadingConnection[] = [];
  for (const [objectId, usage] of uses) {
    if (usage.length < 2) continue;
    const producer = usage.find(use => use.produces);
    // A star retains connectivity without a quadratic mesh for frequently shared constants.
    const anchor = producer ?? usage[0]!;
    for (const other of usage) {
      if (other === anchor) continue;
      connections.push({ objectId, fromRelationId: anchor.relation.id, toRelationId: other.relation.id, kind: producer && other.consumes ? 'feeds' : 'shared' });
    }
  }
  return connections;
}

function relationGroup(relations: readonly SemanticRelation[], scopeId: string, nodeId: string, scope: SemanticScope | undefined): ReadingRelationGroup {
  const connections = connectionsFor(relations);
  const topLevel = relations.filter(relation => relation.provenance.expressionPath === 'expression').map(relation => relation.id);
  const childProducers = new Set(connections.filter(connection => connection.kind === 'feeds').map(connection => connection.fromRelationId));
  const roots = topLevel.length ? topLevel : relations.filter(relation => !childProducers.has(relation.id)).map(relation => relation.id);
  return { id: `reading-group:${nodeId}:${scopeId}`, scopeId, role: scopeId === `scope:${nodeId}` ? 'clause' : 'local-expression', relationIds: relations.map(relation => relation.id), rootRelationIds: roots, objectIds: unique(relations.flatMap(relation => relation.ports.map(port => port.objectId))), connections, context: scope?.context ?? [] };
}

/**
 * Compile the whole logical statement before choosing a spatial or sequential presentation.
 * Selection marks a focus and its context; it never deletes clauses from this document.
 */
export function compileReading(document: SemanticDocument, options: ReadingOptions = {}): ReadingDocument {
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const scopes = new Map(document.scopes.map(scope => [scope.id, scope]));
  const relationsByNode = new Map<string, SemanticRelation[]>();
  for (const relation of document.relations) {
    const relations = relationsByNode.get(relation.nodeId) ?? [];
    relations.push(relation);
    relationsByNode.set(relation.nodeId, relations);
  }
  const coverageByNode = new Map(document.coverage.map(coverage => [coverage.nodeId, coverage]));
  const choicesByBinder = new Map(document.choices.map(choice => [choice.binderId, choice]));
  const objectsByBinder = new Map(document.objects.flatMap(object => object.binder ? [[object.binder.id, object] as const] : []));
  const seenNodes = new Set<string>();
  const panels: ReadingPanel[] = [];
  const nodeIndex = new Map<string, ReadingNode>();
  const sourceOrder: string[] = [];
  const branchPaths = new Map<string, ReadingQuantifierGroup['branchPath']>();
  const diagnostics = [...document.diagnostics];

  function visit(source: StatementNode, parent?: StatementNode, edge?: ReadingEdge, branchPath: ReadingQuantifierGroup['branchPath'] = []): ReadingNode {
    if (seenNodes.has(source.id)) throw new Error(`Duplicate statement node id: ${source.id}`);
    seenNodes.add(source.id);
    sourceOrder.push(source.id);
    branchPaths.set(source.id, branchPath);
    const scopeId = `scope:${source.id}`;
    const scope = scopes.get(scopeId);
    const relations = relationsByNode.get(source.id) ?? [];
    const coverage = coverageByNode.get(source.id);
    const rootRelation = relations.find(relation => relation.provenance.expressionPath === 'expression' && relation.scopeId === scopeId);
    const phrase = phraseFor(source, rootRelation, objects);
    let binder: ReadingBinder | undefined;
    if (source.binder) {
      const sourceBinder = source.binder;
      const choice = choicesByBinder.get(sourceBinder.id);
      binder = { binderId: sourceBinder.id, objectId: choice?.objectId ?? objectsByBinder.get(sourceBinder.id)?.id, choiceId: choice?.id, name: sourceBinder.name, type: sourceBinder.type, role: sourceBinder.role, dependsOn: choice?.dependsOn ?? [], scopeId: choice?.scopeId ?? scopeId };
    }
    const children = source.children.map((child, index) => {
      const childEdge = edgeFor(source, index);
      return visit(child, source, childEdge, [...branchPath, { nodeId: source.id, edge: childEdge }]);
    });
    let panel: ReadingPanel | undefined;
    if (!source.children.length) {
      const scopeGroups = new Map<string, SemanticRelation[]>();
      for (const relation of relations) {
        const group = scopeGroups.get(relation.scopeId) ?? [];
        group.push(relation);
        scopeGroups.set(relation.scopeId, group);
      }
      const groups = [...scopeGroups].map(([groupScopeId, groupRelations]) => relationGroup(groupRelations, groupScopeId, source.id, scopes.get(groupScopeId)));
      panel = { id: `reading-panel:${source.id}`, nodeId: source.id, phrase, relationIds: relations.map(relation => relation.id), rootRelationIds: groups.filter(group => group.role === 'clause').flatMap(group => group.rootRelationIds), objectIds: unique([...(coverage?.objectIds ?? []), ...relations.flatMap(relation => relation.ports.map(port => port.objectId))]), sceneIds: coverage?.sceneIds ?? document.scenes.filter(scene => scene.nodeId === source.id).map(scene => scene.id), opaqueRegionIds: coverage?.opaqueRegionIds ?? document.opaqueRegions.filter(region => region.nodeId === source.id).map(region => region.id), coverage: coverage?.status ?? 'structural', groups };
      panels.push(panel);
    }
    const directions = source.kind === 'iff' && children.length === 2 ? [
      { id: `direction:${source.id}:forward`, label: 'First implies second', assumptionNodeId: children[0]!.id, conclusionNodeId: children[1]!.id },
      { id: `direction:${source.id}:backward`, label: 'Second implies first', assumptionNodeId: children[1]!.id, conclusionNodeId: children[0]!.id },
    ] : undefined;
    const result: ReadingNode = { id: source.id, kind: source.kind, phrase, lean: source.lean, children, parentId: parent?.id, edgeFromParent: edge, binder, scopeId, context: scope?.context ?? [], assumptionNodeIds: scope?.assumptionNodeIds ?? [], relationIds: relations.map(relation => relation.id), objectIds: unique([...(scope?.objectIds ?? []), ...(coverage?.objectIds ?? []), ...relations.flatMap(relation => relation.ports.map(port => port.objectId))]), coverage: coverage?.status, panelId: panel?.id, directions };
    nodeIndex.set(source.id, result);
    return result;
  }

  const root = visit(document.tree);
  const nodes = sourceOrder.map(id => nodeIndex.get(id)!);
  const quantifierGroups: ReadingQuantifierGroup[] = [];
  const groupedNodes = new Set<string>();
  for (const node of nodes) {
    if (groupedNodes.has(node.id) || !['forall', 'exists', 'parameter'].includes(node.kind) || !node.binder) continue;
    const members: ReadingNode[] = [];
    let current = node;
    while (current.kind === node.kind && current.binder && !groupedNodes.has(current.id)) {
      members.push(current);
      groupedNodes.add(current.id);
      if (current.children.length !== 1 || current.children[0]!.kind !== node.kind || !current.children[0]!.binder) break;
      current = current.children[0]!;
    }
    const last = members.at(-1)!;
    quantifierGroups.push({ id: `reading-quantifiers:${node.id}`, kind: node.kind as ReadingQuantifierGroup['kind'], nodeIds: members.map(member => member.id), binders: members.map(member => member.binder!), bodyNodeId: last.children.length === 1 ? last.children[0]!.id : undefined, branchPath: branchPaths.get(node.id) ?? [] });
  }
  const selectedId = options.selectedNodeId ?? root.id;
  const selected = nodeIndex.get(selectedId);
  if (!selected) throw new Error(`Unknown reading selection node: ${selectedId}`);
  const descendantNodeIds: string[] = [];
  const collect = (node: ReadingNode): void => { descendantNodeIds.push(node.id); node.children.forEach(collect); };
  collect(selected);
  const descendants = new Set(descendantNodeIds);
  const ancestorNodeIds: string[] = [];
  let ancestorId = selected.parentId;
  while (ancestorId) { ancestorNodeIds.unshift(ancestorId); ancestorId = nodeIndex.get(ancestorId)?.parentId; }
  const selectedScope = scopes.get(selected.scopeId);
  const sequence: ReadingStep[] = nodes.map((node, index) => ({ id: `reading-step:${node.id}`, nodeId: node.id, kind: ['forall', 'exists', 'parameter'].includes(node.kind) ? 'binder' : node.children.length ? 'connective' : 'clause', ordinal: index + 1, ancestorNodeIds: (branchPaths.get(node.id) ?? []).map(position => position.nodeId), branchPath: branchPaths.get(node.id) ?? [], panelId: node.panelId }));
  return { schemaVersion: READING_DOCUMENT_VERSION, root, nodes, panels, quantifierGroups, sequence, selection: { nodeId: selectedId, descendantNodeIds, ancestorNodeIds, assumptionNodeIds: selected.assumptionNodeIds, scopeObjectIds: selectedScope?.objectIds ?? [], panelIds: panels.filter(panel => descendants.has(panel.nodeId)).map(panel => panel.id) }, diagnostics };
}
