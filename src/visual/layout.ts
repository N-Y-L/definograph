import type { PlannedView, SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';

export const MAP_LIMITS = { objects: 12, relations: 8 } as const;
export interface ObjectNode { object: SemanticObject; x: number; y: number; width: number; height: number }
export interface RelationNode { relation: SemanticRelation; x: number; y: number; width: number; height: number; omittedPorts: number }
export interface RelationEdge { id: string; objectId: string; relationId: string; role: string; path: string }
export interface SemanticLayout {
  width: number;
  height: number;
  objects: ObjectNode[];
  relations: RelationNode[];
  edges: RelationEdge[];
  totalObjects: number;
  totalRelations: number;
}

/** A stable bipartite layout. Every displayed edge has two displayed endpoints. */
export function layoutSemanticMap(document: SemanticDocument, view: PlannedView, selectedObjectId?: string): SemanticLayout {
  const objectById = new Map(document.objects.map(object => [object.id, object]));
  const wantedRelations = new Set(view.relationIds);
  const allRelations = document.relations.filter(relation => wantedRelations.has(relation.id));
  const wantedObjects = new Set(view.objectIds.filter(id => objectById.has(id)));
  allRelations.forEach(relation => relation.ports.forEach(port => { if (objectById.has(port.objectId)) wantedObjects.add(port.objectId); }));
  const relationOrder = [...allRelations].sort((a, b) => Number(b.ports.some(p => p.objectId === selectedObjectId)) - Number(a.ports.some(p => p.objectId === selectedObjectId)));
  const relations = relationOrder.slice(0, MAP_LIMITS.relations);
  const orderedObjectIds = new Set<string>();
  if (selectedObjectId && wantedObjects.has(selectedObjectId)) orderedObjectIds.add(selectedObjectId);
  relations.forEach(relation => relation.ports.forEach(port => { if (objectById.has(port.objectId)) orderedObjectIds.add(port.objectId); }));
  wantedObjects.forEach(id => orderedObjectIds.add(id));
  const objectIds = [...orderedObjectIds].slice(0, MAP_LIMITS.objects);
  const objectIndex = new Map(objectIds.map((id, index) => [id, index]));
  const meanEndpoint = (relation: SemanticRelation) => {
    const indices = relation.ports.flatMap(port => objectIndex.has(port.objectId) ? [objectIndex.get(port.objectId)!] : []);
    return indices.length ? indices.reduce((sum, index) => sum + index, 0) / indices.length : Infinity;
  };
  relations.sort((a, b) => meanEndpoint(a) - meanEndpoint(b));
  const rowCount = Math.max(objectIds.length, relations.length, 1);
  const height = Math.max(260, 100 + rowCount * 88);
  const availableHeight = height - 100;
  const position = (index: number, count: number) => 64 + (index + 0.5) * availableHeight / Math.max(count, 1) - 32;
  const objectNodes = objectIds.map((id, index) => ({ object: objectById.get(id)!, x: 24, y: position(index, objectIds.length), width: 284, height: 64 }));
  const relationNodes = relations.map((relation, index) => ({ relation, x: 482, y: position(index, relations.length), width: 310, height: 64, omittedPorts: relation.ports.filter(port => !objectIndex.has(port.objectId)).length }));
  const positionedObjects = new Map(objectNodes.map(node => [node.object.id, node]));
  const edges = relationNodes.flatMap(node => node.relation.ports.flatMap((port, portIndex) => {
    const objectNode = positionedObjects.get(port.objectId);
    if (!objectNode) return [];
    const x1 = objectNode.x + objectNode.width;
    const y1 = objectNode.y + objectNode.height / 2;
    const y2 = node.y + 12 + (portIndex + 0.5) * 40 / Math.max(node.relation.ports.length, 1);
    return [{ id: `${node.relation.id}:${portIndex}`, objectId: port.objectId, relationId: node.relation.id, role: port.role, path: `M ${x1} ${y1} C ${x1 + 74} ${y1}, ${node.x - 74} ${y2}, ${node.x} ${y2}` }];
  }));
  return { width: 816, height, objects: objectNodes, relations: relationNodes, edges, totalObjects: wantedObjects.size, totalRelations: allRelations.length };
}

export function compactLabel(value: string, maximum = 32): string {
  const text = value.replace(/\s+/g, ' ').trim();
  return text.length > maximum ? `${text.slice(0, maximum - 1)}…` : text;
}
