import { describe, expect, it } from 'vitest';
import type { PlannedView, SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { layoutSemanticMap, MAP_LIMITS } from './layout';

const object = (id: string): SemanticObject => ({ id, label: id, kind: 'variable', type: 'ℝ', expression: { kind: 'const', name: id }, scopeId: 'root', provenance: [] });
const relation = (id: string, ids: string[]): SemanticRelation => ({ id, kind: 'equality', label: id, ports: ids.map((objectId, index) => ({ role: `argument ${index}`, objectId })), expression: { kind: 'const', name: id }, scopeId: 'root', nodeId: id, pluginId: 'test', fidelity: 'symbolic', provenance: { nodeId: id, expressionPath: id, origin: 'elaborated-expression' }, conditions: [] });
const document = (objects: SemanticObject[], relations: SemanticRelation[]): SemanticDocument => ({ schemaVersion: '1.0.0', prover: 'lean', source: '', tree: { id: 'root', kind: 'predicate', label: '', lean: '', children: [], expression: { kind: 'const', name: 'True' } }, objects, relations, scopes: [], choices: [], opaqueRegions: [], coverage: [], scenes: [], diagnostics: [] });
const view = (doc: SemanticDocument): PlannedView => ({ id: 'overview', kind: 'semantic-map', title: 'Overview', score: 1, reason: '', fidelity: 'structural', nodeIds: [], objectIds: doc.objects.map(item => item.id), relationIds: doc.relations.map(item => item.id), sceneIds: [], conditions: [] });

describe('bounded semantic map layout', () => {
  it('uses a single shared object with independently labeled connections', () => {
    const doc = document([object('x'), object('A'), object('B')], [relation('member', ['x', 'A']), relation('image', ['x', 'B'])]);
    const layout = layoutSemanticMap(doc, view(doc));
    expect(layout.objects.filter(node => node.object.id === 'x')).toHaveLength(1);
    expect(layout.edges.filter(edge => edge.objectId === 'x').map(edge => edge.relationId)).toEqual(['member', 'image']);
    expect(layout.edges.every(edge => layout.objects.some(node => node.object.id === edge.objectId) && layout.relations.some(node => node.relation.id === edge.relationId))).toBe(true);
  });

  it('keeps a selected object and its relation visible in a large statement', () => {
    const objects = Array.from({ length: 40 }, (_, index) => object(`x${index}`));
    const relations = Array.from({ length: 20 }, (_, index) => relation(`r${index}`, [`x${index * 2}`, `x${index * 2 + 1}`]));
    const doc = document(objects, relations);
    const layout = layoutSemanticMap(doc, view(doc), 'x39');
    expect(layout.objects.length).toBeLessThanOrEqual(MAP_LIMITS.objects);
    expect(layout.relations.length).toBeLessThanOrEqual(MAP_LIMITS.relations);
    expect(layout.objects.some(node => node.object.id === 'x39')).toBe(true);
    expect(layout.edges.some(edge => edge.objectId === 'x39' && edge.relationId === 'r19')).toBe(true);
    expect(layout.totalObjects).toBe(40);
    expect(layout.totalRelations).toBe(20);
  });

  it('does not invent objects for unresolved ports or edges beyond the object bound', () => {
    const objects = Array.from({ length: 20 }, (_, index) => object(`x${index}`));
    const doc = document(objects, [relation('many', [...objects.map(item => item.id), 'missing'])]);
    const layout = layoutSemanticMap(doc, view(doc));
    expect(layout.edges).toHaveLength(MAP_LIMITS.objects);
    expect(layout.relations[0].omittedPorts).toBe(9);
    expect(layout.objects.some(node => node.object.id === 'missing')).toBe(false);
  });

  it('keeps rectangles within the canvas and nonoverlapping in each column', () => {
    const objects = Array.from({ length: 12 }, (_, index) => object(`x${index}`));
    const doc = document(objects, Array.from({ length: 8 }, (_, index) => relation(`r${index}`, [`x${index}`, `x${index + 1}`])));
    const layout = layoutSemanticMap(doc, view(doc));
    for (const nodes of [layout.objects, layout.relations]) {
      nodes.forEach((node, index) => {
        expect(node.x).toBeGreaterThanOrEqual(0);
        expect(node.x + node.width).toBeLessThanOrEqual(layout.width);
        expect(node.y).toBeGreaterThanOrEqual(40);
        expect(node.y + node.height).toBeLessThanOrEqual(layout.height);
        if (index > 0) expect(node.y).toBeGreaterThan(nodes[index - 1].y + nodes[index - 1].height);
      });
    }
    expect(layoutSemanticMap(doc, view(doc))).toEqual(layout);
  });

  it('limits layout scope to the selected view and its relation endpoints', () => {
    const doc = document([object('x'), object('A'), object('outside')], [relation('inside', ['x', 'A']), relation('outsideRelation', ['outside'])]);
    const selected = { ...view(doc), objectIds: ['x'], relationIds: ['inside'] };
    const layout = layoutSemanticMap(doc, selected, 'outside');
    expect(layout.objects.map(node => node.object.id)).toEqual(['x', 'A']);
    expect(layout.relations.map(node => node.relation.id)).toEqual(['inside']);
    expect(layout.totalObjects).toBe(2);
  });
});
