import { describe, expect, it } from 'vitest';
import type { ReadingDocument, ReadingNode } from './types';
import { planReadingPresentation, visibleReadingNodes, type ReadingRegion } from './presentation';

const node = (id: string, kind: ReadingNode['kind'], children: ReadingNode[] = []): ReadingNode => ({ id, kind, phrase: id, lean: id, children, scopeId: id, context: [], assumptionNodeIds: [], relationIds: [], objectIds: [], ...(['forall', 'exists', 'parameter'].includes(kind) ? { binder: { binderId: id, name: id, type: 'X', role: kind === 'exists' ? 'existential' as const : kind === 'parameter' ? 'parameter' as const : 'universal' as const, dependsOn: [], scopeId: id } } : {}) });
const present = (root: ReadingNode) => planReadingPresentation({ root } as ReadingDocument);
const children = (region: ReadingRegion): ReadingRegion[] => region.kind === 'binders' ? region.body ? [region.body] : [] : region.kind === 'implication' ? [...region.assumptions, region.conclusion] : region.kind === 'negation' ? [region.body] : region.kind === 'clause' ? [] : [...region.children];
const sourceIds = (region: ReadingRegion): string[] => [...region.sourceNodeIds, ...children(region).flatMap(sourceIds)];

describe('mathematical reading regions', () => {
  it('combines direct implication chains without losing any source node', () => {
    const p = present(node('first', 'implies', [node('A', 'predicate'), node('second', 'implies', [node('B', 'predicate'), node('C', 'predicate')])]));
    expect(p.root.kind).toBe('implication');
    if (p.root.kind === 'implication') {
      expect(p.root.assumptions.map(region => region.id)).toEqual(['A', 'B']);
      expect(p.root.conclusion.id).toBe('C');
    }
    expect(p.nodeToRegionId.second).toBe('first');
    expect(sourceIds(p.root).sort()).toEqual(['A', 'B', 'C', 'first', 'second']);
  });

  it('does not move a quantifier across a premise to merge implications', () => {
    const p = present(node('if', 'implies', [node('P', 'predicate'), node('x', 'forall', [node('inner', 'implies', [node('Q', 'predicate'), node('R', 'predicate')])])]));
    expect(p.root.kind).toBe('implication');
    if (p.root.kind === 'implication') {
      expect(p.root.assumptions).toHaveLength(1);
      expect(p.root.conclusion.kind).toBe('binders');
      if (p.root.conclusion.kind === 'binders') expect(p.root.conclusion.body?.kind).toBe('implication');
    }
  });

  it('groups only adjacent binders of the same role and keeps their order', () => {
    const p = present(node('a', 'forall', [node('b', 'forall', [node('witness', 'exists', [node('later', 'forall', [node('body', 'predicate')])])])]));
    expect(p.root.kind).toBe('binders');
    if (p.root.kind === 'binders') {
      expect(p.root.binders.map(binder => binder.id)).toEqual(['a', 'b']);
      expect(p.root.body?.id).toBe('witness');
    }
    expect(Object.keys(p.nodeToRegionId).sort()).toEqual(['a', 'b', 'body', 'later', 'witness']);
  });

  it('keeps all, alternatives, equivalence, and negation as distinct scope envelopes', () => {
    const p = present(node('all', 'and', [node('alternatives', 'or', [node('not', 'not', [node('p', 'predicate')]), node('q', 'predicate')]), node('iff', 'iff', [node('r', 'predicate'), node('s', 'predicate')])]));
    expect(p.root.kind).toBe('all');
    if (p.root.kind === 'all') {
      expect(p.root.children.map(region => region.kind)).toEqual(['alternatives', 'equivalence']);
      if (p.root.children[0].kind === 'alternatives') expect(p.root.children[0].children[0].kind).toBe('negation');
    }
    expect(new Set(sourceIds(p.root)).size).toBe(8);
  });

  it('keeps the complete enclosing path when a selected clause exceeds the ordinary display limit', () => {
    const ancestors = Array.from({ length: 120 }, (_, index) => `negation-${index}`);
    const reading = { nodes: [...ancestors.map(id => node(id, 'not')), node('clause', 'predicate')], selection: { nodeId: 'clause', ancestorNodeIds: ancestors, descendantNodeIds: [], assumptionNodeIds: [] } } as unknown as ReadingDocument;
    const visible = visibleReadingNodes(reading, 100);
    expect(visible.size).toBe(121);
    expect(visible.has('clause')).toBe(true);
    expect(ancestors.every(id => visible.has(id))).toBe(true);
  });
});
