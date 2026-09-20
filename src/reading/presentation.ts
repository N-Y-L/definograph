import type { ReadingDocument, ReadingNode } from './types';

interface RegionBase { readonly id: string; readonly sourceNodeIds: readonly string[]; readonly node: ReadingNode }
export type ReadingRegion =
  | RegionBase & { readonly kind: 'binders'; readonly binders: readonly ReadingNode[]; readonly body?: ReadingRegion }
  | RegionBase & { readonly kind: 'implication'; readonly assumptions: readonly ReadingRegion[]; readonly conclusion: ReadingRegion }
  | RegionBase & { readonly kind: 'all' | 'alternatives' | 'equivalence' | 'structure'; readonly children: readonly ReadingRegion[] }
  | RegionBase & { readonly kind: 'negation'; readonly body: ReadingRegion }
  | RegionBase & { readonly kind: 'clause' };

export interface ReadingPresentation {
  readonly root: ReadingRegion;
  /** Source IDs survive grouping; selection and source navigation never depend on labels. */
  readonly nodeToRegionId: Readonly<Record<string, string>>;
}

/** A selected fragment remains connected to every enclosing logical region. */
export function visibleReadingNodes(reading: ReadingDocument, limit: number): Set<string> {
  const protectedIds = new Set([reading.selection.nodeId, ...reading.selection.ancestorNodeIds, ...reading.selection.assumptionNodeIds]);
  const candidates = [...new Set([...reading.selection.descendantNodeIds, ...reading.nodes.map(node => node.id)])].filter(id => !protectedIds.has(id));
  return new Set([...protectedIds, ...candidates.slice(0, Math.max(0, limit - protectedIds.size))]);
}

/** Layout grouping only. Quantifiers never cross a connective, and implication
 * premises combine only along an uninterrupted right-associated chain. */
export function planReadingPresentation(reading: ReadingDocument): ReadingPresentation {
  const nodeToRegionId: Record<string, string> = {};
  const register = <T extends ReadingRegion>(region: T): T => {
    region.sourceNodeIds.forEach(id => { nodeToRegionId[id] = region.id; });
    return region;
  };
  const visit = (node: ReadingNode): ReadingRegion => {
    if (['forall', 'exists', 'parameter'].includes(node.kind) && node.binder) {
      const binders = [node];
      let final = node;
      while (final.children.length === 1 && final.children[0].kind === node.kind && final.children[0].binder) {
        final = final.children[0];
        binders.push(final);
      }
      return register({ id: node.id, node, kind: 'binders', sourceNodeIds: binders.map(binder => binder.id), binders, body: final.children[0] ? visit(final.children[0]) : undefined });
    }
    if (node.kind === 'implies' && node.children.length === 2) {
      const sources = [node.id];
      const assumptions = [visit(node.children[0])];
      let conclusion = node.children[1];
      while (conclusion.kind === 'implies' && conclusion.children.length === 2) {
        sources.push(conclusion.id);
        assumptions.push(visit(conclusion.children[0]));
        conclusion = conclusion.children[1];
      }
      return register({ id: node.id, node, kind: 'implication', sourceNodeIds: sources, assumptions, conclusion: visit(conclusion) });
    }
    if (node.kind === 'not' && node.children.length === 1) return register({ id: node.id, node, kind: 'negation', sourceNodeIds: [node.id], body: visit(node.children[0]) });
    if (node.children.length) return register({ id: node.id, node, kind: node.kind === 'and' ? 'all' : node.kind === 'or' ? 'alternatives' : node.kind === 'iff' ? 'equivalence' : 'structure', sourceNodeIds: [node.id], children: node.children.map(visit) });
    return register({ id: node.id, node, kind: 'clause', sourceNodeIds: [node.id] });
  };
  return { root: visit(reading.root), nodeToRegionId };
}
