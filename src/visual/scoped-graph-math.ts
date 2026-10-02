import { relationObjectMathDisplay } from '../notation/relation-math-display';
import type { MathDisplay } from '../notation/math-display';
import type { ScopedClauseGraph, ScopedGraphNode } from '../reading/scoped-graph';

/** Use the same admitted-output display templates as the guided relation view.
 * Only objects and relations in this exact clause graph are available. */
export function scopedGraphMathDisplay(node: ScopedGraphNode, graph: ScopedClauseGraph): MathDisplay | undefined {
  if (!node.object) return;
  const objects = new Map(graph.nodes.flatMap(candidate => candidate.object ? [[candidate.object.id, candidate.object] as const] : []));
  const relations = graph.nodes.flatMap(candidate => candidate.relation ? [candidate.relation] : []);
  return relationObjectMathDisplay(node.object, relations, objects);
}
