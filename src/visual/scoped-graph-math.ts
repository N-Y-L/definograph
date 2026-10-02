import { applicationParts } from '../semantic/expression';
import { expressionDisplayNode, expressionMathDisplay, mathDisplay, type MathDisplay, type MathDisplayNode } from '../notation/math-display';
import type { ScopedClauseGraph, ScopedGraphNode } from '../reading/scoped-graph';

/** A display template only for outputs of already admitted operations. Roles
 * are supplied by the semantic relation; source expressions remain unchanged. */
export function scopedGraphMathDisplay(node: ScopedGraphNode, graph: ScopedClauseGraph): MathDisplay | undefined {
  if (!node.object) return;
  const exact = expressionMathDisplay(node.object.expression, node.object.label);
  if (exact.latex) return exact;
  const producer = graph.nodes.find(candidate => candidate.relation && candidate.ports.some(port => port.output && port.objectId === node.object!.id))?.relation;
  const template = producer?.kind === 'metric-region' ? { roles: ['center', 'radius'] }
    : producer?.kind === 'distance' ? { roles: ['from', 'to'] } : undefined;
  if (!template || !producer) return exact;
  const head = applicationParts(producer.expression).fn;
  // A relation kind alone cannot distinguish an open ball, closed ball, or
  // sphere. Retain the admitted operation's actual constructor identifier.
  if (head.kind !== 'const' || head.canonical === false) return exact;
  const arguments_: MathDisplayNode[] = [];
  for (const role of template.roles) {
    const id = producer.ports.find(port => port.role === role)?.objectId;
    const object = graph.nodes.find(candidate => candidate.object?.id === id)?.object;
    const argument = object && expressionDisplayNode(object.expression);
    if (!argument) return exact;
    arguments_.push(argument);
  }
  return mathDisplay({ kind: 'application', fn: { kind: 'identifier', name: head.name }, args: arguments_ }, node.object.label);
}
