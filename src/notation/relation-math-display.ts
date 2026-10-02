import type { SemanticObject, SemanticRelation } from '../semantic/types';
import { applicationParts, expressionKey } from '../semantic/expression';
import { expressionDisplayNode, expressionMathDisplay, mathDisplay, type MathDisplay, type MathDisplayNode } from './math-display';

/** Display templates for outputs of already admitted operations. The caller
 * supplies its current clause/group relations; these labels add no recognition. */
export function relationObjectMathDisplay(object: SemanticObject, relations: readonly SemanticRelation[], objects: ReadonlyMap<string, SemanticObject>): MathDisplay {
  const exact = expressionMathDisplay(object.expression, object.label);
  if (exact.latex) return exact;
  const producers = relations.filter(relation => relation.ports.some(port => port.objectId === object.id
    && (relation.kind === 'metric-region' && port.role === 'region' || relation.kind === 'distance' && port.role === 'distance')));
  if (producers.length !== 1) return exact;
  const producer = producers[0], outputRole = producer.kind === 'metric-region' ? 'region' : 'distance';
  if (producer.ports.filter(port => port.role === outputRole).length !== 1) return exact;
  if (expressionKey(producer.expression) !== expressionKey(object.expression)) return exact;
  const roles = producer.kind === 'metric-region' ? ['center', 'radius'] : ['from', 'to'];
  const head = applicationParts(producer.expression).fn;
  // Preserve the actual admitted constructor, including ball/closedBall/sphere.
  if (head.kind !== 'const' || head.canonical === false) return exact;
  const args: MathDisplayNode[] = [];
  for (const role of roles) {
    const ports = producer.ports.filter(port => port.role === role);
    if (ports.length !== 1) return exact;
    const id = ports[0].objectId;
    const argument = id && objects.get(id);
    const node = argument && expressionDisplayNode(argument.expression);
    if (!node) return exact;
    args.push(node);
  }
  return mathDisplay({ kind: 'application', fn: { kind: 'identifier', name: head.name }, args }, object.label);
}
