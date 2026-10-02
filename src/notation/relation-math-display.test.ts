import { describe, expect, it } from 'vitest';
import type { Expr } from '../core';
import type { SemanticObject, SemanticRelation } from '../semantic';
import { relationObjectMathDisplay } from './relation-math-display';

const variable = (name: string): Expr => ({ kind: 'var', id: name, name, type: 'X' });
const object = (id: string, expression: Expr): SemanticObject => ({ id, expression, label: id, type: 'X', kind: 'expression', scopeId: 'scope', provenance: [] });
function fixture(head: string, distance = false) {
  const expression: Expr = { kind: 'app', fn: { kind: 'const', name: head, canonical: true }, args: [{ kind: 'opaque', text: 'exact implicit metric instance' }, variable('x'), variable('δ')], argumentKinds: ['instance', 'value', 'value'] };
  const output = object('exact-output', expression), x = object('x', variable('x')), radius = object('radius', variable('δ'));
  const relation: SemanticRelation = { id: 'producer', kind: distance ? 'distance' : 'metric-region', expression, label: head, nodeId: 'clause', scopeId: 'scope', pluginId: 'metric', fidelity: 'symbolic', provenance: { nodeId: 'clause', expressionPath: 'expression', origin: 'elaborated-expression' }, conditions: [], ports: [{ role: distance ? 'distance' : 'region', objectId: output.id }, { role: distance ? 'from' : 'center', objectId: x.id }, { role: distance ? 'to' : 'radius', objectId: radius.id }] };
  return { output, relation, objects: new Map([output, x, radius].map(value => [value.id, value])) };
}

describe('admitted output mathematical display', () => {
  it('typesets the actual constructor and role expressions when implicit instance syntax is opaque', () => {
    for (const head of ['Metric.ball', 'Metric.closedBall', 'Metric.sphere', 'dist']) {
      const { output, relation, objects } = fixture(head, head === 'dist');
      const before = JSON.stringify({ output, relation });
      const display = relationObjectMathDisplay(output, [relation], objects);
      expect(display.latex).toContain(head === 'dist' ? '\\text{dist}' : `\\text{${head}}`);
      expect(display.latex).toContain('x,\\,\\delta');
      expect(display.source).toBe(output.label);
      expect(JSON.stringify({ output, relation })).toBe(before);
    }
  });

  it('refuses missing output associations, unavailable arguments, unknown producers, and noncanonical heads', () => {
    const { output, relation, objects } = fixture('Metric.ball');
    const wrong = { ...relation, ports: relation.ports.map(port => port.role === 'region' ? { ...port, objectId: 'other-result' } : port) };
    const unknown = { ...relation, kind: 'predicate' as const };
    const noncanonical = { ...relation, expression: { ...relation.expression, kind: 'app' as const, fn: { kind: 'const' as const, name: 'Metric.ball', canonical: false }, args: [] } };
    const mismatched = { ...relation, expression: { ...relation.expression, kind: 'app' as const, fn: { kind: 'const' as const, name: 'Metric.closedBall', canonical: true }, args: [] } };
    const repeatedRole = { ...relation, ports: [...relation.ports, relation.ports[1]] };
    const repeatedOutput = { ...relation, ports: [...relation.ports, relation.ports[0]] };
    for (const relations of [[], [wrong], [unknown], [noncanonical], [mismatched], [repeatedRole], [repeatedOutput], [relation, relation]]) expect(relationObjectMathDisplay(output, relations, objects).latex).toBeUndefined();
    const missing = new Map(objects); missing.delete('radius');
    expect(relationObjectMathDisplay(output, [relation], missing).latex).toBeUndefined();
    const opaque = new Map(objects); opaque.set('radius', object('radius', { kind: 'opaque', text: 'unavailable exact role' }));
    expect(relationObjectMathDisplay(output, [relation], opaque).latex).toBeUndefined();
  });
});
