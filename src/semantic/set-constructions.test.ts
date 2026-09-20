import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from './compiler';
import { expressionKey, formatExpression, setConstructionParts } from './expression';

const c = (name: string): Expr => ({ kind: 'const', name });
const set = (id: string, name = id): Expr => ({ kind: 'var', id, name, type: 'Set X', typeDescriptor: { kind: 'set', lean: 'Set X', element: { kind: 'unknown', lean: 'X' } } });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: c(name), args, ...extra });
const construction = (name: string, operands: Expr[], standard = true): Expr => app(name, [app('Set', [c('X')]), { kind: 'opaque', text: `instance:${standard}` }, ...operands], { argumentKinds: ['type', 'instance', ...operands.map(() => 'value' as const)], standard, type: 'Set X', typeDescriptor: { kind: 'set', lean: 'Set X', element: { kind: 'unknown', lean: 'X' } } });
const compile = (expression: Expr) => { const tree: StatementNode = { id: 'clause', kind: 'predicate', lean: 'source', label: 'source', expression, children: [] }; return compileSemanticDocument({ source: 'source', tree, expression }); };

describe('audited compositional set semantics', () => {
  it('recognizes all four standard set constructors with ordered operand and result identities', () => {
    const expression = construction('Inter.inter', [construction('Union.union', [set('a'), set('b')]), construction('SDiff.sdiff', [set('a'), construction('Compl.compl', [set('c')])])]);
    const document = compile(expression);
    expect(document.relations.map(relation => relation.setOperation)).toEqual(['intersection', 'union', 'difference', 'complement']);
    expect(document.opaqueRegions).toHaveLength(0);
    expect(document.relations.every(relation => relation.ports.at(-1)?.role === 'result')).toBe(true);
    const union = document.relations.find(relation => relation.setOperation === 'union')!;
    const difference = document.relations.find(relation => relation.setOperation === 'difference')!;
    expect(union.ports[0].objectId).toBe(difference.ports[0].objectId);
    expect(formatExpression(expression)).toBe('((a ∪ b) ∩ (a ∖ cᶜ))');
  });

  it('keeps custom instances structural and includes their exact instances in identity', () => {
    const standard = construction('Union.union', [set('a'), set('b')]);
    const custom = construction('Union.union', [set('a'), set('b')], false);
    expect(setConstructionParts(custom)).toBeUndefined();
    expect(expressionKey(standard)).not.toBe(expressionKey(custom));
    expect(compile(custom).relations.some(relation => relation.kind === 'set-construction')).toBe(false);
    expect(compile(custom).opaqueRegions).toHaveLength(1);
    expect(formatExpression(custom)).toContain('Union.union(');
  });

  it('rejects partial, overapplied, non-set and unaudited overloaded applications', () => {
    const base = construction('Union.union', [set('a'), set('b')]) as Extract<Expr, { kind: 'app' }>;
    const nearMisses: Expr[] = [construction('Union.union', [set('a')]), construction('Union.union', [set('a'), set('b'), set('c')]), { ...base, typeDescriptor: { kind: 'map', lean: 'Set X → Set X' } }, { ...base, typeDescriptor: { kind: 'structure', lean: 'Finset X' } }, { ...base, standard: undefined }, { ...base, argumentKinds: ['type', 'value'] }];
    expect(nearMisses.every(expression => setConstructionParts(expression) === undefined)).toBe(true);
    expect(setConstructionParts(app('Set.union', [set('a'), set('b')]))?.operation).toBe('union');
    expect(setConstructionParts(app('Set.compl', []))).toBeUndefined();
  });

  it('preserves constructed objects as the operands of membership, inclusion and equality', () => {
    const built = construction('SDiff.sdiff', [set('a'), set('b')]);
    for (const expression of [app('Set.Mem', [built, c('x')]), app('Set.Subset', [built, set('c')]), app('Eq', [built, set('c')])]) {
      const document = compile(expression);
      const constructor = document.relations.find(relation => relation.kind === 'set-construction')!;
      const result = constructor.ports.find(port => port.role === 'result')!.objectId;
      expect(document.relations[0].ports.some(port => port.objectId === result)).toBe(true);
      expect(document.objects.find(object => object.id === result)?.kind).toBe('set');
    }
  });

  it('never identifies same-named distinct set binders or reverses difference operands', () => {
    const left = construction('SDiff.sdiff', [set('left', 'A'), set('right', 'A')]);
    const right = construction('SDiff.sdiff', [set('right', 'A'), set('left', 'A')]);
    expect(expressionKey(left)).not.toBe(expressionKey(right));
    const ports = compile(left).relations[0].ports;
    expect(ports[0].objectId).not.toBe(ports[1].objectId);
  });

  it('keeps nested expression identity linear in its structure instead of repeatedly escaping child keys', () => {
    let expression = set('A');
    for (let index = 0; index < 80; index++) expression = app('Set.compl', [expression]);
    const key = expressionKey(expression);
    expect(key.length).toBeLessThan(10_000);
    expect(key).not.toContain('\\\\');
    expect(expressionKey(app('Set.compl', [expression]))).not.toBe(key);
  });
});
