import { describe, expect, it } from 'vitest';
import { discoverScenes } from './scenes';
import type { Binder, Expr, StatementNode } from './types';

const real: Expr = { kind: 'const', name: 'Real' };
const instance: Expr = { kind: 'opaque', text: 'standard instance' };
const point: Expr = { kind: 'var', id: 'x', name: 'x', type: 'ℝ' };
const value: Expr = { kind: 'literal', value: 1 };
const binder: Binder = { id: 'x', name: 'x', type: 'ℝ', role: 'universal', domain: 'real', dependsOn: [] };
const analyze = (expression: Expr) => {
  const leaf: StatementNode = { id: 'leaf', kind: 'predicate', label: '', lean: '', children: [], expression };
  return discoverScenes({ id: 'root', kind: 'forall', label: '', lean: '', binder, expression: { kind: 'forall', binder, body: expression }, children: [leaf] });
};
const application = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: { kind: 'const', name }, args, standard: true, ...extra });

describe('complete applications in numerical scene discovery', () => {
  it.each(['Metric.ball', 'Metric.closedBall', 'Metric.sphere'])('does not treat partial %s as a region', name => {
    const partial = application(name, [real, instance, point], { metric: 'real', dimension: 1, argumentKinds: ['type', 'instance', 'value'], typeDescriptor: { kind: 'map', lean: 'ℝ → Set ℝ' } });
    expect(analyze(partial)).toEqual([]);
    expect(analyze(application(name, [real, instance, point], { metric: 'real', dimension: 1 }))).toEqual([]);
    expect(analyze(application(name, [real, instance, point, value], { metric: 'real', dimension: 1, argumentKinds: ['type', 'instance', 'value', 'value'], typeDescriptor: { kind: 'set', lean: 'Set ℝ' } }))).toHaveLength(1);
    expect(analyze(application(name, [real, instance, point, value], { metric: 'real', dimension: 1 }))).toHaveLength(1);
  });

  it.each(['Eq', 'Ne', 'LT.lt', 'LE.le', 'GT.gt', 'GE.ge'])('does not treat partial %s as a scalar condition', name => {
    const prefix = name === 'Eq' || name === 'Ne' ? [real] : [real, instance];
    const kinds = prefix.map((_, index) => index === 0 ? 'type' as const : 'instance' as const);
    expect(analyze(application(name, [...prefix, point], { argumentKinds: [...kinds, 'value'], typeDescriptor: { kind: 'relation', lean: 'ℝ → Prop' } }))).toEqual([]);
    expect(analyze(application(name, [...prefix, point]))).toEqual([]);
    expect(analyze(application(name, [...prefix, point, value], { argumentKinds: [...kinds, 'value', 'value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } }))).toHaveLength(1);
  });

  it.each(['Function.Injective', 'Function.Surjective', 'Function.Bijective'])('does not treat partial %s type parameters as a mapped function', name => {
    expect(analyze(application(name, [real, real], { argumentKinds: ['type', 'type'], typeDescriptor: { kind: 'relation', lean: '(ℝ → ℝ) → Prop' } }))).toEqual([]);
    expect(analyze(application(name, [real, real]))).toEqual([]);
    expect(analyze(application(name, [real, real, { kind: 'var', id: 'f', name: 'f', type: 'ℝ → ℝ' }], { argumentKinds: ['type', 'type', 'value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } }))).toHaveLength(1);
  });

  it('does not attach a representative through partially applied membership', () => {
    const set = application('Metric.ball', [real, instance, point, value], { metric: 'real', dimension: 1 });
    const partial = application('Set.Mem', [real, set], { argumentKinds: ['type', 'value'], typeDescriptor: { kind: 'relation', lean: 'ℝ → Prop' } });
    const scene = analyze(partial)[0];
    expect(scene?.kind).toBe('ball');
    if (scene?.kind === 'ball') expect(scene.point).toBeUndefined();
  });

  it('checks the result type even when a value count appears complete', () => {
    const applicationToPoint = application('Metric.ball', [point, value], { metric: 'real', dimension: 1, argumentKinds: ['value', 'value'], typeDescriptor: { kind: 'map', lean: 'ℝ → Set ℝ' } });
    expect(analyze(applicationToPoint)).toEqual([]);
  });
});
