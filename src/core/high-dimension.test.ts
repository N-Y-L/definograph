import { describe, expect, it } from 'vitest';
import { ballGeometry, discoverScenes, evaluateExpression, initialScenario, metricDistance, sliceGeometry, updateScenario } from './index';
import { MAX_NUMERICAL_DIMENSION } from './limits';
import { distanceProfile } from '../visual/distance-profile';
import type { BallScene, Binder, Expr, StatementNode } from './types';

const point = (id: string, dimension: number): Binder => ({ id, name: id, role: 'universal', type: `EuclideanSpace ℝ (Fin ${dimension})`, domain: 'euclideanN', dimension, dependsOn: [] });
const variable = (binder: Binder): Expr => ({ kind: 'var', id: binder.id, name: binder.name, type: binder.type });
function statement(dimension: number): StatementNode {
  const binder = point('p', dimension);
  const center: Expr = { kind: 'app', fn: { kind: 'const', name: 'OfNat.ofNat' }, args: [{ kind: 'const', name: binder.type }, { kind: 'literal', value: 0 }, { kind: 'opaque', text: 'standard zero' }], standard: true, domain: 'euclideanN', dimension };
  const set: Expr = { kind: 'app', fn: { kind: 'const', name: 'Metric.ball' }, args: [center, { kind: 'literal', value: 5 }], argumentKinds: ['value', 'value'], metric: 'euclideanN', dimension };
  const membership: Expr = { kind: 'app', fn: { kind: 'const', name: 'Set.Mem' }, args: [set, variable(binder)], argumentKinds: ['value', 'value'] };
  const leaf: StatementNode = { id: 'membership', kind: 'predicate', label: '', lean: '', children: [], expression: membership };
  return { id: 'root', kind: 'forall', label: '', lean: '', binder, children: [leaf], expression: { kind: 'forall', binder, body: membership } };
}

describe('bounded high-dimensional numerical views', () => {
  it.each([21, MAX_NUMERICAL_DIMENSION])('uses the final coordinate of a %iD point in distance, slice, and profile', dimension => {
    const tree = statement(dimension);
    const scene = discoverScenes(tree)[0] as BallScene;
    expect(scene).toMatchObject({ kind: 'ball', dimension });
    const initial = initialScenario(tree);
    expect(initial.p).toHaveLength(dimension);
    const value = Array(dimension).fill(0);
    value[0] = 4;
    value[dimension - 1] = 3;
    const scenario = updateScenario(tree, initial, 'p', value);
    expect(ballGeometry(scene, scenario)).toMatchObject({ status: 'geometry', membership: { status: 'false' } });
    expect(metricDistance('euclideanN', value, Array(dimension).fill(0), dimension)).toBe(5);
    expect(metricDistance('supN', value, Array(dimension).fill(0), dimension)).toBe(4);
    const fixed = Array(dimension).fill(0);
    fixed[dimension - 1] = 3;
    expect(sliceGeometry(scene, scenario, { fixed })).toMatchObject({ status: 'geometry', radius: 4, pointInSlice: true });
    const profile = distanceProfile(scene, scenario);
    expect(profile).toMatchObject({ status: 'profile', distance: 5, dimension });
    if (profile.status === 'profile') {
      expect(profile.absoluteDisplacements).toHaveLength(dimension);
      expect(profile.absoluteDisplacements[dimension - 1]).toBe(3);
    }
  });

  it('keeps dimensions above the numerical cap symbolic before allocating controls', () => {
    const dimension = MAX_NUMERICAL_DIMENSION + 1;
    const tree = statement(dimension);
    expect(initialScenario(tree)).toEqual({});
    expect(discoverScenes(tree)).toEqual([]);
    expect(evaluateExpression(variable(tree.binder!), { p: Array(dimension).fill(0) }).status).toBe('unknown');
    expect(updateScenario(tree, {}, 'p', Array(dimension).fill(0))).toEqual({});
    expect(metricDistance('euclideanN', Array(dimension).fill(0), Array(dimension).fill(0), dimension)).toBeUndefined();
  });

  it('measures a point outside the displayed slice without pretending it belongs to the slice', () => {
    const tree = statement(21);
    const scene = discoverScenes(tree)[0] as BallScene;
    const value = Array(21).fill(0);
    value[20] = 3;
    expect(sliceGeometry(scene, { p: value })).toMatchObject({ pointInSlice: false });
    expect(distanceProfile(scene, { p: value })).toMatchObject({ status: 'profile', distance: 3, membership: { status: 'true' } });
  });
});
