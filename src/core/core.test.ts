import { describe, expect, it } from 'vitest';
import { ballGeometry, collectBinders, compareNumbers, discoverScenes, evaluateExpression, evaluatePredicate, initialScenario, sampleGraph, scenesForNode, sliceGeometry, updateScenario } from './index';
import type { BallScene, Binder, Expr, GraphScene, StatementNode } from './types';

const cn = (name: string): Expr => ({ kind: 'const', name });
const lit = (value: number): Expr => ({ kind: 'literal', value });
const vr = (id: string): Expr => ({ kind: 'var', id, name: id, type: 'ℝ' });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: cn(name), args, standard: true, type: 'ℝ', domain: 'real', ...extra });
const binder = (id: string, role: Binder['role'] = 'universal', dependsOn: string[] = []): Binder => ({ id, name: id, type: 'ℝ', role, domain: 'real', dependsOn });
const leaf = (id: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean: id, children: [], expression });
const quantified = (b: Binder, child: StatementNode): StatementNode => ({ id: `q-${b.id}`, kind: b.role === 'existential' ? 'exists' : 'forall', label: b.name, lean: b.name, binder: b, children: [child], expression: { kind: 'forall', binder: b, body: child.expression } });
const ball = (metric: BallScene['metric'] = 'euclidean2', dimension = 2, boundary: BallScene['boundary'] = 'open'): BallScene => ({ id: 'ball', nodeId: 'n', title: 'Ball', expression: cn('Metric.ball'), scope: [], guards: [], context: [], kind: 'ball', metric, dimension, center: vr('c'), radius: vr('r'), point: vr('p'), boundary });

describe('audited expression evaluation', () => {
  it('evaluates an actual beta application, not the display label', () => {
    const fn: Expr = { kind: 'lambda', binder: binder('x', 'lambda'), body: app('HMul.hMul', [vr('x'), vr('x')]) };
    expect(evaluateExpression({ kind: 'app', fn, args: [lit(3)] })).toMatchObject({ status: 'value', value: 9 });
  });
  it('does not trust a familiar operation with an unvalidated instance', () => {
    expect(evaluateExpression(app('HAdd.hAdd', [lit(1), lit(2)], { standard: false })).status).toBe('unknown');
  });
  it('does not apply real subtraction to natural-number subtraction', () => {
    expect(evaluateExpression(app('HSub.hSub', [lit(1), lit(2)], { type: 'ℕ', domain: 'unknown' })).status).toBe('unknown');
  });
  it('respects Lean totalized real division at zero', () => {
    expect(evaluateExpression(app('HDiv.hDiv', [lit(7), lit(0)]))).toMatchObject({ status: 'value', value: 0 });
  });
  it('reads the numeral argument, not the typeclass instance argument', () => {
    expect(evaluateExpression(app('OfNat.ofNat', [cn('Real'), lit(7), { kind: 'opaque', text: 'instance' }]))).toMatchObject({ status: 'value', value: 7 });
  });
  it('does not treat modular Fin or custom numerals as real numbers', () => {
    const expr = app('OfNat.ofNat', [app('Fin', [lit(5)]), lit(7), { kind: 'opaque', text: 'Fin.instOfNat' }], { type: 'Fin 5', domain: 'unknown' });
    expect(evaluateExpression(expr).status).toBe('unknown');
    expect(evaluateExpression(app('OfNat.ofNat', [cn('Nat'), lit(7), cn('NatInstance')], { type: 'ℕ', domain: 'unknown' }))).toMatchObject({ status: 'value', value: 7 });
  });
  it('rejects unimplemented real powers and overflow', () => {
    expect(evaluateExpression(app('HPow.hPow', [lit(2), lit(0.5)])).status).toBe('unknown');
    expect(evaluateExpression(app('HMul.hMul', [lit(1e308), lit(1e308)])).status).toBe('unknown');
  });
  it('does not collapse distinct large Lean integer literals into a true equality', () => {
    const left: Expr = { kind: 'literal', value: '9007199254740992' };
    const right: Expr = { kind: 'literal', value: '9007199254740993' };
    expect(evaluatePredicate(app('Eq', [left, right])).status).toBe('unknown');
  });
  it('uses the validated max metric rather than Euclidean distance', () => {
    const expr = app('Dist.dist', [vr('a'), vr('b')], { metric: 'sup2', dimension: 2 });
    expect(evaluateExpression(expr, { a: [0, 0], b: [3, 4] })).toMatchObject({ status: 'value', value: 4 });
  });
  it('refuses distances with unknown metrics or mismatched dimensions', () => {
    expect(evaluateExpression(app('Dist.dist', [vr('a'), vr('b')], { metric: 'unknown' }), { a: [0, 0], b: [1, 1] }).status).toBe('unknown');
    expect(evaluateExpression(app('Dist.dist', [vr('a'), vr('b')], { metric: 'euclidean2' }), { a: [0, 0], b: [1, 1, 1] }).status).toBe('unknown');
  });
  it('projects both product coordinates correctly', () => {
    expect(evaluateExpression(app('Prod.snd', [vr('p')]), { p: [2, 7] })).toMatchObject({ status: 'value', value: 7 });
  });
  it('does not execute strings or arbitrary functions', () => {
    expect(evaluateExpression({ kind: 'literal', value: 'process.exit()' }).status).toBe('unknown');
    expect(evaluateExpression({ kind: 'app', fn: vr('f'), args: [lit(2)] }).status).toBe('unknown');
  });
});

describe('sample predicates', () => {
  it('interprets GT and GE in their actual argument order', () => {
    expect(evaluatePredicate(app('GT.gt', [lit(2), lit(1)])).status).toBe('true');
    expect(evaluatePredicate(app('GE.ge', [lit(0), lit(1)])).status).toBe('false');
  });
  it('keeps a strict boundary strict and flags numerically ambiguous near misses', () => {
    expect(compareNumbers(1, 1, 'lt').status).toBe('false');
    expect(compareNumbers(1, 1, 'le').status).toBe('true');
    expect(compareNumbers(1 + Number.EPSILON, 1, 'lt').status).toBe('unknown');
  });
  it('does not turn a successful sample into a quantified statement', () => {
    const q = quantified(binder('x'), leaf('p', app('Eq', [vr('x'), vr('x')])));
    expect(evaluatePredicate(q, { x: 1 }).status).toBe('unknown');
    expect(evaluatePredicate(q.expression, { x: 1 }).status).toBe('unknown');
  });
  it('preserves vacuous implication semantics for a false premise', () => {
    const node: StatementNode = { id: 'imp', kind: 'implies', label: '', lean: '', expression: cn('unused'), children: [leaf('a', cn('False')), leaf('b', cn('False'))] };
    expect(evaluatePredicate(node).status).toBe('true');
  });
  it('keeps the negated predicate explanation consistent with its status', () => {
    expect(evaluatePredicate(app('Not', [app('Eq', [lit(1), lit(1)])]))).toMatchObject({ status: 'false', explanation: expect.stringContaining('does not hold') });
  });
  it('uses Membership.mem set-before-point order from Lean', () => {
    const set = app('Metric.ball', [vr('c'), lit(1)], { metric: 'sup2', dimension: 2 });
    expect(evaluatePredicate(app('Membership.mem', [set, vr('p')]), { c: [0, 0], p: [0.9, 0.9] }).status).toBe('true');
  });
});

describe('quantifier scope and scenario state', () => {
  it('resets a witness after changing an earlier universal', () => {
    const tree = quantified(binder('x'), quantified(binder('y', 'existential', ['x']), leaf('p', cn('True'))));
    expect(updateScenario(tree, { x: 1, y: 8 }, 'x', 2)).toEqual({ x: 2 });
  });
  it('keeps an earlier witness fixed when a later universal changes', () => {
    const tree = quantified(binder('y', 'existential'), quantified(binder('x', 'universal', ['y']), leaf('p', cn('True'))));
    expect(updateScenario(tree, { x: 1, y: 8 }, 'x', 2)).toEqual({ x: 2, y: 8 });
  });
  it('keeps chosen witnesses when a control repeats the same value', () => {
    const tree = quantified(binder('x'), quantified(binder('y', 'existential', ['x']), leaf('p', cn('True'))));
    expect(updateScenario(tree, { x: 1, y: 8 }, 'x', 1)).toEqual({ x: 1, y: 8 });
  });
  it('does not offer an assumption as a numerical control', () => {
    const tree = quantified({ ...binder('h', 'assumption'), domain: 'unknown' }, leaf('p', cn('True')));
    expect(initialScenario(tree)).toEqual({});
  });
  it('uses distinct binder IDs even when names are shadowed', () => {
    const tree = quantified({ ...binder('outer'), name: 'x' }, quantified({ ...binder('inner', 'universal', ['outer']), name: 'x' }, leaf('p', cn('True'))));
    expect(collectBinders(tree).map(b => b.id)).toEqual(['outer', 'inner']);
    expect(updateScenario(tree, { outer: 3, inner: 4 }, 'inner', 9)).toEqual({ outer: 3, inner: 9 });
  });
  it('rejects incompatible state updates', () => {
    const tree = quantified(binder('x'), leaf('p', cn('True')));
    expect(updateScenario(tree, { x: 1 }, 'x', [1, 2])).toEqual({ x: 1 });
  });
});

describe('automatic recognition with partial coverage', () => {
  it('discovers a supported child inside an unknown predicate', () => {
    const expr = app('Mystery.P', [app('Metric.ball', [vr('c'), lit(1)], { metric: 'sup2', dimension: 2 })]);
    const scenes = discoverScenes(leaf('unknown', expr));
    expect(scenes).toHaveLength(1);
    expect(scenes[0]).toMatchObject({ kind: 'ball', metric: 'sup2', nodeId: 'unknown' });
  });
  it('does not invent geometry for an unrecognized metric', () => {
    const expr = app('Metric.ball', [vr('c'), lit(1)], { metric: 'unknown', dimension: 2 });
    expect(discoverScenes(leaf('unknown', expr))).toEqual([]);
  });
  it('does not pretend a one-coordinate vector is a scalar real-line renderer input', () => {
    const expr = app('Metric.ball', [vr('c'), lit(1)], { metric: 'euclideanN', dimension: 1 });
    expect(discoverScenes(leaf('one-coordinate-vector', expr))).toEqual([]);
  });
  it('does not attach a membership condition through an overridden membership instance', () => {
    const set = app('Metric.ball', [vr('c'), lit(1)], { metric: 'sup2', dimension: 2 });
    const expr = app('Membership.mem', [set, vr('p')], { standard: false });
    const scene = discoverScenes(leaf('custom-membership', expr))[0];
    expect(scene?.kind).toBe('ball');
    if (scene?.kind === 'ball') expect(scene.point).toBeUndefined();
    expect(evaluatePredicate(expr, { c: [0, 0], p: [0, 0] }).status).toBe('unknown');
  });
  it('retains negation and antecedent context instead of asserting the subcondition', () => {
    const inner = leaf('p', app('Metric.ball', [vr('c'), lit(1)], { metric: 'real', dimension: 1 }));
    const not: StatementNode = { id: 'n', kind: 'not', label: '', lean: '', expression: cn('unused'), children: [inner] };
    expect(discoverScenes(not)[0]?.context).toEqual(['Inside a negation']);
    expect(scenesForNode(not, 'n')).toHaveLength(1);
    expect(scenesForNode(not, 'missing')).toHaveLength(0);
  });
  it('recognizes a numeric explicit lambda graph and samples its actual body', () => {
    const fn: Expr = { kind: 'lambda', binder: binder('t', 'lambda'), body: app('HMul.hMul', [vr('t'), vr('t')]) };
    const scene = discoverScenes(leaf('p', app('Eq', [fn, fn]))).find(s => s.kind === 'graph') as GraphScene;
    expect(sampleGraph(scene, {}, { min: -2, max: 2, count: 3 })).toEqual([{ x: -2, y: 4 }, { x: 0, y: 0 }, { x: 2, y: 4 }]);
  });
});

describe('metric balls, spheres, and high-dimensional slices', () => {
  it('shows max-metric square membership independently of Euclidean membership', () => {
    const state = { c: [0, 0], p: [0.9, 0.9], r: 1 };
    expect(ballGeometry(ball('sup2'), state)).toMatchObject({ membership: { status: 'true' } });
    expect(ballGeometry(ball('euclidean2'), state)).toMatchObject({ membership: { status: 'false' } });
  });
  it('handles zero and negative radii without a fictitious region', () => {
    expect(ballGeometry(ball(), { c: [0, 0], r: 0 })).toMatchObject({ empty: true, singleton: false });
    expect(ballGeometry(ball('euclidean2', 2, 'closed'), { c: [0, 0], r: 0 })).toMatchObject({ empty: false, singleton: true });
    expect(ballGeometry(ball('euclidean2', 2, 'sphere'), { c: [0, 0], r: -1 })).toMatchObject({ empty: true });
  });
  it('computes an actual 4D sphere intersection with the selected 2D plane', () => {
    const result = sliceGeometry(ball('euclideanN', 4, 'sphere'), { c: [0, 0, 0, 0], r: 5 }, { fixed: [0, 0, 3, 0] });
    expect(result).toMatchObject({ status: 'geometry', radius: 4, ambientDimension: 4, intrinsicDimension: 3, boundary: 'sphere', isSlice: true });
  });
  it('distinguishes tangent closed/spherical slices from empty open slices', () => {
    const state = { c: [0, 0, 0], r: 1 };
    expect(sliceGeometry(ball('euclideanN', 3, 'closed'), state, { fixed: [0, 0, 1] })).toMatchObject({ empty: false, singleton: true });
    expect(sliceGeometry(ball('euclideanN', 3, 'open'), state, { fixed: [0, 0, 1] })).toMatchObject({ empty: true });
    expect(sliceGeometry(ball('euclideanN', 3, 'sphere'), state, { fixed: [0, 0, 2] })).toMatchObject({ empty: true });
  });
  it('renders a sup sphere boundary slice as a filled square when appropriate', () => {
    expect(sliceGeometry(ball('supN', 3, 'sphere'), { c: [0, 0, 0], r: 1 }, { fixed: [0, 0, 1] })).toMatchObject({ empty: false, boundary: 'closed', radius: 1 });
    expect(sliceGeometry(ball('supN', 3, 'sphere'), { c: [0, 0, 0], r: 1 }, { fixed: [0, 0, 0.5] })).toMatchObject({ empty: false, boundary: 'sphere' });
  });
  it('does not show a projected point as belonging to the slice', () => {
    const shape = sliceGeometry(ball('euclideanN', 4), { c: [0, 0, 0, 0], r: 2, p: [0.1, 0.2, 1, 0] });
    expect(shape).toMatchObject({ point: [0.1, 0.2], pointInSlice: false });
    if (shape.status === 'geometry') expect(shape.note).toContain('outside this slice');
  });
  it('handles arbitrary coordinate axes and rejects invalid axes', () => {
    expect(sliceGeometry(ball('euclideanN', 4), { c: [1, 2, 3, 4], r: 5 }, { axes: [2, 3], fixed: [1, 2, 0, 0] })).toMatchObject({ center: [3, 4], radius: 5 });
    expect(sliceGeometry(ball('euclideanN', 4), { c: [0, 0, 0, 0], r: 1 }, { axes: [1, 1] }).status).toBe('unknown');
  });
});
