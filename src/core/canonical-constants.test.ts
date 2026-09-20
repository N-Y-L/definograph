import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from './types';
import { evaluateExpression, evaluatePredicate, headName, numericOperator } from './expression';
import { discoverScenes } from './scenes';
import { compileSemanticDocument, expressionKey, formatExpression, setConstructionParts } from '../semantic';
import { compileReading } from '../reading';
import { compileTypedConstruction } from '../constructions/model';

const constant = (name: string, canonical?: boolean): Expr => ({ kind: 'const', name, ...(canonical === undefined ? {} : { canonical }) });
const literal = (value: number): Expr => ({ kind: 'literal', value });
const app = (name: string, args: Expr[], canonical?: boolean, extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: constant(name, canonical), args, argumentKinds: args.map(() => 'value'), ...extra });
const leaf = (expression: Expr): StatementNode => ({ id: 'p', kind: 'predicate', label: 'p', lean: 'source condition', expression, children: [] });
const semantic = (expression: Expr) => compileSemanticDocument({ source: 'source condition', expression, tree: leaf(expression) });
const twoValues = [literal(0), literal(1)];

describe('constant provenance controls built-in interpretation', () => {
  it.each([
    ['Set.union', 'set-construction'], ['Set.inter', 'set-construction'], ['Set.diff', 'set-construction'], ['Set.compl', 'set-construction'],
    ['Set.Mem', 'membership'], ['Set.Subset', 'subset'], ['Set.image', 'image'], ['Set.preimage', 'preimage'],
    ['Membership.mem', 'membership'], ['HasSubset.Subset', 'subset'],
    ['Metric.ball', 'metric-region'], ['Metric.closedBall', 'metric-region'], ['Metric.sphere', 'metric-region'], ['Dist.dist', 'distance'],
    ['Eq', 'equality'], ['Ne', 'equality'], ['LE.le', 'inequality'],
    ['Function.Injective', 'function-property'], ['Function.Surjective', 'function-property'], ['Function.Bijective', 'function-property'],
  ])('does not interpret a project-defined %s as %s', (name, kind) => {
    const args = name === 'Set.compl' || name.startsWith('Function.') ? [constant('input')] : twoValues;
    const known = app(name, args, undefined, { standard: true, metric: 'real', dimension: 1 });
    const foreign = app(name, args, false, { standard: true, metric: 'real', dimension: 1 });
    expect(semantic(known).relations.some(relation => relation.kind === kind)).toBe(true);
    const document = semantic(foreign);
    expect(document.relations).toHaveLength(1);
    expect(document.relations[0]!.kind).toBe('predicate');
    expect(document.relations[0]!.fidelity).toBe('structural');
    expect(document.relations[0]!.label).toBe(name);
    expect(document.coverage[0]!.status).toBe('structural');
    expect(discoverScenes(leaf(foreign))).toEqual([]);
    expect(evaluatePredicate(foreign).status).toBe('unknown');
  });

  it('propagates an untrusted head through nested application association', () => {
    const inner = app('Eq', [literal(0)], false);
    const outer: Expr = { kind: 'app', fn: inner, args: [literal(0)], standard: true, operator: 'eq' };
    expect(headName(outer)).toBeUndefined();
    expect(numericOperator(outer)).toBeUndefined();
    expect(evaluatePredicate(outer).status).toBe('unknown');
  });

  it.each(['Union.union', 'Inter.inter', 'SDiff.sdiff', 'Compl.compl'])('rejects an untrusted overloaded %s despite affirmative instance metadata', name => {
    const args = name === 'Compl.compl' ? [constant('A')] : [constant('A'), constant('B')];
    const metadata = { standard: true, typeDescriptor: { kind: 'set' as const, lean: 'Set X' } };
    expect(setConstructionParts(app(name, args, true, metadata))).toBeDefined();
    const foreign = app(name, args, false, metadata);
    expect(setConstructionParts(foreign)).toBeUndefined();
    expect(semantic(foreign).relations.map(relation => relation.kind)).toEqual(['predicate']);
  });

  it.each([
    ['HAdd.hAdd', 'add', [literal(1), literal(2)]],
    ['Prod.mk', 'pair', [literal(1), literal(2)]],
    ['OfNat.ofNat', 'ofNat', [constant('Real'), literal(1), constant('inst')]],
  ] as const)('does not let operation metadata bypass an untrusted %s head', (name, operator, args) => {
    const trusted = app(name, [...args], true, { standard: true, operator, domain: 'real' });
    const foreign = app(name, [...args], false, { standard: true, operator, domain: 'real' });
    expect(evaluateExpression(trusted).status).toBe('value');
    expect(numericOperator(foreign)).toBeUndefined();
    expect(evaluateExpression(foreign).status).toBe('unknown');
    expect(formatExpression(foreign)).toContain(name);
  });

  it.each(['dist', 'Dist.dist'])('does not numerically evaluate an untrusted %s using metric metadata', name => {
    expect(evaluateExpression(app(name, twoValues, true, { metric: 'real' })).status).toBe('value');
    expect(evaluateExpression(app(name, twoValues, false, { metric: 'real' })).status).toBe('unknown');
  });

  it.each(['True', 'False'])('retains an untrusted %s as an uninterpreted constant', name => {
    const foreign = constant(name, false), trusted = constant(name);
    expect(evaluatePredicate(foreign).status).toBe('unknown');
    expect(evaluatePredicate(trusted).status).toBe(name === 'True' ? 'true' : 'false');
    expect(semantic(foreign).coverage[0]!.status).toBe('structural');
    expect(semantic(foreign).opaqueRegions).toHaveLength(1);
    expect(semantic(trusted).coverage[0]!.status).toBe('interpreted');
  });

  it.each(['Not', 'And', 'Or', 'Iff'])('does not evaluate project-defined %s with logical connective semantics', name => {
    const args = name === 'Not' ? [constant('False')] : [constant('True'), constant('True')];
    expect(evaluatePredicate(app(name, args)).status).not.toBe('unknown');
    expect(evaluatePredicate(app(name, args, false)).status).toBe('unknown');
  });

  it('preserves supported children under an unfamiliar wrapper without transferring its claim', () => {
    const ball = app('Metric.ball', twoValues, true, { metric: 'real', dimension: 1 });
    const wrapper = app('Set.Mem', [ball, literal(0)], false);
    const document = semantic(wrapper), reading = compileReading(document);
    expect(document.relations.map(relation => relation.kind)).toEqual(['predicate', 'metric-region']);
    expect(reading.panels[0]!.rootRelationIds).toEqual([document.relations[0]!.id]);
    expect(document.scenes).toHaveLength(1);
    expect(document.scenes[0]!.kind === 'ball' && document.scenes[0]!.point).toBeUndefined();
    expect(evaluatePredicate(wrapper).status).toBe('unknown');
  });

  it('does not numerically evaluate membership in a project-defined metric constructor', () => {
    const foreignBall = app('Metric.ball', twoValues, false, { metric: 'real', dimension: 1 });
    const membership = app('Set.Mem', [foreignBall, literal(0)]);
    expect(semantic(membership).relations.map(relation => relation.kind)).toEqual(['membership', 'predicate']);
    expect(discoverScenes(leaf(membership))).toEqual([]);
    expect(evaluatePredicate(membership).status).toBe('unknown');
  });

  it('preserves names and universe identity independently of interpretation provenance', () => {
    const trusted: Expr = { kind: 'const', name: 'Set.union', levels: ['u'], canonical: true };
    const foreign: Expr = { ...trusted, canonical: false };
    expect(expressionKey(foreign)).toBe(expressionKey(trusted));
    expect(formatExpression(foreign)).toBe('Set.union');
    expect(expressionKey({ ...foreign, levels: ['v'] })).not.toBe(expressionKey(foreign));
    const foreignUnion = app('Set.union', [constant('A'), constant('B')], false);
    expect(setConstructionParts(foreignUnion)).toBeUndefined();
    expect(formatExpression(foreignUnion)).toBe('Set.union(A, B)');
  });

  it('does not infer a carrier from a project-defined Set type constructor', () => {
    const type = app('Set', [constant('Carrier')], false);
    const binder: Binder = { id: 's', name: 's', type: 'Set Carrier', role: 'parameter', dependsOn: [], typeExpression: type, typeDescriptor: { kind: 'set', lean: 'Set Carrier' } };
    const expression: Expr = { kind: 'forall', binder, binderType: type, body: constant('True') };
    const tree: StatementNode = { id: 'binder', kind: 'parameter', label: 's', lean: 'context', expression, binder, children: [leaf(constant('True'))] };
    const document = compileSemanticDocument({ source: 'context', expression, tree });
    const reading = compileReading(document), model = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
    expect(model.members[0]!.kind).toBe('element');
    expect(model.types[0]!.expression).toEqual(type);
  });
});
