import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { evaluateExpression } from '../core/expression';
import { compileSemanticDocument, createSemanticRegistry, expressionKey, formatExpression, planViews } from './index';
import euclidean from '../core/fixtures/euclidean-ball.json';
import customMetric from '../core/fixtures/custom-metric.json';
import product from '../core/fixtures/product-ball.json';

const c = (name: string): Expr => ({ kind: 'const', name });
const lit = (value: number | string): Expr => ({ kind: 'literal', value });
const variable = (binder: Binder): Expr => ({ kind: 'var', id: binder.id, name: binder.name, type: binder.type });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: c(name), args, ...extra });
const bind = (id: string, name = id, extra: Partial<Binder> = {}): Binder => ({ id, name, type: 'ℝ', domain: 'real', role: 'universal', dependsOn: [], ...extra });
const leaf = (id: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean: id, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binder?: Binder): StatementNode => ({ id, kind, label: id, lean: id, expression: c('True'), children, binder });
const compile = (tree: StatementNode) => compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
const eq = (a: Expr, b: Expr) => app('Eq', [c('Real'), a, b]);
const relationPairs = (doc: ReturnType<typeof compile>) => doc.relations.filter(r => r.kind === 'equality').map(r => r.ports.map(p => p.objectId));

describe('semantic identities and composition', () => {
  it('uses one object for a bound variable shared across predicate fragments', () => {
    const x = bind('x');
    const doc = compile(node('root', 'forall', [node('both', 'and', [leaf('p', eq(variable(x), lit(1))), leaf('q', eq(variable(x), lit(2)))])], x));
    expect(doc.objects.filter(o => o.binder?.id === 'x')).toHaveLength(1);
    expect(relationPairs(doc)[0]![0]).toBe(relationPairs(doc)[1]![0]);
    expect(planViews(doc).sharedObjectIds).toContain(doc.choices[0]!.objectId);
  });

  it('preserves identity under alpha-renaming of both names and backend binder ids', () => {
    const build = (id: string, name: string) => {
      const x = bind(id, name);
      return compile(node('root', 'forall', [leaf('p', eq(variable(x), lit(1)))], x));
    };
    const left = build('opaque-server-id-7', 'x'), right = build('other-id-201', 'z');
    expect(left.objects.map(o => o.id)).toEqual(right.objects.map(o => o.id));
    expect(relationPairs(left)).toEqual(relationPairs(right));
    expect(right.objects.find(o => o.binder)?.label).toBe('z');
  });

  it('keeps shadowed binders distinct even when printed names are identical', () => {
    const x = bind('outer', 'x'), y = bind('inner', 'x', { role: 'existential', dependsOn: ['outer'] });
    const doc = compile(node('root', 'forall', [node('exists', 'exists', [leaf('p', eq(variable(x), variable(y)))], y)], x));
    expect(doc.choices[0]!.objectId).not.toBe(doc.choices[1]!.objectId);
    expect(doc.choices[1]!.dependsOn).toEqual([doc.choices[0]!.objectId]);
  });

  it('composes the same mathematical objects across equivalent conjunction nesting', () => {
    const x = bind('x');
    const a = leaf('a', eq(variable(x), lit(1))), b = leaf('b', eq(variable(x), lit(2))), d = leaf('d', eq(variable(x), lit(3)));
    const left = compile(node('root', 'forall', [node('left', 'and', [node('ab', 'and', [a, b]), d])], x));
    const right = compile(node('root', 'forall', [node('right', 'and', [a, node('bd', 'and', [b, d])])], x));
    expect(left.objects.map(o => o.id).sort()).toEqual(right.objects.map(o => o.id).sort());
    expect(relationPairs(left)).toEqual(relationPairs(right));
    expect(planViews(left).sharedObjectIds).toEqual(planViews(right).sharedObjectIds);
  });

  it('normalizes association of raw applications without reordering arguments', () => {
    const flat = app('f', [lit(1), lit(2)]);
    const nested: Expr = { kind: 'app', fn: app('f', [lit(1)]), args: [lit(2)] };
    expect(expressionKey(flat)).toBe(expressionKey(nested));
    expect(expressionKey(flat)).not.toBe(expressionKey(app('f', [lit(2), lit(1)])));
  });

  it('retains full expressions and provenance for inspecting shared objects', () => {
    const x = bind('x');
    const expression = eq(variable(x), lit('9007199254740993'));
    const doc = compile(node('root', 'forall', [leaf('p', expression)], x));
    expect(doc.relations[0]!.expression).toBe(expression);
    expect(doc.relations[0]!.provenance).toEqual({ nodeId: 'p', expressionPath: 'expression', origin: 'elaborated-expression' });
    expect(doc.objects.find(o => o.binder)?.provenance.length).toBeGreaterThan(1);
    expect(evaluateExpression(doc.objects.find(o => o.label === '9007199254740993')!.expression).status).toBe('unknown');
  });

  it('recognizes typed sets and functions using descriptors rather than variable names', () => {
    const set = bind('s', 'f', { domain: 'unknown', type: 'Set X', typeDescriptor: { kind: 'set', lean: 'Set X' } });
    const fn = bind('f', 'S', { domain: 'unknown', type: 'X → Y', typeDescriptor: { kind: 'map', lean: 'X → Y' } });
    const doc = compile(node('root', 'forall', [node('inner', 'forall', [leaf('p', c('True'))], fn)], set));
    expect(doc.objects.find(o => o.binder?.id === set.id)?.kind).toBe('set');
    expect(doc.objects.find(o => o.binder?.id === fn.id)?.kind).toBe('function');
  });

  it('prints Lean universe levels as sorts rather than mathematical numeral objects', () => {
    expect(formatExpression({ kind: 'sort', name: '0' })).toBe('Prop');
    expect(formatExpression({ kind: 'sort', name: '1' })).toBe('Type');
    expect(formatExpression({ kind: 'sort', name: 'u + 1' })).toBe('Sort (u + 1)');
    expect(compile(leaf('root', { kind: 'sort', name: '0' })).objects[0]!.kind).toBe('type');
  });
});

describe('logical scopes and choices', () => {
  it('keeps implication premises local to the consequent', () => {
    const tree = node('root', 'and', [node('imp', 'implies', [leaf('premise', c('P')), leaf('conclusion', c('Q'))]), leaf('sibling', c('R'))]);
    const doc = compile(tree);
    expect(doc.scopes.find(s => s.nodeId === 'conclusion')?.assumptionNodeIds).toEqual(['premise']);
    expect(doc.scopes.find(s => s.nodeId === 'sibling')?.assumptionNodeIds).toEqual([]);
    expect(doc.scopes.find(s => s.nodeId === 'premise')?.context).toContain('Premise of an implication');
  });

  it('makes an implication proof binder available only in its consequent', () => {
    const h = bind('h', 'h', { role: 'assumption', domain: 'unknown', type: 'P' });
    const ball = app('Metric.ball', [lit(0), lit(1)], { metric: 'real', dimension: 1, argumentKinds: ['value', 'value'] });
    const doc = compile(node('root', 'implies', [leaf('premise', ball), leaf('conclusion', ball)], h));
    const hypothesisId = doc.choices[0]!.objectId;
    expect(doc.scopes.find(s => s.nodeId === 'premise')!.objectIds).not.toContain(hypothesisId);
    expect(doc.scopes.find(s => s.nodeId === 'conclusion')!.objectIds).toContain(hypothesisId);
    expect(doc.scenes.find(s => s.nodeId === 'premise')!.scope).toEqual([]);
    expect(doc.scenes.find(s => s.nodeId === 'conclusion')!.scope).toEqual([h]);
    expect(planViews(doc, { selectedNodeId: 'premise' }).views.some(v => v.kind === 'quantifier-flow')).toBe(false);
  });

  it('retains a local expression scope for lambda inputs and body relations', () => {
    const t = bind('t', 't', { role: 'lambda' });
    const lambda: Expr = { kind: 'lambda', binder: t, body: eq(variable(t), lit(1)) };
    const doc = compile(leaf('root', app('Unknown.lambdaConsumer', [lambda])));
    const choice = doc.choices.find(c => c.binderId === 't')!;
    const bodyRelation = doc.relations.find(r => r.kind === 'equality')!;
    expect(bodyRelation.scopeId).toBe(choice.scopeId);
    expect(bodyRelation.scopeId).not.toBe('scope:root');
    expect(doc.scopes.find(s => s.id === bodyRelation.scopeId)!.context).toContain('Within a function body');
  });

  it('does not leak objects or dependencies between disjunction branches', () => {
    const x = bind('x'), y = bind('y', 'y', { role: 'existential', dependsOn: ['x'] });
    const doc = compile(node('root', 'or', [node('left', 'forall', [leaf('p', c('True'))], x), node('right', 'exists', [leaf('q', c('True'))], y)]));
    expect(doc.choices[1]!.dependsOn).toEqual([]);
    expect(doc.choices[1]!.availableObjectIds).not.toContain(doc.choices[0]!.objectId);
    expect(doc.scopes.find(s => s.nodeId === 'q')?.context).toContain('Alternative 2 of a disjunction');
  });

  it('retains negation and equivalence contexts on semantic relations', () => {
    const doc = compile(node('root', 'not', [node('equiv', 'iff', [leaf('left', eq(lit(1), lit(1))), leaf('right', eq(lit(2), lit(2)))])]));
    const relation = doc.relations[0]!;
    expect(doc.scopes.find(s => s.id === relation.scopeId)?.context).toEqual(['Inside a negation', 'Side 1 of an equivalence']);
  });

  it('distinguishes definition parameters from quantified propositions', () => {
    const parameter = bind('x', 'x', { role: 'parameter' });
    const doc = compile(node('root', 'parameter', [leaf('result', c('Real'))], parameter));
    expect(doc.choices[0]!.role).toBe('parameter');
    expect(doc.choices[0]!.explanation).toContain('not a universally quantified proposition');
  });
});

describe('semantic rules and honest coverage', () => {
  it('renders a generic map even when no numerical or semantic adapter applies', () => {
    const doc = compile(leaf('root', app('Unknown.hairyBallOrAnything', [c('X')], { type: 'Prop', argumentKinds: ['value'] })));
    const plan = planViews(doc);
    expect(plan.views.some(v => v.kind === 'semantic-map')).toBe(true);
    expect(plan.coverage.structural).toBe(1);
    expect(doc.opaqueRegions).toHaveLength(1);
    expect(doc.scenes).toHaveLength(0);
  });

  it('keeps interpreted children while reporting their unknown parent', () => {
    const ball = app('Metric.ball', [lit(0), lit(1)], { metric: 'real', dimension: 1, standard: true, argumentKinds: ['value', 'value'] });
    const doc = compile(leaf('root', app('Unknown.predicate', [ball])));
    expect(doc.coverage[0]!.status).toBe('partial');
    expect(doc.relations.some(r => r.kind === 'metric-region')).toBe(true);
    expect(doc.scenes.some(s => s.kind === 'ball')).toBe(true);
    expect(doc.opaqueRegions[0]!.supportedRelationIds).toContain(doc.relations.find(r => r.kind === 'metric-region')!.id);
  });

  it('excludes typeclass and proof arguments from displayed generic relation ports', () => {
    const expression = app('Unknown.predicate', [c('Real'), { kind: 'opaque', text: 'instFoo' }, { kind: 'opaque', text: 'proof' }, lit(3)], { argumentKinds: ['type', 'instance', 'proof', 'value'] });
    const doc = compile(leaf('root', expression));
    expect(doc.relations[0]!.ports).toHaveLength(2);
    expect(doc.objects.some(o => o.label === 'instFoo' || o.label === 'proof')).toBe(false);
  });

  it('keeps proposition arguments and their recognized children inside an uninterpreted wrapper', () => {
    const proposition = app('Set.Mem', [c('A'), c('x')], { argumentKinds: ['value', 'value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } });
    const expression = app('Unknown.wrapper', [c('Real'), proposition, { kind: 'opaque', text: 'instance' }, { kind: 'opaque', text: 'proof' }], { argumentKinds: ['type', 'type', 'instance', 'proof'] });
    const doc = compile(leaf('wrapped', expression));
    expect(doc.relations.map(relation => relation.kind)).toEqual(['predicate', 'membership']);
    expect(doc.relations[0]!.ports.map(port => port.role)).toEqual(['symbol', 'argument 1']);
    expect(doc.relations[0]!.fidelity).toBe('structural');
    expect(doc.relations[1]!.provenance.expressionPath).not.toBe('expression');
    expect(doc.opaqueRegions[0]!.supportedRelationIds).toContain(doc.relations[1]!.id);
    expect(doc.objects.some(object => ['instance', 'proof', 'Real'].includes(object.label))).toBe(false);
    expect(formatExpression(expression)).toContain('Set.Mem(A, x)');
  });

  it('preserves proposition inputs of abstract predicates without treating proof arguments as propositions', () => {
    const predicate: Expr = { kind: 'var', id: 'F', name: 'F', type: 'Prop → Prop', typeDescriptor: { kind: 'relation', lean: 'Prop → Prop' } };
    const proposition: Expr = { kind: 'var', id: 'P', name: 'P', type: 'Prop', typeDescriptor: { kind: 'proposition', lean: 'Prop' } };
    const expression: Expr = { kind: 'app', fn: predicate, args: [proposition, { ...proposition, id: 'proof', name: 'proof' }], argumentKinds: ['type', 'proof'] };
    const doc = compile(leaf('wrapped', expression));
    expect(doc.relations[0]!.ports.map(port => doc.objects.find(object => object.id === port.objectId)!.label)).toEqual(['F', 'P']);
    expect(formatExpression(expression)).toBe('F(P)');
  });

  it('retains quantified propositions in their local scope while ordinary function types stay hidden', () => {
    const input = bind('local-x', 'x');
    const body = app('Eq', [variable(input), lit(0)], { argumentKinds: ['value', 'value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } });
    const quantified: Expr = { kind: 'forall', binder: input, binderType: c('Real'), body };
    const arrow: Expr = { ...quantified, body: { kind: 'const', name: 'Real', typeDescriptor: { kind: 'type', lean: 'Type' } } };
    const doc = compile(leaf('wrapped', app('Unknown.wrapper', [quantified, arrow], { argumentKinds: ['type', 'type'] })));
    expect(doc.relations.map(relation => relation.kind)).toEqual(['predicate', 'equality']);
    expect(doc.relations[0]!.ports).toHaveLength(2);
    expect(doc.relations[1]!.scopeId).not.toBe(doc.relations[0]!.scopeId);
  });

  it('does not conflate expressions using different metric instances', () => {
    const args = [lit(0), lit(1)];
    const euclideanExpr = app('Metric.ball', args, { metric: 'euclidean2', metricInstance: 'l2', dimension: 2 });
    const supExpr = app('Metric.ball', args, { metric: 'sup2', metricInstance: 'linfty', dimension: 2 });
    expect(expressionKey(euclideanExpr)).not.toBe(expressionKey(supExpr));
  });

  it('keeps custom metrics symbolic and never grants a geometric view', () => {
    const doc = compile(customMetric.tree as StatementNode);
    expect(doc.relations.some(r => r.kind === 'metric-region')).toBe(true);
    expect(doc.relations.find(r => r.kind === 'metric-region')!.conditions.join(' ')).toContain('no audited numerical');
    expect(doc.scenes.filter(s => s.kind === 'ball')).toHaveLength(0);
    expect(planViews(doc).views.filter(v => v.kind === 'ball')).toHaveLength(0);
  });

  it('does not reinterpret overloaded membership without an audited set instance', () => {
    const expr = app('Membership.mem', [c('mystery'), lit(1)], { standard: false });
    const doc = compile(leaf('root', expr));
    expect(doc.relations.some(r => r.kind === 'membership')).toBe(false);
    expect(doc.coverage[0]!.status).toBe('structural');
  });

  it('recognizes canonical overloaded subset only when the prover audits its instance', () => {
    const safe = compile(leaf('root', app('HasSubset.Subset', [c('S'), c('T')], { standard: true })));
    const custom = compile(leaf('root', app('HasSubset.Subset', [c('S'), c('T')], { standard: false })));
    expect(safe.relations[0]!.kind).toBe('subset');
    expect(custom.relations[0]!.kind).toBe('predicate');
  });

  it('represents an abstract typed relation as a relation rather than a numeric function output', () => {
    const relation: Expr = { kind: 'var', id: 'R', name: 'R', type: 'X → X → Prop', typeDescriptor: { kind: 'relation', lean: 'X → X → Prop' } };
    const doc = compile(leaf('root', { kind: 'app', fn: relation, args: [c('x'), c('y')] }));
    expect(doc.relations[0]!.kind).toBe('predicate');
    expect(doc.relations[0]!.fidelity).toBe('symbolic');
    expect(doc.relations[0]!.ports.map(p => p.role)).toEqual(['relation', 'argument 1', 'argument 2']);
  });

  it('does not treat higher-order partial constructors as completed sets or propositions', () => {
    const partialEq = app('Eq', [c('X'), c('x')], { argumentKinds: ['type', 'value'], typeDescriptor: { kind: 'relation', lean: 'X → Prop' } });
    const partialImage = app('Set.image', [c('X'), c('Y'), c('f')], { argumentKinds: ['type', 'type', 'value'], typeDescriptor: { kind: 'map', lean: 'Set X → Set Y' } });
    const partialBall = app('Metric.ball', [c('Real'), { kind: 'opaque', text: 'realMetric' }, lit(0)], { argumentKinds: ['type', 'instance', 'value'], typeDescriptor: { kind: 'map', lean: 'ℝ → Set ℝ' }, metric: 'real', dimension: 1 });
    const doc = compile(node('root', 'and', [leaf('eq', partialEq), leaf('image', partialImage), leaf('ball', partialBall)]));
    expect(doc.relations.some(r => ['equality', 'image', 'metric-region'].includes(r.kind))).toBe(false);
    expect(formatExpression(partialEq)).toBe('Eq(x)');
    expect(formatExpression(partialBall)).toBe('Metric.ball(0)');
  });

  it('supports image, preimage, subset, and mapping properties compositionally', () => {
    const image = app('Set.image', [c('f'), c('S')]);
    const preimage = app('Set.preimage', [c('f'), c('T')]);
    const doc = compile(node('root', 'and', [leaf('sub', app('Set.Subset', [image, preimage])), leaf('inj', app('Function.Injective', [c('f')]))]));
    expect(doc.relations.map(r => r.kind)).toEqual(['subset', 'image', 'preimage', 'function-property']);
    expect(doc.coverage.every(c => c.status === 'interpreted')).toBe(true);
  });

  it('rejects ambiguous duplicate plugin registrations and undeclared capabilities', () => {
    const p = { id: 'example', version: '1', title: 'Example', capabilities: ['predicate'] as const, limitations: [], match: () => undefined };
    expect(() => createSemanticRegistry([p, p])).toThrow('Duplicate');
    expect(() => compileSemanticDocument({ source: '', tree: leaf('root', c('P')), expression: c('P') }, [{ ...p, match: () => ({ kind: 'membership', label: 'unsafe', arguments: [], fidelity: 'symbolic' }) }])).toThrow('undeclared capability');
  });

  it('binds plugin-carried structure only to an introduced value and its exact type', () => {
    const typeExpression = app('Audited.Structure', [c('A')]);
    const x = bind('x', 'x', { type: 'Audited.Structure A', typeExpression, domain: 'unknown' });
    const tree = node('intro', 'forall', [leaf('claim', c('True'))], x);
    const plugin = { id: 'bundle-test', version: '1', title: 'Bundle test', capabilities: ['predicate'] as const, limitations: [], match: () => undefined,
      matchBinder: (value: Expr, type: Expr) => type === typeExpression ? { kind: 'predicate' as const, label: 'declared structure', arguments: [{ role: 'value', expression: value }], fidelity: 'symbolic' as const } : undefined };
    const analysis = { source: '', tree, expression: tree.expression };
    const document = compileSemanticDocument(analysis, [plugin]);
    const relation = document.relations[0]!;
    expect(relation.provenance.expressionPath).toBe('binder.type');
    expect(relation.expression).toBe(typeExpression);
    expect(relation.scopeId).toBe('scope:intro');
    expect(document.scopes.find(scope => scope.id === relation.scopeId)!.objectIds).toContain(relation.ports[0]!.objectId);
    expect(document.objects.find(object => object.id === relation.ports[0]!.objectId)!.binder?.id).toBe('x');
    expect(compileSemanticDocument(analysis, []).relations).toHaveLength(0);
  });

  it('exposes checked type aliases through the same binder hook while keeping the declared name', () => {
    const exposed = app('Audited.Structure', [c('A')]);
    const expansion = { expression: exposed, before: 'MyStructure', after: 'Audited.Structure A', constants: ['MyStructure'], definitionalEquality: true as const, maxDepth: 2 as const };
    const x = bind('x', 'x', { type: 'MyStructure', typeExpression: c('MyStructure'), typeExpansion: expansion, domain: 'unknown' });
    const plugin = { id: 'alias-test', version: '1', title: 'Alias test', capabilities: ['predicate'] as const, limitations: [], match: () => undefined,
      matchBinder: (value: Expr, type: Expr) => type === exposed ? { kind: 'predicate' as const, label: 'declared structure', arguments: [{ role: 'value', expression: value }], fidelity: 'symbolic' as const } : undefined };
    const run = (binder: Binder) => { const tree = node('intro', 'forall', [leaf('claim', c('True'))], binder); return compileSemanticDocument({ source: '', tree, expression: tree.expression }, [plugin]); };
    const document = run(x);
    expect(document.relations).toHaveLength(1);
    expect(document.objects.find(object => object.binder?.id === 'x')!.type).toBe('MyStructure');
    expect(document.relations[0]!.conditions.join(' ')).toContain('definitionally equal');
    expect(run({ ...x, typeExpansion: { ...expansion, before: 'AnotherType' } }).relations).toHaveLength(0);
    expect(run({ ...x, typeExpansion: { ...expansion, constants: ['a', 'b', 'c'] } }).relations).toHaveLength(0);
    expect(run({ ...x, typeExpansion: { ...expansion, expression: { kind: 'opaque', text: 'truncated' } } }).relations).toHaveLength(0);
  });

  it('validates binder plugin capabilities and never treats a proof assumption as a structured witness', () => {
    const x = bind('x', 'x', { typeExpression: c('A'), domain: 'unknown' });
    const tree = node('intro', 'forall', [leaf('claim', c('True'))], x);
    const plugin = { id: 'bundle-test', version: '1', title: 'Bundle test', capabilities: ['predicate'] as const, limitations: [], match: () => undefined,
      matchBinder: () => ({ kind: 'membership' as const, label: 'undeclared', arguments: [], fidelity: 'symbolic' as const }) };
    expect(() => compileSemanticDocument({ source: '', tree, expression: tree.expression }, [plugin])).toThrow('undeclared capability');
    const assumption = node('hypothesis', 'implies', [leaf('premise', c('True')), leaf('conclusion', c('True'))], { ...x, role: 'assumption' });
    expect(compileSemanticDocument({ source: '', tree: assumption, expression: assumption.expression }, [plugin]).relations).toHaveLength(0);
  });
});

describe('automatic view planning', () => {
  it('ranks audited metric geometry first for a single ball predicate', () => {
    const doc = compile(euclidean.tree as StatementNode);
    const plan = planViews(doc);
    expect(plan.views[0]!.kind).toBe('ball');
    expect(plan.views.some(v => v.kind === 'semantic-map')).toBe(true);
    expect(plan.views.some(v => v.kind === 'quantifier-flow')).toBe(true);
    expect(plan.views[0]!.conditions.join(' ')).toContain('finite precision');
  });

  it('does not choose the first discovered numerical scene merely by order', () => {
    const x = bind('x');
    const interval = leaf('interval', app('LT.lt', [variable(x), lit(1)], { standard: true, domain: 'real', operator: 'lt', argumentKinds: ['value', 'value'] }));
    const ball = leaf('ball', app('Metric.ball', [lit(0), lit(1)], { metric: 'real', dimension: 1, argumentKinds: ['value', 'value'] }));
    const doc = compile(node('root', 'forall', [node('both', 'and', [interval, ball])], x));
    expect(doc.scenes[0]!.kind).toBe('interval');
    expect(planViews(doc).views.find(v => v.sceneIds.length)?.kind).toBe('ball');
  });

  it('prefers direct geometry for the whole epsilon-ball statement while retaining connected relations', () => {
    const doc = compile(product.tree as StatementNode);
    const plan = planViews(doc);
    expect(plan.views[0]!.kind).toBe('ball');
    expect(plan.views.some(v => v.kind === 'relation-map')).toBe(true);
    expect(plan.views.some(v => v.kind === 'semantic-map')).toBe(true);
  });

  it('selects only descendant fragments while retaining inherited choices and assumptions', () => {
    const doc = compile(product.tree as StatementNode);
    const leafNode = doc.coverage.at(-1)!.nodeId;
    const plan = planViews(doc, { selectedNodeId: leafNode });
    expect(plan.coverage.fragments).toBe(1);
    expect(plan.views.some(v => v.kind === 'quantifier-flow')).toBe(true);
    expect(plan.views.filter(v => v.kind !== 'quantifier-flow').every(v => v.nodeIds.every(id => id === leafNode))).toBe(true);
    expect(doc.scopes.find(s => s.nodeId === leafNode)!.assumptionNodeIds.length).toBeGreaterThan(0);
  });

  it('cannot select an unrelated or nonexistent source node', () => {
    const doc = compile(leaf('root', c('True')));
    expect(() => planViews(doc, { selectedNodeId: 'untrusted' })).toThrow('Unknown statement node');
  });

  it('keeps complete logical coverage when the detailed-view budget is zero', () => {
    const doc = compile(euclidean.tree as StatementNode);
    const plan = planViews(doc, { maxDetailedViews: 0 });
    expect(plan.views.every(v => !v.sceneIds.length)).toBe(true);
    expect(plan.coverage.fragments).toBe(1);
    expect(plan.views.some(v => v.kind === 'semantic-map')).toBe(true);
  });
});

it('prioritizes the selected relationship over inherited quantifier context', () => {
  const a = bind('A','A',{type:'Set α',domain:'unknown',typeDescriptor:{kind:'set',lean:'Set α'}});
  const b = bind('B','B',{type:'Set α',domain:'unknown',typeDescriptor:{kind:'set',lean:'Set α'}});
  const x = bind('x','x',{type:'α',domain:'unknown'});
  const subset = app('Set.Subset',[c('α'),variable(a),variable(b)],{standard:true,argumentKinds:['type','value','value'],type:'Prop',typeDescriptor:{kind:'proposition',lean:'Prop'}});
  const tree = node('root','forall',[node('next','forall',[node('point','forall',[leaf('condition',subset)],x)],b)],a);
  const document=compile(tree);
  const plan=planViews(document,{selectedNodeId:'condition'});
  expect(plan.views[0]?.kind).toBe('relation-map');
  expect(plan.views.some(v=>v.kind==='quantifier-flow')).toBe(true);
});
