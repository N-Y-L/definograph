import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic';
import { compileReading, compileReadingCues } from './index';

const constant = (name: string): Expr => ({ kind: 'const', name });
const literal = (value: number): Expr => ({ kind: 'literal', value });
const bind = (id: string, role: Binder['role'] = 'universal', name = id, dependsOn: string[] = []): Binder => ({ id, name, role, type: 'ℝ', domain: 'real', dependsOn });
const variable = (binder: Binder): Expr => ({ kind: 'var', id: binder.id, name: binder.name, type: binder.type, typeDescriptor: binder.typeDescriptor });
const call = (fn: Expr, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn, args, argumentKinds: args.map(() => 'value'), ...extra });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => call(constant(name), args, extra);
const leaf = (id: string, expression: Expr = { kind: 'opaque', text: `condition ${id}` }): StatementNode => ({ id, kind: 'predicate', label: id, lean: `condition ${id}`, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binder?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder });
const prepare = (tree: StatementNode) => {
  const document = compileSemanticDocument({ source: 'test source', tree, expression: tree.expression });
  const reading = compileReading(document);
  return { document, reading, plan: compileReadingCues(reading, document) };
};
const deepFreeze = <T>(value: T): T => {
  if (typeof value === 'object' && value !== null && !Object.isFrozen(value)) {
    Object.freeze(value); Object.values(value).forEach(deepFreeze);
  }
  return value;
};

describe('guided choice and logical context', () => {
  it('retains forall/exists order, exact allowed dependencies, and grouped binder order', () => {
    const x = bind('x'), z = bind('z'), y = bind('y', 'existential', 'y', ['x', 'z']);
    const forward = prepare(node('nx', 'forall', [node('nz', 'forall', [node('ny', 'exists', [leaf('p')], y)], z)], x));
    const reverse = prepare(node('ny', 'exists', [node('nx', 'forall', [leaf('p')], x)], bind('y', 'existential')));
    const introductions = forward.plan.cues.filter(cue => cue.intent === 'introduce');
    expect(introductions.map(cue => cue.role)).toEqual(['arbitrary', 'witness']);
    expect(introductions[0]!.binders.map(binder => binder.binderId)).toEqual(['x', 'z']);
    expect(introductions[0]!.sourceNodeIds).toEqual(['nx', 'nz']);
    expect(introductions[0]!.nodeId).toBe('nz');
    expect(introductions[0]!.contextObjectIds).toEqual(introductions[0]!.focusObjectIds);
    expect(introductions[1]!.binders[0]!.dependsOn).toEqual(introductions[0]!.focusObjectIds);
    expect(reverse.plan.cues.filter(cue => cue.intent === 'introduce').map(cue => cue.role)).toEqual(['witness', 'arbitrary']);
    expect(reverse.plan.cues[0]!.binders[0]!.dependsOn).toEqual([]);
  });

  it('does not merge same-spelled choices across alternatives or retain sibling-local objects', () => {
    const { plan } = prepare(node('or', 'or', [node('left', 'forall', [leaf('p')], bind('a', 'universal', 'x')), node('right', 'forall', [leaf('q')], bind('b', 'universal', 'x'))]));
    const introductions = plan.cues.filter(cue => cue.intent === 'introduce');
    expect(introductions).toHaveLength(2);
    expect(introductions[0]!.focusObjectIds[0]).not.toBe(introductions[1]!.focusObjectIds[0]);
    expect(introductions.map(cue => cue.branchPath[0]!.edge.index)).toEqual([0, 1]);
    expect(introductions[1]!.retainedObjectIds).not.toContain(introductions[0]!.focusObjectIds[0]);
    expect(introductions.every(cue => cue.roles.includes('alternative'))).toBe(true);
  });

  it('keeps separate dependency lists within a group of existential choices', () => {
    const { plan } = prepare(node('nx', 'forall', [node('ny', 'exists', [node('nz', 'exists', [leaf('p')], bind('z', 'existential', 'z', ['x', 'y']))], bind('y', 'existential', 'y', ['x']))], bind('x')));
    const witnesses = plan.cues.find(cue => cue.role === 'witness')!;
    expect(witnesses.binders).toHaveLength(2);
    expect(witnesses.binders[0]!.dependsOn).not.toContain(witnesses.binders[0]!.objectId);
    expect(witnesses.binders[1]!.dependsOn).toContain(witnesses.binders[0]!.objectId);
    expect(witnesses.detail).toContain('each may use only its listed earlier choices');
  });

  it('keeps alternatives, negation, implication assumptions and iff directions on every descendant cue', () => {
    const tree = node('not', 'not', [node('or', 'or', [node('imp', 'implies', [leaf('p'), node('iff', 'iff', [leaf('q'), leaf('r')])], bind('h', 'assumption')), leaf('s')])]);
    const { plan } = prepare(tree);
    expect(plan.cues.map(cue => cue.nodeId)).toEqual(['not', 'or', 'imp', 'p', 'iff', 'q', 'r', 's']);
    const byNode = new Map(plan.cues.map(cue => [cue.nodeId, cue]));
    expect(byNode.get('p')!.roles).toEqual(['negated', 'alternative', 'assumption']);
    expect(byNode.get('p')!.assumptionNodeIds).toEqual([]);
    expect(byNode.get('q')!.roles).toEqual(['negated', 'alternative', 'conclusion', 'equivalence-left']);
    expect(byNode.get('r')!.roles).toEqual(['negated', 'alternative', 'conclusion', 'equivalence-right']);
    expect(byNode.get('q')!.assumptionNodeIds).toEqual(['p']);
    expect(byNode.get('s')!.assumptionNodeIds).toEqual([]);
    expect(byNode.get('q')!.ancestorNodeIds).toEqual(['not', 'or', 'imp', 'iff']);
    expect(byNode.get('q')!.contextLabels).toContain('Under negation');
    expect(byNode.get('or')!.detail).toContain('does not require both');
    expect(byNode.get('iff')!.detail).toContain('Each condition implies the other');
  });

  it('groups only the uninterrupted implication chain and retains each premise’s scope', () => {
    const tree = node('i1', 'implies', [leaf('p'), node('i2', 'implies', [leaf('q'), node('x', 'forall', [node('i3', 'implies', [leaf('r'), leaf('s')])], bind('x'))])]);
    const { plan } = prepare(tree);
    expect(plan.cues.filter(cue => cue.intent === 'logic').map(cue => cue.sourceNodeIds)).toEqual([['i1', 'i2'], ['i3']]);
    expect(plan.cues.find(cue => cue.nodeId === 'q')!.assumptionNodeIds).toEqual(['p']);
    expect(plan.cues.find(cue => cue.nodeId === 'r')!.assumptionNodeIds).toEqual(['p', 'q']);
    expect(plan.cues.find(cue => cue.nodeId === 's')!.assumptionNodeIds).toEqual(['p', 'q', 'r']);
  });

  it('distinguishes definition parameters from arbitrary choices and witnesses', () => {
    const { plan } = prepare(node('f', 'parameter', [node('x', 'forall', [leaf('p')], bind('x'))], bind('f', 'parameter')));
    expect(plan.cues[0]!.role).toBe('parameter');
    expect(plan.cues[0]!.detail).toContain('typed parameters');
    expect(plan.cues[1]!.role).toBe('arbitrary');
    expect(plan.cues[1]!.roles).toEqual(['result', 'arbitrary']);
  });
});

describe('source-linked construction stages', () => {
  it('follows inner application dependencies and both expression paths before comparing them', () => {
    const x = bind('x'), f = bind('f'), g = bind('g'), h = bind('h');
    const fx = call(variable(f), [variable(x)]), gfx = call(variable(g), [fx]), hx = call(variable(h), [variable(x)]);
    const { plan, document } = prepare(node('nx', 'forall', [leaf('eq', app('Eq', [gfx, hx]))], x));
    const stages = plan.cues.filter(cue => cue.panelId);
    expect(stages.map(cue => cue.intent)).toEqual(['apply', 'apply', 'apply', 'compare']);
    expect(stages.map(cue => cue.stage.index)).toEqual([1, 2, 3, 4]);
    expect(stages.every(cue => cue.stage.count === 4)).toBe(true);
    expect(stages.map(cue => cue.title)).toEqual(['Follow f', 'Follow g', 'Follow h', 'Compare the expressions with =']);
    const fRelation = document.relations.find(relation => relation.id === stages[0]!.stage.relationId)!;
    const fxId = fRelation.ports.find(port => port.role === 'output')!.objectId;
    expect(stages[1]!.retainedObjectIds).toContain(fxId);
    expect(stages.at(-1)!.stage.kind).toBe('clause');
  });

  it('composes nested image and preimage terms before their containing membership', () => {
    const image = app('Set.image', [constant('f'), constant('S')]);
    const preimage = app('Set.preimage', [constant('g'), image]);
    const { plan } = prepare(leaf('member', app('Set.Mem', [preimage, constant('x')])));
    expect(plan.cues.map(cue => cue.stage.relationKind)).toEqual(['image', 'preimage', 'membership']);
    expect(plan.cues.map(cue => cue.stage.kind)).toEqual(['construction', 'construction', 'clause']);
    expect(new Set(plan.cues.flatMap(cue => cue.focusRelationIds)).size).toBe(3);
  });

  it('reuses a shared expression once while retaining its identity in both comparison paths', () => {
    const fx = call(variable(bind('f')), [literal(0)]), gfx = call(variable(bind('g')), [fx]);
    const { plan, document } = prepare(leaf('eq', app('Eq', [gfx, fx])));
    expect(plan.cues.map(cue => cue.title)).toEqual(['Follow f', 'Follow g', 'Compare the expressions with =']);
    const firstRelation = document.relations.find(relation => relation.id === plan.cues[0]!.stage.relationId)!;
    const shared = firstRelation.ports.find(port => port.role === 'output')!.objectId;
    expect(plan.cues[1]!.focusObjectIds).toContain(shared);
    expect(plan.cues[2]!.focusObjectIds).toContain(shared);
    expect(plan.cues[2]!.retainedObjectIds).toContain(shared);
  });

  it('orders nested set constructions before the membership that uses their result', () => {
    const intersection = app('Set.inter', [constant('B'), constant('C')]);
    const difference = app('Set.diff', [constant('A'), intersection]);
    const { plan } = prepare(leaf('member', app('Set.Mem', [difference, constant('x')])));
    expect(plan.cues.map(cue => cue.stage.relationKind)).toEqual(['set-construction', 'set-construction', 'membership']);
    expect(plan.cues.map(cue => cue.title)).toEqual(['Form the intersection', 'Form the difference', 'Read the membership condition']);
    expect(plan.cues[0]!.detail).toContain('No membership region is assumed nonempty');
  });

  it('introduces the unknown wrapper before inspecting its recognized expression parts', () => {
    const ball = app('Metric.ball', [literal(0), literal(1)], { metric: 'real', dimension: 1 });
    const { plan, document, reading } = prepare(leaf('wrapper', app('Unknown.F', [app('Set.Mem', [ball, literal(0)])])));
    expect(plan.cues[0]!.title).toBe('Read the complete clause');
    expect(plan.cues[0]!.focusRelationIds).toEqual(reading.panels[0]!.rootRelationIds);
    expect(document.relations.find(relation => relation.id === plan.cues[0]!.focusRelationIds[0])!.fidelity).toBe('structural');
    expect(plan.cues.slice(1).map(cue => cue.stage.relationKind)).toEqual(['metric-region', 'membership']);
    expect(plan.cues.slice(1).every(cue => cue.role === 'contained' && cue.detail.includes('not a separate assertion'))).toBe(true);
  });

  it('treats an abstract Prop-valued predicate as its own root instead of asserting its argument', () => {
    const f = { ...bind('F'), type: 'Prop → Prop', typeDescriptor: { kind: 'relation' as const, lean: 'Prop → Prop' } };
    const proposition = app('Eq', [literal(0), literal(1)], { typeDescriptor: { kind: 'proposition', lean: 'Prop' } });
    const { plan } = prepare(node('f', 'forall', [leaf('wrapped', call(variable(f), [proposition], { argumentKinds: ['type'] }))], f));
    const clauses = plan.cues.filter(cue => cue.panelId);
    expect(clauses).toHaveLength(2);
    expect(clauses[0]!.stage.kind).toBe('clause');
    expect(clauses[1]!.intent).toBe('compare');
    expect(clauses[1]!.role).toBe('contained');
  });

  it('keeps lambda-body relations in their local scope and drops their variables when leaving it', () => {
    const local = bind('local', 'lambda', 'x');
    const lambda: Expr = { kind: 'lambda', binder: local, body: app('Eq', [variable(local), literal(0)]) };
    const { plan, document } = prepare(node('and', 'and', [leaf('wrapped', app('Unknown.P', [lambda])), leaf('later', app('Eq', [literal(1), literal(2)]))]));
    const localCue = plan.cues.find(cue => cue.nodeId === 'wrapped' && cue.stage.relationKind === 'equality')!;
    const localObject = document.objects.find(object => object.binder?.id === local.id)!;
    expect(localCue.role).toBe('contained');
    expect(localCue.scopeId).not.toBe('scope:wrapped');
    expect(localCue.scopePath.at(-2)).toBe('scope:wrapped');
    expect(localCue.contextObjectIds).toContain(localObject.id);
    expect(localCue.contextLabels).toContain('Within a function body');
    const laterCue = plan.cues.find(cue => cue.nodeId === 'later')!;
    expect(laterCue.retainedObjectIds).not.toContain(localObject.id);
    expect(laterCue.contextObjectIds).not.toContain(localObject.id);
    expect(plan.cues.every(cue => cue.focusRelationIds.every(id => document.relations.some(relation => relation.id === id && relation.scopeId === cue.scopeId && relation.nodeId === cue.nodeId)))).toBe(true);
  });

  it('retains every source clause, including opaque leaves without recognized relations', () => {
    const { plan, reading } = prepare(node('or', 'or', [leaf('unknown'), leaf('known', app('Eq', [literal(0), literal(0)]))]));
    expect(reading.panels.every(panel => plan.cues.some(cue => cue.panelId === panel.id))).toBe(true);
    expect(plan.cues.find(cue => cue.nodeId === 'unknown')!.detail).toBe('condition unknown');
    expect(plan.cues.find(cue => cue.nodeId === 'unknown')!.focusRelationIds).toEqual([]);
  });
});

describe('determinism, coverage, and bounded presentation', () => {
  it('is pure and deterministic; source selection does not reorder the reading', () => {
    const { reading, document, plan } = prepare(node('or', 'or', [leaf('p'), leaf('q')]));
    deepFreeze(reading); deepFreeze(document);
    expect(compileReadingCues(reading, document)).toEqual(plan);
    expect(compileReadingCues(compileReading(document, { selectedNodeId: 'q' }), document)).toEqual(plan);
    expect(new Set(plan.cues.map(cue => cue.id)).size).toBe(plan.cues.length);
  });

  it('binder renaming changes words but never cue topology or semantic identities', () => {
    const build = (xName: string, yName: string) => {
      const x = bind('x', 'universal', xName), y = bind('y', 'existential', yName, ['x']);
      return prepare(node('nx', 'forall', [node('ny', 'exists', [leaf('eq', app('Eq', [variable(x), variable(y)]))], y)], x)).plan;
    };
    const topology = (plan: ReturnType<typeof compileReadingCues>) => plan.cues.map(({ id, intent, role, roles, nodeId, scopeId, focusObjectIds, focusRelationIds, ancestorNodeIds, branchPath, stage }) => ({ id, intent, role, roles, nodeId, scopeId, focusObjectIds, focusRelationIds, ancestorNodeIds, branchPath, stage }));
    const first = build('x', 'y'), renamed = build('point', 'radius');
    expect(topology(first)).toEqual(topology(renamed));
    expect(first.cues[0]!.title).not.toBe(renamed.cues[0]!.title);
  });

  it('truncates only a complete-plan prefix and reports every omitted or partially shown source', () => {
    const { document, reading, plan } = prepare(node('not', 'not', [node('or', 'or', [leaf('a'), leaf('b'), leaf('c')])]));
    const bounded = compileReadingCues(reading, document, { maxCues: 3 });
    expect(bounded.cues).toEqual(plan.cues.slice(0, 3));
    expect(bounded.cues.map(cue => cue.nodeId)).toEqual(['not', 'or', 'a']);
    expect(bounded.totalCueCount).toBe(plan.cues.length);
    expect(bounded.omittedCueCount).toBe(2);
    expect(bounded.omittedNodeIds).toEqual(['b', 'c']);
    expect(bounded.truncated).toBe(true);
    const zero = compileReadingCues(reading, document, { maxCues: 0 });
    expect(zero.cues).toEqual([]);
    expect(zero.omittedNodeIds).toEqual(reading.nodes.map(node => node.id));
    expect(() => compileReadingCues(reading, document, { maxCues: -1 })).toThrow('nonnegative integer');
    expect(() => compileReadingCues(reading, document, { maxCues: 1.5 })).toThrow('nonnegative integer');
    expect(compileReadingCues(reading, document, { maxCues: 1001 }).diagnostics.some(message => message.includes('capped at 1000'))).toBe(true);
  });

  it('reports a partially emitted atomic construction by its source node', () => {
    const image = app('Set.image', [constant('f'), constant('S')]);
    const { document, reading } = prepare(leaf('member', app('Set.Mem', [image, constant('x')])));
    const bounded = compileReadingCues(reading, document, { maxCues: 1 });
    expect(bounded.cues).toHaveLength(1);
    expect(bounded.cues[0]!.stage.count).toBe(2);
    expect(bounded.omittedNodeIds).toEqual(['member']);
    expect(bounded.omittedCueCount).toBe(1);
  });

  it('retains source logic when the semantic traversal budget omits a scope', () => {
    const { document } = prepare(node('not', 'not', [node('imp', 'implies', [leaf('premise'), leaf('conclusion')])]));
    const limited = { ...document, scopes: document.scopes.filter(scope => scope.nodeId !== 'conclusion') };
    const reading = compileReading(limited);
    const plan = compileReadingCues(reading, limited);
    const cue = plan.cues.find(cue => cue.nodeId === 'conclusion')!;
    expect(cue.roles).toEqual(['negated', 'conclusion']);
    expect(cue.assumptionNodeIds).toEqual(['premise']);
    expect(cue.focusRelationIds).toEqual([]);
    expect(cue.contextObjectIds).toEqual([]);
    expect(plan.diagnostics.some(message => message.includes('scopes were not exported'))).toBe(true);
  });
});
