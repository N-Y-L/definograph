import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic/compiler';
import { compileReading } from './compiler';
import { compileScopedStatementGraph } from './scoped-graph';

export const variable = (binder: Binder): Expr => ({ kind: 'var', id: binder.id, name: binder.name, type: binder.type });
export const constant = (name: string, canonical = true): Expr => ({ kind: 'const', name, canonical });
export const call = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value'), ...extra });
export const leaf = (id: string, lean: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: lean, lean, expression, children: [] });
export const frame = (id: string, kind: StatementNode['kind'], children: StatementNode[], binder?: Binder): StatementNode => ({ id, kind, label: kind, lean: `${kind} ${binder?.name ?? ''}`, expression: constant('True'), children, binder });
export function fixture(tree: StatementNode) {
  const document = compileSemanticDocument({ source: 'generic scoped graph fixture', expression: tree.expression, tree });
  const reading = compileReading(document), model = compileScopedStatementGraph(document, reading)!;
  return { document, reading, model };
}

export function scopedFixture(names = { radius: 'δ', point: 'x', index: 'i', family: 'c', set: 's' }) {
  const bind = (id: string, name: string, role: Binder['role'], type: string): Binder => ({ id, name, role, type, dependsOn: [] });
  const radius = bind('radius', names.radius, 'existential', 'ℝ'), point = bind('point', names.point, 'universal', 'X');
  const index = bind('index', names.index, 'existential', 'I'), family = bind('family', names.family, 'universal', 'I → Set X'), set = bind('set', names.set, 'universal', 'Set X');
  const ball = call('Metric.ball', [variable(point), variable(radius)]);
  const image: Expr = { kind: 'app', fn: variable(family), args: [variable(index)] };
  const inclusion = leaf('inclusion', `Metric.ball ${names.point} ${names.radius} ⊆ ${names.family} ${names.index}`, call('Set.Subset', [ball, image]));
  const positive = leaf('positive', `${names.radius} > 0`, call('GT.gt', [variable(radius), { kind: 'literal', value: 0 }], { standard: true }));
  const member = leaf('membership', `${names.point} ∈ ${names.set}`, call('Set.Mem', [variable(set), variable(point)]));
  const guarded = frame('guard', 'implies', [member, frame('exists-index', 'exists', [inclusion], index)]);
  const body = frame('exists-radius', 'exists', [frame('both', 'and', [positive, frame('forall-point', 'forall', [guarded], point)])], radius);
  const tree = frame('forall-family', 'forall', [frame('forall-set', 'forall', [body], set)], family);
  return { ...fixture(tree), binders: { radius, point, index, family, set }, nodes: { tree, body, positive, member, guarded, inclusion } };
}
