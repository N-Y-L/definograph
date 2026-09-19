import { comparisonArguments, evaluateExpression, expressionVariables, headName, numericOperator } from './expression';
import type { Binder, Expr, GraphScene, Scene, SceneBase, StatementNode } from './types';
import { MAX_NUMERICAL_DIMENSION } from './limits';

const setNames = ['Metric.ball', 'Metric.closedBall', 'Metric.sphere'];
const knownMetrics = new Set(['real', 'sup2', 'euclidean2', 'supN', 'euclideanN']);

/** Constructor names also occur as partially applied functions; only saturated
 * applications have the geometric/predicate meaning understood by these views.
 * Legacy exports retain all Lean arguments, so their full arity is required. */
function completeApplication(expr: Extract<Expr, { kind: 'app' }>, values: number, leanArity: number, output: 'set' | 'proposition' | 'real'): boolean {
  if (expr.typeDescriptor && expr.typeDescriptor.kind !== output) return false;
  if (!expr.argumentKinds) return expr.args.length === leanArity;
  return expr.argumentKinds.length === expr.args.length
    && expr.argumentKinds.filter(kind => kind === 'value').length === values
    && expr.argumentKinds.slice(-values).every(kind => kind === 'value');
}

/** Recognized fragments remain discoverable even below an unsupported predicate. */
export function discoverScenes(tree: StatementNode): Scene[] {
  const scenes: Scene[] = [];
  let visits = 0;
  const walk = (node: StatementNode, scope: Binder[], guards: Expr[], context: string[], depth: number): void => {
    if (depth > 128 || ++visits > 20_000) return;
    const scoped = node.binder ? [...scope, node.binder] : scope;
    if (node.children.length) {
      node.children.forEach((child, i) => {
        const childGuards = node.kind === 'implies' && i === 1 && node.children[0] ? [...guards, node.children[0].expression] : guards;
        const childContext = node.kind === 'not' ? [...context, 'Inside a negation']
          : node.kind === 'implies' && i === 0 ? [...context, 'Assumption of an implication']
            : node.kind === 'or' ? [...context, `Alternative ${i + 1} of a disjunction`]
              : node.kind === 'iff' ? [...context, `Side ${i + 1} of an equivalence`] : context;
        // An implication's proof binder is available only in its consequent, not its own type.
        const childScope = node.kind === 'implies' && i === 0 && node.binder?.role === 'assumption' ? scope : scoped;
        walk(child, childScope, childGuards, childContext, depth + 1);
      });
      return;
    }
    const emitted = new Set<string>();
    let index = 0;
    const base = (expression: Expr, title: string): SceneBase => ({ id: `${node.id}:${index++}`, nodeId: node.id, title, expression, scope: scoped, guards, context });
    const visit = (expr: Expr, path: string, point?: Expr, exprDepth = 0): void => {
      if (exprDepth > 128 || ++visits > 20_000) return;
      if (expr.kind === 'app') {
        const name = headName(expr);
        if (setNames.includes(name ?? '') && completeApplication(expr, 2, 4, 'set') && expr.metric && expr.metric !== 'unknown' && knownMetrics.has(expr.metric)) {
          const dimension = expr.dimension ?? (expr.metric === 'real' ? 1 : expr.metric.endsWith('2') ? 2 : undefined);
          const center = expr.args.at(-2), radius = expr.args.at(-1);
          const supportedDimension = dimension !== undefined && Number.isInteger(dimension) && (expr.metric === 'real' ? dimension === 1 : dimension >= 2 && dimension <= MAX_NUMERICAL_DIMENSION) && (!expr.metric.endsWith('2') || dimension === 2);
          if (center && radius && dimension && supportedDimension) {
            scenes.push({ ...base(expr, `${name === 'Metric.sphere' ? 'Sphere' : name === 'Metric.closedBall' ? 'Closed ball' : 'Open ball'} in ${dimension}D`), kind: 'ball', metric: expr.metric, dimension, metricInstance: expr.metricInstance, center, radius, boundary: name === 'Metric.sphere' ? 'sphere' : name === 'Metric.closedBall' ? 'closed' : 'open', point });
            emitted.add(path);
          }
        }
        const op = numericOperator(expr);
        if (op && ['lt', 'le', 'eq', 'ne'].includes(op) && completeApplication(expr, 2, op === 'eq' || op === 'ne' ? 3 : 4, 'proposition')) {
          const [left, right] = comparisonArguments(expr)!;
          const variables = new Set([...expressionVariables(left), ...expressionVariables(right)]);
          const variable = [...scoped].reverse().find(b => b.domain === 'real' && variables.has(b.id));
          if (variable) scenes.push({ ...base(expr, `Condition on ${variable.name}`), kind: 'interval', variable, relation: op as 'lt' | 'le' | 'eq' | 'ne', left, right });
        }
        if ((name === 'Membership.mem' || name === 'Set.Mem') && completeApplication(expr, 2, name === 'Membership.mem' ? 5 : 3, 'proposition')) {
          const element = expr.args.at(-1)!;
          const indexOfSet = expr.args.length - 2;
          expr.args.forEach((arg, i) => visit(arg, `${path}.${i}`, i === indexOfSet && (name === 'Set.Mem' || expr.standard === true) ? element : undefined, exprDepth + 1));
          return;
        }
        if (['Function.Injective', 'Function.Surjective', 'Function.Bijective'].includes(name ?? '') && completeApplication(expr, 1, 3, 'proposition')) {
          const fn = expr.args.at(-1);
          if (fn) scenes.push({ ...base(expr, (name ?? '').replace('Function.', '')), kind: 'mapping', fn, property: name === 'Function.Injective' ? 'injective' : name === 'Function.Surjective' ? 'surjective' : 'bijective' });
        }
        if (expr.fn.kind === 'var') {
          const fnId = expr.fn.id;
          if (completeApplication(expr, 1, 1, 'real') && scoped.some(b => b.id === fnId && b.domain === 'realFunction')) scenes.push({ ...base(expr, `Mapping ${expr.fn.name}`), kind: 'mapping', fn: expr.fn, input: expr.args.at(-1) });
        }
        visit(expr.fn, `${path}.fn`, undefined, exprDepth + 1);
        expr.args.forEach((arg, i) => { if (!emitted.has(`${path}.${i}`)) visit(arg, `${path}.${i}`, undefined, exprDepth + 1); });
      } else if (expr.kind === 'lambda') {
        if (expr.binder.domain === 'real') {
          const trial = evaluateExpression(expr.body, Object.fromEntries([...scoped, expr.binder].filter(b => b.domain === 'real').map(b => [b.id, 0.5])));
          if (trial.status === 'value' && typeof trial.value === 'number') {
            scenes.push({ ...base(expr, `Graph in ${expr.binder.name}`), kind: 'graph', input: expr.binder, body: expr.body, fn: expr } as GraphScene);
          }
        }
        visit(expr.body, `${path}.body`, undefined, exprDepth + 1);
      }
    };
    visit(node.expression, 'root');
  };
  walk(tree, [], [], [], 0);
  return scenes;
}

export function scenesForNode(tree: StatementNode, nodeId: string, scenes = discoverScenes(tree)): Scene[] {
  const descendants = new Set<string>();
  const collect = (node: StatementNode): void => { descendants.add(node.id); node.children.forEach(collect); };
  const find = (node: StatementNode): StatementNode | undefined => node.id === nodeId ? node : node.children.map(find).find(Boolean);
  const node = find(tree);
  if (node) collect(node);
  return scenes.filter(scene => descendants.has(scene.nodeId));
}
