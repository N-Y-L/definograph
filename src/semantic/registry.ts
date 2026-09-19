import { headName, numericOperator, comparisonArguments } from '../core/expression';
import type { Expr } from '../core/types';
import type { SemanticPlugin, SemanticRuleMatch } from './types';

const arg = (role: string, expression: Expr) => ({ role, expression });
const match = (kind: SemanticRuleMatch['kind'], label: string, args: SemanticRuleMatch['arguments'], conditions: readonly string[] = []): SemanticRuleMatch => ({ kind, label, arguments: args, fidelity: 'symbolic', conditions });
function hasValues(expr: Extract<Expr, { kind: 'app' }>, count: number): boolean {
  return expr.argumentKinds ? expr.argumentKinds.filter(kind => kind === 'value').length >= count : expr.args.length >= count;
}
function returns(expr: Extract<Expr, { kind: 'app' }>, kind: 'set' | 'proposition' | 'real'): boolean {
  return !expr.typeDescriptor || expr.typeDescriptor.kind === kind;
}

export const builtInSemanticPlugins: readonly SemanticPlugin[] = [
  {
    id: 'sets', version: '1.0.0', title: 'Sets and membership', capabilities: ['membership', 'subset', 'image', 'preimage'],
    limitations: ['Set diagrams encode relations; area, distance, and cardinality are not inferred.'],
    match(expr) {
      if (expr.kind !== 'app') return;
      const name = headName(expr), args = expr.args;
      if (!hasValues(expr, 2)) return;
      if ((name === 'Set.Mem' || name === 'Membership.mem' && expr.standard === true) && returns(expr, 'proposition')) return match('membership', 'belongs to', [arg('element', args.at(-1)!), arg('set', args.at(-2)!)]);
      if ((name === 'Set.Subset' || name === 'HasSubset.Subset' && expr.standard === true) && returns(expr, 'proposition')) return match('subset', 'is a subset of', [arg('subset', args.at(-2)!), arg('superset', args.at(-1)!)]);
      if ((name === 'Set.image' || name === 'Set.preimage') && returns(expr, 'set')) return match(name === 'Set.image' ? 'image' : 'preimage', name === 'Set.image' ? 'image under a function' : 'preimage under a function', [arg('function', args.at(-2)!), arg('set', args.at(-1)!), arg('result', expr)]);
    },
  },
  {
    id: 'mappings', version: '1.0.0', title: 'Mappings and function properties', capabilities: ['application', 'function-property', 'predicate'],
    limitations: ['A symbolic arrow does not supply a numerical function or a proof of a property.'],
    match(expr) {
      if (expr.kind !== 'app') return;
      const name = headName(expr);
      if (name && ['Function.Injective', 'Function.Surjective', 'Function.Bijective'].includes(name) && hasValues(expr, 1) && returns(expr, 'proposition')) return match('function-property', name.replace('Function.', '').toLowerCase(), [arg('function', expr.args.at(-1)!)]);
      if (expr.fn.kind === 'var' || expr.fn.kind === 'lambda') {
        const args = expr.args.filter((_, i) => !expr.argumentKinds || expr.argumentKinds[i] === 'value');
        if (expr.fn.kind === 'var' && expr.fn.typeDescriptor?.kind === 'relation') return match('predicate', expr.fn.name, [arg('relation', expr.fn), ...args.map((e, i) => arg(`argument ${i + 1}`, e))], ['An abstract relation on these objects; no additional properties are inferred.']);
        return match('application', 'maps to', [arg('function', expr.fn), ...args.map((e, i) => arg(`input ${i + 1}`, e)), arg('output', expr)]);
      }
    },
  },
  {
    id: 'relations', version: '1.0.0', title: 'Equality and audited order', capabilities: ['equality', 'inequality'],
    limitations: ['Relations remain symbolic unless a separate numerical evaluator accepts their operands.'],
    match(expr) {
      const op = numericOperator(expr);
      if (!op || !['eq', 'ne', 'lt', 'le'].includes(op)) return;
      if (expr.kind !== 'app' || !hasValues(expr, 2) || !returns(expr, 'proposition')) return;
      const args = comparisonArguments(expr);
      if (!args) return;
      return match(op === 'eq' || op === 'ne' ? 'equality' : 'inequality', { eq: '=', ne: '≠', lt: '<', le: '≤' }[op as 'eq' | 'ne' | 'lt' | 'le'], [arg('left', args[0]), arg('right', args[1])]);
    },
  },
  {
    id: 'metric', version: '1.0.0', title: 'Metric regions and distances', capabilities: ['metric-region', 'distance'],
    limitations: ['Numerical geometry requires an audited metric instance and dimension; other metrics remain symbolic.'],
    match(expr) {
      if (expr.kind !== 'app' || !hasValues(expr, 2)) return;
      const name = headName(expr);
      const conditions = expr.metric && expr.metric !== 'unknown' ? [`Metric: ${expr.metric}${expr.dimension ? `; ambient dimension ${expr.dimension}` : ''}.`] : ['The metric instance has no audited numerical interpretation.'];
      if (name && ['Metric.ball', 'Metric.closedBall', 'Metric.sphere'].includes(name) && returns(expr, 'set')) return match('metric-region', name === 'Metric.ball' ? 'open ball' : name === 'Metric.closedBall' ? 'closed ball' : 'sphere', [arg('center', expr.args.at(-2)!), arg('radius', expr.args.at(-1)!), arg('region', expr)], conditions);
      if ((name === 'dist' || name === 'Dist.dist') && returns(expr, 'real')) return match('distance', 'distance', [arg('from', expr.args.at(-2)!), arg('to', expr.args.at(-1)!), arg('distance', expr)], conditions);
    },
  },
];

/** Explicit registry construction makes third-party rules inspectable and testable. */
export function createSemanticRegistry(plugins: readonly SemanticPlugin[] = builtInSemanticPlugins): readonly SemanticPlugin[] {
  const ids = new Set<string>();
  for (const plugin of plugins) {
    if (!plugin.id || ids.has(plugin.id)) throw new Error(`Duplicate or empty semantic plugin id: ${plugin.id}`);
    if (!plugin.version || !plugin.capabilities.length) throw new Error(`Plugin ${plugin.id} must declare a version and capabilities.`);
    ids.add(plugin.id);
  }
  return Object.freeze([...plugins]);
}
