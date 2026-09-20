import { comparisonArguments, headName, numericOperator } from '../core';
import type { BallScene, Expr } from '../core';
import { expressionKey, formatExpression } from '../semantic';

type Sign = -1 | 0 | 1;
/** Exact syntactic signs only: no sampling, floating-point arithmetic, or theorem proving. */
export function literalSign(expr: Expr, depth = 0): Sign | undefined {
  if (depth > 32) return;
  if (expr.kind === 'literal') {
    const text = String(expr.value);
    if (!/^-?\d+$/.test(text)) return;
    const integer = BigInt(text);
    return integer === 0n ? 0 : integer < 0n ? -1 : 1;
  }
  if (expr.kind !== 'app') return;
  if (numericOperator(expr) === 'ofNat' && expr.args.length === 3 && (expr.domain === 'real' || expr.type === 'ℝ' || expr.type === 'Real')) return literalSign(expr.args[1]!, depth + 1);
  if (numericOperator(expr) === 'neg' && expr.args.length === 3 && (expr.domain === 'real' || expr.type === 'ℝ' || expr.type === 'Real')) {
    const sign = literalSign(expr.args[2]!, depth + 1);
    return sign === undefined ? undefined : sign === 0 ? 0 : sign === 1 ? -1 : 1;
  }
}

function positiveGuard(guard: Expr, radius: Expr): boolean {
  if (guard.kind !== 'app') return false;
  if (headName(guard) === 'And' && guard.args.length === 2) return guard.args.some(g => positiveGuard(g, radius));
  if (numericOperator(guard) !== 'lt' || guard.args.length !== 4 || guard.typeDescriptor?.kind && guard.typeDescriptor.kind !== 'proposition') return false;
  const args = comparisonArguments(guard);
  return !!args && literalSign(args[0]) === 0 && expressionKey(args[1]) === expressionKey(radius);
}

export interface MetricReading {
  center: string; radius: string; point?: string;
  pointIsCenter: boolean;
  sign?: Sign; signFromAssumption: boolean;
  presentation: 'interval' | 'circle' | 'square' | 'distance';
  boundary: BallScene['boundary']; dimension: number;
  relation: '<' | '≤' | '=';
  zero: 'empty' | 'singleton';
}

export function metricReading(scene: BallScene): MetricReading {
  const exact = literalSign(scene.radius);
  const signFromAssumption = exact === undefined && scene.guards.some(g => positiveGuard(g, scene.radius));
  return {
    center: formatExpression(scene.center), radius: formatExpression(scene.radius),
    point: scene.point ? formatExpression(scene.point) : undefined,
    pointIsCenter: !!scene.point && expressionKey(scene.point) === expressionKey(scene.center),
    sign: exact ?? (signFromAssumption ? 1 : undefined), signFromAssumption,
    presentation: scene.dimension === 1 ? 'interval' : scene.dimension > 2 ? 'distance' : scene.metric.startsWith('sup') ? 'square' : 'circle',
    boundary: scene.boundary, dimension: scene.dimension,
    relation: scene.boundary === 'open' ? '<' : scene.boundary === 'closed' ? '≤' : '=',
    zero: scene.boundary === 'open' ? 'empty' : 'singleton',
  };
}
