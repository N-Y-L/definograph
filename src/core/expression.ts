import type { Expr, NumericOperator, NumericResult, PredicateResult, Scenario, ScenarioValue, StatementNode } from './types';
import { MAX_NUMERICAL_DIMENSION } from './limits';

const UNKNOWN = (reason: string): NumericResult => ({ status: 'unknown', reason });
const MAX_DEPTH = 128;

export function headName(expr: Expr): string | undefined {
  if (expr.kind === 'const') return expr.name;
  return expr.kind === 'app' ? headName(expr.fn) : undefined;
}

export function tailArguments(expr: Expr, count: number): Expr[] {
  return expr.kind === 'app' ? expr.args.slice(-count) : [];
}

const operators: Record<string, NumericOperator> = {
  'HAdd.hAdd': 'add', 'Add.add': 'add', 'HSub.hSub': 'sub', 'Sub.sub': 'sub',
  'HMul.hMul': 'mul', 'Mul.mul': 'mul', 'HDiv.hDiv': 'div', 'Div.div': 'div',
  'Neg.neg': 'neg', 'HPow.hPow': 'pow', 'Pow.pow': 'pow',
  abs: 'abs', 'Abs.abs': 'abs', 'Min.min': 'min', 'Max.max': 'max',
  'LT.lt': 'lt', 'LE.le': 'le', 'GT.gt': 'lt', 'GE.ge': 'le', 'OfNat.ofNat': 'ofNat',
};

/** The Lean exporter, not the browser, validates overloaded operation instances. */
export function numericOperator(expr: Expr): NumericOperator | undefined {
  if (expr.kind !== 'app') return undefined;
  const name = headName(expr);
  if (name === 'Prod.mk') return 'pair';
  if (name === 'Prod.fst') return 'proj1';
  if (name === 'Prod.snd') return 'proj2';
  if (name === 'Eq') return 'eq';
  if (name === 'Ne') return 'ne';
  if (expr.standard !== true) return undefined;
  return expr.operator ?? (name ? operators[name] : undefined);
}

export function comparisonArguments(expr: Expr): [Expr, Expr] | undefined {
  if (expr.kind !== 'app' || expr.args.length < 2) return undefined;
  const reversed = headName(expr) === 'GT.gt' || headName(expr) === 'GE.ge';
  return reversed ? [expr.args.at(-1)!, expr.args.at(-2)!] : [expr.args.at(-2)!, expr.args.at(-1)!];
}

function result(value: ScenarioValue): NumericResult {
  if (Array.isArray(value) && value.length > MAX_NUMERICAL_DIMENSION) return UNKNOWN(`Numerical vectors are limited to ${MAX_NUMERICAL_DIMENSION} coordinates; larger objects remain symbolic.`);
  if (typeof value === 'number' ? Number.isFinite(value) : value.every(Number.isFinite)) {
    return { status: 'value', value, approximate: true };
  }
  return UNKNOWN('The numerical illustration is outside the finite floating-point range.');
}

export function isPoint(value: ScenarioValue): value is number[] { return Array.isArray(value); }

export function metricDistance(metric: string, left: ScenarioValue, right: ScenarioValue, dimension?: number): number | undefined {
  if (metric === 'real') return typeof left === 'number' && typeof right === 'number' ? Math.abs(left - right) : undefined;
  if (!isPoint(left) || !isPoint(right) || left.length !== right.length || left.length === 0 || left.length > MAX_NUMERICAL_DIMENSION) return undefined;
  const expected = metric.endsWith('2') ? 2 : dimension;
  if (expected !== undefined && left.length !== expected) return undefined;
  const delta = left.map((x, i) => x - right[i]!);
  if (metric === 'sup2' || metric === 'supN') return Math.max(...delta.map(Math.abs));
  if (metric === 'euclidean2' || metric === 'euclideanN') return Math.hypot(...delta);
  return undefined;
}

export function evaluateExpression(expression: Expr, scenario: Scenario = {}): NumericResult {
  let visits = 0;
  const evaluate = (expr: Expr, env: Scenario, depth: number): NumericResult => {
    if (depth > MAX_DEPTH || ++visits > 10_000) return UNKNOWN('Expression exceeds the numerical evaluator limit.');
    if (expr.kind === 'literal') {
      if (typeof expr.value === 'string' && !/^-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?$/.test(expr.value)) return UNKNOWN('Unsupported numeric literal.');
      const value = Number(expr.value);
      if (Number.isInteger(value) && !Number.isSafeInteger(value)) return UNKNOWN('This integer literal is outside the exact integer range of the numerical renderer.');
      return result(value);
    }
    if (expr.kind === 'var') {
      const value = env[expr.id];
      return value === undefined ? UNKNOWN(`Choose a value for ${expr.name}.`) : result(value);
    }
    if (expr.kind !== 'app') return UNKNOWN('No audited numerical interpretation is available for this expression.');
    if (expr.fn.kind === 'lambda') {
      const arg = expr.args.at(-1);
      if (!arg) return UNKNOWN('Missing function argument.');
      const value = evaluate(arg, env, depth + 1);
      return value.status === 'value' ? evaluate(expr.fn.body, { ...env, [expr.fn.binder.id]: value.value }, depth + 1) : value;
    }
    const name = headName(expr);
    const op = numericOperator(expr);
    if (op === 'ofNat') {
      const scalarDomain = expr.domain === 'real' || expr.type === 'ℝ' || expr.type === 'Real' || expr.type === 'ℕ' || expr.type === 'Nat';
      const vectorDomain = expr.domain === 'sup2' || expr.domain === 'euclidean2' || expr.domain === 'supN' || expr.domain === 'euclideanN';
      if (!scalarDomain && !vectorDomain) return UNKNOWN('Numerals are supported only in standard real, natural, and recognized zero-vector domains.');
      // OfNat.ofNat has arguments α, numeral, instance. The instance is not a numeral.
      const numeral = expr.args[1];
      if (!numeral) return UNKNOWN('Missing numeral.');
      const value = evaluate(numeral, env, depth + 1);
      if (vectorDomain && value.status === 'value' && typeof value.value === 'number') {
        if (!expr.dimension || !Number.isSafeInteger(expr.dimension) || expr.dimension < 1 || expr.dimension > MAX_NUMERICAL_DIMENSION) return UNKNOWN(`The numerical zero-vector dimension must be between 1 and ${MAX_NUMERICAL_DIMENSION}.`);
        if (value.value !== 0) return UNKNOWN('Only the zero vector has an audited numeral interpretation.');
        return result(Array.from({ length: expr.dimension }, () => 0));
      }
      return value;
    }
    if (op === 'pair') {
      const values = expr.args.slice(-2).map(a => evaluate(a, env, depth + 1));
      if (values.length === 2 && values.every(v => v.status === 'value' && typeof v.value === 'number')) {
        return result(values.map(v => (v as { status: 'value'; value: number }).value));
      }
      return UNKNOWN('Both point coordinates need numerical values.');
    }
    if (op === 'proj1' || op === 'proj2') {
      const arg = expr.args.at(-1);
      if (!arg) return UNKNOWN('Missing point.');
      const value = evaluate(arg, env, depth + 1);
      return value.status === 'value' && isPoint(value.value) && value.value.length === 2
        ? result(value.value[op === 'proj1' ? 0 : 1]!) : UNKNOWN('Projection requires a two-coordinate point.');
    }
    if ((name === 'dist' || name === 'Dist.dist') && expr.metric && expr.metric !== 'unknown') {
      const args = expr.args.slice(-2);
      const left = args[0] && evaluate(args[0], env, depth + 1);
      const right = args[1] && evaluate(args[1], env, depth + 1);
      if (left?.status !== 'value' || right?.status !== 'value') return UNKNOWN('Distance arguments need numerical values.');
      const distance = metricDistance(expr.metric, left.value, right.value, expr.dimension);
      return distance === undefined ? UNKNOWN('Point dimensions do not match the recognized metric.') : result(distance);
    }
    if (!op || ['lt', 'le', 'eq', 'ne'].includes(op)) return UNKNOWN('No audited numerical interpretation is available for this expression.');
    if (expr.domain !== 'real' && expr.type !== 'ℝ' && expr.type !== 'Real') return UNKNOWN('Arithmetic evaluation is restricted to standard real operations.');
    const unary = op === 'neg' || op === 'abs';
    const args = expr.args.slice(unary ? -1 : -2);
    const values = args.map(a => evaluate(a, env, depth + 1));
    const missing = values.find(v => v.status === 'unknown');
    if (missing) return missing;
    if (values.length !== (unary ? 1 : 2) || values.some(v => v.status !== 'value' || typeof v.value !== 'number')) {
      return UNKNOWN('This operation is supported only for scalar numerical values.');
    }
    const a = (values[0] as { value: number }).value;
    const b = unary ? 0 : (values[1] as { value: number }).value;
    switch (op) {
      case 'add': return result(a + b);
      case 'sub': return result(a - b);
      case 'mul': return result(a * b);
      case 'div': return result(b === 0 ? 0 : a / b); // Lean's field division is totalized at zero.
      case 'neg': return result(-a);
      case 'abs': return result(Math.abs(a));
      case 'min': return result(Math.min(a, b));
      case 'max': return result(Math.max(a, b));
      case 'pow':
        if (!Number.isSafeInteger(b) || b < 0 || b > 1000) return UNKNOWN('Only natural-number powers up to 1000 are supported.');
        return result(a ** b);
      default: return UNKNOWN('Unsupported numerical operation.');
    }
  };
  return evaluate(expression, scenario, 0);
}

/** Near-but-unequal floating values are not silently rounded into a satisfied condition. */
export function compareNumbers(left: number, right: number, relation: 'lt' | 'le' | 'eq' | 'ne'): PredicateResult {
  if (!Number.isFinite(left) || !Number.isFinite(right)) return { status: 'unknown', reason: 'The comparison is outside the finite numerical range.' };
  const uncertainty = Number.EPSILON * 32 * Math.max(Math.abs(left), Math.abs(right), Number.MIN_VALUE);
  if (left !== right && Math.abs(left - right) <= uncertainty) return { status: 'unknown', reason: 'This sample is too close to the boundary for a reliable floating-point comparison.' };
  const holds = relation === 'lt' ? left < right : relation === 'le' ? left <= right : relation === 'eq' ? left === right : left !== right;
  return { status: holds ? 'true' : 'false', approximate: true, explanation: `${holds ? 'Holds' : 'Does not hold'} at the current numerical sample. This does not prove the statement.` };
}

export function evaluatePredicate(expression: Expr | StatementNode, scenario: Scenario = {}): PredicateResult {
  let visits = 0;
  const unknown = (reason: string): PredicateResult => ({ status: 'unknown', reason });
  const negate = (value: PredicateResult): PredicateResult => value.status === 'unknown' ? value : { ...value, status: value.status === 'true' ? 'false' : 'true', explanation: `The negated condition ${value.status === 'true' ? 'does not hold' : 'holds'} at this numerical sample.` };
  const combine = (kind: string, a: PredicateResult, b: PredicateResult): PredicateResult => {
    if (kind === 'implies') return combine('or', negate(a), b);
    if (kind === 'and' && (a.status === 'false' || b.status === 'false')) return { status: 'false', approximate: true, explanation: 'A conjunct does not hold at this sample.' };
    if (kind === 'or' && (a.status === 'true' || b.status === 'true')) return { status: 'true', approximate: true, explanation: 'A disjunct holds at this sample.' };
    if (a.status === 'unknown') return a;
    if (b.status === 'unknown') return b;
    return { status: (kind === 'iff' ? a.status === b.status : kind === 'and' ? a.status === 'true' && b.status === 'true' : a.status === 'true' || b.status === 'true') ? 'true' : 'false', approximate: true, explanation: 'Evaluated only at the current numerical sample.' };
  };
  const evaluate = (input: Expr | StatementNode, depth: number): PredicateResult => {
    if (depth > MAX_DEPTH || ++visits > 10_000) return unknown('Predicate exceeds the evaluator limit.');
    if ('children' in input) {
      if (input.kind === 'forall' || input.kind === 'exists') return unknown('An individual sample cannot establish a quantified statement.');
      if (input.kind === 'predicate') return evaluate(input.expression, depth + 1);
      if (input.kind === 'not' && input.children[0]) return negate(evaluate(input.children[0], depth + 1));
      if (input.children.length >= 2) return combine(input.kind, evaluate(input.children[0]!, depth + 1), evaluate(input.children[1]!, depth + 1));
      return unknown('Incomplete logical expression.');
    }
    if (input.kind === 'const' && (input.name === 'True' || input.name === 'False')) return { status: input.name === 'True' ? 'true' : 'false', approximate: true, explanation: 'Logical constant.' };
    if (input.kind !== 'app') return unknown('No audited sample evaluation is available for this predicate.');
    const name = headName(input);
    const args = input.args;
    if (name === 'Not' && args.at(-1)) return negate(evaluate(args.at(-1)!, depth + 1));
    if (name && ['And', 'Or', 'Iff'].includes(name) && args.length >= 2) return combine(name.toLowerCase(), evaluate(args.at(-2)!, depth + 1), evaluate(args.at(-1)!, depth + 1));
    const op = numericOperator(input);
    if (op && ['lt', 'le', 'eq', 'ne'].includes(op)) {
      if (args.length < 2) return unknown('Missing comparison argument.');
      const compared = comparisonArguments(input)!;
      const a = evaluateExpression(compared[0], scenario);
      const b = evaluateExpression(compared[1], scenario);
      if (a.status !== 'value') return a;
      if (b.status !== 'value') return b;
      if (typeof a.value === 'number' && typeof b.value === 'number') return compareNumbers(a.value, b.value, op as 'lt' | 'le' | 'eq' | 'ne');
      if ((op === 'eq' || op === 'ne') && isPoint(a.value) && isPoint(b.value) && a.value.length === b.value.length) {
        const comparisons = a.value.map((v, i) => compareNumbers(v, (b.value as number[])[i]!, 'eq'));
        const equality = comparisons.reduce((a, b) => combine('and', a, b), { status: 'true', approximate: true, explanation: 'Coordinate equality at this sample.' } as PredicateResult);
        return op === 'eq' ? equality : negate(equality);
      }
      return unknown('Comparison arguments have incompatible numerical domains.');
    }
    if (((name === 'Membership.mem' && input.standard === true) || name === 'Set.Mem') && args.length >= 2) {
      const set = args.at(-2)!;
      const point = args.at(-1)!;
      const setName = headName(set);
      if (set.kind === 'app' && set.metric && set.metric !== 'unknown' && ['Metric.ball', 'Metric.closedBall', 'Metric.sphere'].includes(setName ?? '')) {
        const center = set.args.at(-2), radius = set.args.at(-1);
        if (!center || !radius) return unknown('Incomplete metric set.');
        const c = evaluateExpression(center, scenario), r = evaluateExpression(radius, scenario), p = evaluateExpression(point, scenario);
        if (c.status !== 'value' || r.status !== 'value' || p.status !== 'value' || typeof r.value !== 'number') return unknown('Choose numerical values for the point, center, and radius.');
        const d = metricDistance(set.metric, c.value, p.value, set.dimension);
        return d === undefined ? unknown('Point dimensions do not match the recognized metric.') : compareNumbers(d, r.value, setName === 'Metric.ball' ? 'lt' : setName === 'Metric.closedBall' ? 'le' : 'eq');
      }
    }
    return unknown('No audited sample evaluation is available for this predicate.');
  };
  return evaluate(expression, 0);
}

export function expressionVariables(expr: Expr): string[] {
  const ids = new Set<string>();
  const walk = (e: Expr, depth: number): void => {
    if (depth > MAX_DEPTH) return;
    if (e.kind === 'var') ids.add(e.id);
    if (e.kind === 'app') { walk(e.fn, depth + 1); e.args.forEach(arg => walk(arg, depth + 1)); }
    if (e.kind === 'lambda' || e.kind === 'forall') { walk(e.body, depth + 1); ids.delete(e.binder.id); }
  };
  walk(expr, 0);
  return [...ids];
}
