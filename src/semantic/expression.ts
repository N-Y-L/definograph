import { headName, numericOperator } from '../core/expression';
import type { Expr } from '../core/types';

/** Flatten application association, while preserving the elaborator's argument order. */
export function applicationParts(expr: Expr): { fn: Expr; args: Expr[] } {
  if (expr.kind !== 'app') return { fn: expr, args: [] };
  const inner = applicationParts(expr.fn);
  return { fn: inner.fn, args: [...inner.args, ...expr.args] };
}

/** Proposition expressions inhabit Prop (a sort), so Lean correctly marks them as
 * type arguments. They are still mathematical inputs to a higher-order predicate.
 * A dependent forall is a proposition precisely when its body is a proposition. */
function propositionArgument(expr: Expr, depth = 0): boolean {
  if (depth > 80) return false;
  if ('typeDescriptor' in expr && expr.typeDescriptor?.kind === 'proposition') return true;
  return expr.kind === 'forall' && propositionArgument(expr.body, depth + 1);
}

export function visibleApplicationArguments(expr: Extract<Expr, { kind: 'app' }>): Expr[] {
  return expr.args.filter((argument, index) => !expr.argumentKinds || expr.argumentKinds[index] === 'value'
    || expr.argumentKinds[index] === 'type' && propositionArgument(argument));
}

export function expressionKey(expr: Expr, identities: ReadonlyMap<string, string> = new Map(), depth = 0): string {
  if (depth > 128) return 'depth-limit';
  const key = (e: Expr) => expressionKey(e, identities, depth + 1);
  switch (expr.kind) {
    case 'var': return `var:${identities.get(expr.id) ?? expr.id}`;
    case 'const': return expr.levels?.length ? JSON.stringify(['const', expr.name, expr.levels]) : `const:${expr.name}`;
    case 'literal': return `literal:${typeof expr.value}:${expr.value}`;
    case 'sort': return `sort:${expr.name}`;
    case 'opaque': return `opaque:${expr.text}`;
    case 'app': {
      const { fn, args } = applicationParts(expr);
      // Audited metric and operation metadata are part of meaning, not a rendering hint.
      return JSON.stringify(['app', key(fn), args.map(key), expr.metric ?? null, expr.metricInstance ?? null, expr.dimension ?? null, expr.standard ?? null, expr.operator ?? null]);
    }
    case 'forall': case 'lambda': {
      const local = new Map(identities);
      local.set(expr.binder.id, `local:${depth}`);
      const type = expr.binderType ?? expr.binder.typeExpression;
      return JSON.stringify([expr.kind, type ? key(type) : expr.binder.type, expressionKey(expr.body, local, depth + 1)]);
    }
  }
}

/** Stable compact ids. The compiler additionally resolves collisions by comparing full keys. */
export function stableHash(text: string): string {
  let a = 2166136261, b = 5381;
  for (let i = 0; i < text.length; i++) { a = Math.imul(a ^ text.charCodeAt(i), 16777619); b = Math.imul(b, 33) ^ text.charCodeAt(i); }
  return `${(a >>> 0).toString(36)}${(b >>> 0).toString(36)}`;
}

export function formatExpression(expr: Expr, depth = 0): string {
  if (depth > 5) return '…';
  const format = (e: Expr) => formatExpression(e, depth + 1);
  switch (expr.kind) {
    case 'var': return expr.name;
    case 'const': return expr.name;
    case 'literal': return String(expr.value);
    case 'opaque': return expr.text.length > 90 ? `${expr.text.slice(0, 87)}…` : expr.text;
    case 'sort': return expr.name === '0' || expr.name === 'Prop' ? 'Prop' : expr.name === '1' || expr.name === 'Type' ? 'Type' : `Sort (${expr.name})`;
    case 'forall': return `∀ ${expr.binder.name}, ${format(expr.body)}`;
    case 'lambda': return `${expr.binder.name} ↦ ${format(expr.body)}`;
    case 'app': {
      const name = headName(expr);
      const op = numericOperator(expr);
      const argumentValues = visibleApplicationArguments(expr);
      const isPartial = expr.typeDescriptor?.kind === 'map' || expr.typeDescriptor?.kind === 'relation';
      if (!isPartial && op === 'ofNat' && expr.args[1]) return format(expr.args[1]);
      const symbols: Record<string, string> = { add: '+', sub: '−', mul: '·', div: '/', pow: '^', eq: '=', ne: '≠', lt: '<', le: '≤' };
      if (!isPartial && op && symbols[op] && argumentValues.length >= 2) return `${format(expr.args.at(-2)!)} ${symbols[op]} ${format(expr.args.at(-1)!)}`;
      if (!isPartial && op === 'neg' && argumentValues.length) return `−${format(expr.args.at(-1)!)}`;
      if (!isPartial && op === 'abs' && argumentValues.length) return `|${format(expr.args.at(-1)!)}|`;
      const count = !isPartial && name?.startsWith('Metric.') ? 2 : !isPartial && name?.startsWith('Function.') ? 1 : undefined;
      const args = count && !expr.argumentKinds ? expr.args.slice(-count) : argumentValues;
      return `${format(expr.fn)}(${args.slice(0, 5).map(format).join(', ')}${args.length > 5 ? ', …' : ''})`;
    }
  }
}
