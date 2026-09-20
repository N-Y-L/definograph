import { headName, numericOperator } from '../core/expression';
import type { Binder, Expr, StatementNode } from '../core/types';
import type { SetOperation } from './types';
import { graphSemanticPlugin } from '../graphs/semantics';

/** Recover the exact exported binder type without parsing the printed Lean type. */
export function binderTypeExpression(node: StatementNode, binder: Binder): Expr | undefined {
  if (binder.typeExpression) return binder.typeExpression;
  const expression = node.expression;
  if ((expression.kind === 'forall' || expression.kind === 'lambda') && expression.binder.id === binder.id) return expression.binderType ?? expression.binder.typeExpression;
  if (node.kind === 'exists' && expression.kind === 'app') {
    const { fn, args } = applicationParts(expression);
    if (headName(fn) === 'Exists' && args.length === 2) {
      const body = args[1];
      if (body.kind === 'lambda' && body.binder.id === binder.id) return body.binderType ?? args[0];
    }
  }
}

/** Exact constructor semantics from Mathlib.Data.Set.Defs. Overloaded notation
 * requires the exporter's canonical-instance audit and a Set result type. */
export function setConstructionParts(expr: Expr): { operation: SetOperation; operands: readonly Expr[] } | undefined {
  if (expr.kind !== 'app') return;
  const name = headName(expr);
  const direct: Record<string, SetOperation> = { 'Set.union': 'union', 'Set.inter': 'intersection', 'Set.diff': 'difference', 'Set.compl': 'complement' };
  const overloaded: Record<string, SetOperation> = { 'Union.union': 'union', 'Inter.inter': 'intersection', 'SDiff.sdiff': 'difference', 'Compl.compl': 'complement' };
  const operation = name && (direct[name] ?? overloaded[name]);
  if (!operation) return;
  if (overloaded[name!] && (expr.standard !== true || expr.typeDescriptor?.kind !== 'set')) return;
  if (expr.typeDescriptor && expr.typeDescriptor.kind !== 'set') return;
  if (expr.argumentKinds && expr.argumentKinds.length !== expr.args.length) return;
  const operands = expr.argumentKinds ? expr.args.filter((_, index) => expr.argumentKinds![index] === 'value') : expr.args;
  if (operands.length !== (operation === 'complement' ? 1 : 2)) return;
  return { operation, operands };
}

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
  type KeyData = string | number | boolean | null | KeyData[];
  // Build a structural value, then serialize once. Serializing child keys as
  // strings repeatedly escaped their quotes and grew exponentially with depth.
  const encode = (current: Expr, names: ReadonlyMap<string, string>, level: number): KeyData => {
    if (level > 128) return 'depth-limit';
    const key = (child: Expr) => encode(child, names, level + 1);
    switch (current.kind) {
      case 'var': return `var:${names.get(current.id) ?? current.id}`;
      case 'const': return current.levels?.length ? ['const', current.name, current.levels] : `const:${current.name}`;
      case 'literal': return `literal:${typeof current.value}:${current.value}`;
      case 'sort': return `sort:${current.name}`;
      case 'opaque': return `opaque:${current.text}`;
      case 'app': {
        const { fn, args } = applicationParts(current);
        return ['app', key(fn), args.map(key), current.metric ?? null, current.metricInstance ?? null, current.dimension ?? null, current.standard ?? null, current.operator ?? null];
      }
      case 'forall': case 'lambda': {
        const local = new Map(names);
        local.set(current.binder.id, `local:${level}`);
        const type = current.binderType ?? current.binder.typeExpression;
        return [current.kind, type ? key(type) : current.binder.type, encode(current.body, local, level + 1)];
      }
    }
  };
  const data = encode(expr, identities, depth);
  return typeof data === 'string' ? data : JSON.stringify(data);
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
      const graph = graphSemanticPlugin.match(expr);
      if (graph?.kind === 'graph-coloring' || graph?.kind === 'graph-map') {
        const map = graph.arguments.find(port => port.role === (graph.kind === 'graph-coloring' ? 'coloring' : 'map'))?.expression;
        const vertex = graph.arguments.find(port => port.role === (graph.kind === 'graph-coloring' ? 'vertex' : 'source vertex'))?.expression;
        if (map && vertex) return `${format(map)}(${format(vertex)})`;
      }
      const set = setConstructionParts(expr);
      if (set) return set.operation === 'complement' ? `${format(set.operands[0])}ᶜ` : `(${format(set.operands[0])} ${{ union: '∪', intersection: '∩', difference: '∖' }[set.operation]} ${format(set.operands[1])})`;
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
