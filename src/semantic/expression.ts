import { headName, numericOperator } from '../core/expression';
import type { Binder, Expr, StatementNode } from '../core/types';
import type { SetOperation } from './types';
import { graphSemanticPlugin } from '../graphs/semantics';
import { restrictedMapParts } from '../restricted/semantics';

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

/** Accept only the bounded, checked type view; original names and types stay on
 * the binder. This exposes aliases without a visual rule for each user name. */
export function checkedBinderTypeExpansion(binder: Binder): Expr | undefined {
  const expansion = binder.typeExpansion;
  if (!expansion || expansion.definitionalEquality !== true || expansion.maxDepth !== 2 || expansion.before !== binder.type
    || !expansion.constants.length || expansion.constants.length > 2 || expansion.constants.some(name => !name || name.length > 512)
    || JSON.stringify(expansion).length > 65_536) return;
  let size = 0;
  const bounded = (expr: Expr, depth = 0, instance = false): boolean => {
    if (depth > 24 || ++size > 80) return false;
    if (expr.kind === 'opaque') return instance;
    if (expr.kind === 'app') return bounded(expr.fn, depth + 1) && expr.args.every((arg, index) => bounded(arg, depth + 1, expr.argumentKinds?.[index] === 'instance'));
    if (expr.kind === 'forall' || expr.kind === 'lambda') {
      const type = expr.binderType ?? expr.binder.typeExpression;
      return Boolean(type && bounded(type, depth + 1) && bounded(expr.body, depth + 1));
    }
    return true;
  };
  return bounded(expansion.expression) ? expansion.expression : undefined;
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

/** The positions of the arguments a reader sees: values and propositions, or every argument when no kinds were exported. */
function visibleArgumentIndices(expr: Extract<Expr, { kind: 'app' }>): number[] {
  return expr.args.flatMap((argument, index) => !expr.argumentKinds || expr.argumentKinds[index] === 'value'
    || expr.argumentKinds[index] === 'type' && propositionArgument(argument) ? [index] : []);
}

export function visibleApplicationArguments(expr: Extract<Expr, { kind: 'app' }>): Expr[] {
  return visibleArgumentIndices(expr).map(index => expr.args[index]!);
}

export function expressionKey(expr: Expr, identities: ReadonlyMap<string, string> = new Map(), depth = 0): string {
  type KeyData = string | number | boolean | null | KeyData[];
  // Build a structural value, then serialize once. Serializing child keys as
  // strings repeatedly escaped their quotes and grew exponentially with depth.
  const encode = (current: Expr, names: ReadonlyMap<string, string>, level: number): KeyData => {
    if (current.exactIdentity !== undefined) return ['exact', current.exactIdentity];
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

/** How tightly a written label holds together: an operand whose level is too low for its position is bracketed. */
interface FormattedExpression { text: string; level: number }
/** A name, a literal, a call written `f(x)`, a bracketed or barred label: never split by a neighbouring operator. */
const ATOMIC = 1024;
/** `∀ x, …` and `x ↦ …` extend as far right as they can, so they are bracketed wherever they are an operand. */
const BINDING = 0;
/** Lean 4.28.0's own levels for these notations (`Init/Notation.lean`, `Init/Core.lean`): `infixl:65` for + and −,
 * `infixl:70` for * and /, `infixr:80` for ^, `infix:50` for =, ≠, <, ≤, > and ≥, and `prefix:75` for negation. */
const binaryNotation: Record<string, { symbol: string; level: number; associativity: 'left' | 'right' | 'none' }> = {
  add: { symbol: '+', level: 65, associativity: 'left' }, sub: { symbol: '−', level: 65, associativity: 'left' },
  mul: { symbol: '·', level: 70, associativity: 'left' }, div: { symbol: '/', level: 70, associativity: 'left' },
  pow: { symbol: '^', level: 80, associativity: 'right' },
  eq: { symbol: '=', level: 50, associativity: 'none' }, ne: { symbol: '≠', level: 50, associativity: 'none' },
  lt: { symbol: '<', level: 50, associativity: 'none' }, le: { symbol: '≤', level: 50, associativity: 'none' },
};
const NEGATION = 75;
/** `¬` and `!` take their argument at level 40, so text that opens with one is bracketed wherever a relation could
 * otherwise extend it. */
const PREFIX_PROPOSITION = 40;
/** `GT.gt a b` and `GE.ge a b` keep their own symbol and argument order; they are not rewritten as `b < a`. */
const reversedComparison: Record<string, string> = { 'GT.gt': '>', 'GE.ge': '≥' };
const bracketed = (operand: FormattedExpression, needed: boolean) => needed ? `(${operand.text})` : operand.text;

/** A one-line label for an expression. Every operator label shows exactly the grouping of the term: an operand is
 * bracketed whenever Lean's own precedence and associativity would otherwise read the label with another grouping,
 * so `(a + b) · c` and `a + b · c` never share a label. */
export function formatExpression(expr: Expr, depth = 0): string {
  return formatWithLevel(expr, depth).text;
}

function formatWithLevel(expr: Expr, depth: number): FormattedExpression {
  // The packet path's display text brackets every application and binder itself (packets/syntax.ts).
  if (expr.exactIdentity !== undefined && expr.displayText !== undefined) return { text: expr.displayText, level: ATOMIC };
  if (depth > 5) return { text: '…', level: ATOMIC };
  const format = (e: Expr) => formatWithLevel(e, depth + 1);
  const atomic = (text: string): FormattedExpression => ({ text, level: ATOMIC });
  /** An operand that must hold together as one unit, such as a called function or what a postfix mark applies to. */
  const unit = (e: Expr) => { const operand = format(e); return bracketed(operand, operand.level < ATOMIC); };
  switch (expr.kind) {
    case 'var': return atomic(expr.name);
    case 'const': return atomic(expr.name);
    case 'literal': {
      // A string value is a Lean string, or a natural number kept as decimal text to stay exact; the value alone does
      // not say which (notation/math-display.ts). Text that is not a decimal numeral can only be a Lean string, so it
      // keeps its quotes; a numeral stays as it is.
      if (typeof expr.value === 'string' && !/^\d+$/.test(expr.value)) return atomic(JSON.stringify(expr.value));
      const text = String(expr.value);
      return { text, level: text.startsWith('-') ? NEGATION : ATOMIC };
    }
    case 'opaque': {
      // Lean's printed text of a part without inspectable structure. It holds together as an operand only when it is
      // one word that does not open with a prefix operator: `¬p` and `!b` take what follows down to level 40
      // (`notation:max "¬" p:40`, `notation:max "!" b:40`), and `-x` is `prefix:75`.
      const text = expr.text.length > 90 ? `${expr.text.slice(0, 87)}…` : expr.text;
      return { text, level: /\s/.test(text) ? BINDING : /^[¬!]/.test(text) ? PREFIX_PROPOSITION : /^[-−]/.test(text) ? NEGATION : ATOMIC };
    }
    case 'sort': return atomic(expr.name === '0' || expr.name === 'Prop' ? 'Prop' : expr.name === '1' || expr.name === 'Type' ? 'Type' : `Sort (${expr.name})`);
    case 'forall': return { text: `∀ ${expr.binder.name}, ${format(expr.body).text}`, level: BINDING };
    case 'lambda': return { text: `${expr.binder.name} ↦ ${format(expr.body).text}`, level: BINDING };
    case 'app': {
      const restricted = restrictedMapParts(expr);
      if (restricted?.region) return atomic(`${unit(restricted.map)}.${restricted.region}`);
      if (restricted?.input) return atomic(`${unit(restricted.map)}${restricted.direction === 'inverse' ? '.symm' : ''}(${format(restricted.input).text})`);
      const graph = graphSemanticPlugin.match(expr);
      if (graph?.kind === 'graph-coloring' || graph?.kind === 'graph-map') {
        const map = graph.arguments.find(port => port.role === (graph.kind === 'graph-coloring' ? 'coloring' : 'map'))?.expression;
        const vertex = graph.arguments.find(port => port.role === (graph.kind === 'graph-coloring' ? 'vertex' : 'source vertex'))?.expression;
        if (map && vertex) return atomic(`${unit(map)}(${format(vertex).text})`);
      }
      const set = setConstructionParts(expr);
      if (set) return atomic(set.operation === 'complement' ? `${unit(set.operands[0])}ᶜ` : `(${format(set.operands[0]).text} ${{ union: '∪', intersection: '∩', difference: '∖' }[set.operation]} ${format(set.operands[1]).text})`);
      const name = headName(expr);
      const op = numericOperator(expr);
      const visible = visibleArgumentIndices(expr);
      const argumentValues = visible.map(index => expr.args[index]!);
      const isPartial = expr.typeDescriptor?.kind === 'map' || expr.typeDescriptor?.kind === 'relation';
      // An operator applied to more than its own arguments, such as `(f + g) x` for functions f and g: the operator part
      // is written on its own arguments, bracketed, and applied to the rest. Only exported argument kinds say where an
      // operator's own arguments end.
      const kinds = expr.argumentKinds?.length === expr.args.length;
      const applied = (end: number): FormattedExpression => {
        const head: Extract<Expr, { kind: 'app' }> = { ...expr, args: expr.args.slice(0, end), argumentKinds: expr.argumentKinds?.slice(0, end) };
        // The recorded type is the whole application's, not the operator part's.
        delete head.typeDescriptor; delete head.type;
        const rest = visible.filter(index => index >= end).map(index => format(expr.args[index]!).text);
        return atomic(`${unit(head)}(${rest.slice(0, 5).join(', ')}${rest.length > 5 ? ', …' : ''})`);
      };
      if (!isPartial && op === 'ofNat' && expr.args[1]) return kinds && expr.args.length > 3 ? applied(3) : format(expr.args[1]);
      const notation = op ? binaryNotation[op] : undefined;
      if (!isPartial && notation && argumentValues.length >= 2) {
        if (kinds && argumentValues.length > 2) return applied(visible[1]! + 1);
        const left = format(argumentValues.at(-2)!), right = format(argumentValues.at(-1)!);
        // A left-associative operator reads `a − b − c` as `(a − b) − c`, so only its right operand is bracketed at its
        // own level; a right-associative one the reverse; a relation brackets both.
        const leftNeeds = notation.associativity === 'left' ? left.level < notation.level : left.level <= notation.level;
        const rightNeeds = notation.associativity === 'right' ? right.level < notation.level : right.level <= notation.level;
        const symbol = (name && reversedComparison[name]) ?? notation.symbol;
        return { text: `${bracketed(left, leftNeeds)} ${symbol} ${bracketed(right, rightNeeds)}`, level: notation.level };
      }
      if (!isPartial && (op === 'neg' || op === 'abs') && kinds && argumentValues.length > 1) return applied(visible[0]! + 1);
      if (!isPartial && op === 'neg' && argumentValues.length) {
        const operand = format(argumentValues.at(-1)!);
        return { text: `−${bracketed(operand, operand.level < NEGATION || operand.text.startsWith('−') || operand.text.startsWith('-'))}`, level: NEGATION };
      }
      if (!isPartial && op === 'abs' && argumentValues.length) return atomic(`|${format(argumentValues.at(-1)!).text}|`);
      const count = !isPartial && name?.startsWith('Metric.') ? 2 : !isPartial && name?.startsWith('Function.') ? 1 : undefined;
      const args = count && !expr.argumentKinds ? expr.args.slice(-count) : argumentValues;
      return atomic(`${unit(expr.fn)}(${args.slice(0, 5).map(arg => format(arg).text).join(', ')}${args.length > 5 ? ', …' : ''})`);
    }
  }
}
