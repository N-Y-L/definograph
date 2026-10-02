import type { Expr } from '../core/types';
import { headName, numericOperator } from '../core/expression';
import { formatExpression } from '../semantic/expression';

/** A display convention over typed syntax, not a Lean printer or an identity. */
export type MathDisplayNode =
  | { kind: 'identifier'; name: string }
  | { kind: 'literal'; value: number | string }
  | { kind: 'application'; fn: MathDisplayNode; args: readonly MathDisplayNode[] }
  | { kind: 'binary'; operator: 'add' | 'sub' | 'mul' | 'div' | 'pow' | 'eq' | 'ne' | 'lt' | 'le'; left: MathDisplayNode; right: MathDisplayNode }
  | { kind: 'unary'; operator: 'neg' | 'abs'; argument: MathDisplayNode }
  | { kind: 'script'; base: MathDisplayNode; subscript?: MathDisplayNode; superscript?: MathDisplayNode }
  | { kind: 'symbol'; symbol: 'eq' | 'ne' | 'lt' | 'le' | 'empty' }
  | { kind: 'parentheses'; body: MathDisplayNode };
export interface MathDisplay {
  readonly source: string;
  readonly latex?: string;
  /** Measurement identity only. Mathematical identities stay on their source objects. */
  readonly key: string;
  readonly prefix?: string;
  readonly suffix?: string;
  readonly unavailable?: string;
}
const MAX_NODES = 128, MAX_DEPTH = 20, MAX_TEXT = 1024, MAX_TEX = 8192;
const greek: Record<string, string> = { α: 'alpha', β: 'beta', γ: 'gamma', δ: 'delta', ε: 'varepsilon', ζ: 'zeta', η: 'eta', θ: 'theta', ι: 'iota', κ: 'kappa', λ: 'lambda', μ: 'mu', ν: 'nu', ξ: 'xi', π: 'pi', ρ: 'rho', σ: 'sigma', τ: 'tau', υ: 'upsilon', φ: 'varphi', χ: 'chi', ψ: 'psi', ω: 'omega', Γ: 'Gamma', Δ: 'Delta', Θ: 'Theta', Λ: 'Lambda', Ξ: 'Xi', Π: 'Pi', Σ: 'Sigma', Υ: 'Upsilon', Φ: 'Phi', Ψ: 'Psi', Ω: 'Omega' };
const escaped: Record<string, string> = { '\\': '\\textbackslash{}', '{': '\\{', '}': '\\}', '$': '\\$', '&': '\\&', '#': '\\#', '%': '\\%', '_': '\\_', '^': '\\textasciicircum{}', '~': '\\textasciitilde{}' };
const symbolTex = { eq: '=', ne: '\\ne', lt: '<', le: '\\le', empty: '\\varnothing' };
const symbolSource = { eq: '=', ne: '≠', lt: '<', le: '≤', empty: '∅' };
const compoundScriptBase = (node: MathDisplayNode): boolean => node.kind !== 'identifier' && node.kind !== 'parentheses'
  && !(node.kind === 'literal' && typeof node.value === 'number' && node.value >= 0)
  && !(node.kind === 'symbol' && node.symbol === 'empty');
function literalText(value: string): string {
  if (value.length > MAX_TEXT || /[\u0000-\u001f\u007f-\u009f\u202a-\u202e\u2066-\u2069]/u.test(value)) throw Error('Identifier display limit.');
  return [...value].map(char => escaped[char] ?? char).join('');
}
function identifierTex(name: string): string {
  // This is an identifier typography convention only: no word is interpreted
  // as a function/operator, and neither its spelling nor glyphs become an ID.
  literalText(name);
  const suffix = /^(.*?)([₀₁₂₃₄₅₆₇₈₉]+)$/u.exec(name);
  if (suffix?.[1]) return `{${identifierTex(suffix[1])}}_{${[...suffix[2]].map(c => '₀₁₂₃₄₅₆₇₈₉'.indexOf(c)).join('')}}`;
  if (greek[name]) return `\\${greek[name]}`;
  if (/^[A-Za-z]$/u.test(name)) return name;
  if (name === 'ℝ' || name === 'ℕ' || name === 'ℤ' || name === 'ℚ' || name === 'ℂ') return `\\mathbb{${{ 'ℝ': 'R', 'ℕ': 'N', 'ℤ': 'Z', 'ℚ': 'Q', 'ℂ': 'C' }[name]}}`;
  // KaTeX's strict text mode rejects Greek inside an otherwise literal name.
  // Segment only actual Greek glyphs; words and TeX-looking strings stay text.
  return name.split(/([αβγδεζηθικλμνξπρστυφχψωΓΔΘΛΞΠΣΥΦΨΩ])/u)
    .filter(Boolean).map(part => greek[part] ? `{\\${greek[part]}}` : `\\text{${literalText(part)}}`).join('');
}
const fallback = (source: string, reason: string): MathDisplay => ({ source, key: `source:${source}`, unavailable: reason });

export function mathDisplay(node: MathDisplayNode, readableSource?: string): MathDisplay {
  let count = 0;
  function compile(value: MathDisplayNode, depth: number): { source: string; latex: string } {
    if (++count > MAX_NODES || depth > MAX_DEPTH) throw Error('Mathematical label display limit.');
    const child = (item: MathDisplayNode) => compile(item, depth + 1);
    switch (value.kind) {
      case 'identifier': return { source: value.name, latex: identifierTex(value.name) };
      case 'literal': {
        // This display constructor distinguishes strings from numeric literals.
        // The Expr transport adapter below does not assume this from a JS string.
        const source = typeof value.value === 'string' ? JSON.stringify(value.value) : String(value.value); literalText(source);
        return { source, latex: typeof value.value === 'number' && Number.isFinite(value.value) && /^-?\d+(?:\.\d+)?$/u.test(source)
          ? source : `\\text{${literalText(source)}}` };
      }
      case 'symbol': return { source: symbolSource[value.symbol], latex: symbolTex[value.symbol] };
      case 'application': {
        if (value.args.length > 32) throw Error('Too many displayed arguments.');
        const fn = child(value.fn), args = value.args.map(child);
        return { source: `${fn.source}(${args.map(arg => arg.source).join(', ')})`, latex: `{${fn.latex}}\\left(${args.map(arg => arg.latex).join(',\\,')}\\right)` };
      }
      case 'binary': {
        const left = child(value.left), right = child(value.right), op = value.operator;
        const symbol = { add: '+', sub: '−', mul: '·', div: '/', pow: '^', ...symbolSource }[op];
        const base = compoundScriptBase(value.left) ? `\\left(${left.latex}\\right)` : left.latex;
        const sourceBase = compoundScriptBase(value.left) ? `(${left.source})` : left.source;
        const latex = op === 'div' ? `\\frac{${left.latex}}{${right.latex}}` : op === 'pow' ? `{${base}}^{${right.latex}}`
          : `\\left(${left.latex} ${{ add: '+', sub: '-', mul: '\\cdot', ...symbolTex }[op]} ${right.latex}\\right)`;
        return { source: `(${op === 'pow' ? sourceBase : left.source} ${symbol} ${right.source})`, latex };
      }
      case 'unary': {
        const arg = child(value.argument);
        return value.operator === 'abs' ? { source: `|${arg.source}|`, latex: `\\left|${arg.latex}\\right|` }
          : { source: `−(${arg.source})`, latex: `-\\left(${arg.latex}\\right)` };
      }
      case 'script': {
        const base = child(value.base), sub = value.subscript && child(value.subscript), sup = value.superscript && child(value.superscript);
        return { source: `${compoundScriptBase(value.base) ? `(${base.source})` : base.source}${sub ? `_${sub.source}` : ''}${sup ? `^${sup.source}` : ''}`,
          latex: `{${compoundScriptBase(value.base) ? `\\left(${base.latex}\\right)` : base.latex}}${sub ? `_{${sub.latex}}` : ''}${sup ? `^{${sup.latex}}` : ''}` };
      }
      case 'parentheses': { const body = child(value.body); return { source: `(${body.source})`, latex: `\\left(${body.latex}\\right)` }; }
    }
  }
  try {
    const rendered = compile(node, 0), source = readableSource ?? rendered.source;
    if (rendered.latex.length > MAX_TEX) throw Error('Mathematical label display limit.');
    return { ...rendered, source, key: `${source}\n${rendered.latex}` };
  } catch { return fallback(readableSource ?? 'Expression outside the mathematical label display limit', 'Typed mathematical notation is unavailable; the source label is retained.'); }
}
export const identifierMathDisplay = (name: string): MathDisplay => mathDisplay({ kind: 'identifier', name }, name);
export const sourceMathDisplay = (source: string): MathDisplay => fallback(source, 'No typed mathematical notation is available for this source label.');

function boundedExpression(expression: Expr): boolean {
  const pending = [{ expression, depth: 0 }]; let count = 0;
  while (pending.length) {
    const { expression: expr, depth } = pending.pop()!;
    if (++count > MAX_NODES || depth > MAX_DEPTH || !expr || typeof expr !== 'object') return false;
    if (expr.kind === 'app') {
      if (!Array.isArray(expr.args) || expr.args.length > 32) return false;
      pending.push(...[expr.fn, ...expr.args].map(expression => ({ expression, depth: depth + 1 })));
    } else if (expr.kind === 'forall' || expr.kind === 'lambda') {
      const type = expr.binderType ?? expr.binder.typeExpression;
      pending.push({ expression: expr.body, depth: depth + 1 });
      if (type) pending.push({ expression: type, depth: depth + 1 });
    }
  }
  return true;
}
export function expressionDisplayNode(expression: Expr): MathDisplayNode | undefined {
  if (!boundedExpression(expression)) return;
  let count = 0;
  function convert(expr: Expr, depth: number): MathDisplayNode {
    if (++count > MAX_NODES || depth > MAX_DEPTH) throw Error('Display limit.');
    const child = (value: Expr) => convert(value, depth + 1);
    switch (expr.kind) {
      case 'var': case 'const': return { kind: 'identifier', name: expr.name };
      case 'literal': {
        // Profile-2 positional naturals and Lean strings both use JS strings.
        // Their exact constructor-faithful displayText remains the fallback;
        // decimal spelling alone is not evidence for either constructor.
        if (typeof expr.value === 'string') throw Error('Literal constructor is not carried by Expr.value.');
        return { kind: 'literal', value: expr.value };
      }
      case 'app': {
        if (expr.args.length > 32) throw Error('Argument display limit.');
        const op = numericOperator(expr), partial = expr.typeDescriptor?.kind === 'map' || expr.typeDescriptor?.kind === 'relation';
        // Operator roles come from the existing audited exporter gate, never a label.
        // Applications outside those roles preserve every ordered exported argument.
        const values = expr.argumentKinds?.length === expr.args.length ? expr.args.filter((_, i) => expr.argumentKinds![i] === 'value') : expr.args;
        if (!partial && op && ['add', 'sub', 'mul', 'div', 'pow', 'eq', 'ne', 'lt', 'le'].includes(op) && values.length === 2) {
          const reverse = headName(expr) === 'GT.gt' || headName(expr) === 'GE.ge';
          const args = reverse ? [values[1], values[0]] : values;
          return { kind: 'binary', operator: op as Extract<MathDisplayNode, { kind: 'binary' }>['operator'], left: child(args[0]), right: child(args[1]) };
        }
        if (!partial && (op === 'neg' || op === 'abs') && values.length === 1) return { kind: 'unary', operator: op, argument: child(values[0]) };
        return { kind: 'application', fn: child(expr.fn), args: expr.args.map(child) };
      }
      default: throw Error('Unsupported expression constructor.');
    }
  }
  try { return convert(expression, 0); } catch { return undefined; }
}
export function expressionMathDisplay(expression: Expr, readableSource?: string): MathDisplay {
  const bounded = boundedExpression(expression);
  const ambiguousLiteral = (expr: Expr): boolean => {
    if (expr.displayText !== undefined) return false;
    if (expr.kind === 'literal') return typeof expr.value === 'string';
    return expr.kind === 'app' && [expr.fn, ...expr.args].some(ambiguousLiteral);
  };
  const source = expression.kind === 'literal' && typeof expression.value === 'string'
    ? expression.displayText ?? `Literal (constructor unspecified): ${JSON.stringify(expression.value)}`
    : readableSource ?? (bounded ? formatExpression(expression) : expression.displayText ?? 'Expression outside the mathematical label display limit');
  const node = bounded ? expressionDisplayNode(expression) : undefined;
  return node ? mathDisplay(node, source) : sourceMathDisplay(bounded && expression.kind !== 'literal' && ambiguousLiteral(expression)
    ? `${source} [literal constructor unspecified]` : source);
}
/** Prose around a mathematical label stays ordinary HTML text. */
export function withMathProse(label: MathDisplay, prefix = '', suffix = ''): MathDisplay {
  return { ...label, source: `${prefix}${label.source}${suffix}`, key: `${prefix}\n${label.key}\n${suffix}`, prefix, suffix };
}
