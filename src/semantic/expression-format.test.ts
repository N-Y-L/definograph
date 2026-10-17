import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument, formatExpression } from './index';

/** Expressions shaped as the Lean exporter writes them: the head constant, the implicit types and the instance first,
 * the two values last, and the instance audit's verdict in `standard`. */
const real: Expr = { kind: 'const', name: 'Real' };
const instance: Expr = { kind: 'opaque', text: 'instHAdd' };
const variable = (name: string): Expr => ({ kind: 'var', id: name, name, type: 'ℝ' });
const [a, b, c, d] = ['a', 'b', 'c', 'd'].map(variable) as [Expr, Expr, Expr, Expr];
const heads = { add: 'HAdd.hAdd', sub: 'HSub.hSub', mul: 'HMul.hMul', div: 'HDiv.hDiv', pow: 'HPow.hPow' } as const;
type Operation = keyof typeof heads;
const binary = (operation: Operation, left: Expr, right: Expr): Expr => ({ kind: 'app', fn: { kind: 'const', name: heads[operation] }, standard: true,
  args: [real, real, real, instance, left, right], argumentKinds: ['type', 'type', 'type', 'instance', 'value', 'value'] });
const negate = (operand: Expr): Expr => ({ kind: 'app', fn: { kind: 'const', name: 'Neg.neg' }, standard: true, args: [real, instance, operand], argumentKinds: ['type', 'instance', 'value'] });
const relation = (head: 'Eq' | 'Ne' | 'LT.lt' | 'LE.le' | 'GT.gt' | 'GE.ge', left: Expr, right: Expr): Expr => head === 'Eq' || head === 'Ne'
  ? { kind: 'app', fn: { kind: 'const', name: head }, args: [real, left, right], argumentKinds: ['type', 'value', 'value'] }
  : { kind: 'app', fn: { kind: 'const', name: head }, standard: true, args: [real, instance, left, right], argumentKinds: ['type', 'instance', 'value', 'value'] };
const [add, sub, mul, pow] = (['add', 'sub', 'mul', 'pow'] as const).map(operation => (left: Expr, right: Expr) => binary(operation, left, right));

/** The grouping of a term, written with every bracket. */
type Tree = string | { op: string; left: Tree; right: Tree } | { op: 'neg'; operand: Tree };
const symbols: Record<string, string> = { add: '+', sub: '−', mul: '·', div: '/', pow: '^', eq: '=', ne: '≠', lt: '<', le: '≤', gt: '>', ge: '≥' };
const relationHeads: Record<string, 'Eq' | 'Ne' | 'LT.lt' | 'LE.le' | 'GT.gt' | 'GE.ge'> = { eq: 'Eq', ne: 'Ne', lt: 'LT.lt', le: 'LE.le', gt: 'GT.gt', ge: 'GE.ge' };
const toExpr = (tree: Tree): Expr => typeof tree === 'string' ? variable(tree) : 'operand' in tree ? negate(toExpr(tree.operand))
  : relationHeads[tree.op] ? relation(relationHeads[tree.op]!, toExpr(tree.left), toExpr(tree.right)) : binary(tree.op as Operation, toExpr(tree.left), toExpr(tree.right));
const show = (tree: Tree): string => typeof tree === 'string' ? tree : 'operand' in tree ? `(−${show(tree.operand)})` : `(${show(tree.left)} ${symbols[tree.op]} ${show(tree.right)})`;

/** Reads a label back with Lean 4.28.0's levels and associativity (Init/Notation.lean): an independent parser, so the
 * label must carry the grouping on its own. */
function readLabel(label: string): Tree {
  const tokens = label.match(/[a-z]+|[()+−·/^=≠<≤>≥]/g) ?? [];
  expect(tokens.join('')).toBe(label.replace(/\s+/g, ''));
  const infix: Record<string, { op: string; level: number; associativity: 'left' | 'right' | 'none' }> = {
    '+': { op: 'add', level: 65, associativity: 'left' }, '−': { op: 'sub', level: 65, associativity: 'left' },
    '·': { op: 'mul', level: 70, associativity: 'left' }, '/': { op: 'div', level: 70, associativity: 'left' }, '^': { op: 'pow', level: 80, associativity: 'right' },
    '=': { op: 'eq', level: 50, associativity: 'none' }, '≠': { op: 'ne', level: 50, associativity: 'none' }, '<': { op: 'lt', level: 50, associativity: 'none' },
    '≤': { op: 'le', level: 50, associativity: 'none' }, '>': { op: 'gt', level: 50, associativity: 'none' }, '≥': { op: 'ge', level: 50, associativity: 'none' },
  };
  let position = 0;
  const parse = (minimum: number): Tree => {
    let left: Tree;
    const token = tokens[position++];
    if (token === '(') { left = parse(0); expect(tokens[position++]).toBe(')'); }
    else if (token === '−') left = { op: 'neg', operand: parse(75) };
    else { expect(token).toMatch(/^[a-z]+$/); left = token!; }
    for (;;) {
      const next = infix[tokens[position] ?? ''];
      if (!next || next.level < minimum) return left;
      position++;
      const right = parse(next.associativity === 'right' ? next.level : next.level + 1);
      left = { op: next.op, left, right };
      // A non-associative relation does not take a second relation at its own level.
      if (next.associativity === 'none' && infix[tokens[position] ?? '']?.level === next.level) throw new Error(`ambiguous relation chain: ${label}`);
    }
  };
  const tree = parse(0);
  expect(position).toBe(tokens.length);
  return tree;
}

describe('expression labels show exactly the grouping of the term', () => {
  it('brackets an operand where precedence or associativity would otherwise regroup it', () => {
    expect(formatExpression(mul(add(a, b), c))).toBe('(a + b) · c');
    expect(formatExpression(add(a, mul(b, c)))).toBe('a + b · c');
    expect(formatExpression(sub(a, sub(b, c)))).toBe('a − (b − c)');
    expect(formatExpression(sub(sub(a, b), c))).toBe('a − b − c');
    expect(formatExpression(pow(a, pow(b, c)))).toBe('a ^ b ^ c');
    expect(formatExpression(pow(pow(a, b), c))).toBe('(a ^ b) ^ c');
    expect(formatExpression(negate(add(a, b)))).toBe('−(a + b)');
    expect(formatExpression(add(negate(a), b))).toBe('−a + b');
    expect(formatExpression(pow(negate(a), b))).toBe('(−a) ^ b');
    expect(formatExpression(negate(pow(a, b)))).toBe('−a ^ b');
    expect(formatExpression(negate(negate(a)))).toBe('−(−a)');
    // Grouping that associativity makes harmless is still shown: the label is of the term, not of its value.
    expect(formatExpression(add(a, add(b, c)))).toBe('a + (b + c)');
  });

  it('brackets relations whose sides are sums, and relations used as operands', () => {
    expect(formatExpression(relation('Eq', add(a, b), add(c, d)))).toBe('a + b = c + d');
    expect(formatExpression(relation('LT.lt', mul(add(a, b), c), add(a, mul(b, c))))).toBe('(a + b) · c < a + b · c');
    expect(formatExpression(relation('Eq', relation('Eq', a, b), relation('Eq', c, d)))).toBe('(a = b) = (c = d)');
    expect(formatExpression(relation('Ne', sub(a, b), sub(b, a)))).toBe('a − b ≠ b − a');
  });

  it('keeps the symbol and argument order of > and ≥', () => {
    // `GT.gt a b` is Lean's `a > b`. Writing it `a < b` reversed the claim.
    expect(formatExpression(relation('GT.gt', add(a, b), c))).toBe('a + b > c');
    expect(formatExpression(relation('GE.ge', a, b))).toBe('a ≥ b');
    expect(formatExpression(relation('LE.le', a, b))).toBe('a ≤ b');
  });

  it('brackets a function or a binding form used as an operand', () => {
    const lambda: Expr = { kind: 'lambda', binder: { id: 'x', name: 'x', type: 'ℝ', role: 'lambda', dependsOn: [] }, body: variable('x') };
    expect(formatExpression({ kind: 'app', fn: lambda, args: [a] })).toBe('(x ↦ x)(a)');
    expect(formatExpression(add(lambda, b))).toBe('(x ↦ x) + b');
    expect(formatExpression(add({ kind: 'opaque', text: 'f a' }, b))).toBe('(f a) + b');
  });

  it('writes an operator applied to more than its own arguments as the operator part applied to the rest', () => {
    // `(f + g) x` for f g : ℝ → ℝ: Lean records one application of HAdd.hAdd to seven arguments, the last a value.
    const [f, g, x] = ['f', 'g', 'x'].map(variable) as [Expr, Expr, Expr];
    const overApplied = (head: Expr, extra: Expr): Expr => head.kind === 'app'
      ? { ...head, args: [...head.args, extra], argumentKinds: [...head.argumentKinds!, 'value'] } : head;
    expect(formatExpression(overApplied(add(f, g), x))).toBe('(f + g)(x)');
    expect(formatExpression(overApplied(negate(f), x))).toBe('(−f)(x)');
    const absolute: Expr = { kind: 'app', fn: { kind: 'const', name: 'abs' }, standard: true, args: [real, instance, instance, f], argumentKinds: ['type', 'instance', 'instance', 'value'] };
    expect(formatExpression(absolute)).toBe('|f|');
    expect(formatExpression(overApplied(absolute, x))).toBe('|f|(x)');
    // `(1 : ℝ → ℝ) x`: OfNat.ofNat with its type, literal and instance, then one more argument.
    const one: Expr = { kind: 'app', fn: { kind: 'const', name: 'OfNat.ofNat' }, standard: true, args: [real, { kind: 'literal', value: 1 }, instance], argumentKinds: ['type', 'value', 'instance'] };
    expect(formatExpression(one)).toBe('1');
    expect(formatExpression(overApplied(one, x))).toBe('1(x)');
    // The pointwise sum read as an equality keeps both sides apart.
    const apply = (fn: Expr, argument: Expr): Expr => ({ kind: 'app', fn, args: [argument] });
    expect(formatExpression(relation('Eq', overApplied(add(f, g), x), add(apply(f, x), apply(g, x))))).toBe('(f + g)(x) = f(x) + g(x)');
  });

  it('brackets printed text that opens with a prefix operator, and quotes a string', () => {
    // `¬p = q` is Lean's `¬(p = q)` and `-x ^ 2` is `-(x ^ 2)`, so such text is bracketed where it would regroup.
    const [notP, minusX] = [{ kind: 'opaque', text: '¬p' }, { kind: 'opaque', text: '-x' }] as Expr[];
    expect(formatExpression(relation('Eq', notP!, b))).toBe('(¬p) = b');
    expect(formatExpression(relation('Eq', b, notP!))).toBe('b = (¬p)');
    expect(formatExpression(pow(minusX!, b))).toBe('(-x) ^ b');
    expect(formatExpression(add(minusX!, b))).toBe('-x + b');
    expect(formatExpression(relation('Eq', { kind: 'literal', value: 'a + b' }, c))).toBe('"a + b" = c');
    expect(formatExpression({ kind: 'literal', value: 3 })).toBe('3');
    // Decimal text may be an exact natural number as well as a string, so it is not quoted as if it were a string.
    expect(formatExpression({ kind: 'literal', value: '9007199254740993' })).toBe('9007199254740993');
  });

  it('reads every label back to the term it was written from', () => {
    const operations = ['add', 'sub', 'mul', 'div', 'pow'];
    const shapes = (leaves: string[]): Tree[] => leaves.length === 1 ? [leaves[0]!] : leaves.slice(1).flatMap((_, split) =>
      shapes(leaves.slice(0, split + 1)).flatMap(left => shapes(leaves.slice(split + 1)).flatMap(right => operations.map(op => ({ op, left, right })))));
    const negations = (tree: Tree): Tree[] => {
      const inner = typeof tree === 'string' ? [tree] : 'operand' in tree ? [tree]
        : negations(tree.left).flatMap(left => negations(tree.right).map(right => ({ ...tree, left, right })));
      return inner.flatMap(variant => [variant, { op: 'neg' as const, operand: variant }]);
    };
    const arithmetic = [...shapes(['a', 'b', 'c', 'd']), ...shapes(['a', 'b', 'c']).flatMap(negations)];
    const relations = shapes(['a', 'b', 'c']).slice(0, 40).flatMap(left => ['eq', 'lt', 'ge'].map(op => ({ op, left, right: { op: 'add', left: 'a', right: 'b' } as Tree })));
    const labels = new Map<string, string>();
    for (const tree of [...arithmetic, ...relations]) {
      const label = formatExpression(toExpr(tree));
      expect(show(readLabel(label)), label).toBe(show(tree));
      expect(labels.get(label), `two terms share the label ${label}`).toBeUndefined();
      labels.set(label, show(tree));
    }
    expect(labels.size).toBeGreaterThan(1500);
  });

  it('gives the two members of an operand-grouping pair different labels in the drawn equality', () => {
    // intent fixture C8b: `2 * n + 1 = m` against `2 * (n + 1) = m`.
    const binder = (name: string): Binder => ({ id: name, name, type: 'ℕ', role: 'universal', dependsOn: [] });
    const literal = (value: number): Expr => ({ kind: 'literal', value });
    const [n, m] = [binder('n'), binder('m')];
    const read = (left: Expr) => {
      const clause: StatementNode = { id: 'clause', kind: 'predicate', label: 'clause', lean: 'clause', children: [], expression: relation('Eq', left, variable('m')) };
      const tree: StatementNode = { id: 'n', kind: 'forall', label: 'n', lean: '∀ n m', binder: n, expression: { kind: 'const', name: 'True' },
        children: [{ id: 'm', kind: 'forall', label: 'm', lean: '∀ m', binder: m, expression: { kind: 'const', name: 'True' }, children: [clause] }] };
      const document = compileSemanticDocument({ source: 'pair', tree, expression: tree.expression });
      const equality = document.relations.find(item => item.kind === 'equality')!;
      return equality.ports.map(port => document.objects.find(object => object.id === port.objectId)!.label);
    };
    const first = read(add(mul(literal(2), variable('n')), literal(1))), second = read(mul(literal(2), add(variable('n'), literal(1))));
    expect(first).toEqual(['2 · n + 1', 'm']);
    expect(second).toEqual(['2 · (n + 1)', 'm']);
  });
});
