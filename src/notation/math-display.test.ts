import { describe, expect, it } from 'vitest';
import type { Expr } from '../core/types';
import { expressionKey } from '../semantic/expression';
import { expressionDisplayNode, expressionMathDisplay, identifierMathDisplay, mathDisplay, withMathProse, type MathDisplayNode } from './math-display';
import { typesetStatement } from './render';

const variable = (name: string, id = name): Expr => ({ kind: 'var', name, id, type: 'ℝ' });
const identifier = (name: string): MathDisplayNode => ({ kind: 'identifier', name });
const literal = (value: number): MathDisplayNode => ({ kind: 'literal', value });
describe('typed mathematical display notation', () => {
  it('typesets Greek, subscripts, ordered function arguments and stacked operators', () => {
    const fraction: MathDisplayNode = { kind: 'binary', operator: 'div', left: identifier('α'), right: { kind: 'binary', operator: 'div', left: literal(1), right: identifier('δ') } };
    const node: MathDisplayNode = { kind: 'application', fn: { kind: 'script', base: identifier('f'), subscript: literal(2), superscript: literal(-1) },
      args: [fraction, { kind: 'binary', operator: 'pow', left: identifier('x₁'), right: literal(3) }] };
    const display = mathDisplay(node), result = typesetStatement(display.latex!);
    expect(display.latex).toContain('\\alpha'); expect(display.latex).toContain('\\delta'); expect(display.latex).toContain('\\frac');
    expect(result.status).toBe('rendered');
    if (result.status !== 'rendered') throw Error(result.reason);
    expect(result.html).toContain('class="mfrac"'); expect(result.html).toContain('<msubsup>'); expect(result.html).toContain('<math');
  });
  it('escapes unknown and hostile identifiers literally without treating English names as commands', () => {
    for (const name of ['Unknown\\href{javascript:evil}{click}', '<img src=x onerror=alert(1)>', 'name_value%$#&_{}^~', 'alpha', 'forall', 'sin']) {
      const display = identifierMathDisplay(name), rendered = typesetStatement(display.latex!);
      expect(display.source).toBe(name); expect(display.latex).toMatch(/^\\text/);
      expect(rendered.status).toBe('rendered');
      if (rendered.status !== 'rendered') throw Error(rendered.reason);
      expect(rendered.html).not.toContain('<img'); expect(rendered.html).not.toContain('<a '); expect(rendered.html).not.toContain('href=');
    }
    const mixed = identifierMathDisplay('long_{exact}\\name%&δ');
    expect(mixed.source).toBe('long_{exact}\\name%&δ');
    expect(mixed.latex).toBe('\\text{long\\_\\{exact\\}\\textbackslash{}name\\%\\&}{\\delta}');
    expect(typesetStatement(mixed.latex!).status).toBe('rendered');
  });
  it('retains literal underscores and distinct source identities even where glyphs resemble one another', () => {
    const literalUnderscore = identifierMathDisplay('x_1'), subscriptDigit = identifierMathDisplay('x₁');
    expect(literalUnderscore.latex).toBe('\\text{x\\_1}'); expect(subscriptDigit.latex).toContain('_{1}');
    expect(literalUnderscore.key).not.toBe(subscriptDigit.key);
    const first = variable('x', 'outer'), second = variable('x', 'inner');
    expect(expressionMathDisplay(first).latex).toBe(expressionMathDisplay(second).latex);
    expect(expressionKey(first)).not.toBe(expressionKey(second));
  });
  it('preserves repeated ordered operands and nested application association', () => {
    const x = variable('x'), y = variable('y'), expr: Expr = { kind: 'app', fn: variable('f'), args: [x, x, y] };
    const before = JSON.stringify(expr), display = expressionMathDisplay(expr);
    expect(expressionDisplayNode(expr)).toMatchObject({ kind: 'application', args: [identifier('x'), identifier('x'), identifier('y')] });
    expect(display.latex).toBe('{f}\\left(x,\\,x,\\,y\\right)'); expect(JSON.stringify(expr)).toBe(before);
    const nested: Expr = { kind: 'app', fn: { kind: 'app', fn: variable('f'), args: [x] }, args: [y] };
    expect(expressionMathDisplay(nested).latex).not.toBe(expressionMathDisplay({ ...expr, args: [x, y] }).latex);
  });
  it('uses the existing operator gate and exact value roles, never a familiar user label', () => {
    const x = variable('α'), y = variable('β'), app: Expr = { kind: 'app', fn: { kind: 'const', name: 'HDiv.hDiv' }, args: [x, y] };
    expect(expressionMathDisplay(app).latex).not.toContain('\\frac');
    const admitted: Expr = { ...app, standard: true, operator: 'div' };
    expect(expressionMathDisplay(admitted).latex).toBe('\\frac{\\alpha}{\\beta}');
    expect(expressionMathDisplay({ ...admitted, fn: { kind: 'const', name: 'HDiv.hDiv', canonical: false } }).latex).not.toContain('\\frac');
    const comparison: Expr = { kind: 'app', fn: { kind: 'const', name: 'GT.gt' }, standard: true, args: [x, y, { kind: 'opaque', text: 'instance' }], argumentKinds: ['value', 'value', 'instance'] };
    expect(expressionDisplayNode(comparison)).toEqual({ kind: 'binary', operator: 'lt', left: identifier('β'), right: identifier('α') });
  });
  it('preserves unsupported source labels and ends boundedly for large or cyclic expressions', () => {
    const opaque: Expr = { kind: 'opaque', text: 'retained source expression' };
    expect(expressionMathDisplay(opaque)).toMatchObject({ source: opaque.text, unavailable: expect.any(String) });
    expect(expressionMathDisplay(opaque).latex).toBeUndefined();
    const many: Expr = { kind: 'app', fn: variable('f'), args: Array.from({ length: 129 }, () => variable('x')) };
    expect(expressionMathDisplay(many, 'f with its full source retained').source).toBe('f with its full source retained');
    expect(expressionMathDisplay(many).latex).toBeUndefined();
    const cyclic = { kind: 'app', args: [], fn: null } as unknown as Extract<Expr, { kind: 'app' }>; cyclic.fn = cyclic;
    expect(expressionMathDisplay(cyclic, 'cyclic control').latex).toBeUndefined();
  });
  it('keeps ordinary prose separate from the generated mathematical TeX', () => {
    const label = withMathProse(identifierMathDisplay('δ'), 'radius ', ' (positive case)');
    expect(label.latex).toBe('\\delta'); expect(label.source).toBe('radius δ (positive case)');
    expect(label.prefix).toBe('radius '); expect(label.suffix).toBe(' (positive case)');
  });
  it('visibly groups negative, nested-power and compound script bases', () => {
    const power = (left: MathDisplayNode): MathDisplayNode => ({ kind: 'binary', operator: 'pow', left, right: literal(2) });
    for (const base of [literal(-2), { kind: 'unary', operator: 'neg', argument: identifier('x') } as const, power(identifier('x'))]) {
      const display = mathDisplay(power(base)), scripted = mathDisplay({ kind: 'script', base, superscript: literal(2) });
      expect(display.latex).toMatch(/^\{\\left\(/); expect(scripted.latex).toMatch(/^\{\\left\(/);
      expect(display.source).toMatch(/^\(\(/); expect(scripted.source).toMatch(/^\(/);
      const result = typesetStatement(display.latex!);
      expect(result.status).toBe('rendered');
      if (result.status === 'rendered') expect(result.html).toContain('<mo fence="true">(</mo>');
    }
    expect(mathDisplay(power(identifier('x'))).latex).toBe('{x}^{2}');
  });
  it('distinguishes explicit display strings from numbers and identifiers, preserving ambiguous exact literal source', () => {
    const number = mathDisplay({ kind: 'literal', value: 12 }), string = mathDisplay({ kind: 'literal', value: '12' });
    expect(string.source).toBe('"12"'); expect(number.source).toBe('12'); expect(string.key).not.toBe(number.key);
    const word = mathDisplay({ kind: 'literal', value: 'hello' }), name = identifierMathDisplay('hello');
    expect(word.latex).toBe('\\text{"hello"}'); expect(word.latex).not.toBe(name.latex);
    const stringRendered = typesetStatement(string.latex!), numberRendered = typesetStatement(number.latex!);
    if (stringRendered.status !== 'rendered' || numberRendered.status !== 'rendered') throw Error('Missing literal typesetting.');
    expect(stringRendered.html).toContain('<mtext>'); expect(numberRendered.html).toContain('<mn>12</mn>');
    for (const displayText of ['12', '"12"']) {
      const exact: Expr = { kind: 'literal', value: '12', exactIdentity: `literal:${displayText}`, displayText };
      const display = expressionMathDisplay(exact, 'an ambiguous display label');
      expect(display.source).toBe(displayText); expect(display.latex).toBeUndefined();
    }
    const unspecified = expressionMathDisplay({ kind: 'literal', value: '12' }, '12');
    expect(unspecified.latex).toBeUndefined();
    expect(unspecified.source).toBe('Literal (constructor unspecified): "12"');
    expect(unspecified.source).not.toBe(number.source);
    expect(expressionMathDisplay({ kind: 'app', fn: variable('f'), args: [{ kind: 'literal', value: '12' }] }).source)
      .toBe('f(12) [literal constructor unspecified]');
  });
});
