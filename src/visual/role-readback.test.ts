import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileReading } from '../reading';
import { compileSemanticDocument } from '../semantic';
import { assertFigureRoles, assertFigureRolesReadBack, assertStageReadsBack } from './role-marks.test-fixtures';
import { readFigureRoles } from './role-readback';
import { renderReading } from './statement-skeleton.test-fixtures';

const frame = (role: string, index: number, label: string, inner: string) => `<div class="role-frame" data-role-frame="" data-role="${role}" data-role-index="${index}"><span class="role-label" data-role-label="">${label}</span>${inner}</div>`;
const leaf = (node: string, inner: string, mark?: string, kind = 'clause') => `<div class="role-leaf" data-role-leaf="${kind}" data-role-node="${node}">${mark === undefined ? '' : `<span class="role-mark" data-role-mark="">${mark}</span>`}<div class="role-figure">${inner}</div></div>`;
const root = (inner: string, standing = 'statement') => `<div class="statement-reading-view" data-role-root="${standing}"><div class="rg-stage" data-role-surface="">${inner}</div></div>`;
const figure = '<figure class="sr-relation-figure"><svg viewBox="0 0 1 1"><circle r="1"></circle><path d="M0 0"/></svg><figcaption>x &lt; y</figcaption></figure>';

describe('reading role frames back from markup', () => {
  it('recovers each leaf\'s chain of frames, outermost first, with the labels and marks they print', () => {
    const html = root(frame('assumption', 1, 'Given', leaf('member-A', figure)) + frame('conclusion', 0, 'Then', frame('negated', 0, '¬ Not', leaf('member-B', figure))) + leaf('top', figure, '⊢'));
    expect(readFigureRoles(html)).toEqual([
      { nodeId: 'member-A', leaf: 'clause', required: false, chain: [{ role: 'assumption', index: 1, label: 'Given' }], standing: 'statement', depth: 0 },
      { nodeId: 'member-B', leaf: 'clause', required: false, chain: [{ role: 'conclusion', index: 0, label: 'Then' }, { role: 'negated', index: 0, label: '¬ Not' }], standing: 'statement', depth: 0 },
      { nodeId: 'top', leaf: 'clause', required: true, mark: '⊢', chain: [], standing: 'statement', depth: 0 },
    ]);
  });

  it('starts a fresh chain inside a reading nested in a figure, and says what that reading is', () => {
    const nested = root(leaf('law', figure), 'law');
    const [outer, inner] = readFigureRoles(root(frame('assumption', 0, 'Given', leaf('owner', nested, '∀', 'binder'))));
    expect(outer).toMatchObject({ nodeId: 'owner', leaf: 'binder', mark: '∀', required: false, chain: [{ role: 'assumption' }], depth: 0 });
    expect(inner).toMatchObject({ nodeId: 'law', chain: [], standing: 'law', depth: 1, required: false });
  });

  it('refuses markup it cannot read back', () => {
    expect(() => readFigureRoles(root(figure))).toThrow('outside every role leaf');
    expect(() => readFigureRoles(root(frame('negated', 0, '¬ Not', figure)))).toThrow('outside every role leaf');
    expect(() => readFigureRoles(frame('negated', 0, '¬ Not', leaf('p', figure)))).toThrow('outside every reading');
    expect(() => readFigureRoles(root(frame('negated', 0, '¬ Not', '<span data-role-label="">Given</span>' + leaf('p', figure))))).toThrow('two labels');
    expect(() => readFigureRoles(root('<div data-role-frame="" data-role="negated" data-role-index="0">' + leaf('p', figure) + '</div>'))).toThrow('no label');
    expect(() => readFigureRoles(root(leaf('p', '<span data-role-mark="">∀</span>' + figure, '⊢')))).toThrow('two marks');
    expect(() => readFigureRoles(root(leaf('p', figure)).replace('</figure>', '</div>'))).toThrow('not well nested');
    expect(() => readFigureRoles(root(leaf('p', figure), 'theorem'))).toThrow('no standing');
    // A frame or a leaf drawn inside a leaf of the same reading, and a frame around no figure.
    expect(() => readFigureRoles(root(leaf('p', frame('negated', 0, '¬ Not', figure))))).toThrow('inside a leaf of the same reading');
    expect(() => readFigureRoles(root(leaf('p', leaf('q', figure))))).toThrow('inside a leaf of the same reading');
    expect(() => readFigureRoles(root(frame('negated', 0, '¬ Not', '<p>no figure</p>') + leaf('p', figure)))).toThrow('negated frame holds no figure');
    expect(() => readFigureRoles(root(frame('negated', 0, '¬ Not', frame('alternative', 0, '∨ Alternative 1', '')) + leaf('p', figure)))).toThrow('holds no figure');
    // Outside a surface, such as the full reading before it is framed, a figure needs no leaf.
    expect(readFigureRoles(`<div data-role-root="statement">${figure}</div>`)).toEqual([]);
  });
});

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, type = 'ℝ'): Binder => ({ id, name: id, type, role: 'universal', dependsOn: [] });
const variable = (b: Binder): Expr => ({ kind: 'var', id: b.id, name: b.name, type: b.type });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value') });
const clause = (id: string, lean: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });

describe('the role oracle', () => {
  // ∀ (A : Set ℝ) (x : ℝ), ¬ (x ∈ A ∧ P x): a membership figure under a negation.
  const A = binder('A', 'Set ℝ'), x = binder('x');
  const tree = node('all-A', 'forall', [node('all-x', 'forall', [node('not', 'not', [node('both', 'and', [clause('member', 'x ∈ A', app('Set.Mem', [variable(A), variable(x)])), clause('other', 'P x', app('Unknown.condition', [variable(x)]))])])], x)], A);
  const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
  const reading = compileReading(document, { selectedNodeId: 'member' });
  const html = renderReading(document, reading);

  it('accepts the drawn figure of a negated membership', () => {
    expect(assertFigureRolesReadBack(document, reading, html).map(figure => [figure.nodeId, figure.chain.map(position => position.label)])).toEqual([['member', ['¬ Not']]]);
  });

  it('rejects a planted wrong label, a planted ⊢ and a frame of the wrong role, though each reads back as a well-formed chain', () => {
    const planted = (from: string, to: string) => { expect(html).toContain(from); return readFigureRoles(html.replace(from, to)); };
    expect(() => assertFigureRoles(document, reading, planted('data-role-label="">¬ Not<', 'data-role-label="">Given<'))).toThrow('prints the wrong label');
    expect(() => assertFigureRoles(document, reading, planted('<div class="role-figure">', '<span class="role-mark" data-role-mark="">⊢</span><div class="role-figure">'))).toThrow('marked as required');
    expect(() => assertFigureRoles(document, reading, planted('data-role="negated"', 'data-role="assumption"'))).toThrow('prints the wrong label');
    expect(() => assertFigureRoles(document, reading, planted('data-role="negated" data-role-index="0"><span class="role-label" data-role-label="">¬ Not', 'data-role="assumption" data-role-index="0"><span class="role-label" data-role-label="">Given'))).toThrow('wrong role frames');
  });

  it('rejects a whole clause drawn as a law, and, knowing the step shown, as a part of a clause', () => {
    const planted = (kind: string) => html.replace('data-role-leaf="clause"', `data-role-leaf="${kind}"`);
    expect(html).toContain('data-role-leaf="clause"');
    expect(() => assertFigureRolesReadBack(document, reading, planted('law'))).toThrow('which a clause region does not hold');
    expect(() => assertStageReadsBack(document, reading, planted('part'))).toThrow('not as a clause');
    expect(assertStageReadsBack(document, reading, html).cue?.nodeId).toBe('member');
  });
});
