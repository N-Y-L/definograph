import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic/compiler';
import { compileSetConstruction, evaluateSetMembership } from './model';
import { SetConstructionFigure } from './SetConstructionFigure';
const c = (name: string): Expr => ({ kind: 'const', name });
const set = (id: string): Expr => ({ kind: 'var', id, name: id, type: 'Set X', typeDescriptor: { kind: 'set', lean: 'Set X', element: { kind: 'unknown', lean: 'X' } } });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: c(name), args, argumentKinds: args.map(() => 'value') });
const op = (name: string, ...args: Expr[]) => app(`Set.${name}`, args);
function compile(expression: Expr) { const tree: StatementNode = { id: 'clause', kind: 'predicate', lean: 'source', label: 'source', expression, children: [] }; const document = compileSemanticDocument({ source: 'source', tree, expression }); const relation = document.relations[0]; return { document, relation, model: compileSetConstruction(document, relation)! }; }
const bits = (model: ReturnType<typeof compile>['model']) => model.regions!.filter(region => region.highlighted).map(region => region.bits.map(bit => bit ? '1' : '0').join(''));

describe('set construction interpretation', () => {
  it('does not choose which union operand contains a named member', () => {
    const result = compile(app('Set.Mem', [op('union', set('A'), set('B')), c('x')]));
    expect(result.model.mode).toBe('allowed-membership');
    expect(bits(result.model)).toEqual(['10', '01', '11']);
    const html = renderToStaticMarkup(createElement(SetConstructionFigure, result));
    expect(html).toContain('no particular membership combination is chosen');
    expect(html).toContain('Drawing a region does not assert that it contains an element');
    expect(html).not.toContain('sc-named-point');
  });

  it('computes intersection, difference and complement membership without assuming inhabited regions', () => {
    expect(bits(compile(op('inter', set('A'), set('B'))).model)).toEqual(['11']);
    expect(bits(compile(op('diff', set('A'), set('B'))).model)).toEqual(['10']);
    expect(bits(compile(op('compl', set('A'))).model)).toEqual(['0']);
    expect(bits(compile(op('inter', set('A'), op('compl', set('A')))).model)).toEqual([]);
  });

  it('marks counterexample regions empty for inclusion and equality instead of drawing incompatible sample sets', () => {
    const subset = compile(app('Set.Subset', [op('union', set('A'), set('B')), set('A')])).model;
    expect(subset.mode).toBe('required-empty');
    expect(bits(subset)).toEqual(['01']);
    const equal = compile(app('Eq', [op('union', set('A'), set('B')), op('inter', set('A'), set('B'))])).model;
    expect(bits(equal)).toEqual(['10', '01']);
    const different = compile(app('Ne', [op('union', set('A'), set('B')), set('A')])).model;
    expect(different.mode).toBe('required-witness');
    expect(bits(different)).toEqual(['01']);
  });

  it('retains ordered nested construction with shared identities and image codomains as atoms', () => {
    const union = op('union', set('A'), set('B'));
    const image = app('Set.image', [c('f'), union]);
    const result = compile(op('inter', image, set('C'))).model;
    expect(result.steps.map(step => step.kind === 'operation' ? step.operation : step.kind)).toEqual(['union', 'image', 'intersection']);
    expect(result.atoms.map(atom => atom.label)).toEqual(['Set.image(f, (A ∪ B))', 'C']);
    expect(result.atoms.some(atom => atom.label === 'A')).toBe(false);
  });

  it('uses ordered construction instead of inventing a Venn arrangement for more than three atoms', () => {
    const result = compile(op('union', op('inter', set('A'), set('B')), op('diff', set('C'), set('D'))));
    expect(result.model.regions).toBeUndefined();
    expect(result.model.steps).toHaveLength(3);
    const html = renderToStaticMarkup(createElement(SetConstructionFigure, result));
    expect(html).toContain('without assigning shapes to their intersections');
    expect(html).toContain('class="sc-construction-details" open=""');
  });

  it('refuses to capture a producer from a different expression scope', () => {
    const result = compile(app('Set.Mem', [op('union', set('A'), set('B')), c('x')]));
    const scoped = result.document.relations.map(relation => relation.kind === 'set-construction' ? { ...relation, scopeId: 'different-scope' } : relation);
    expect(compileSetConstruction(result.document, result.relation, scoped)).toBeUndefined();
  });

  it('shares one atom when an operand occurs repeatedly and evaluates exact Boolean membership', () => {
    const result = compile(op('union', set('A'), set('A'))).model;
    expect(result.atoms).toHaveLength(1);
    expect(bits(result)).toEqual(['1']);
    expect(evaluateSetMembership(result.left, new Map([[result.atoms[0].id, false]]))).toBe(false);
    expect(() => evaluateSetMembership(result.left, new Map())).toThrow('Missing symbolic membership assignment');
  });

  it('bounds deep construction while retaining named subexpressions consistently', () => {
    let expression = set('A');
    for (let index = 0; index < 24; index++) expression = op('compl', expression);
    const result = compile(expression).model;
    expect(result.collapsed).toBe(true);
    expect(result.steps).toHaveLength(18);
    expect(result.atoms).toHaveLength(1);
    expect(result.atoms[0].expression.kind).toBe('app');
    expect(new Set(result.steps.map(step => step.objectId)).size).toBe(result.steps.length);
    expect(result.regions).toHaveLength(2);
  });
});
