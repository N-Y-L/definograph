import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileSemanticDocument } from '../semantic';
import { compileReading } from '../reading';
import { expressionMapPath, readingObjectColor, StatementReadingView } from './StatementReadingView';

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, type = 'ℝ', role: Binder['role'] = 'universal', dependsOn: string[] = []): Binder => ({ id, name: id, type, role, dependsOn });
const variable = (b: Binder): Expr => ({ kind: 'var', id: b.id, name: b.name, type: b.type });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value'), ...extra });
const leaf = (id: string, expression: Expr = constant('Unknown.condition')): StatementNode => ({ id, kind: 'predicate', label: id, lean: `${id} source`, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });
function render(tree: StatementNode, selectedNodeId?: string) {
  const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
  const reading = compileReading(document, { selectedNodeId });
  const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
  return { html, document, reading };
}

describe('statement-first visual sequence', () => {
  it('keeps arbitrary objects, assumptions, and conclusions in source order with a whole-statement overview', () => {
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ'), x = binder('x');
    const tree = node('bind-A', 'forall', [node('bind-B', 'forall', [node('bind-x', 'forall', [node('implication', 'implies', [leaf('premise', app('Set.Subset', [variable(A), variable(B)])), leaf('conclusion', app('Set.Mem', [variable(B), variable(x)]))])], x)], B)], A);
    const { html } = render(tree);
    expect(html).toContain('Whole statement');
    expect(html).toContain('Given → conclusion');
    expect(html.indexOf('data-reading-step="bind-A"')).toBeLessThan(html.indexOf('data-reading-step="premise"'));
    expect(html.indexOf('data-reading-step="premise"')).toBeLessThan(html.indexOf('data-reading-step="conclusion"'));
    expect(html).toContain('sr-step-context-assumption');
    expect(html).toContain('sr-step-context-conclusion');
    expect(html).not.toContain('type="range"');
    expect(html).not.toContain('type="number"');
  });

  it('draws inclusion while explicitly allowing equal sets and links repeated objects by identity', () => {
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ');
    const tree = node('a', 'forall', [node('b', 'forall', [node('both', 'and', [leaf('ab', app('Set.Subset', [variable(A), variable(B)])), leaf('ba', app('Set.Subset', [variable(B), variable(A)]))])], B)], A);
    const { html, document } = render(tree);
    expect(html).toContain('The sets may be equal');
    expect(html).toContain('sr-set-outline');
    expect(html).toContain('Same objects throughout');
    const a = document.objects.find(object => object.binder?.id === 'A')!;
    expect(html.split(`data-reading-object="${a.id}"`).length - 1).toBe(3);
    expect(html).toContain(readingObjectColor(a.id));
  });

  it('preserves existential dependence and does not move the witness before an assumption', () => {
    const x = binder('x'), y = binder('y', 'ℝ', 'existential', ['x']);
    const tree = node('x-choice', 'forall', [node('if', 'implies', [leaf('assumption'), node('y-choice', 'exists', [leaf('result')], y)])], x);
    const { html } = render(tree);
    expect(html.indexOf('data-reading-step="assumption"')).toBeLessThan(html.indexOf('data-reading-step="y-choice"'));
    expect(html).toContain('A witness is required');
    expect(html).toContain('may use x');
  });

  it('keeps alternatives distinct from conjunction and makes the negation scope explicit', () => {
    const { html } = render(node('options', 'or', [node('negative', 'not', [leaf('p')]), leaf('q')]));
    expect(html).toContain('At least one alternative is required');
    expect(html).toContain('Alternative 1 · at least one');
    expect(html).toContain('Alternative 2 · at least one');
    expect(html).toContain('Under negation');
    expect(html).not.toContain('These conditions are required together');
  });

  it('shows both directions of equivalence without drawing an equality relation', () => {
    const { html } = render(node('equivalent', 'iff', [leaf('p'), leaf('q')]));
    expect(html).toContain('First implies second');
    expect(html).toContain('Second implies first');
    expect(html).toContain('First equivalent condition');
    expect(html).toContain('Second equivalent condition');
    expect(html).not.toContain('sr-comparison-symbol');
  });

  it('does not draw the center inside a metric region when no radius sign is known', () => {
    const { html } = render(leaf('region', app('Metric.ball', [constant('c'), constant('r')], { metric: 'unknown' })));
    expect(html).toContain('No nonemptiness or membership of the center is assumed');
    expect(html).not.toContain('sr-set-outline');
  });

  it('composes unary application into membership without dropping arguments of a binary application', () => {
    const f = binder('f', 'X → X → X'), x = binder('x', 'X'), y = binder('y', 'X');
    const application = (args: Expr[]): Expr => ({ kind: 'app', fn: variable(f), args, argumentKinds: args.map(() => 'value') });
    const unary = render(leaf('member', app('Set.Mem', [constant('A'), application([variable(x)])]))).html;
    const binary = render(leaf('member', app('Set.Mem', [constant('A'), application([variable(x), variable(y)])]))).html;
    expect(unary).toContain('sr-map-arrow');
    expect(binary).not.toContain('sr-map-arrow');
    expect(binary).toContain('f(x, y)');
  });

  it('keeps abstract objects and unknown predicates readable without assigning numerical coordinates', () => {
    const a = binder('A', 'C'), b = binder('B', 'C');
    const relation: Expr = { kind: 'app', fn: { kind: 'var', id: 'R', name: 'R', type: 'C → C → Prop', typeDescriptor: { kind: 'relation', lean: 'C → C → Prop' } }, args: [variable(a), variable(b)], argumentKinds: ['value', 'value'] };
    const { html } = render(node('a', 'forall', [node('b', 'forall', [leaf('relation', relation)], b)], a));
    expect(html).toContain('Symbolic schematics · no numerical choices');
    expect(html).toContain('A : C');
    expect(html).toContain('B : C');
    expect(html).not.toContain('type="range"');
  });

  it('provides progressive disclosure for large statements and reveals a selected late clause', () => {
    const tree = node('all', 'and', Array.from({ length: 120 }, (_, index) => leaf(`condition-${index}`)));
    const initial = render(tree).html;
    expect(initial).toContain('Show the next 21 nodes');
    const selected = render(tree, 'condition-119').html;
    expect(selected).toContain('data-reading-step="condition-119"');
    expect(selected).toContain('Show the next 21 nodes');
  });

  it('shows function composition as ordered map paths in an abstract equality', () => {
    const x = variable(binder('x', 'X'));
    const invoke = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: variable(binder(name, 'X → X')), args, argumentKinds: args.map(() => 'value') });
    const left = invoke('g', [invoke('f', [x])]);
    const right = invoke('h', [x]);
    const { html, document } = render(leaf('equation', app('Eq', [left, right])));
    expect(html).toContain('sr-has-map-paths');
    expect(html).toContain('Compare the outputs of these map paths');
    const equality = document.relations.find(relation => relation.kind === 'equality')!;
    const leftId = equality.ports.find(p => p.role === 'left')!.objectId;
    const path = expressionMapPath(leftId, document.relations);
    const names = new Map(document.objects.map(object => [object.id, object.label]));
    expect(path.maps.map(id => names.get(id))).toEqual(['f', 'g']);
    expect(path.inputs.map(id => names.get(id))).toEqual(['x']);
    expect(html.indexOf(`data-map-function="${path.maps[0]}"`)).toBeLessThan(html.indexOf(`data-map-function="${path.maps[1]}"`));
  });

  it('preserves ordered inputs and bounds expansion with a named expression fallback', () => {
    const invoke = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: variable(binder(name, 'X → X → X')), args, argumentKinds: args.map(() => 'value') });
    let expression = invoke('combine', [variable(binder('a', 'X')), variable(binder('b', 'X'))]);
    for (const name of ['f', 'g', 'h', 'k']) expression = invoke(name, [expression]);
    const { document } = render(leaf('equation', app('Eq', [expression, constant('target')])));
    const equality = document.relations.find(relation => relation.kind === 'equality')!;
    const leftId = equality.ports.find(p => p.role === 'left')!.objectId;
    const path = expressionMapPath(leftId, document.relations);
    expect(path.maps).toHaveLength(3);
    expect(path.collapsed).toBe(true);
    const combine = document.relations.find(relation => relation.kind === 'application' && document.objects.find(object => object.id === relation.ports.find(p => p.role === 'function')?.objectId)?.label === 'combine')!;
    const pair = expressionMapPath(combine.ports.find(p => p.role === 'output')!.objectId, document.relations);
    expect(pair.inputs.map(id => document.objects.find(object => object.id === id)!.label)).toEqual(['a', 'b']);
    expect(document.objects.find(object => object.id === path.inputs[0])!.label).toContain('combine(a, b)');
  });
});
