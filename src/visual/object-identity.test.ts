import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileReading } from '../reading';
import { compileScopedStatementGraph } from '../reading/scoped-graph';
import { scopedFixture } from '../reading/scoped-graph.test-fixtures';
import { compileSemanticDocument } from '../semantic';
import type { SemanticDocument } from '../semantic/types';
import { assignIdentityColors, IDENTITY_PALETTE, IdentityColorProvider, NEUTRAL_INK } from './object-identity';
import { ScopedStatementGraph } from './ScopedStatementGraph';
import { renderReading } from './statement-skeleton.test-fixtures';

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, role: Binder['role'] = 'universal', type = 'X'): Binder => ({ id, name: id, type, role, dependsOn: [] });
const variable = (b: Binder): Expr => ({ kind: 'var', id: b.id, name: b.name, type: b.type });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value') });
const leaf = (id: string, expression: Expr = constant('Unknown.condition')): StatementNode => ({ id, kind: 'predicate', label: id, lean: `${id} source`, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });
const compile = (tree: StatementNode) => compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
const objectOf = (document: SemanticDocument, binderId: string) => document.objects.find(object => object.binder?.id === binderId)!;

/** `∀ A B C x, x ∈ (A ∪ B) ∩ Cᶜ → x ∈ (A ∖ C) ∪ (B ∖ C)`: four binders, a named hypothesis and many compound sets. */
function setAlgebra() {
  const [A, B, C, x] = ['A', 'B', 'C', 'x'].map(id => binder(id, 'universal', id === 'x' ? 'α' : 'Set α')), h = binder('h', 'assumption', 'x ∈ (A ∪ B) ∩ Cᶜ');
  const premise = app('Set.Mem', [app('Set.inter', [app('Set.union', [variable(A!), variable(B!)]), app('Set.compl', [variable(C!)])]), variable(x!)]);
  const conclusion = app('Set.Mem', [app('Set.union', [app('Set.diff', [variable(A!), variable(C!)]), app('Set.diff', [variable(B!), variable(C!)])]), variable(x!)]);
  return node('a', 'forall', [node('b', 'forall', [node('c', 'forall', [node('x', 'forall', [node('if', 'implies', [leaf('premise', premise), leaf('conclusion', conclusion)], h)], x)], C)], B)], A);
}
/** Nine arbitrary choices in a row: two more than the palette holds. */
function nineBinders() {
  const binders = Array.from({ length: 9 }, (_, index) => binder(`v${index}`));
  return binders.reduceRight<StatementNode>((body, b) => node(`n-${b.id}`, 'forall', [body], b), leaf('claim', app('Unknown.claim', binders.map(variable))));
}
/** A function body binds `t` inside the first clause, before the statement's own later binder `late`. */
function localBeforeLate() {
  const f = binder('f', 'universal', 'X → X'), t = binder('t', 'lambda'), late = binder('late');
  const body: Expr = { kind: 'app', fn: variable(f), args: [variable(t)], argumentKinds: ['value'] };
  return node('n-f', 'forall', [node('both', 'and', [leaf('wrapped', app('Opaque.wrapper', [{ kind: 'lambda', binder: t, body }])), node('n-late', 'forall', [leaf('use', app('Unknown.claim', [variable(late)]))], late)])], f);
}
const documents = (): [string, SemanticDocument][] => [['set algebra', compile(setAlgebra())], ['nine binders', compile(nineBinders())], ['a local binder before a later one', compile(localBeforeLate())], ['the Lebesgue-shaped fixture', scopedFixture().document]];

function relativeLuminance(hex: string): number {
  const [r, g, b] = [1, 3, 5].map(index => { const channel = parseInt(hex.slice(index, index + 2), 16) / 255; return channel <= 0.04045 ? channel / 12.92 : ((channel + 0.055) / 1.055) ** 2.4; });
  return 0.2126 * r! + 0.7152 * g! + 0.0722 * b!;
}
const lightness = (hex: string) => 116 * Math.cbrt(relativeLuminance(hex)) - 16;

describe('identity colours', () => {
  it('uses at most seven hues, no two of one lightness, each readable on the light surface', () => {
    expect(IDENTITY_PALETTE.length).toBeLessThanOrEqual(7);
    expect(new Set(IDENTITY_PALETTE).size).toBe(IDENTITY_PALETTE.length);
    const levels = IDENTITY_PALETTE.map(lightness).sort((a, b) => a - b);
    for (let index = 1; index < levels.length; index++) expect(levels[index]! - levels[index - 1]!).toBeGreaterThan(3);
    for (const color of IDENTITY_PALETTE) expect(1.05 / (relativeLuminance(color) + 0.05)).toBeGreaterThanOrEqual(4.5);
    // The darkest hue is the nearest to neutral ink, so it is the last one a statement is given.
    expect(IDENTITY_PALETTE.map(lightness).indexOf(levels[0]!)).toBe(IDENTITY_PALETTE.length - 1);
  });

  it.each(documents())('never gives two objects of %s one colour, and colours only what a binder introduces', (_, document) => {
    const colors = assignIdentityColors(document);
    expect(new Set(colors.values()).size).toBe(colors.size);
    expect(colors.size).toBeGreaterThan(0);
    for (const [id, color] of colors) {
      const object = document.objects.find(candidate => candidate.id === id)!;
      expect(IDENTITY_PALETTE).toContain(color);
      expect(object.binder).toBeDefined();
      expect(['assumption', 'auxiliary']).not.toContain(object.binder!.role);
    }
    // Deterministic: the same statement, compiled or copied again, gets the same assignment.
    expect([...assignIdentityColors(document)]).toEqual([...colors]);
    expect([...assignIdentityColors(structuredClone(document))]).toEqual([...colors]);
  });

  it('assigns in order of introduction and leaves compound expressions and hypotheses in neutral ink', () => {
    const document = compile(setAlgebra()), colors = assignIdentityColors(document);
    expect(['A', 'B', 'C', 'x'].map(id => colors.get(objectOf(document, id).id))).toEqual(IDENTITY_PALETTE.slice(0, 4));
    expect(colors.size).toBe(4);
    expect(document.objects.filter(object => !object.binder).length).toBeGreaterThan(4);
    expect(colors.has(objectOf(document, 'h').id)).toBe(false);
  });

  it('leaves objects beyond the palette neutral and never reuses a hue', () => {
    const document = compile(nineBinders()), colors = assignIdentityColors(document);
    expect(Array.from({ length: 9 }, (_, index) => colors.get(objectOf(document, `v${index}`).id))).toEqual([...IDENTITY_PALETTE, undefined, undefined]);
  });

  it('colours the statement\'s own binders before a binder local to one expression', () => {
    const document = compile(localBeforeLate()), colors = assignIdentityColors(document);
    expect(document.objects.findIndex(object => object.binder?.id === 't')).toBeLessThan(document.objects.findIndex(object => object.binder?.id === 'late'));
    expect(['f', 'late', 't'].map(id => colors.get(objectOf(document, id).id))).toEqual(IDENTITY_PALETTE.slice(0, 3));
  });

  it('keeps the enclosing statement\'s hues in a nested reading and adds only unused ones', () => {
    const outer = compile(setAlgebra()), inherited = assignIdentityColors(outer);
    // A field law is compiled with the enclosing identities, as src/decomposition does.
    const law = node('n-u', 'forall', [leaf('law', app('Unknown.law', [variable(binder('u')), variable(binder('A', 'universal', 'Set α'))]))], binder('u'));
    const nested = compileSemanticDocument({ source: 'law', tree: law, expression: law.expression }, undefined, { identities: new Map(outer.objects.flatMap(object => object.binder ? [[object.binder.id, object.id] as const] : [])) });
    expect(nested.objects.some(object => object.id === objectOf(outer, 'A').id)).toBe(true);
    const colors = assignIdentityColors(nested, inherited);
    for (const [id, color] of inherited) expect(colors.get(id)).toBe(color);
    expect(colors.get(objectOf(nested, 'u').id)).toBe(IDENTITY_PALETTE[4]);
    expect(new Set(colors.values()).size).toBe(colors.size);
  });

  it.each(documents())('draws every object of %s in its assigned colour or in neutral ink, on every step, in the full reading and in the construction graph', (_, document) => {
    const colors = assignIdentityColors(document), drawn = new Map<string, Set<string>>(), sources = new Set<string>();
    // Every node selected in turn reaches each step of the guide, and with it the in-scope chips of later steps.
    const drawings = compileReading(document).nodes.map(node => { const reading = compileReading(document, { selectedNodeId: node.id }); return { reading, html: renderReading(document, reading) }; });
    const graphs = drawings.flatMap(({ reading }) => { const model = compileScopedStatementGraph(document, reading); return model?.clauses.some(clause => clause.node.id === reading.selection.nodeId)
      ? [renderToStaticMarkup(createElement(IdentityColorProvider, { value: colors }, createElement(ScopedStatementGraph, { model, document, reading })))] : []; });
    for (const html of [...drawings.map(drawing => drawing.html), ...graphs]) for (const [element] of html.matchAll(/<[^<>]*\sdata-reading-object="[^<>]*>/g)) {
      const id = /data-reading-object="([^"]*)"/.exec(element)![1]!, color = /style="--([a-z-]+):([^";]*)/.exec(element);
      if (color) { drawn.set(id, (drawn.get(id) ?? new Set()).add(color[2]!)); sources.add(color[1]!); }
    }
    expect(drawn.size).toBeGreaterThan(0);
    for (const [id, used] of drawn) expect([...used]).toEqual([colors.get(id) ?? NEUTRAL_INK]);
    // The guide's chips are among what was drawn, and so is the graph wherever the statement has one.
    expect(drawings.some(drawing => drawing.html.includes('class="rg-in-scope"'))).toBe(true);
    if (graphs.length) expect(sources).toContain('ssg-object');
  });
});
