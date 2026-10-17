import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileSemanticDocument } from '../semantic';
import { compileReading } from '../reading';
import { expressionMapPath, StatementReadingView } from './StatementReadingView';
import { assignIdentityColors } from './object-identity';
import { assertStageReadsBack } from './role-marks.test-fixtures';
import { assertSkeletonReadsBack } from './statement-skeleton.test-fixtures';
import { compileReadingCues } from '../reading/cues';

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
  assertSkeletonReadsBack(document, reading, html);
  const { figures } = assertStageReadsBack(document, reading, html);
  return { html, document, reading, figures };
}

describe('mathematical atlas reading', () => {
  it('can focus different applications within the same logical clause', () => {
    const f = binder('F', 'Nat → Nat');
    const call = (name: string): Expr => ({ kind: 'app', fn: variable(f), args: [constant(name)] });
    const tree = leaf('same-clause', app('Eq', [call('a'), call('b')]));
    const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
    const reading = compileReading(document);
    const calls = document.relations.filter(relation => relation.kind === 'application' && relation.ports.some(port =>
      port.role === 'function' && document.objects.find(object => object.id === port.objectId)?.label === 'F'));
    expect(calls).toHaveLength(2);
    expect(calls[0].nodeId).toBe(calls[1].nodeId);
    const cues = compileReadingCues(reading, document);
    for (const call of calls) {
      const cue = cues.cues.find(candidate => candidate.stage.relationId === call.id)!;
      expect(cue).toBeDefined();
      const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedRelationId: call.id }));
      expect(html).toContain(`data-cue-id="${cue.id}"`);
      const other = cues.cues.find(candidate => candidate.stage.relationId === calls.find(candidate => candidate.id !== call.id)!.id)!;
      expect(html).not.toContain(`data-cue-id="${other.id}"`);
    }
  });

  it('keeps arbitrary objects, assumptions, and conclusions in source order with a whole-statement overview', () => {
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ'), x = binder('x');
    const tree = node('bind-A', 'forall', [node('bind-B', 'forall', [node('bind-x', 'forall', [node('implication', 'implies', [leaf('premise', app('Set.Subset', [variable(A), variable(B)])), leaf('conclusion', app('Set.Mem', [variable(B), variable(x)]))])], x)], B)], A);
    const { html } = render(tree);
    expect(html).toContain('<section class="statement-skeleton" aria-label="Whole statement">');
    expect(html.indexOf('class="statement-skeleton"')).toBeLessThan(html.indexOf('class="reading-guide"'));
    expect(html).not.toContain('sr-overview');
    expect(html.indexOf('data-reading-step="bind-A"')).toBeLessThan(html.indexOf('data-reading-step="premise"'));
    expect(html.indexOf('data-reading-step="premise"')).toBeLessThan(html.indexOf('data-reading-step="conclusion"'));
    expect(html).toContain('aria-label="Given assumptions"');
    expect(html).toContain('aria-label="Then the conclusion is required"');
    expect(html).not.toContain('sr-sequence-connective');
    expect(html).toContain('data-source-nodes="bind-A bind-B bind-x"');
    expect(html).not.toContain('type="range"');
    expect(html).not.toContain('type="number"');
  });

  it('draws inclusion while explicitly allowing equal sets and links repeated objects by identity', () => {
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ');
    const tree = node('a', 'forall', [node('b', 'forall', [node('both', 'and', [leaf('ab', app('Set.Subset', [variable(A), variable(B)])), leaf('ba', app('Set.Subset', [variable(B), variable(A)]))])], B)], A);
    const { html, document } = render(tree);
    expect(html).toContain('The sets may be equal');
    expect(html).toContain('sr-set-outline');
    expect(html).not.toContain('Same objects throughout');
    expect(html).not.toContain('sr-identity-traces');
    const a = document.objects.find(object => object.binder?.id === 'A')!;
    expect(html.split(`data-reading-object="${a.id}"`).length - 1).toBeGreaterThanOrEqual(3);
    expect(html).toContain(`data-reading-object="${a.id}" style="--object-color:${assignIdentityColors(document).get(a.id)}"`);
  });

  it('names a step once, in its selector, and folds its explanation and context behind one counted disclosure', () => {
    const x = binder('x'), y = binder('y', 'ℝ', 'existential', ['x']);
    const { html, document, reading, figures } = render(node('x-choice', 'forall', [node('y-choice', 'exists', [node('both', 'and', [leaf('first'), leaf('second')])], y)], x), 'second');
    const cues = compileReadingCues(reading, document).cues, cue = cues.find(candidate => candidate.nodeId === 'second')!;
    // The title is the selected option. It is repeated for assistive technology only, not drawn as a caption.
    expect(html).toContain(`<option value="${cue.id}" selected="">${cues.indexOf(cue) + 1}. ${cue.title}</option>`);
    expect(html).toContain(`<h2 class="sr-only" aria-live="polite" aria-atomic="true">${cue.title}</h2>`);
    expect(html).not.toContain('rg-heading');
    // One native disclosure, closed until opened. Its label counts what it holds: the skeleton above already draws
    // the two binders in scope and the sibling conjunct, with this step's row marked.
    expect(html).toContain(`<details class="rg-about"><summary>About this step · 2 in scope · 1 alongside</summary><p>${cue.detail}</p><div class="rg-in-scope"><span class="rg-context-label">In scope</span>`);
    expect(html).toContain('<div class="rg-listed"><span class="rg-context-label">Alongside this clause</span><ul><li><code>first source</code></li></ul></div></details>');
    expect(html.match(/<details class="rg-about"/g)).toHaveLength(1);
    // The step's standing is on its figure, not in a line of text beside it: a conjunct stands where its conjunction
    // stands, so this clause of the statement is required.
    expect(html).not.toContain('rg-logical-path');
    expect(figures).toEqual([{ nodeId: 'second', leaf: 'clause', required: true, mark: '⊢', chain: [], standing: 'statement', depth: 0 }]);
  });

  it('counts the assumptions a step stands under in the disclosure label and keeps them listed inside it', () => {
    const { html } = render(node('if', 'implies', [leaf('p'), node('then', 'implies', [leaf('q'), leaf('r')])]), 'r');
    expect(html).toContain('<summary>About this step · 2 given</summary>');
    expect(html).toContain('<div class="rg-listed"><span class="rg-context-label">Given</span><ul><li><code>p source</code></li><li><code>q source</code></li></ul></div>');
  });

  it('shows a connective step as the marked skeleton row and repeats none of its parts below', () => {
    const { html } = render(node('a', 'forall', [node('if', 'implies', [leaf('p'), node('then', 'implies', [leaf('q'), leaf('r')])])], binder('a')), 'then');
    // The stage of a logic step holds the link to the Lean fragment and nothing else.
    expect(html).toMatch(/<div class="rg-stage"[^>]*data-cue-kind="logic"><details class="rg-source-context"><summary>Lean fragment and source context<\/summary><code>[^<]*<\/code><\/details><\/div>/);
    expect(html).not.toContain('rg-logic-child');
    const skeleton = html.slice(html.indexOf('<section class="statement-skeleton"'), html.indexOf('</section>'));
    expect(skeleton.match(/class="sk-row sk-selected" aria-current="true">Given<\/button>/g)).toHaveLength(1);
  });

  it('draws a relation figure at one unit per CSS pixel, never stretched to the column', () => {
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ');
    const { html } = render(node('a', 'forall', [node('b', 'forall', [leaf('ab', app('Set.Subset', [variable(A), variable(B)]))], B)], A), 'ab');
    const figures = [...html.matchAll(/<svg style="([^"]*)" viewBox="0 0 ([\d.]+) ([\d.]+)" role="group" aria-label="[^"]*: schematic/g)];
    expect(figures.length).toBeGreaterThan(0);
    for (const [, style, width] of figures) expect(style).toMatch(new RegExp(`^width:${width}px;max-width:100%;min-width:${Number(width) * .75}px;height:auto;aspect-ratio:`));
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
    expect(html).toContain('At least one alternative');
    expect(html).toContain('Either or both may hold');
    expect(html).toContain('Alternative 1');
    expect(html).toContain('Alternative 2');
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
    const membership = binary.slice(binary.indexOf('sr-figure-membership'), binary.indexOf('</figure>', binary.indexOf('sr-figure-membership')));
    expect(membership).not.toContain('sr-map-arrow');
    expect(binary).toContain('f(x, y)');
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

  it('keeps scalar premises inline while retaining their source identity and logical placement', () => {
    const epsilon = variable(binder('ε'));
    const { html } = render(node('if', 'implies', [leaf('positive', app('LT.lt', [constant('0'), epsilon], { operator: 'lt', standard: true })), leaf('conclusion')]));
    expect(html).toContain('class="sr-inline-constraint" data-reading-node="positive"');
    expect(html).not.toContain('sr-figure-inequality');
    expect(html.indexOf('aria-label="Given assumptions"')).toBeLessThan(html.indexOf('data-reading-node="positive"'));
    expect(html.indexOf('data-reading-node="positive"')).toBeLessThan(html.indexOf('aria-label="Then the conclusion is required"'));
  });

  it('tells assistive technology which inline object is selected, as the binder buttons do', () => {
    const epsilon = binder('ε');
    const tree = node('bind-ε', 'forall', [leaf('positive', app('LT.lt', [constant('0'), variable(epsilon)], { operator: 'lt', standard: true }))], epsilon);
    const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
    const reading = compileReading(document, { selectedNodeId: 'positive' });
    const selected = document.objects.find(object => object.label === 'ε')!;
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedObjectId: selected.id, onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
    const inline = [...html.matchAll(/<button type="button" class="sr-inline-object[^"]*"[^>]*>/g)].map(match => match[0]);
    const chosen = inline.filter(button => button.includes(`data-reading-object="${selected.id}"`)), others = inline.filter(button => !chosen.includes(button));
    expect(chosen.length).toBeGreaterThan(0);
    expect(others.length).toBeGreaterThan(0);
    for (const button of chosen) expect(button).toContain('aria-pressed="true"');
    for (const button of others) expect(button).toContain('aria-pressed="false"');
  });

  it('keeps a proposition wrapper primary and exposes its geometry as parts of the expression', () => {
    const predicate: Expr = { kind: 'var', id: 'F', name: 'F', type: 'Prop → Prop', typeDescriptor: { kind: 'relation', lean: 'Prop → Prop' } };
    const proposition = app('Set.Mem', [app('Metric.ball', [constant('c'), constant('r')]), constant('x')], { typeDescriptor: { kind: 'proposition', lean: 'Prop' } });
    const expression: Expr = { kind: 'app', fn: predicate, args: [proposition], argumentKinds: ['type'] };
    const { html, document, reading } = render(leaf('wrapper', expression));
    const root = document.relations.find(relation => relation.id === reading.panels[0].rootRelationIds[0])!;
    expect(root.kind).toBe('predicate');
    expect(html).toContain('Inside this expression');
    expect(html).toContain('These are parts of the expression, not separate assertions.');
    expect(html).toContain('<details class="sr-contained-expressions">');
    expect(html.indexOf('Inside this expression')).toBeLessThan(html.indexOf('Membership condition · this condition places the named element'));
    expect(html.indexOf('sr-figure-predicate')).toBeLessThan(html.indexOf('sr-contained-expressions'));
  });

  it('reveals a constructed set operand without replacing the outer equality by an image claim', () => {
    const image = app('Set.image', [variable(binder('f', 'X → Y')), variable(binder('A', 'Set X'))]);
    const { html, document, reading } = render(leaf('equation', app('Eq', [image, variable(binder('B', 'Set Y'))])));
    expect(reading.panels[0].rootRelationIds).toHaveLength(1);
    expect(document.relations.find(relation => relation.id === reading.panels[0].rootRelationIds[0])?.kind).toBe('equality');
    expect(html).toContain('data-reading-node="equation"');
    expect(html).toContain('sc-regions-required-empty');
    expect(html).toContain('The hatched membership regions must be empty');
    expect(html).toContain('Inside this expression');
    expect(html).toContain('How this set is constructed');
    expect(html.indexOf('data-reading-node="equation"')).toBeLessThan(html.indexOf('Inside this expression'));
    expect(html.slice(html.indexOf('Inside this expression'))).toContain('sr-figure-image');
    expect(html).toContain('These are parts of the expression, not separate assertions.');
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

  it('starts a law-free reflected structure closed and keeps a law-bearing one open', () => {
    const limits = { maxFields: 16, maxFieldNodes: 120, maxDepth: 24 } as const;
    const reflect = (owner: Binder, name: string, fields: [string, 'data' | 'law', string][]): Binder => ({ ...owner, structure: { name, typeExpression: constant(name), omittedFields: 0, kernelChecked: true, limits,
      fields: fields.map(([field, kind, type]) => ({ name: field, projection: `${name}.${field}`, expression: app(`${name}.${field}`, [variable(owner)]), type, typeExpression: constant(type),
        typeDescriptor: { kind: kind === 'law' ? 'proposition' : 'unknown', lean: type }, kind, dependsOn: [] })) } });
    const x = reflect(binder('x', 'Wrapped'), 'Wrapped', [['inner', 'data', 'Hidden']]);
    const r = reflect(binder('r', 'Lawful'), 'Lawful', [['value', 'data', 'Hidden'], ['bounded', 'law', 'Bounded r.value']]);
    const tree = node('bind-x', 'forall', [node('bind-r', 'forall', [leaf('claim', app('Unknown.claim', [variable(x), variable(r)]))], r)], x);
    const { html, document } = render(tree);
    const owner = (id: string) => document.objects.find(object => object.binder?.id === id)!.id;
    expect(html).toContain(`<details class="sd-closed-structure"><summary>Inside x · 1 data field · 0 laws</summary><section class="structural-object" data-structural-object="${owner('x')}"`);
    expect(html).toContain(`data-structural-object="${owner('r')}"`);
    expect(html).not.toContain('Inside r · ');
    expect(html).toContain('aria-label="Laws carried by r"');
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
