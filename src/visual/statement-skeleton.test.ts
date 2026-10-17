import { readFileSync } from 'node:fs';
import { createElement, type ReactElement, type ReactNode } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileReading } from '../reading';
import { planReadingPresentation } from '../reading/presentation';
import { scopedFixture } from '../reading/scoped-graph.test-fixtures';
import { compileSemanticDocument } from '../semantic';
import { ROLE_MARKS } from './role-marks';
import { readSkeleton, type SkeletonRow } from './skeleton-readback';
import { StatementReadingView } from './StatementReadingView';
import { skeletonFrames } from './StatementSkeleton';
import { assertSkeletonReadsBack, renderReading, rowView } from './statement-skeleton.test-fixtures';

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, role: Binder['role'] = 'universal', dependsOn: string[] = []): Binder => ({ id, name: id, type: 'ℝ', role, dependsOn });
const variable = (b: Binder): Expr => ({ kind: 'var', id: b.id, name: b.name, type: b.type });
const leaf = (id: string, lean = `${id} source`, expression: Expr = constant('Unknown.condition')): StatementNode => ({ id, kind: 'predicate', label: id, lean, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });
function draw(tree: StatementNode, selectedNodeId?: string) {
  const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
  const reading = compileReading(document, { selectedNodeId });
  const html = renderReading(document, reading);
  return { document, reading, html, skeleton: assertSkeletonReadsBack(document, reading, html) };
}
const rows = (row: SkeletonRow): SkeletonRow[] => [row, ...row.children.flatMap(child => rows(child.row))];
const depth = (row: SkeletonRow): number => 1 + Math.max(0, ...row.children.map(child => depth(child.row)));
/** The rows that enclose a row, outermost first. */
function enclosing(row: SkeletonRow, id: string, path: SkeletonRow[] = []): SkeletonRow[] | undefined {
  if (row.id === id) return path;
  for (const child of row.children) { const found = enclosing(child.row, id, [...path, row]); if (found) return found; }
}
const skeletonMarkup = (html: string) => { const start = html.indexOf('<section class="statement-skeleton"'); return html.slice(start, html.indexOf('</section>', start)); };
/** What a row prints, tags removed: the text of the button that directly follows the row's own element. */
function rowText(html: string, id: string): string {
  const markup = skeletonMarkup(html), from = markup.indexOf('<button', markup.indexOf(`data-skeleton-row="${id}"`));
  return markup.slice(from, markup.indexOf('</button>', from)).replace(/<[^>]*>/g, '').replace(/&lt;/g, '<');
}
type Button = ReactElement<{ onClick: () => void; 'aria-current'?: string; children?: ReactNode }>;
/** Every button of a drawn skeleton, in order. */
const buttons = (value: ReactNode): Button[] => Array.isArray(value) ? value.flatMap(buttons)
  : typeof value === 'object' && value !== null && 'props' in value ? [...(value.type === 'button' ? [value as Button] : []), ...buttons((value.props as { children?: ReactNode }).children)] : [];

/** `∀ x : ℝ, ∃ y : ℝ, x < y` and `∃ y : ℝ, ∀ x : ℝ, x < y`, the two quantifier orders of src/examples.ts. */
function quantifierOrder(first: 'forall' | 'exists') {
  const x = binder('x'), y = binder('y', 'existential', first === 'forall' ? ['x'] : []);
  const clause = leaf('less', 'x < y', { kind: 'app', fn: constant('LT.lt'), args: [variable(x), variable(y)], argumentKinds: ['value', 'value'], operator: 'lt', standard: true });
  return first === 'forall' ? node('for-x', 'forall', [node('some-y', 'exists', [clause], y)], x) : node('some-y', 'exists', [node('for-x', 'forall', [clause], x)], y);
}

describe('the statement skeleton', () => {
  it('tells the two quantifier orders apart by the clause row\'s chain of enclosing binder rows', () => {
    const chain = (tree: StatementNode) => enclosing(draw(tree).skeleton, 'less')!.map(row => `${row.binder} ${row.names.join(' ')}`);
    expect(chain(quantifierOrder('forall'))).toEqual(['forall x', 'exists y']);
    expect(chain(quantifierOrder('exists'))).toEqual(['exists y', 'forall x']);
  });

  it('draws a witness in a different frame and weight from an arbitrary choice, not only a different glyph or hue', () => {
    const { html } = draw(quantifierOrder('forall'));
    expect(html).toContain('class="sk-region sk-binders sk-universal" data-skeleton-row="for-x"');
    expect(html).toContain('class="sk-region sk-binders sk-existential" data-skeleton-row="some-y"');
    const rules = cssRules(css('statement-skeleton.css'));
    const witness = rules.filter(rule => rule.selector.includes('.sk-existential')), arbitrary = rules.filter(rule => rule.selector.includes('.sk-universal'));
    expect(witness.find(rule => rule.selector === '.sk-existential')!.declarations).toMatch(/border:2px solid/);
    expect(witness.some(rule => /font-weight:700/.test(rule.declarations))).toBe(true);
    expect([...witness, ...arbitrary].filter(rule => /(?:^|;)\s*(?:color|background(?:-color)?)\s*:/.test(rule.declarations))).toEqual([]);
  });

  it('prints on each row its own mark, name, type and role words, and nothing else', () => {
    const order = draw(quantifierOrder('forall'));
    expect(rowText(order.html, 'for-x')).toBe('∀x: ℝ');
    expect(rowText(order.html, 'some-y')).toBe('∃y: ℝ');
    expect(rowText(order.html, 'less')).toBe('x < y');
    expect(rows(order.skeleton).map(row => row.mark)).toEqual(['∀', '∃', undefined]);
    expect(rows(draw(quantifierOrder('exists')).skeleton).map(row => row.mark)).toEqual(['∃', '∀', undefined]);
    // A connective row is its glyph and the full reading's words for it.
    const connectives = draw(node('either', 'or', [node('both', 'and', [leaf('p'), leaf('q')]), node('no', 'not', [node('same', 'iff', [leaf('r'), leaf('s')])])]));
    expect(['either', 'both', 'no', 'same'].map(id => rowText(connectives.html, id))).toEqual(['∨At least one alternative', '∧Together', '¬Not', '↔Equivalent conditions']);
    // A local definition keeps its value on the row.
    const defined: Binder = { id: 'd', name: 'd', type: 'ℝ', role: 'definition', dependsOn: [], definition: { value: constant('c'), nondep: true } };
    expect(rowText(draw(node('let-d', 'definition', [leaf('body')], defined)).html, 'let-d')).toBe(':=Local definitionsd: ℝ := c');
    // A selected expression says what each binder group is to it; a statement's quantifier rows carry no such words.
    const component = { ...order.document, presentation: { kind: 'component' as const, target: 'term' as const, logicalRootNodeId: 'some-y' } };
    const selected = renderReading(component, compileReading(component));
    expect(rowText(selected, 'for-x')).toBe('∀Function inputsx: ℝ');
    expect(rowText(selected, 'some-y')).toBe('∃Candidate within the existential statementy: ℝ');
  });

  it('never draws an empty row: a clause without text shows its region kind', () => {
    const { html, skeleton } = draw(node('for-x', 'forall', [{ ...leaf('blank', ''), phrase: '' } as StatementNode], binder('x')));
    expect(rowText(html, 'blank')).toBe('clause');
    expect(rows(skeleton).map(row => row.kind)).toEqual(['binders', 'clause']);
  });

  it('is the first thing in the reading, with the formal clause and never a paraphrase', () => {
    const { html } = draw(quantifierOrder('forall'));
    expect(html.indexOf('class="statement-skeleton"')).toBeLessThan(html.indexOf('class="reading-guide"'));
    expect(html.match(/class="statement-skeleton"/g)).toHaveLength(1);
    expect(skeletonMarkup(html)).toContain('>x &lt; y</button>');
    expect(skeletonMarkup(html)).not.toContain('is less than');
    expect(html).not.toContain('sr-overview');
  });

  it('reads back to the region tree through every connective, hypothesis chain and binder group', () => {
    const p = leaf('p'), q = leaf('q'), r = leaf('r'), s = leaf('s');
    const { skeleton } = draw(node('a', 'forall', [node('b', 'forall', [node('if', 'implies', [node('premise', 'implies', [p, q]), node('then', 'implies', [r, node('either', 'or', [node('no', 'not', [s]), node('same', 'iff', [leaf('t'), leaf('u')])])])])], binder('b'))], binder('a')));
    expect(rowView(skeleton)).toMatchObject({ kind: 'binders', nodeIds: ['a', 'b'], children: [{ edge: 'body', row: { kind: 'implication', nodeIds: ['if', 'then'],
      children: [{ edge: 'assumption', row: { kind: 'implication', nodeIds: ['premise'] } }, { edge: 'assumption', row: { kind: 'clause', nodeIds: ['r'] } }, { edge: 'conclusion', row: { kind: 'alternatives', children: [{ edge: 'alternative', row: { kind: 'negation' } }, { edge: 'alternative', row: { kind: 'equivalence' } }] } }] } }] });
    expect(skeleton.names).toEqual(['a', 'b']);
    draw(scopedFixture().nodes.tree);
  });

  it('keeps a region beyond the display bound as one stub that counts the rows it stands for', () => {
    const tree = node('all', 'and', Array.from({ length: 120 }, (_, index) => node(`not-${index}`, 'not', [leaf(`condition-${index}`)])));
    const { skeleton, html } = draw(tree);
    const stubs = rows(skeleton).filter(row => row.folded !== undefined);
    expect(stubs.length).toBeGreaterThan(0);
    expect(stubs.every(row => row.children.length === 0)).toBe(true);
    // Nothing is lost: the drawn rows and the rows the stubs stand for are the statement's 1 + 120 × 2 regions.
    expect(rows(skeleton).length - stubs.length + stubs.reduce((sum, row) => sum + row.folded!, 0)).toBe(241);
    expect(skeletonMarkup(html)).toContain('¬ Not · 2 folded rows');
    expect(skeletonMarkup(html)).toContain('source · 1 folded row');
    const selected = draw(tree, 'condition-119').skeleton;
    expect(enclosing(selected, 'condition-119')!.map(row => row.id)).toEqual(['all', 'not-119']);
  });

  it('draws every row strictly inside its parent at depth 6 and beyond, with one frame per level', () => {
    let tree: StatementNode = leaf('innermost');
    for (const [index, kind] of (['not', 'exists', 'and', 'forall', 'or', 'iff', 'exists', 'forall'] as const).entries())
      tree = node(`level-${index}`, kind, kind === 'and' || kind === 'or' || kind === 'iff' ? [leaf(`side-${index}`), tree] : [tree], kind === 'exists' ? binder(`w${index}`, 'existential') : kind === 'forall' ? binder(`v${index}`) : undefined);
    tree = node('guard', 'implies', [leaf('given'), tree]);
    const { skeleton, html } = draw(tree);
    expect(depth(skeleton)).toBeGreaterThanOrEqual(6);
    expect(enclosing(skeleton, 'innermost')!.map(row => row.id)).toEqual(['guard', 'level-7', 'level-6', 'level-5', 'level-4', 'level-3', 'level-2', 'level-1', 'level-0']);
    // readSkeleton refuses a row that is not inside a frame of its parent; every such frame is one of the two indenting kinds.
    const frames = [...skeletonMarkup(html).matchAll(/<div class="([^"]*)" data-skeleton-edge="[^"]*">/g)].map(match => match[1]);
    expect(frames).toHaveLength(rows(skeleton).length - 1);
    expect(new Set(frames)).toEqual(new Set(['sk-children', 'sk-given']));
    expect(skeletonMarkup(html)).not.toMatch(/deep/);
  });

  it('selects the source node of the row that is pressed, as the outline did', () => {
    const tree = node('a', 'forall', [node('if', 'implies', [leaf('p'), node('then', 'implies', [leaf('q'), node('w', 'exists', [node('both', 'and', [leaf('r'), leaf('s')])], binder('w', 'existential'))])])], binder('a'));
    const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression }), reading = compileReading(document);
    const pressed: string[] = [];
    const frames = (visible: ReadonlySet<string>) => skeletonFrames({ root: planReadingPresentation(reading).root, document, visibleNodes: visible, onNodeSelect: id => pressed.push(id), colorOf: () => 'var(--ink)' });
    buttons(frames(new Set(reading.nodes.map(item => item.id)))).forEach(button => button.props.onClick());
    // One Given mark per implication node of the chain, each hypothesis and clause by its own node.
    expect(pressed).toEqual(['a', 'if', 'p', 'then', 'q', 'w', 'both', 'r', 's']);
    pressed.length = 0;
    buttons(frames(new Set(['a', 'if', 'p', 'then', 'q']))).forEach(button => button.props.onClick());
    expect(pressed).toEqual(['a', 'if', 'p', 'then', 'q', 'w']);
  });

  it('marks the row of the current reading step and no other', () => {
    const { html } = draw(quantifierOrder('forall'), 'less');
    expect(skeletonMarkup(html)).toContain('<button type="button" class="sk-row sk-selected" aria-current="true">x &lt; y</button>');
    expect(skeletonMarkup(html).match(/aria-current/g)).toHaveLength(1);
    expect(skeletonMarkup(draw(quantifierOrder('forall')).html)).toContain('data-skeleton-row="for-x" data-skeleton-kind="binders" data-skeleton-nodes="for-x" data-skeleton-binder="forall"><button type="button" class="sk-row sk-selected" aria-current="true"');
  });

  it('marks one Given row of a hypothesis chain: the selected hypothesis, otherwise the first', () => {
    const tree = node('a', 'forall', [node('if', 'implies', [leaf('p'), node('then', 'implies', [leaf('q'), leaf('r')])])], binder('a'));
    for (const [selected, marked] of [[undefined, 'if'], ['if', 'if'], ['then', 'then']] as const) {
      const { document, reading, html } = draw(tree, selected);
      expect(skeletonMarkup(html).match(/aria-current/g), String(selected)).toHaveLength(1);
      // Pressing the marked row tells which node it stands for.
      const pressed: string[] = [];
      const frames = skeletonFrames({ root: planReadingPresentation(reading).root, document, visibleNodes: new Set(reading.nodes.map(item => item.id)), activeRegionId: 'if', activeNodeId: selected, onNodeSelect: id => pressed.push(id), colorOf: () => 'var(--ink)' });
      buttons(frames).filter(button => button.props['aria-current']).forEach(button => button.props.onClick());
      expect(pressed, String(selected)).toEqual([marked]);
    }
  });

  it('marks the row of the step being read, not the row of the selection, when the two differ', () => {
    // The whole statement is still selected while the guide is on the clause's own relation.
    const { document, reading } = draw(quantifierOrder('forall'));
    const relation = document.relations.find(candidate => candidate.nodeId === 'less')!;
    const markup = skeletonMarkup(renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedRelationId: relation.id })));
    expect(reading.selection.nodeId).toBe('for-x');
    expect(markup).toContain('<button type="button" class="sk-row sk-selected" aria-current="true">x &lt; y</button>');
    expect(markup.match(/aria-current/g)).toHaveLength(1);
  });

  it('underlines the name of the selected object and no other', () => {
    const { document, reading } = draw(quantifierOrder('forall'));
    const y = document.objects.find(object => object.binder?.id === 'y')!;
    const markup = skeletonMarkup(renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedObjectId: y.id })));
    expect(markup.match(/sk-object-selected/g)).toHaveLength(1);
    expect(markup).toContain(`<span class="sk-name sk-object-selected" data-skeleton-name="" data-reading-object="${y.id}"`);
  });

  it('is unchanged by renaming bound variables, apart from the labels', () => {
    const first = scopedFixture(), renamed = scopedFixture({ radius: 'uniformAllowance', point: 'candidatePoint', index: 'labelChoice', family: 'localDomains', set: 'admissibleInputs' });
    const drawn = (value: typeof first) => { const html = renderReading(value.document, value.reading); return { html: skeletonMarkup(html), skeleton: readSkeleton(html) }; };
    const a = drawn(first), b = drawn(renamed);
    expect(rowView(b.skeleton)).toEqual(rowView(a.skeleton));
    expect(rows(b.skeleton).map(row => row.binder)).toEqual(rows(a.skeleton).map(row => row.binder));
    expect(rows(a.skeleton).flatMap(row => row.names)).toEqual(['c', 's', 'δ', 'x', 'i']);
    expect(rows(b.skeleton).flatMap(row => row.names)).toEqual(['localDomains', 'admissibleInputs', 'uniformAllowance', 'candidatePoint', 'labelChoice']);
    const unlabelled = (html: string) => html.replace(/ title="[^"]*"/g, '').replace(/>[^<]+</g, '><');
    expect(unlabelled(b.html)).toBe(unlabelled(a.html));
    expect(b.html).not.toBe(a.html);
  });
});

const css = (file: string) => readFileSync(new URL(file, import.meta.url), 'utf8').replace(/\/\*[\s\S]*?\*\//g, '');
function cssRules(source: string) {
  return [...source.matchAll(/([^{}]+)\{([^{}]*)\}/g)].flatMap(match => match[1]!.split(',').map(selector => ({ selector: selector.trim(), declarations: match[2]!.replace(/\s+/g, ' ').trim() })));
}
const nestedFrames = /\.sk-children\b|\.sk-given\b|\.sr-negated-body\b|\.sr-alternative\b(?!s)|\.sr-equivalent-conditions\s*>\s*section\b|\[data-role-frame\]|\.role-frame\b/;
/** Rules that take the left step or rail away from a frame that holds nested children. */
function flatteningRules(source: string): string[] {
  const zero = (value: string) => /^0(?:px|em|rem)?$/.test(value.trim());
  const leftOf = (shorthand: string) => { const parts = shorthand.trim().split(/\s+/); return parts[3] ?? parts[1] ?? parts[0]!; };
  return cssRules(source).filter(rule => nestedFrames.test(rule.selector) && rule.declarations.split(';').some(declaration => {
    const [property, value = ''] = declaration.split(':').map(part => part.trim());
    if (property === 'margin-left' || property === 'padding-left' || property === 'border-left-width') return zero(value);
    if (property === 'margin' || property === 'padding') return zero(leftOf(value));
    return (property === 'border-left' || property === 'border') && /^(?:0(?:px)?\b|none\b)/.test(value);
  })).map(rule => rule.selector);
}
/** Grid tracks of the skeleton that may become narrower than their content: a fixed length, or a `minmax` whose
 * minimum is a fixed length. Such a track lets a grid report a min-content width without its items, and an enclosing
 * frame sized from that width no longer encloses them. */
function shrinkingTracks(source: string): string[] {
  const tracks = (list: string) => { const out: string[] = []; let depth = 0, current = '';
    for (const character of list.trim()) { if (character === '(') depth++; if (character === ')') depth--;
      if (/\s/.test(character) && depth === 0) { if (current) out.push(current); current = ''; } else current += character; }
    if (current) out.push(current); return out; };
  const fixed = (value: string) => /^-?[\d.]+(?:px|em|rem|%|vw|ch)?$/.test(value.trim());
  // `repeat(n, tracks)` is read as the tracks it repeats, each listed once.
  const expanded = (track: string): string[] => /^repeat\(/.test(track) ? tracks(track.slice(7, -1).split(',').slice(1).join(',')).flatMap(expanded) : [track];
  return cssRules(source).flatMap(rule => rule.declarations.split(';').flatMap(declaration => {
    const [property, value = ''] = declaration.split(':').map(part => part.trim());
    if (property !== 'grid-template-columns') return [];
    return tracks(value).flatMap(expanded).filter(track => fixed(track) || /^minmax\(/.test(track) && fixed(track.slice(7).split(',')[0]!))
      .map(track => `${rule.selector}: ${track}`);
  }));
}
const pixels = (declarations: string, property: string) => Number(new RegExp(`(?:^|;)\\s*${property}:\\s*([\\d.]+)px`).exec(declarations)?.[1] ?? 0);

describe('reader stylesheets', () => {
  const sheets = ['statement-skeleton.css', 'statement-reading.css', 'guided-reading.css', 'scoped-statement-graph.css', 'role-marks.css'].map(css);

  it('give every nested frame the same nonzero step and rail at every depth', () => {
    const frame = cssRules(sheets[0]!).find(rule => rule.selector === '.sk-children')!;
    expect(pixels(frame.declarations, 'margin-left') + pixels(frame.declarations, 'padding-left')).toBeGreaterThanOrEqual(16);
    expect(frame.declarations).toMatch(/border-left:1px solid/);
    expect(sheets.flatMap(flatteningRules)).toEqual([]);
    // The rule this replaces, and its like, are caught.
    expect(flatteningRules('.sk-deep > .sk-children { margin-left:0; padding-left:0; }')).toEqual(['.sk-deep > .sk-children']);
    expect(flatteningRules('.sr-deep-region .sr-negated-body { padding-left:0; border-left:0; } .sr-deep-region .sr-alternative { padding:12px 0 0 0; }')).toEqual(['.sr-deep-region .sr-negated-body', '.sr-deep-region .sr-alternative']);
    expect(flatteningRules('.sr-alternatives { padding-left:0; } .sr-alternative { padding:12px 0 0 15px; }')).toEqual([]);
  });

  it('set the formal clause larger than any instruction and no smaller than a relation figure\'s text', () => {
    const size = (sheet: string, selector: string) => pixels(cssRules(sheet).find(rule => rule.selector === selector)!.declarations, 'font-size');
    const clauseSizes = cssRules(sheets[0]!).filter(rule => rule.selector === '.sk-clause > .sk-row').map(rule => pixels(rule.declarations, 'font-size'));
    // The second rule is the narrow column's.
    expect(clauseSizes).toHaveLength(2);
    const clause = Math.min(...clauseSizes);
    expect(clause).toBeGreaterThanOrEqual(22);
    // The guide draws no step title: it is the selector's text, kept for assistive technology only.
    expect(sheets[2]!).not.toMatch(/\.rg-heading/);
    const guideSizes = [...sheets[2]!.matchAll(/font(?:-size)?:[^;{}]*?([\d.]+)px/g)].map(match => Number(match[1]));
    expect(Math.max(...guideSizes)).toBeLessThan(clause);
    for (const selector of ['.sr-region-heading .sr-source-button', '.sr-role-heading', '.sr-heading-lead']) expect(size(sheets[1]!, selector)).toBeLessThan(clause);
    // A relation figure is drawn at one unit per pixel (statement-reading.test.ts), so these are its sizes on screen.
    for (const selector of ['.sr-object-label', '.sr-comparison-symbol']) expect(size(sheets[1]!, selector)).toBeLessThanOrEqual(clause);
    const figure = cssRules(sheets[1]!).filter(rule => /^\.sr-relation-figure(?: svg)?$/.test(rule.selector)).map(rule => rule.declarations).join(';');
    expect(figure).not.toMatch(/(?:^|;)\s*(?:width|max-width)\s*:|margin:[^;]*auto/);
  });

  it('let no skeleton grid column shrink below what it holds, so every frame encloses its rows at any width', () => {
    // Measured in a 300px column on 2026-10-17: with `minmax(0,1fr)` the ε–δ example's δ box was 236px wide and its
    // hypothesis and conclusion rows crossed its right border by 59px and 82px.
    expect(shrinkingTracks(sheets[0]!)).toEqual([]);
    expect(shrinkingTracks('.sk-implication { display:grid; grid-template-columns:auto minmax(0,1fr); }')).toEqual(['.sk-implication: minmax(0,1fr)']);
    expect(shrinkingTracks('.x { grid-template-columns:120px 1fr minmax(min-content, 1fr) repeat(2, auto); }')).toEqual(['.x: 120px']);
    expect(shrinkingTracks('.x { grid-template-columns:repeat(2,minmax(0,1fr)); }')).toEqual(['.x: minmax(0,1fr)']);
    // The reading view's two grids are listed so that no new one passes unnoticed. Neither draws a frame around its
    // items: the alternatives carry a rail on their left and top edges only, and the Given grid has no border. So a
    // too-wide item runs past its column instead of crossing a border that claims to hold it. Whether it then runs
    // under the neighbouring alternative's rail in a narrow column has not been measured.
    expect(shrinkingTracks(sheets[1]!)).toEqual([
      '.sr-alternatives: minmax(0,1fr)', '.sr-equivalent-conditions: minmax(0,1fr)',
      '.sr-given-region:has(> .sr-region-stack > .sr-region-clause:only-child > .sr-inline-constraint): 64px',
      '.sr-given-region:has(> .sr-region-stack > .sr-region-clause:only-child > .sr-inline-constraint): minmax(0,1fr)']);
    for (const sheet of sheets.slice(2)) expect(shrinkingTracks(sheet)).toEqual([]);
    // A region is never narrower than its own content, and the outermost one keeps that minimum over its maximum.
    expect(cssRules(sheets[0]!).find(rule => rule.selector === '.sk-region')!.declarations).toBe('min-width:min-content;');
  });

  it('keep the skeleton frame\'s height the same whether or not it scrolls', () => {
    // Without its own formatting context the frame loses a witness's outer margin while it does not scroll and gains
    // it when it does, so crossing that width changes the height under the reader.
    expect(cssRules(sheets[0]!).find(rule => rule.selector === '.statement-skeleton > .figure-scroll')!.declarations).toBe('display:flow-root;');
  });

  it('give each role one rail, in ink only, distinct across standings, as the mark table says', () => {
    const rules = cssRules(css('role-marks.css')).filter(rule => rule.selector.startsWith('[data-role-frame]'));
    const ruleOf = (edge: string) => { const found = rules.filter(rule => rule.selector === `[data-role-frame][data-role="${edge}"]`); expect(found, edge).toHaveLength(1); return found[0]!.declarations; };
    const style = (edge: string) => /border-left:\s*[\d.]+px (solid|double|dashed|dotted) /.exec(ruleOf(edge))?.[1];
    for (const [edge, mark] of Object.entries(ROLE_MARKS)) expect(style(edge), edge).toBe(mark.rail);
    // One rule per role and no other: given, then, not and the three that are neither asserted nor denied on their own.
    expect(rules.map(rule => rule.selector).sort()).toEqual(Object.keys(ROLE_MARKS).map(edge => `[data-role-frame][data-role="${edge}"]`).sort());
    expect(new Set(['assumption', 'conclusion', 'negated', 'alternative'].map(style)).size).toBe(4);
    expect(new Set(['alternative', 'side', 'part'].map(style))).toEqual(new Set(['dotted']));
    // The Given rail is wide enough to show two lines, and the Not rail is the skeleton's.
    expect(ruleOf('assumption')).toMatch(/border-left:3px double var\(--sr-ink\)/);
    expect(ruleOf('negated')).toMatch(/border-left:2px dashed var\(--sr-ink\)/);
    // No role rule carries hue: no colour or background, and every rail is ink or the neutral structure line.
    expect(rules.filter(rule => /(?:^|;)\s*(?:color|background(?:-color)?)\s*:/.test(rule.declarations))).toEqual([]);
    expect(rules.every(rule => /border-left:[^;]*var\(--(?:sr-ink|line-structure)\)/.test(rule.declarations))).toBe(true);
    // Every frame steps in by the same amount, rail included.
    const step = (edge: string) => pixels(ruleOf(edge), 'padding-left') + Number(/border-left:\s*([\d.]+)px/.exec(ruleOf(edge))![1]);
    expect(new Set(Object.keys(ROLE_MARKS).map(step))).toEqual(new Set([15]));
  });

  it('let only a frame draw a left rail, and draw no line of logical path beside the figure', () => {
    // A left rail inside a figure would read as one more role frame. The frames that may draw one: the skeleton's and
    // the full reading's (not yet drawn with the role frames), the construction graph's, a local expression scope's
    // neutral rail, and the role frames.
    const frames = /^(?:\.sk-children|\.sk-negation > \.sk-children|\.sr-alternative|\.sr-equivalent-conditions > section|\.sr-negated-body|\.sr-contained-group|\.ssg-frame|\.ssg-frame-equivalence|\[data-role-frame\]\[data-role="[a-z]+"\])$/;
    const rails = (source: string) => cssRules(source).filter(rule => rule.declarations.split(';').some(declaration => {
      const [property, value = ''] = declaration.split(':').map(part => part.trim());
      return property === 'border-left' && !/^(?:0(?:px)?\b|none\b)/.test(value) || (property === 'border-left-style' && value !== 'none') || (property === 'border-left-width' && !/^0(?:px)?$/.test(value));
    })).map(rule => rule.selector);
    const readerSheets = [...sheets, ...['../graphs/graphs.css', '../restricted/restricted.css', '../set-constructions/set-constructions.css', '../decomposition/decomposition.css', '../constructions/constructions.css', '../statement-geometry/metric-statement.css'].map(css)];
    expect(readerSheets.flatMap(rails).filter(selector => !frames.test(selector))).toEqual([]);
    // The rules this replaced are caught.
    expect(rails('.rg-local-binders { border-left:2px solid #b9c5cd; } .gc-one-color{border-left:2px solid #b8cdd1;padding-left:12px}')).toEqual(['.rg-local-binders', '.gc-one-color']);
    expect(sheets.join('\n')).not.toMatch(/rg-logical-path/);
  });

  it('put a conclusion under its hypotheses and what is negated under a heavy dashed rail', () => {
    const rule = (selector: string) => cssRules(sheets[0]!).find(candidate => candidate.selector === selector)!.declarations;
    // The Given marks are the first column; hypotheses and the conclusion share the second, so the conclusion's
    // own step puts it further in than every hypothesis.
    // The marks' column is as wide as the word Given, and the second column never narrower than what it holds.
    expect(rule('.sk-implication')).toMatch(/display:grid; grid-template-columns:max-content minmax\(min-content,1fr\)/);
    expect(rule('.sk-given')).toBe('display:contents;');
    for (const selector of ['.sk-given > .sk-region', '.sk-given > .sk-stub', '.sk-implication > .sk-children']) expect(rule(selector)).toBe('grid-column:2;');
    // The negation's rail is as heavy as the witness's box and keeps the same total step as every other frame.
    const frame = rule('.sk-children'), negated = rule('.sk-negation > .sk-children');
    expect(negated).toMatch(/border-left:2px dashed var\(--sr-ink\)/);
    expect(pixels(negated, 'padding-left') + 2).toBe(pixels(frame, 'padding-left') + 1);
  });
});
