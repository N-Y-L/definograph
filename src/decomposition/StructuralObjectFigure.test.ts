import { Fragment, createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { SemanticObject } from '../semantic/types';
import type { TypedConstruction } from '../constructions/model';
import type { StructuralField, StructuralObjectModel } from './types';
import { StructuralObjectFigure, startsClosed, layoutStructuralCarrier } from './StructuralObjectFigure';

const object = (id: string, label = id, type = 'M'): SemanticObject => ({ id, label, type, kind: 'expression', expression: { kind: 'var', id, name: label, type }, scopeId: 'scope:owner', provenance: [{ nodeId: 'owner', expressionPath: id, origin: 'elaborated-expression' }] });
const field = (name: string, kind: 'data' | 'law' = 'data', type = 'M'): StructuralField => ({ name, projection: `UnseenRecord.${name}`, object: object(`field:${name}`, `e.${name}`, type), type, typeExpression: { kind: 'const', name: type }, kind, dependsOn: [] });
const construction = (extra: Partial<TypedConstruction> = {}): TypedConstruction => ({ status: 'ready', role: 'parameter', objects: [], types: [], maps: [], members: [], signatures: [], unknowns: [], diagnostics: [], ...extra });
const base = (extra: Partial<StructuralObjectModel> = {}): StructuralObjectModel => ({ object: object('e', 'e', 'UnseenRecord M N'), declarationName: 'UnseenRecord', fields: [], construction: construction(), omittedFields: 0, ...extra });
const property = (name: string, type: string) => ({ objectId: `field:${name}`, binderId: `binder:${name}`, name: `e.${name}`, type, role: 'parameter' as const, scopeId: 'scope:owner' });
const types = () => [
  { id: 'type:M', label: 'M', expression: { kind: 'const' as const, name: 'M' }, objectId: 'M', introduced: false },
  { id: 'type:N', label: 'N', expression: { kind: 'const' as const, name: 'N' }, objectId: 'N', introduced: false },
];
const mapped = (): StructuralObjectModel => base({ fields: [field('pass', 'data', 'M → N'), field('area', 'data', 'Set M'), field('law', 'law', '∀ x, P x → Q (e.pass x)')], construction: construction({
  types: types(), maps: [{ ...property('pass', 'M → N'), domainId: 'type:M', codomainId: 'type:N' }],
  members: [{ ...property('area', 'Set M'), kind: 'set', typeId: 'type:M' }],
}) });
const html = (model: StructuralObjectModel) => renderToStaticMarkup(createElement(StructuralObjectFigure, { model }));

describe('generic structural object rendering', () => {
  it('renders previously unseen fields from type primitives while preserving the owner and original type', () => {
    const rendered = html(mapped());
    expect(rendered).toContain('data-structural-object="e"');
    expect(rendered).toContain('UnseenRecord M N');
    expect(rendered).toContain('data-structural-map="field:pass"');
    expect(rendered).toContain('data-structural-region="field:area"');
    expect(rendered).toContain('2 data fields');
    expect(rendered).toContain('Law of this object');
    expect(rendered).not.toContain('Parameter e.pass');
    expect(rendered).not.toContain('There exists');
    expect(rendered).not.toContain('For every e.pass');
  });

  it('uses only provided set and map primitives and creates no point locations or inverse laws', () => {
    const rendered = html(mapped());
    expect(rendered).not.toContain('<circle');
    expect(rendered).not.toContain('inverse');
    expect(rendered).not.toContain('continuous');
    expect(rendered).not.toContain('open source');
    expect(rendered).toContain('with no coordinates, shape, size, or chosen elements');
  });

  it('retains the current owner context rather than asserting field laws globally', () => {
    const rendered = html(mapped());
    expect(rendered).toContain('within the statement’s current quantifiers and assumptions');
    expect(rendered).toContain('data-structural-law="UnseenRecord.law"');
    expect(rendered).toContain('∀ x, P x → Q (e.pass x)');
  });

  it('starts the law sequence in declaration order and delegates interpretation to the ordinary logical reader', () => {
    const first = field('conditionFirst', 'law', 'OpaqueLaw e'), second = field('conditionSecond', 'law', 'SecondLaw e');
    const model = base({ fields: [first, second] });
    const rendered = renderToStaticMarkup(createElement(StructuralObjectFigure, { model, renderLaw: law => createElement('div', { 'data-law-reader': law.projection }, law.type) }));
    expect(rendered).toContain('data-law-reader="UnseenRecord.conditionFirst"');
    expect(rendered).not.toContain('data-law-reader="UnseenRecord.conditionSecond"');
    expect(rendered.indexOf('conditionFirst')).toBeLessThan(rendered.indexOf('conditionSecond'));
    expect(rendered).toContain('aria-label="Field law sequence"');
    expect(rendered).toMatch(/<button type="button" disabled="">Previous law/);
    expect(rendered).toContain('OpaqueLaw e');
  });

  it('keeps unknown field types and laws as explicit text without selecting a familiar-looking scene', () => {
    const model = base({ fields: [field('toFun', 'data', 'Mystery'), field('hairyBall', 'law', 'Unknown e.toFun')] });
    const rendered = html(model);
    expect(rendered).toContain('Mystery');
    expect(rendered).toContain('Unknown e.toFun');
    expect(rendered).not.toContain('data-structural-map=');
    expect(rendered).not.toContain('data-structural-region=');
    expect(rendered).not.toContain('data-graph-');
    expect(rendered).not.toContain('data-restricted-');
  });

  it('shows dependent and multiple input types as signatures, not invented simple maps', () => {
    const model = base({ fields: [field('section', 'data', '(x : M) → F x')], construction: construction({ signatures: [{
      ...property('section', '(x : M) → F x'), kind: 'dependent-map', inputs: [{ name: 'x', type: 'M', dependsOn: [] }], result: 'F x', resultDependsOn: [0], explanation: 'The result type depends on the input.',
    }] }) });
    const rendered = html(model);
    expect(rendered).toContain('data-structural-signature="field:section"');
    expect(rendered).toContain('dependent map field');
    expect(rendered).toContain('Depends on input 1');
    expect(rendered).not.toContain('data-structural-map=');
    expect(rendered).not.toContain('data-structural-region=');
  });

  it('retains different carrier identities even when their labels are equal', () => {
    const model = mapped();
    const renamed = { ...model, construction: { ...model.construction, types: model.construction.types.map(type => ({ ...type, label: 'SameName' })) } };
    const rendered = html(renamed);
    expect(rendered).toContain('data-structural-carrier="type:M"');
    expect(rendered).toContain('data-structural-carrier="type:N"');
    expect(rendered).toContain('data-reading-object="M"');
    expect(rendered).toContain('data-reading-object="N"');
  });

  it('reports bounded omitted fields and does not fabricate empty record contents', () => {
    const rendered = html(base({ omittedFields: 7, stopReason: 'The declared field limit was reached.' }));
    expect(rendered).toContain('7 further fields remain');
    expect(rendered).toContain('The declared field limit was reached.');
    expect(rendered).not.toContain('data-structural-law=');
    expect(rendered).not.toContain('data-structural-map=');
    expect(rendered).not.toContain('Field law sequence');
  });

  it('keeps full long labels accessible and provides selected object keyboard controls', () => {
    const label = `recordWith${'LongName'.repeat(40)}`, model = { ...mapped(), object: object('e', label, 'OriginalRecordType') };
    const rendered = renderToStaticMarkup(createElement(StructuralObjectFigure, { model, selectedObjectId: 'field:pass', onObjectSelect: () => undefined }));
    expect(rendered).toContain(`aria-label="${label} : OriginalRecordType"`);
    expect(rendered).toContain('…');
    expect(rendered).toContain('aria-pressed="true"');
    expect(rendered).toContain('tabindex="0"');
  });

  it('creates unique arrow marker IDs for separately composed object diagrams', () => {
    const rendered = renderToStaticMarkup(createElement(Fragment, null, createElement(StructuralObjectFigure, { model: mapped() }), createElement(StructuralObjectFigure, { model: mapped() })));
    const markers = [...rendered.matchAll(/<marker id="([^"]+)"/g)].map(match => match[1]);
    expect(markers).toHaveLength(2);
    expect(new Set(markers).size).toBe(2);
  });

  it('typesets complete carrier and field labels without changing their exact identities', () => {
    const original = mapped(), long = `field_${'escaped{value}%'.repeat(8)}δ`;
    const model: StructuralObjectModel = { ...original, construction: { ...original.construction,
      types: original.construction.types.map((type, i) => i ? type : { ...type, label: 'α₁', expression: { kind: 'var', id: 'carrier:M', name: 'α₁', type: 'Type' } }),
      maps: original.construction.maps.map(map => ({ ...map, name: long })), members: original.construction.members.map(member => ({ ...member, name: 'σ₂' })),
    } };
    const before = JSON.stringify(model), rendered = html(model), svg = rendered.slice(rendered.indexOf('<svg'), rendered.indexOf('</svg>'));
    expect(svg).toContain('class="katex-html"'); expect(svg).toContain('<msub>'); expect(svg).toContain('<math');
    expect(svg).toContain(`data-diagram-source="${long}"`); expect(svg).not.toContain('…');
    expect(svg).toContain('data-reading-object="field:pass"'); expect(svg).toContain('data-structural-region="field:area"');
    expect(JSON.stringify(model)).toBe(before);
  });

  it('reserves disjoint rows and carrier bounds for tall notation and wide set names', () => {
    const type = { width: 190, height: 78, ascent: 56, descent: 22 };
    const members = [{ kind: 'set' as const, size: { width: 680, height: 66, ascent: 46, descent: 20 } },
      { kind: 'element' as const, size: { width: 210, height: 48, ascent: 36, descent: 12 } }];
    const layout = layoutStructuralCarrier(type, members);
    expect(layout.width).toBeGreaterThan(members[0].size.width + 26);
    expect(layout.typeBaseline + type.descent).toBeLessThan(layout.captionBaseline);
    expect(layout.captionBaseline).toBeLessThan(layout.rows[0].top);
    layout.rows.forEach((row, index) => {
      expect(row.baseline - members[index].size.ascent).toBeGreaterThan(row.top);
      expect(row.baseline + members[index].size.descent).toBeLessThan(row.top + row.height);
      expect(row.top + row.height).toBeLessThan(index + 1 < layout.rows.length ? layout.rows[index + 1].top : layout.height);
    });
  });
});

describe('closed boxes for law-free structures', () => {
  const lawFree = () => base({ fields: [field('inner', 'data', 'Opaque M')] });
  const enclosed = (model: StructuralObjectModel) => renderToStaticMarkup(createElement(StructuralObjectFigure, { model, enclosed: true }));

  it('starts a complete law-free structure closed, naming the owner and counts, with the unchanged figure inside', () => {
    const model = lawFree();
    expect(startsClosed(model)).toBe(true);
    const open = enclosed(model);
    expect(open).toMatch(/^<section class="structural-object"/);
    expect(open).toContain('<span class="sd-count">1 data field · 0 laws</span>');
    expect(html(model)).toBe(`<details class="sd-closed-structure"><summary>Inside e · 1 data field · 0 laws</summary>${open}</details>`);
    expect(html(model)).toContain('data-reading-object="field:inner"');
  });

  it('keeps law-bearing structures open, as before', () => {
    for (const model of [mapped(), base({ fields: [field('inner', 'data', 'Opaque M'), field('bounded', 'law', 'Bounded e.inner')] }), base({ fields: [field('twice', 'law', 'Twice e')] })]) {
      expect(startsClosed(model)).toBe(false);
      const rendered = html(model);
      expect(rendered).toMatch(/^<section class="structural-object"/);
      expect(rendered).not.toContain('sd-closed-structure');
      expect(rendered).toContain('aria-label="Laws carried by e"');
    }
  });

  it('keeps a law-free box open when fields were omitted, reflection stopped, a parent is packed, nothing was reflected, or a disclosure already encloses it', () => {
    const data = [field('inner', 'data', 'Opaque M')];
    const models = [base({ fields: data, omittedFields: 1 }), base({ fields: data, stopReason: 'A field could not be reflected within its checked export budget.' }),
      base({ fields: [{ ...field('toBase', 'data', 'Base M'), parent: 'Base' }] }), base()];
    for (const model of models) {
      expect(startsClosed(model)).toBe(false);
      expect(html(model)).not.toContain('sd-closed-structure');
    }
    expect(enclosed(lawFree())).not.toContain('sd-closed-structure');
  });

  it('shares one count between the header and the summary', () => {
    const rendered = html(base({ fields: [field('first'), field('second')] }));
    expect(rendered).toContain('<summary>Inside e · 2 data fields · 0 laws</summary>');
    expect(rendered).toContain('<span class="sd-count">2 data fields · 0 laws</span>');
    expect(html(base({ fields: [field('first'), field('rule', 'law'), field('other', 'law')] }))).toContain('<span class="sd-count">1 data field · 2 laws</span>');
  });
});
