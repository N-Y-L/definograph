import { Fragment, createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { SemanticObject } from '../semantic/types';
import type { TypedConstruction } from '../constructions/model';
import type { StructuralField, StructuralObjectModel } from './types';
import { StructuralObjectFigure } from './StructuralObjectFigure';

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
});
