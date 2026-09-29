import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { expandStructuralBranch, PositionalDeclarationFields, recordedContextAligned, recordedContextHeadings, StructuralReading, type RecordedContextEntry } from './StructuralReading';
import { UNMATCHED_RECORDED_KINDS } from '../core/context-entry';
import { buildPositionalStructuralDrawing, type PositionalStructuralDrawing, type PositionalStructuralInput,
  type PositionalStructuralDeclaration, type StructuralLocalKind, type StructuralName, type StructuralNode } from './structure';
import type { JsonValue } from './packet';

const name = (value = 'same'): StructuralName => ['str', ['anonymous'], value];
const b = (value: number): JsonValue => ['bvar', ['nat', String(value)]];
const sort: JsonValue = ['sort', ['succ', ['zero']]];
const app = (fn: JsonValue, arg: JsonValue): JsonValue => ['app', fn, arg];
// Four chronological entries: A : Sort 1, x : A, y := x, h := y.
// All four deliberately share a display name; only position establishes identity.
const home: PositionalStructuralInput['home'] = { arity: 4, telescope:
  ['letE', ['letE', ['port', ['port', ['nil'], { name: name(), info: 'implicit' }, sort],
    { name: name(), info: 'default' }, b(0)], name(), false, b(1), b(0)], name(), true, b(2), b(0)] };
const term: JsonValue = ['lam', name(), b(3), app(b(0), b(1)), 'default'];
const type: JsonValue = ['forallE', name(), b(3), b(4), 'default'];
function drawing(input: PositionalStructuralInput = { home, term, type }): PositionalStructuralDrawing {
  const result = buildPositionalStructuralDrawing(input, { sourceIdentity: 'positional-render-test', sourcePath: ['checking', 'selected'] });
  if (!result.ok) throw new Error(`${result.error.code}: ${result.error.message}`);
  return result.value;
}
function render(model: PositionalStructuralDrawing, initialNodeLimit = 200): string {
  return renderToStaticMarkup(createElement(StructuralReading, { drawing: model, initialNodeLimit }));
}
function context(model: PositionalStructuralDrawing): PositionalStructuralDeclaration[] {
  return model.contextDeclarationIds.map(id => model.declarations.find(declaration => declaration.id === id) as PositionalStructuralDeclaration);
}

describe('positional structural rendering', () => {
  it('renders the complete chronological context and two distinctly labelled roots sharing its home', () => {
    const model = drawing(), html = render(model), entries = context(model);
    expect(html).toContain('data-positional="true"');
    expect(html).toContain('aria-label="Exact selected structure"');
    expect(html).toContain('Surrounding context, oldest first');
    expect(html).toContain('All 4 context entries are retained, including unused entries.');
    expect(html).toContain('data-structure-root="term"'); expect(html).toContain('data-structure-root="type"');
    expect(html.match(new RegExp(`data-root-home="${model.rootHomeId}"`, 'g'))).toHaveLength(2);
    expect(html.match(/class="struct-node"/g)).toHaveLength(model.nodes.length + 4);
    const positions = entries.map((entry, i) => {
      const card = `data-context-declaration="${entry.id}" data-context-position="${i + 1}" data-home="${entry.homeId}" data-context-body-home="${entry.bodyHomeId}"`;
      expect(html).toContain(card); return html.indexOf(card);
    });
    expect(positions).toEqual([...positions].sort((a, b) => a - b));
    expect(positions.at(-1)).toBeLessThan(html.indexOf('data-structure-root="term"'));
    expect(html.indexOf('data-structure-root="term"')).toBeLessThan(html.indexOf('data-structure-root="type"'));
    expect(html).toContain('Its type uses only the preceding context.');
    expect(html).toContain('Its type and defining value use only the preceding context.');
    expect(html).toContain('does not assert typing or evidence');
    expect(html).not.toContain('Registered'); expect(html).not.toContain('Registry identity');
  });

  it('retains both definition values and flags, including nondependent true as an equation', () => {
    const model = drawing(), html = render(model), definitions = context(model).filter(entry => entry.constructor === 'letE');
    expect(definitions).toHaveLength(2);
    for (const entry of definitions) {
      expect(entry.children.map(edge => edge.role)).toEqual(['type', 'definitionValue']);
      const first = `data-role="type" data-child-node="${entry.children[0].nodeId}" data-port-order="1"`;
      const second = `data-role="definitionValue" data-child-node="${entry.children[1].nodeId}" data-port-order="2"`;
      expect(html).toContain(first); expect(html).toContain(second); expect(html.indexOf(first)).toBeLessThan(html.indexOf(second));
      const fields = renderToStaticMarkup(createElement(PositionalDeclarationFields, { declaration: entry }));
      expect(fields).toContain('<dt>Constructor</dt>');
      expect(fields).toContain('Original nondependent flag'); expect(fields).toContain(`<code>${entry.nondep}</code>`);
      expect(fields).toContain('Structured name');
    }
    expect(html.match(/This entry retains its defining equation\./g)).toHaveLength(2);
    expect(html).not.toContain('stored value'); expect(html).not.toContain('opaque');
  });

  it('links all ambient positions to their distinct declaration cards despite identical names', () => {
    const model = drawing({ home, term: app(b(0), app(b(1), app(b(2), b(3)))), type: sort }), html = render(model);
    const entries = context(model), refs = model.nodes.filter((node): node is Extract<StructuralNode, { kind: 'bvar' }> => node.kind === 'bvar' && node.sourcePath.includes('term'));
    expect(refs.map(node => node.declarationId)).toEqual(entries.slice().reverse().map(entry => entry.id));
    const links = [...html.matchAll(/data-reference-target="([^"]+)"[^>]*><span>Refers to<\/span><button type="button" aria-controls="([^"]+)"/g)];
    for (const entry of entries) {
      const targets = links.filter(link => link[1] === entry.id).map(link => link[2]);
      expect(targets.length).toBeGreaterThan(0); expect(new Set(targets).size).toBe(1);
      expect(html).toContain(`id="${targets[0]}" data-context-declaration="${entry.id}"`);
    }
    expect(new Set(refs.map(node => links.find(link => link[1] === node.declarationId)![2])).size).toBe(4);
    for (let position = 0; position < 4; position++) expect(html).toContain(`Bound position ${position}`);
  });

  it('keeps term and type owned binders separate while linking their ambient references to the common context', () => {
    const model = drawing({ home, term, type: ['forallE', name(), b(3), app(b(0), b(1)), 'default'] }), html = render(model);
    const termRoot = model.nodes.find(node => node.id === model.rootId)!, typeRoot = model.nodes.find(node => node.id === model.typeRootId)!;
    expect(termRoot.kind).toBe('lam'); expect(typeRoot.kind).toBe('forallE');
    if (termRoot.kind !== 'lam' || typeRoot.kind !== 'forallE') throw Error('fixture binder roots unavailable');
    expect(termRoot.declarationId).not.toBe(typeRoot.declarationId);
    const ownTerm = model.nodes.find(node => node.kind === 'bvar' && node.declarationId === termRoot.declarationId)!;
    const ownType = model.nodes.find(node => node.kind === 'bvar' && node.declarationId === typeRoot.declarationId)!;
    expect(ownTerm.homeId).not.toBe(ownType.homeId);
    for (const id of [termRoot.declarationId, typeRoot.declarationId]) expect(html).toContain(`data-reference-target="${id}"`);
    const recentContext = model.contextDeclarationIds[3];
    expect(model.nodes.filter(node => node.kind === 'bvar' && node.declarationId === recentContext)).toHaveLength(2);
    expect(html.match(/data-body-home=/g)).toHaveLength(2);
  });

  it('B2-8: writes 0, 1 and 2 context entries and a one-node branch with the noun in the right number', () => {
    const entry = (rest: JsonValue): JsonValue => ['port', rest, { name: name(), info: 'default' }, sort];
    const homes: [PositionalStructuralInput['home'], string][] = [
      [{ arity: 0, telescope: ['nil'] }, 'Empty surrounding context.'],
      [{ arity: 1, telescope: entry(['nil']) }, 'The 1 context entry is retained, even if it is unused.'],
      [{ arity: 2, telescope: entry(entry(['nil'])) }, 'All 2 context entries are retained, including unused entries.'],
    ];
    for (const [twoAtMost, sentence] of homes) expect(render(drawing({ home: twoAtMost, term: sort, type: sort }))).toContain(sentence);
    // Showing only the term root folds the type root, a branch of one node.
    const folded = render(drawing({ home: { arity: 0, telescope: ['nil'] }, term: sort, type: sort }), 1);
    expect(folded).toContain('Show next 1 node in this branch');
    expect(folded).toContain('1 of 2 constructor nodes shown');
  });

  it('shows unused entries and context headers even when all their constructor fields are folded', () => {
    const model = drawing({ home, term: sort, type: sort }), html = render(model, 1);
    expect(html.match(/data-context-declaration=/g)).toHaveLength(4);
    expect(html).toContain('No references to this entry in the drawing.');
    expect(html).toContain(`data-context-declaration="${model.contextDeclarationIds[3]}"`);
    expect(html).toContain('data-reference-count="0"');
    expect(html).toContain('data-structure-root="term"'); expect(html).toContain('data-structure-root="type"');
    expect(html).toContain('folded branch');
    expect(html).toContain(`1 of ${model.nodes.length} constructor nodes shown`);
    expect(html.match(/<summary>Exact fields and source position<\/summary>/g)).toHaveLength(5);
  });

  it('keeps branch expansion local to either root and counts all context, term and type nodes', () => {
    let large: JsonValue = sort;
    for (let i = 0; i < 25; i++) large = app(large, ['lit', ['natVal', ['nat', String(i)]]]);
    const model = drawing({ home, term: large, type }), html = render(model, 2);
    const expanded = expandStructuralBranch(model, new Set(), model.rootId, 7);
    expect(expanded.size).toBe(7); expect(expanded.has(model.typeRootId)).toBe(false);
    for (const entry of context(model)) for (const edge of entry.children) expect(expanded.has(edge.nodeId)).toBe(false);
    const omitted = [...html.matchAll(/data-fold-count="(\d+)"/g)].reduce((total, match) => total + Number(match[1]), 0);
    expect(omitted).toBe(model.nodes.length - 2);
    expect(html).toContain('Show next 40 nodes in this branch'); expect(html).toContain('Reset folds');
  });

  it('selects the exact context card path and exposes structured names and annotations without synthetic identities', () => {
    const input = structuredClone({ home, term, type });
    const outerPort = input.home.telescope as JsonValue[];
    const first = array(array(array(outerPort[1])[1])[1]);
    (first[2] as Record<string, JsonValue>).name = ['num', name('N'), ['nat', '9007199254740993']];
    const model = drawing(input), entry = context(model)[0];
    const html = renderToStaticMarkup(createElement(StructuralReading, { drawing: model, selectedPath: entry.sourcePath, initialNodeLimit: 200 }));
    expect(html.match(/data-selected="true"/g)).toHaveLength(1);
    expect(html).toContain('data-reference-count='); expect(html).toContain('#9007199254740993');
    const fields = renderToStaticMarkup(createElement(PositionalDeclarationFields, { declaration: entry }));
    expect(fields).toContain('Numeric name component'); expect(fields).toContain('9007199254740993');
    expect(fields).toContain('Binder annotation'); expect(fields).toContain('implicit');
    expect(fields).not.toContain('Registry identity'); expect(fields).not.toContain('Local declaration kind');
    expect(entry.sourcePath).toEqual(['checking', 'selected', 'home', 'telescope', 1, 1, 1]);
  });

  it('renders an explicit empty context with both roots and no invented declarations', () => {
    const model = drawing({ home: { arity: 0, telescope: ['nil'] }, term: sort, type: sort }), html = render(model);
    expect(html).toContain('Empty surrounding context.');
    expect(html).toContain('aria-label="Selected term"'); expect(html).toContain('aria-label="Inferred type"');
    expect(html).not.toContain('data-context-declaration='); expect(html).not.toContain('data-reference-target=');
    expect(html.match(/data-node-id=/g)).toHaveLength(2);
  });
});

describe('recorded kinds of positional context entries', () => {
  // The fixture's four entries all display the name "same": port A, port x, let y, let h. Only the recorded
  // kind at each position may select a neutral heading; the constructor keeps the ordinary headings.
  const render = (recordedContext?: readonly RecordedContextEntry[], model = drawing()) => renderToStaticMarkup(createElement(StructuralReading, { drawing: model, initialNodeLimit: 200, recordedContext }));
  const withKinds = (kinds?: readonly StructuralLocalKind[]) => render(kinds?.map(kind => ({ name: name(), kind })));
  const headings = (html: string) => [...html.matchAll(/data-context-position="(\d+)"[^>]*>\s*<header class="struct-node-heading"><strong>([^<]*)<\/strong>/g)].map(match => match[2]);

  it('reads auxDecl and implDetail entries by their recorded kind and never as a parameter or definition', () => {
    expect(headings(withKinds(['auxDecl', 'default', 'implDetail']))).toEqual(
      ['Auxiliary entry, recorded kind auxDecl', 'Context parameter', 'Context entry, recorded kind implDetail', 'Context definition']);
    expect(headings(withKinds(['default', 'implDetail', 'auxDecl', 'default']))).toEqual(
      ['Context parameter', 'Context entry, recorded kind implDetail', 'Auxiliary entry, recorded kind auxDecl', 'Context definition']);
  });

  it('keeps ordinary and later entered entries under their constructor headings', () => {
    const ordinary = ['Context parameter', 'Context parameter', 'Context definition', 'Context definition'];
    expect(headings(withKinds())).toEqual(ordinary);
    expect(headings(withKinds(['default', 'default', 'default', 'default']))).toEqual(ordinary);
    // Only the first entry is captured here; the three entered after it have no recorded kind.
    expect(headings(withKinds(['auxDecl']))).toEqual(['Auxiliary entry, recorded kind auxDecl', ...ordinary.slice(1)]);
    expect(withKinds(['default', 'default', 'default', 'default'])).toBe(withKinds());
  });

  it('changes only the heading text of the neutral entries', () => {
    const neutral = withKinds(['auxDecl', 'default', 'implDetail']);
    expect(neutral).toContain('<strong>Auxiliary entry, recorded kind auxDecl</strong>');
    expect(neutral.replace('Auxiliary entry, recorded kind auxDecl', 'Context parameter').replace('Context entry, recorded kind implDetail', 'Context definition')).toBe(withKinds());
    expect(neutral).toContain('Its type and defining value use only the preceding context. This entry retains its defining equation.');
  });

  // Entries A, x, y, h with distinct names: port, port, let, let.
  const distinct = () => drawing({ home: { arity: 4, telescope: ['letE', ['letE', ['port', ['port', ['nil'], { name: name('A'), info: 'implicit' }, sort],
    { name: name('x'), info: 'default' }, b(0)], name('y'), false, b(1), b(0)], name('h'), true, b(2), b(0)] }, term, type });
  const entry = (text: string, kind: StructuralLocalKind): RecordedContextEntry => ({ name: name(text), kind });

  it('applies recorded kinds only when the leading entries carry the recorded names in order', () => {
    expect(headings(render([entry('A', 'auxDecl'), entry('x', 'default'), entry('y', 'implDetail')], distinct()))).toEqual(
      ['Auxiliary entry, recorded kind auxDecl', 'Context parameter', 'Context entry, recorded kind implDetail', 'Context definition']);
    expect(recordedContextHeadings(distinct(), [entry('A', 'default'), entry('x', 'auxDecl')])).toEqual([undefined, 'Auxiliary entry, recorded kind auxDecl', undefined, undefined]);
    expect(recordedContextHeadings(distinct())).toBeUndefined();
  });

  it('reads every entry as a neutral context entry when the records do not align, never by constructor', () => {
    const neutral = ['Context entry', 'Context entry', 'Context entry', 'Context entry'];
    for (const recorded of [
      [entry('x', 'auxDecl'), entry('A', 'default')],
      [entry('A', 'auxDecl'), entry('y', 'default')],
      [entry('A', 'default'), entry('x', 'default'), entry('y', 'default'), entry('h', 'default'), entry('later', 'default')],
    ]) {
      expect(headings(render(recorded, distinct()))).toEqual(neutral);
      expect(render(recorded, distinct())).not.toMatch(/<strong>Context (parameter|definition)<\/strong>|recorded kind/);
    }
    // A name encoded differently, here a numeric component, does not match its string spelling.
    const numeric: RecordedContextEntry = { name: ['num', ['anonymous'], ['nat', '1']], kind: 'default' };
    expect(recordedContextHeadings(drawing({ home: { arity: 1, telescope: ['port', ['nil'], { name: ['str', ['anonymous'], '1'], info: 'default' }, sort] }, term: sort, type: sort }), [numeric])).toEqual(['Context entry']);
  });

  it('states once, only when the records do not align, that the recorded kinds could not be matched', () => {
    const note = (html: string) => html.split(UNMATCHED_RECORDED_KINDS).length - 1;
    for (const recorded of [undefined, [], [entry('A', 'auxDecl')], [entry('A', 'default'), entry('x', 'auxDecl'), entry('y', 'implDetail'), entry('h', 'default')]])
      expect(note(render(recorded, distinct()))).toBe(0);
    for (const recorded of [[entry('x', 'auxDecl')], [entry('A', 'default'), entry('x', 'default'), entry('y', 'default'), entry('h', 'default'), entry('later', 'default')]]) {
      const html = render(recorded, distinct());
      expect(note(html)).toBe(1);
      expect(html).toContain(`<p class="struct-context-note" data-recorded-kinds-unmatched="">${UNMATCHED_RECORDED_KINDS}</p>`);
      expect(html.indexOf(UNMATCHED_RECORDED_KINDS)).toBeLessThan(html.indexOf('data-context-position="1"'));
    }
  });

  it('checks each record name as plain data before comparing it, without evaluating accessors', () => {
    let evaluated = false;
    const nested: Record<string, unknown> = {};
    Object.defineProperty(nested, 'part', { enumerable: true, get() { evaluated = true; return 'A'; } });
    const hostile: RecordedContextEntry[] = [{ name: ['str', ['anonymous'], nested] as never, kind: 'auxDecl' }];
    expect(recordedContextAligned(distinct(), hostile)).toBe(false);
    expect(headings(render(hostile, distinct()))).toEqual(['Context entry', 'Context entry', 'Context entry', 'Context entry']);
    expect(evaluated).toBe(false);
    for (const name of [['str', ['anonymous'], () => 'A'], ['num', ['anonymous'], Number.NaN], Object.assign(['str', ['anonymous'], 'A'], { [Symbol('x')]: 1 })])
      expect(recordedContextAligned(distinct(), [{ name: name as never, kind: 'default' }])).toBe(false);
    expect(recordedContextAligned(distinct(), [entry('A', 'default')])).toBe(true);
  });
});

function array(value: JsonValue): JsonValue[] { return value as JsonValue[]; }
