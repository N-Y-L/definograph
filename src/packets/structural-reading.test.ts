import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { expandStructuralBranch, StructuralFieldValue, StructuralNodeFields, StructuralReading } from './StructuralReading';
import { buildStructuralDrawing, type ExternalDeclarationInput, type StructuralDrawing, type StructuralLevel, type StructuralName } from './structure';
import type { JsonValue } from './packet';

const name = (text: string): StructuralName => ['str', ['anonymous'], text];
const sort: JsonValue = ['sort', ['zero']];
const constant = (text: string, levels: StructuralLevel[] = []): JsonValue => ['const', name(text), levels];
const application = (fn: JsonValue, argument: JsonValue): JsonValue => ['app', fn, argument];
const level: StructuralLevel = ['max', ['succ', ['zero']], ['imax', ['param', ['num', name('u'), 2]], ['zero']]];
function drawing(expression: JsonValue, externalContext: ExternalDeclarationInput[] = []): StructuralDrawing {
  const result = buildStructuralDrawing(expression, { sourceIdentity: 'renderer-test', sourcePath: ['captured', 'value'], externalContext });
  if (!result.ok) throw new Error(`${result.error.code}: ${result.error.message}`);
  return result.value;
}
function render(value: StructuralDrawing, initialNodeLimit = 200): string {
  return renderToStaticMarkup(createElement(StructuralReading, { drawing: value, initialNodeLimit }));
}

describe('visible structural constructor correspondence', () => {
  const externalContext: ExternalDeclarationInput[] = [
    { constructor: 'cdecl', index: 0, fvarId: name('registered'), userName: name('same'), type: sort, kind: 'default', binderInfo: 'implicit' },
    { constructor: 'ldecl', index: 1, fvarId: name('metadata'), userName: name('same'), type: sort, value: ['lit', ['strVal', 'retained metadata']], kind: 'implDetail', nondep: true },
  ];
  // All constructors occur below the outer application, including a lambda in
  // a domain and a projection in a local value. No names select their rendering.
  const nested: JsonValue = application(constant('Unfamiliar'),
    ['lam', name('same'), ['sort', level],
      ['forallE', name('same'), application(['lam', name('domainLocal'), sort, ['bvar', 0], 'strictImplicit'], constant('Carrier')),
        ['letE', name('same'), sort,
          ['proj', ['num', name('UnfamiliarOwner'), 3], 2, application(['fvar', name('registered')], ['lit', ['natVal', 17]])],
          application(application(['bvar', 0], ['lit', ['strVal', 'a\n"b"']]), application(['bvar', 2], constant('Namespaced', [level, ['zero']]))), false],
        'instImplicit'], 'implicit']);

  it('renders every nested constructor and each ordered child role as actual cards and connections', () => {
    const model = drawing(nested, externalContext), html = render(model);
    expect(new Set(model.nodes.map(node => node.kind))).toEqual(new Set(['app', 'const', 'lam', 'sort', 'forallE', 'letE', 'proj', 'fvar', 'lit', 'bvar']));
    expect(html).toContain('aria-label="Exact source structure"');
    expect(html).toContain('Source structure');
    expect(html).not.toContain('folded branch');
    expect(html.match(/class="struct-node"/g)?.length).toBe(model.nodes.length + model.externalDeclarationIds.length);
    for (const node of model.nodes) {
      expect(html).toContain(`data-node-id="${node.id}" data-constructor="${node.kind}" data-home="${node.homeId}"`);
      const positions = node.children.map((edge, position) => {
        const connection = `data-role="${edge.role}" data-parent-node="${node.id}" data-child-node="${edge.nodeId}" data-port-order="${position + 1}"`;
        expect(html).toContain(connection);
        return html.indexOf(connection);
      });
      expect(positions).toEqual([...positions].sort((a, b) => a - b));
    }
    for (const label of ['Function', 'Argument', 'Domain', 'Body', 'Declared type', 'Bound value', 'Projected value']) expect(html).toContain(`</span>${label}</div>`);
    expect(html).toContain('Ordered constructor connection');
    expect(html).toContain('Declaration reference, not a mathematical arrow');
    expect(html).toContain('does not assert typing or evidence');
    expect(html).not.toContain('<pre>');
  });

  it('draws the binder body scope separately while leaving domains and let values in their enclosing homes', () => {
    const model = drawing(nested, externalContext), html = render(model);
    for (const declaration of model.declarations.filter(item => item.kind !== 'external')) {
      expect(html).toContain(`data-body-home="${declaration.bodyHomeId}"`);
      const node = model.nodes.find(item => item.id === declaration.nodeId)!;
      for (const edge of node.children) {
        const child = model.nodes.find(item => item.id === edge.nodeId)!;
        expect(child.homeId).toBe(edge.role === 'body' ? declaration.bodyHomeId : declaration.homeId);
        expect(html).toContain(`data-node-id="${child.id}" data-constructor="${child.kind}" data-home="${child.homeId}"`);
      }
    }
    expect(html).toContain('The domain uses the enclosing scope. This binder enters scope only in the body.');
    expect(html).toContain('The type and value use the enclosing scope. This binding enters scope only in the body.');
  });

  it('makes all constructor fields available in node-attached inspectors, including exact names and universes', () => {
    const model = drawing(nested, externalContext), html = render(model);
    expect(html.match(/<summary>Exact fields and source position<\/summary>/g)?.length).toBe(model.nodes.length + model.externalDeclarationIds.length);
    const fields = model.nodes.map(node => renderToStaticMarkup(createElement(StructuralNodeFields, { node }))).join('');
    for (const text of ['Structured name', 'Binder annotation', 'Original nondependent flag', 'Field index', 'Structured projection owner', 'Registry identity', 'Natural literal', 'String literal', 'Ordered universe instances']) expect(fields).toContain(text);
    for (const constructor of ['anonymous', 'str', 'num', 'zero', 'succ', 'max', 'imax', 'param']) expect(fields).toContain(`data-field-constructor="${constructor}"`);
    expect(fields).toContain('First operand'); expect(fields).toContain('Second operand');
    expect(fields).toContain('implicit'); expect(fields).toContain('strictImplicit'); expect(fields).toContain('instImplicit');
    expect(fields).toContain('<code>false</code>');
    expect(fields).toContain('a\\n');
  });

  it('labels retained opaque local values as metadata rather than defining equations', () => {
    const html = render(drawing(nested, externalContext));
    // This opaque local has recorded kind implDetail, so its heading is the neutral kind label.
    expect(html).toContain('Context entry, recorded kind implDetail');
    expect(render(drawing(nested, externalContext.map(entry => ({ ...entry, kind: 'default' as const }))))).toContain('Registered opaque local');
    expect(html).toContain('The stored value is metadata, not a defining equation.');
    expect(html).toContain('Stored value (not a defining equation)');
    expect(html).toContain('aria-label="Registered context"');
    expect(html.indexOf('data-external-declaration="renderer-test:declaration:0"')).toBeLessThan(html.indexOf('data-external-declaration="renderer-test:declaration:1"'));
  });

  it('draws the complete owned have value while preserving the true original flag', () => {
    const model = drawing(['letE', name('local'), sort, application(constant('producer'), ['lit', ['natVal', 4]]), ['bvar', 0], true]);
    const html = render(model), fields = renderToStaticMarkup(createElement(StructuralNodeFields, { node: model.nodes[0] }));
    expect(html).toContain('Let / have binding');
    expect(html).toContain('Bound value');
    expect(html).toContain('data-constructor="app"');
    expect(html).toContain('data-constructor="lit"');
    expect(html).not.toContain('stored value is metadata');
    expect(fields).toContain('Original nondependent flag');
    expect(fields).toContain('<code>true</code>');
  });

  it('keeps references to shadowed names linked to different exact declaration cards', () => {
    const model = drawing(['lam', name('same'), sort,
      application(['bvar', 0], ['lam', name('same'), sort, application(['bvar', 1], ['bvar', 0]), 'default']), 'default']);
    const html = render(model), declarations = model.declarations.filter(item => item.kind !== 'external');
    expect(declarations).toHaveLength(2);
    const links = [...html.matchAll(/data-reference-target="([^"]+)"/g)].map(match => match[1]);
    expect(links).toEqual([declarations[0].id, declarations[0].id, declarations[1].id]);
    const targets = [...html.matchAll(/aria-controls="([^"]+)"/g)].map(match => match[1]);
    expect(targets[0]).toBe(targets[1]); expect(targets[2]).not.toBe(targets[0]);
    targets.forEach(target => expect(html).toContain(`id="${target}"`));
    expect(html).toContain('same</bdi><span> · declaration 1'); expect(html).toContain('same</bdi><span> · declaration 2');
    expect(html).toContain('Bound position 1'); expect(html).toContain('Bound position 0');
  });

  it('distinguishes numeric name components from equal-looking string components', () => {
    const numeric = renderToStaticMarkup(createElement(StructuralFieldValue, { value: ['num', name('N'), 2] }));
    const string = renderToStaticMarkup(createElement(StructuralFieldValue, { value: ['str', name('N'), '2'] }));
    expect(numeric).toContain('Numeric name component'); expect(numeric).toContain('<code>2</code>');
    expect(string).toContain('String name component'); expect(string).toContain('&quot;2&quot;');
    expect(numeric).not.toBe(string);
    const escaped = renderToStaticMarkup(createElement(StructuralFieldValue, { value: '<script>\nquoted"text' }));
    expect(escaped).not.toContain('<script>'); expect(escaped).toContain('&lt;script&gt;'); expect(escaped).toContain('\\n');
  });

  it('makes invisible, combining, non-BMP and bidirectional string identities visibly exact', () => {
    const cases = [
      ['', '&quot;&quot;'], ['\u200b', '&quot;\\u200b&quot;'],
      ['\u00e9', '&quot;\\u00e9&quot;'], ['e\u0301', '&quot;e\\u0301&quot;'],
      ['\ud83d\ude00', '&quot;\\ud83d\\ude00&quot;'], ['a\u202eb', '&quot;a\\u202eb&quot;'],
    ];
    const rendered = cases.map(([value, expected]) => {
      const html = renderToStaticMarkup(createElement(StructuralFieldValue, { value }));
      expect(html).toContain(expected);
      expect(html).not.toMatch(/[^\x00-\x7f]/);
      return html;
    });
    expect(new Set(rendered).size).toBe(cases.length);
    const encodedName = renderToStaticMarkup(createElement(StructuralFieldValue, { value: name('e\u0301\u200b') }));
    expect(encodedName).toContain('String component'); expect(encodedName).toContain('&quot;e\\u0301\\u200b&quot;');
  });

  it('isolates readable source glyphs from fixed labels and escapes directional controls', () => {
    const controls = '\u061c\u200e\u200f\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069\u206a\u206f';
    const model = drawing(['lam', name(`name${controls}`), sort, application(['bvar', 0], ['proj', name(`owner${controls}`), 2, ['lit', ['strVal', `text${controls}`]]]), 'default']);
    const html = render(model);
    for (const character of controls) {
      expect(html).not.toContain(character);
      expect(html).toContain(`\\u${character.charCodeAt(0).toString(16).padStart(4, '0')}`);
    }
    expect(html).toMatch(/<bdi dir="auto">[^<]*<\/bdi><span> · declaration 1<\/span>/);
    expect(html).toMatch(/<bdi dir="auto">[^<]*<\/bdi><span> · field 2<\/span>/);
    expect(html).toContain('<strong>Lambda</strong>');
    expect(html).toContain('<strong>Literal</strong>');
  });

  it('retains ordinary right-to-left names inside their own readable isolation region', () => {
    const html = render(drawing(['lam', name('שלום'), sort, ['bvar', 0], 'default']));
    expect(html).toContain('<bdi dir="auto">שלום</bdi><span> · declaration 1</span>');
    expect(html).not.toContain('\\u05e9');
    const fields = renderToStaticMarkup(createElement(StructuralFieldValue, { value: name('שלום') }));
    expect(fields).toContain('\\u05e9\\u05dc\\u05d5\\u05dd');
  });

  it('marks an exact externally selected source occurrence without merging identical references', () => {
    const model = drawing(['lam', name('x'), sort, application(['bvar', 0], ['bvar', 0]), 'default']);
    const refs = model.nodes.filter(node => node.kind === 'bvar');
    const html = renderToStaticMarkup(createElement(StructuralReading, { drawing: model, selectedPath: refs[1].sourcePath }));
    expect(html.match(/data-selected="true"/g)).toHaveLength(1);
    expect(html).toContain(`data-node-id="${refs[1].id}" data-constructor="bvar" data-home="${refs[1].homeId}" data-selected="true"`);
    expect(refs[0].sourcePath).not.toEqual(refs[1].sourcePath);
  });
});

describe('bounded structural folds', () => {
  function chain(depth: number): JsonValue {
    let expression = constant('final');
    for (let index = 0; index < depth; index++) expression = application(expression, ['lit', ['natVal', index]]);
    return expression;
  }

  it('renders explicit omitted counts and source-ordered branch expansion controls', () => {
    const model = drawing(chain(25)), html = render(model, 3);
    expect(html.match(/data-node-id=/g)).toHaveLength(3);
    expect(html).toContain('3 of 51 constructor nodes shown');
    expect(html).toContain('folded branch');
    expect(html).toContain('Show next 40 nodes in this branch');
    expect(html).toContain('Reset folds');
    const omitted = [...html.matchAll(/data-fold-count="(\d+)"/g)].reduce((sum, match) => sum + Number(match[1]), 0);
    expect(omitted).toBe(48);
    expect(html.match(/data-port-order=/g)).toHaveLength(6);
    const full = render(model);
    expect(full).not.toContain('folded branch');
    expect(full.match(/data-node-id=/g)).toHaveLength(51);
    expect(full).toContain('Exact fields and source position');
  });

  it('expands only the chosen branch in deterministic finite chunks and eventually exposes every node', () => {
    const model = drawing(application(chain(25), chain(25))), root = model.nodes.find(node => node.id === model.rootId)!;
    const visible = new Set([root.id]);
    const right = expandStructuralBranch(model, visible, root.children[1].nodeId, 7);
    expect(right.size).toBe(8);
    expect(right.has(root.children[0].nodeId)).toBe(false);
    expect([...right]).toEqual([...expandStructuralBranch(model, visible, root.children[1].nodeId, 7)]);
    let all = visible;
    for (let pass = 0; pass < 20 && all.size < model.nodes.length; pass++) {
      const next = expandStructuralBranch(model, all, root.id, 9);
      expect(next.size - all.size).toBeLessThanOrEqual(9);
      expect(next.size).toBeGreaterThan(all.size); all = next;
    }
    expect(all).toEqual(new Set(model.nodes.map(node => node.id)));
  });

  it('retains labelled body regions and exact references when deep nesting uses aligned cards', () => {
    let expression: JsonValue = ['bvar', 47];
    for (let index = 0; index < 48; index++) expression = ['forallE', name('same'), sort, expression, 'default'];
    const model = drawing(expression), html = render(model);
    expect(html.match(/data-node-id=/g)).toHaveLength(97);
    expect(html.match(/data-body-home=/g)).toHaveLength(48);
    expect(html.match(/data-role="domain"/g)).toHaveLength(48);
    expect(html.match(/data-role="body"/g)).toHaveLength(48);
    expect(html).toContain('data-deep="true"');
    expect(html).toContain('Bound position 47');
    expect(html).toContain(`data-reference-target="${model.declarations[0].id}"`);
    let universe: StructuralLevel = ['zero'];
    for (let depth = 0; depth < 48; depth++) universe = ['succ', universe];
    const fields = renderToStaticMarkup(createElement(StructuralFieldValue, { value: universe }));
    expect(fields.match(/data-field-constructor="succ"/g)).toHaveLength(48);
    expect(fields).toContain('class="struct-field-deep"');
    expect(fields).toContain('Universe zero');
  });
});

describe('recorded kinds of registered context entries', () => {
  const headings = (html: string) => [...html.matchAll(/data-external-declaration="[^"]*"[^>]*>\s*<header class="struct-node-heading"><strong>([^<]*)<\/strong>/g)].map(match => match[1]);
  const entries = (kind: ExternalDeclarationInput['kind']): ExternalDeclarationInput[] => [
    { constructor: 'cdecl', index: 0, fvarId: name('first'), userName: name('same'), type: sort, kind, binderInfo: 'default' },
    { constructor: 'ldecl', index: 1, fvarId: name('second'), userName: name('same'), type: sort, value: sort, kind, nondep: false },
    { constructor: 'ldecl', index: 2, fvarId: name('third'), userName: name('same'), type: sort, value: sort, kind, nondep: true },
  ];
  const expression = application(application(['fvar', name('first')], ['fvar', name('second')]), ['fvar', name('third')]);

  it('reads auxDecl and implDetail declarations by their recorded kind, whatever their constructor', () => {
    expect(headings(render(drawing(expression, entries('auxDecl'))))).toEqual(Array(3).fill('Auxiliary entry, recorded kind auxDecl'));
    expect(headings(render(drawing(expression, entries('implDetail'))))).toEqual(Array(3).fill('Context entry, recorded kind implDetail'));
  });

  it('keeps the constructor headings and value wording of ordinary declarations', () => {
    const html = render(drawing(expression, entries('default')));
    expect(headings(html)).toEqual(['Registered declaration', 'Registered local definition', 'Registered opaque local']);
    const neutral = render(drawing(expression, entries('auxDecl')));
    expect(neutral).toContain('The stored value is metadata, not a defining equation.');
    expect(neutral.replaceAll('Auxiliary entry, recorded kind auxDecl', '').replaceAll('auxDecl', 'default')).toBe(
      html.replace('Registered declaration', '').replace('Registered local definition', '').replace('Registered opaque local', ''));
  });
});
