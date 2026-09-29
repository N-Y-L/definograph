import { describe, expect, it } from 'vitest';
import type { JsonValue } from './packet';
import { buildRawInspection, readRawInspection, type RawFamily, type RawInspectionDrawing, type RawResult } from './raw';

const zero: JsonValue = ['nat', '0'];
const natural = (digits: string | number): JsonValue => ['nat', String(digits)];
const anonymous: JsonValue = ['anonymous'];
const name = (text: string): JsonValue => ['str', anonymous, text];
const numbered: JsonValue = ['num', name('component.with.dot'), natural('9007199254740993')];
const sort: JsonValue = ['sort', ['zero']];
const reference: JsonValue = ['fvar', numbered];
const substring: JsonValue = ['substring', 'λ😀\n\u0000', natural('99999999999999999999999999'), natural(1)];
const original: JsonValue = ['original', substring, natural(3), ['substring', ' leading ', natural(8), zero], natural(1)];
const syntax: JsonValue = ['node', original, numbered, [
  ['missing'], ['atom', ['none'], '\"λ\"'],
  ['ident', ['synthetic', natural(7), natural(2), false], substring, name('x'), [
    ['namespace', anonymous], ['decl', numbered, ['x', 'x', '', 'λ😀']],
  ]],
]];
const dataValues: JsonValue[] = [['ofString', '\n\"\\\u0000λ😀'], ['ofBool', false], ['ofBool', true],
  ['ofName', numbered], ['ofNat', natural('9007199254740993')], ['ofInt', ['ofNat', zero]],
  ['ofInt', ['negSucc', natural('999999999999999999999999999999')]], ['ofSyntax', syntax]];
const metadata: JsonValue = ['mdataEntries', dataValues.map(value => [numbered, value])];
const expression: JsonValue = ['mdata', metadata,
  ['lam', numbered, ['sort', ['imax', ['param', name('u')], ['max', ['zero'], ['succ', ['mvar', numbered]]]]],
    ['letE', name('same'), ['const', name('Opaque.Type'), [['param', numbered], ['mvar', name('v')]]],
      ['mvar', name('unresolved')],
      ['forallE', name('same'), ['fvar', name('notRegistered')],
        ['app', ['proj', numbered, natural('9007199254740992'), ['bvar', natural('9007199254740993')]],
          ['app', ['lit', ['natVal', natural('9007199254740993')]], ['lit', ['strVal', '9007199254740993']]]],
        'strictImplicit'], true], 'instImplicit']];

function ok<T>(r: RawResult<T>): T {
  if (!r.ok) throw new Error(JSON.stringify(r.error)); return r.value;
}
function drawing(value: JsonValue = expression, family: RawFamily = 'expression'): RawInspectionDrawing {
  return ok(buildRawInspection({ family, value }, { sourceIdentity: 'test-source', sourcePath: ['capture', 'term'] }));
}
function roundtrip(family: RawFamily, value: JsonValue): RawInspectionDrawing {
  const d = drawing(value, family);
  expect(ok(readRawInspection(d))).toEqual({ family, value });
  return d;
}
function failure(r: RawResult<unknown>, code: 'malformed' | 'unsupported' | 'limit' = 'malformed'): void {
  expect(r.ok).toBe(false);
  if (!r.ok) { expect(r.error.code).toBe(code); expect(r.error.message).not.toBe(''); expect(Array.isArray(r.error.path)).toBe(true); }
}
function frame(): JsonValue {
  return { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: [
    { constructor: 'cdecl', index: natural(7), fvarId: numbered, userName: name('same'), type: sort, binderInfo: 'implicit', kind: 'default' },
    { constructor: 'ldecl', index: natural(2), fvarId: numbered, userName: name('same'), type: reference,
      value: ['mdata', metadata, ['bvar', natural('9999999999999999999999999')]], nondep: true, kind: 'implDetail' },
    { constructor: 'ldecl', index: natural(2), fvarId: numbered, userName: name('same'), type: sort,
      value: ['mvar', numbered], nondep: false, kind: 'auxDecl' },
  ], sourceTerm: expression, sourceType: ['mvar', name('type')] };
}

describe('raw constructor inspection and independent readback', () => {
  it('roundtrips all Expr constructors including arbitrary unresolved references and metadata', () => {
    const d = roundtrip('expression', expression);
    expect(new Set(d.nodes.filter(n => n.family === 'expression').map(n => n.tag))).toEqual(new Set([
      'bvar', 'fvar', 'mvar', 'sort', 'const', 'app', 'lam', 'forallE', 'letE', 'lit', 'mdata', 'proj',
    ]));
    expect(d.schema).toBe('definograph.raw-inspection.v1'); expect(d.naturalProfile).toBe(2);
    expect(d.nodes.every(n => Object.keys(n).sort().join() === ['id', 'family', 'tag', 'sourcePath', 'fields', 'children'].sort().join())).toBe(true);
    expect(d.nodes.find(n => n.tag === 'bvar')?.fields).toEqual([{ role: 'index', kind: 'natural', value: natural('9007199254740993') }]);
    expect(d.nodes.some(n => 'homeId' in n || 'declarationId' in n || 'raw' in n || 'expression' in n)).toBe(false);
  });

  it('exposes every Level constructor and keeps expression/level metavariables in distinct families', () => {
    const d = drawing();
    expect(new Set(d.nodes.filter(n => n.family === 'level').map(n => n.tag))).toEqual(new Set(['zero', 'succ', 'max', 'imax', 'param', 'mvar']));
    expect(d.nodes.filter(n => n.tag === 'mvar').some(n => n.family === 'level')).toBe(true);
    expect(d.nodes.filter(n => n.tag === 'mvar').some(n => n.family === 'expression')).toBe(true);
  });

  it.each(dataValues.map((value, i) => ({ value, i })))('retains DataValue variant $i', ({ value }) => {
    roundtrip('dataValue', value);
  });

  it('retains ordered duplicate metadata keys rather than using a map', () => {
    const d = roundtrip('metadata', metadata), list = d.nodes.find(n => n.family === 'metadataEntries')!;
    expect(list.children.map(e => e.ordinal)).toEqual(dataValues.map((_, i) => i));
    expect(d.nodes.filter(n => n.family === 'metadataEntry').map(n => n.fields[0].value)).toEqual(dataValues.map(() => numbered));
    expect(d.nodes.filter(n => n.family === 'dataValue').map(n => n.tag)).toEqual(dataValues.map(v => (v as JsonValue[])[0]));
  });

  it('exposes all Syntax, SourceInfo and Preresolved variants with ordered string items', () => {
    const d = roundtrip('syntax', syntax);
    expect(new Set(d.nodes.filter(n => n.family === 'syntax').map(n => n.tag))).toEqual(new Set(['node', 'atom', 'ident', 'missing']));
    expect(new Set(d.nodes.filter(n => n.family === 'sourceInfo').map(n => n.tag))).toEqual(new Set(['none', 'original', 'synthetic']));
    expect(d.nodes.filter(n => n.family === 'preresolved').map(n => n.tag)).toEqual(['namespace', 'decl']);
    expect(d.nodes.filter(n => n.family === 'string').map(n => n.fields[0].value)).toEqual(['x', 'x', '', 'λ😀']);
    roundtrip('sourceInfo', ['synthetic', zero, zero, true]);
  });

  it('preserves backing strings and invalid raw byte positions without substring slicing', () => {
    const d = roundtrip('substring', substring);
    expect(d.nodes[0].fields).toEqual([
      { role: 'backingString', kind: 'string', value: 'λ😀\n\u0000' },
      { role: 'startPosition', kind: 'natural', value: natural('99999999999999999999999999') },
      { role: 'stopPosition', kind: 'natural', value: natural(1) },
    ]);
    roundtrip('substring', ['substring', '😀', natural(1), natural(2)]);
  });

  it.each(['default', 'implicit', 'strictImplicit', 'instImplicit'])('keeps binder flag %s', binderInfo => {
    roundtrip('expression', ['lam', anonymous, sort, ['bvar', zero], binderInfo]);
    roundtrip('localDeclaration', { constructor: 'cdecl', index: zero, fvarId: anonymous, userName: anonymous, type: sort, binderInfo, kind: 'default' });
  });

  it.each([false, true])('retains owned and original let nondep=%s without equational edges', nondep => {
    const d = roundtrip('expression', ['letE', anonymous, sort, reference, reference, nondep]);
    expect(d.nodes[0].children.map(e => e.role)).toEqual(['type', 'value', 'body']);
    const external = roundtrip('localDeclaration', { constructor: 'ldecl', index: zero, fvarId: numbered,
      userName: anonymous, type: sort, value: expression, nondep, kind: 'auxDecl' });
    expect(external.nodes[0].children.map(e => e.role)).toEqual(['type', 'value']);
    expect(external.nodes.every(n => n.children.every(e => e.role !== 'definitionValue' && e.role !== 'reference'))).toBe(true);
  });

  it('preserves original declaration order, duplicate IDs/indices and nonmonotone indices', () => {
    const d = roundtrip('frame', frame()), declarations = d.nodes.filter(n => n.family === 'localDeclaration');
    expect(declarations.map(n => n.fields.find(f => f.role === 'index')!.value)).toEqual([natural(7), natural(2), natural(2)]);
    expect(declarations.map(n => n.fields.find(f => f.role === 'fvarId')!.value)).toEqual([numbered, numbered, numbered]);
    expect(declarations.map(n => n.fields.find(f => f.role === 'kind')!.value)).toEqual(['default', 'implDetail', 'auxDecl']);
    expect(d.nodes[0].children.map(e => e.role)).toEqual(['originalDeclarations', 'sourceTerm', 'sourceType']);
  });

  it('retains huge integers, adjacent naturals, and numeric versus string Name components', () => {
    const huge = '9'.repeat(10_000);
    roundtrip('integer', ['negSucc', natural(huge)]);
    roundtrip('integer', ['ofNat', natural(huge)]);
    const a = roundtrip('dataValue', ['ofName', ['num', anonymous, natural('9007199254740992')]]);
    const b = roundtrip('dataValue', ['ofName', ['num', anonymous, natural('9007199254740993')]]);
    const c = roundtrip('dataValue', ['ofName', name('9007199254740993')]);
    expect(a.nodes).not.toEqual(b.nodes); expect(b.nodes).not.toEqual(c.nodes);
    expect(drawing(['lit', ['natVal', natural(12)]]).nodes).not.toEqual(drawing(['lit', ['strVal', '12']]).nodes);
  });

  it('uses occurrence identity even when the caller reuses one object', () => {
    const leaf = ['fvar', numbered] as JsonValue;
    const d = roundtrip('expression', ['app', leaf, leaf]);
    expect(new Set(d.nodes.map(n => n.id)).size).toBe(d.nodes.length);
    expect(d.nodes[0].children[0].nodeId).not.toBe(d.nodes[0].children[1].nodeId);
    expect(d.nodes.slice(1).map(n => n.sourcePath)).toEqual([['capture', 'term', 1], ['capture', 'term', 2]]);
  });

  it('has detached input, drawing, and readback values', () => {
    const input: JsonValue = ['const', ['num', name('x'), natural(7)], [['param', name('u')]]];
    const d = drawing(input), first = ok(readRawInspection(d));
    ((input as JsonValue[])[1] as JsonValue[])[2] = natural(8);
    expect(ok(readRawInspection(d))).toEqual(first);
    (((first.value as JsonValue[])[1] as JsonValue[])[2] as JsonValue[])[1] = '9';
    expect(ok(readRawInspection(d))).not.toEqual(first);
  });

  it('reader reconstructs edits from exposed fields instead of retaining an invisible original', () => {
    const d = drawing(['app', ['lit', ['natVal', natural(7)]], ['mvar', name('m')]]);
    d.nodes.find(n => n.family === 'literal')!.fields[0].value = ['nat', '8'];
    expect(ok(readRawInspection(d)).value).toEqual(['app', ['lit', ['natVal', natural(8)]], ['mvar', name('m')]]);
    // Node array order and the spelling of occurrence IDs carry no hidden source.
    const renamed = structuredClone(d), names = new Map(renamed.nodes.map((n, i) => [n.id, `reordered:${i}`]));
    renamed.rootId = names.get(renamed.rootId)!;
    renamed.nodes.reverse().forEach(n => { n.id = names.get(n.id)!; n.children.forEach(e => { e.nodeId = names.get(e.nodeId)!; }); });
    expect(ok(readRawInspection(renamed))).toEqual(ok(readRawInspection(d)));
  });
});

describe('raw inspection admission and resource boundaries', () => {
  it.each([
    ['expression', ['bvar', 0]], ['expression', ['proj', anonymous, 1, sort]], ['integer', ['ofNat', -1]],
    ['literal', ['natVal', natural('01')]], ['literal', ['natVal', natural('1\n')]],
    ['literal', ['strVal', '\ud800']], ['expression', ['letE', anonymous, sort, sort, sort, 1]],
    ['expression', ['lam', anonymous, sort, sort, 'invalid']], ['expression', ['app', sort]],
    ['dataValue', ['ofBool', 'false']], ['substring', ['substring', 'x', zero]],
  ] as [RawFamily, JsonValue][])('rejects malformed %s source %j', (family, value) => {
    failure(buildRawInspection({ family, value }, { sourceIdentity: 's' }));
  });

  it.each(['expression', 'level', 'literal', 'metadata', 'dataValue', 'integer', 'syntax', 'sourceInfo', 'substring', 'preresolved'] as RawFamily[])(
    'reports unknown %s constructors explicitly', family => {
      failure(buildRawInspection({ family, value: ['futureTag', zero] }, { sourceIdentity: 's' }), 'unsupported');
    });

  it('rejects unknown versions and families', () => {
    failure(buildRawInspection({ family: 'futureFamily' as RawFamily, value: [] }, { sourceIdentity: 's' }), 'unsupported');
    const f = frame() as Record<string, JsonValue>; f.schema = 'definograph.raw-frame.v2';
    failure(buildRawInspection({ family: 'frame', value: f }, { sourceIdentity: 's' }), 'unsupported');
    const d = drawing() as unknown as Record<string, unknown>; d.naturalProfile = 1;
    failure(readRawInspection(d), 'unsupported'); d.naturalProfile = 2; d.schema = 'definograph.raw-inspection.v2';
    failure(readRawInspection(d), 'unsupported');
  });

  it('rejects sparse, extra, symbol, accessor and nonenumerable properties and cycles', () => {
    const malformed: unknown[] = [];
    const sparse = ['app', sort, sort]; delete sparse[1]; malformed.push(sparse);
    malformed.push(Object.assign(['bvar', zero], { extra: true }));
    const symbol = ['bvar', zero]; Object.defineProperty(symbol, Symbol('extra'), { value: true }); malformed.push(symbol);
    const hidden = ['bvar', zero]; Object.defineProperty(hidden, 'hidden', { value: true }); malformed.push(hidden);
    const getter = ['bvar', zero]; Object.defineProperty(getter, 1, { enumerable: true, get() { throw new Error('must not invoke accessor'); } }); malformed.push(getter);
    const cyclic: unknown[] = ['app', sort]; cyclic.push(cyclic); malformed.push(cyclic);
    for (const value of malformed) failure(buildRawInspection({ family: 'expression', value: value as JsonValue }, { sourceIdentity: 's' }));
    const d = drawing(); Object.defineProperty(d.nodes[0], 'hidden', { value: expression }); failure(readRawInspection(d));
  });

  it.each([
    'raw rescue', 'extra field', 'missing field', 'field role', 'field kind', 'child role', 'child ordinal',
    'missing child', 'shared child', 'cyclic edge', 'orphan', 'duplicate id', 'wrong family', 'wrong path', 'wrong collection ordinal',
  ])('rejects drawing mutation: %s', mutation => {
    const d = drawing(['app', ['bvar', natural(4)], ['const', numbered, [['zero']]]]);
    const root = d.nodes[0], bvar = d.nodes.find(n => n.tag === 'bvar')!, levels = d.nodes.find(n => n.family === 'levels')!;
    switch (mutation) {
      case 'raw rescue': Object.assign(root, { rawSource: expression }); break;
      case 'extra field': bvar.fields.push({ role: 'spare', kind: 'boolean', value: true }); break;
      case 'missing field': bvar.fields = []; break;
      case 'field role': bvar.fields[0].role = 'other'; break;
      case 'field kind': bvar.fields[0] = { role: 'index', kind: 'string', value: '4' }; break;
      case 'child role': root.children[0].role = 'argument'; break;
      case 'child ordinal': root.children[0].ordinal = 0; break;
      case 'missing child': root.children.pop(); break;
      case 'shared child': root.children[1].nodeId = root.children[0].nodeId; break;
      case 'cyclic edge': root.children[0].nodeId = root.id; break;
      case 'orphan': d.nodes.push({ ...structuredClone(bvar), id: 'orphan' }); break;
      case 'duplicate id': d.nodes.push(structuredClone(bvar)); break;
      case 'wrong family': bvar.family = 'level'; break;
      case 'wrong path': bvar.sourcePath = [...root.sourcePath, 2]; break;
      case 'wrong collection ordinal': levels.children[0].ordinal = 1; break;
    }
    failure(readRawInspection(d));
  });

  it('rejects sparse or decorated drawings and unknown node tags', () => {
    const sparse = drawing(); delete (sparse.nodes as unknown[])[1]; failure(readRawInspection(sparse));
    const d = drawing(); Object.assign(d.nodes[0].children, { invisible: 1 }); failure(readRawInspection(d));
    const unknown = drawing(); unknown.nodes[0].tag = 'futureTag'; failure(readRawInspection(unknown), 'unsupported');
    const wrongNat = drawing(['bvar', zero]); wrongNat.nodes[0].fields[0].value = 0 as never; failure(readRawInspection(wrongNat));
  });

  it('enforces caller-lowered node/depth/text/digit/output limits on building and reading', () => {
    failure(buildRawInspection({ family: 'expression', value: expression }, { sourceIdentity: 's', limits: { maxNodes: 2 } }), 'limit');
    failure(readRawInspection(drawing(), { limits: { maxNodes: 2 } }), 'limit');
    failure(buildRawInspection({ family: 'expression', value: ['app', sort, sort] }, { sourceIdentity: 's', limits: { maxDepth: 1 } }), 'limit');
    failure(readRawInspection(drawing(['app', sort, sort]), { limits: { maxDepth: 1 } }), 'limit');
    failure(buildRawInspection({ family: 'dataValue', value: ['ofString', '😀😀'] }, { sourceIdentity: 's', limits: { maxTextBytes: 7 } }), 'limit');
    failure(readRawInspection(drawing(['ofString', '😀😀'], 'dataValue'), { limits: { maxTextBytes: 7 } }), 'limit');
    failure(buildRawInspection({ family: 'integer', value: ['negSucc', natural(123)] }, { sourceIdentity: 's', limits: { maxNaturalDigits: 2 } }), 'limit');
    failure(readRawInspection(drawing(['negSucc', natural(123)], 'integer'), { limits: { maxNaturalDigits: 2 } }), 'limit');
    failure(buildRawInspection({ family: 'expression', value: sort }, { sourceIdentity: 's', limits: { maxOutputBytes: 100 } }), 'limit');
    failure(readRawInspection(drawing(sort), { limits: { maxOutputBytes: 100 } }), 'limit');
  });

  it('counts repeated source paths and IDs toward serialized output limits', () => {
    const items: JsonValue = Array.from({ length: 20 }, () => ['missing']);
    const source = { family: 'syntaxList' as const, value: items };
    const options = { sourceIdentity: 's', sourcePath: ['repeated'.repeat(40)], limits: { maxOutputBytes: 5000 } };
    expect(JSON.stringify(source).length).toBeLessThan(5000);
    failure(buildRawInspection(source, options), 'limit');
  });

  it('supports wide collections without list-length depth and rejects default digit/depth excess', () => {
    const d = ok(buildRawInspection({ family: 'syntaxList', value: Array.from({ length: 1000 }, () => ['missing']) },
      { sourceIdentity: 's', limits: { maxDepth: 2 } }));
    expect(ok(readRawInspection(d, { limits: { maxDepth: 2 } })).value).toHaveLength(1000);
    failure(buildRawInspection({ family: 'integer', value: ['ofNat', natural('1'.repeat(10_001))] }, { sourceIdentity: 's' }), 'limit');
    let deep: JsonValue = ['zero']; for (let i = 0; i < 129; i++) deep = ['succ', deep];
    failure(buildRawInspection({ family: 'level', value: deep }, { sourceIdentity: 's' }), 'limit');
    failure(buildRawInspection({ family: 'level', value: ['zero'] }, { sourceIdentity: 's', limits: { maxDepth: 129 } }));
  });

  it('applies one aggregate budget to multiple retained expression roots', () => {
    const value: JsonValue = [sort, ['mdata', ['mdataEntries', []], ['mvar', anonymous]]];
    const d = roundtrip('expressions', value);
    expect(d.nodes[0].children.map(e => e.ordinal)).toEqual([0, 1]);
    expect(d.nodes.filter(n => n.family === 'expression').map(n => n.sourcePath)).toEqual([
      ['capture', 'term', 0], ['capture', 'term', 1], ['capture', 'term', 1, 2],
    ]);
    const source = { family: 'expressions' as const, value: [['lit', ['strVal', 'abcdef']], ['lit', ['strVal', 'abcdef']]] as JsonValue };
    const r = buildRawInspection(source, { sourceIdentity: 's', sourcePath: [], limits: { maxTextBytes: 10 } });
    failure(r, 'limit');
    if (!r.ok) expect(r.error.path[0]).toBe(1);
    const invalid = buildRawInspection({ family: 'expressions', value: [sort, ['lit', ['strVal', '\ud800']]] },
      { sourceIdentity: 's', sourcePath: [] });
    failure(invalid);
    if (!invalid.ok) expect(invalid.error.path).toEqual([1, 1, 1]);
  });
});
