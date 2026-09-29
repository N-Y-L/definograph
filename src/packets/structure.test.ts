import { describe, expect, it } from 'vitest';
import type { JsonValue } from './packet';
import { MAX_NATURAL_DIGITS, type TaggedNatural } from './natural';
import {
  buildStructuralDrawing, readStructuralDrawing,
  type ExternalDeclarationInput, type StructuralDrawing, type StructuralName, type StructureResult,
} from './structure';

const anonymous: StructuralName = ['anonymous'];
const named = (s: string): StructuralName => ['str', anonymous, s];
const c = (s: string): JsonValue => ['const', named(s), []];
const nat = (n: number): JsonValue => ['lit', ['natVal', n]];
const b = (n: number): JsonValue => ['bvar', n];
const fv = (name: StructuralName): JsonValue => ['fvar', name];
const sort: JsonValue = ['sort', ['zero']];
const app = (f: JsonValue, x: JsonValue): JsonValue => ['app', f, x];
const lam = (label: string, type: JsonValue, body: JsonValue): JsonValue => ['lam', named(label), type, body, 'default'];
function ok<T>(r: StructureResult<T>): T {
  if (!r.ok) throw new Error(JSON.stringify(r.error)); return r.value;
}
function build(expr: JsonValue, externalContext: ExternalDeclarationInput[] = []): StructuralDrawing {
  return ok(buildStructuralDrawing(expr, { sourceIdentity: 'test-source', externalContext }));
}
function roundtrip(expr: JsonValue, externalContext: ExternalDeclarationInput[] = []): StructuralDrawing {
  const drawing = build(expr, externalContext);
  expect(ok(readStructuralDrawing(drawing))).toEqual({ expression: expr, externalContext });
  return drawing;
}
function failure(r: StructureResult<unknown>, code?: string): void {
  expect(r.ok).toBe(false);
  if (!r.ok) { if (code) expect(r.error.code).toBe(code); expect(r.error.message.length).toBeGreaterThan(0); }
}
const firstId = ['num', named('internal'), 7] as StructuralName;
const secondId = ['num', named('internal'), 8] as StructuralName;
const externals: ExternalDeclarationInput[] = [
  { constructor: 'cdecl', index: 3, fvarId: firstId, userName: named('x'), type: c('Nat'), binderInfo: 'implicit', kind: 'default' },
  { constructor: 'ldecl', index: 5, fvarId: secondId, userName: named('x'), type: c('Nat'), value: fv(firstId), nondep: false, kind: 'implDetail' },
];

describe('exact constructor drawing', () => {
  it('roundtrips every admitted universe and structured Name without textual canonicalization', () => {
    const numeric: StructuralName = ['num', ['str', anonymous, 'component.with.dot'], 42];
    const universes: JsonValue[] = [['zero'], ['succ', ['zero']], ['max', ['zero'], ['param', numeric]],
      ['imax', ['param', named('u')], ['succ', ['param', anonymous]]]];
    const expr: JsonValue = ['app', ['const', numeric, universes], ['sort', universes[3]]];
    const drawing = roundtrip(expr);
    const constant = drawing.nodes.find(n => n.kind === 'const');
    expect(constant?.kind === 'const' && constant.name).toEqual(numeric);
    expect(constant?.kind === 'const' && constant.levels).toEqual(universes);
    expect(build(c('7')).nodes).not.toEqual(build(['const', ['num', anonymous, 7], []]).nodes);
  });

  it('retains exact literal kind, safe natural value and Unicode scalar strings', () => {
    roundtrip(app(nat(Number.MAX_SAFE_INTEGER), ['lit', ['strVal', 'line\n"λ😀\u0000']]));
    failure(buildStructuralDrawing(nat(Number.MAX_SAFE_INTEGER + 1), { sourceIdentity: 's' }), 'malformed');
    failure(buildStructuralDrawing(['lit', ['strVal', '\ud800']], { sourceIdentity: 's' }), 'malformed');
  });

  it('keeps binary application order and arbitrary higher-order function positions', () => {
    const expr = app(app(lam('f', c('U'), b(0)), c('left')), app(c('g'), c('right')));
    const drawing = roundtrip(expr), root = drawing.nodes.find(n => n.id === drawing.rootId)!;
    expect(root.children.map(e => e.role)).toEqual(['function', 'argument']);
    expect(drawing.nodes.filter(n => n.kind === 'app')).toHaveLength(3);
    expect(drawing.nodes.find(n => n.id === root.children[0].nodeId)?.kind).toBe('app');
    expect(drawing.nodes.find(n => n.id === root.children[1].nodeId)?.sourcePath).toEqual(['expression', 2]);
  });

  it('distinguishes repeated binder names and puts a binder domain in its preceding home', () => {
    const expr = lam('x', c('U'), ['forallE', named('x'), b(0), app(b(1), b(0)), 'strictImplicit']);
    const drawing = roundtrip(expr);
    const binders = drawing.nodes.filter(n => n.kind === 'lam' || n.kind === 'forallE');
    const outer = binders[0], inner = binders[1];
    if ((outer.kind !== 'lam' && outer.kind !== 'forallE') || (inner.kind !== 'lam' && inner.kind !== 'forallE')) throw new Error('expected binders');
    const refs = drawing.nodes.filter(n => n.kind === 'bvar');
    expect(refs.map(n => n.declarationId)).toEqual([outer.declarationId, outer.declarationId, inner.declarationId]);
    expect(refs[0].homeId).toBe(inner.homeId);
    const innerDeclaration = drawing.declarations.find(d => d.id === inner.declarationId)!;
    expect(refs[1].homeId).toBe(innerDeclaration.bodyHomeId);
    expect(inner.children.map(e => e.role)).toEqual(['domain', 'body']);
    expect(outer.declarationId).not.toBe(inner.declarationId);
  });

  it.each(['default', 'implicit', 'strictImplicit', 'instImplicit'])('retains binder information %s', info => {
    roundtrip(['forallE', anonymous, sort, ['lam', named('argument'), b(0), b(1), info], info]);
  });

  it.each([false, true])('preserves nested let type/value/body homes and original nondep=%s', nondep => {
    const proj = (v: JsonValue): JsonValue => ['proj', ['num', named('Owner'), 2], 17, v];
    const expr = lam('x', c('U'), ['letE', named('x'), proj(b(0)), proj(b(0)),
      app(proj(b(0)), ['letE', anonymous, b(1), nat(9), app(b(2), b(0)), !nondep]), nondep]);
    const drawing = roundtrip(expr), lets = drawing.nodes.filter(n => n.kind === 'letE');
    expect(lets.map(n => n.nondep)).toEqual([nondep, !nondep]);
    for (const node of lets) {
      expect(node.children.map(e => e.role)).toEqual(['type', 'value', 'body']);
      const [type, value, body] = node.children.map(e => drawing.nodes.find(n => n.id === e.nodeId)!);
      expect(type.homeId).toBe(node.homeId); expect(value.homeId).toBe(node.homeId);
      expect(body.homeId).not.toBe(node.homeId);
    }
    expect(drawing.nodes.filter(n => n.kind === 'proj')).toHaveLength(3);
  });

  it('supports constructors in domains, values and function positions with no fixture dispatch', () => {
    const expression: JsonValue = ['forallE', named('unfamiliar'),
      ['letE', anonymous, sort, c('UnknownConstant'), ['proj', named('UnknownOwner'), 0, b(0)], false],
      app(['proj', named('UnknownOwner'), 12, lam('z', b(0), b(0))], ['lit', ['strVal', 'argument']]), 'instImplicit'];
    roundtrip(expression);
    roundtrip(JSON.parse(JSON.stringify(expression).replaceAll('unfamiliar', 'renamed').replaceAll('Unknown', 'Foreign')) as JsonValue);
  });

  it('parameterizes source identity/path and copies constructor fields independently of input mutation', () => {
    const expression = ['const', named('before'), [['param', named('u')]]] as JsonValue[];
    const drawing = ok(buildStructuralDrawing(expression, { sourceIdentity: 'document:two', sourcePath: ['operations', 9, 'term'] }));
    expression[1] = named('after');
    expect(drawing.nodes[0].sourcePath).toEqual(['operations', 9, 'term']);
    expect(drawing.nodes[0].id.startsWith('document:two:')).toBe(true);
    expect(ok(readStructuralDrawing(drawing)).expression).toEqual(['const', named('before'), [['param', named('u')]]]);
    expect(Object.values(drawing).some(v => v === expression)).toBe(false);
  });
});

describe('external named homes', () => {
  it('retains full chronological LocalDecl metadata and exact free identities under shadowing', () => {
    const drawing = roundtrip(lam('x', c('Nat'), app(app(fv(firstId), fv(secondId)), b(0))), externals);
    const refs = drawing.nodes.filter(n => n.kind === 'fvar');
    expect(refs.map(n => n.declarationId)).toEqual([drawing.externalDeclarationIds[0], drawing.externalDeclarationIds[0], drawing.externalDeclarationIds[1]]);
    for (const ref of refs) {
      const declaration = drawing.declarations.find(d => d.id === ref.declarationId)!;
      expect(ref.externalHomeId).toBe(declaration.bodyHomeId);
    }
    const definition = drawing.declarations.find(d => d.id === drawing.externalDeclarationIds[1]);
    expect(definition?.kind === 'external' && definition.children.map(e => e.role)).toEqual(['type', 'definitionValue']);
  });

  it('retains opaque nondependent stored values as metadata, including illtyped but representable values', () => {
    const input: ExternalDeclarationInput[] = [{ ...externals[1], constructor: 'ldecl', value: ['lit', ['strVal', 'not a Nat']], nondep: true, kind: 'auxDecl' }];
    const drawing = roundtrip(fv(secondId), input);
    const declaration = drawing.declarations[0];
    expect(declaration.kind === 'external' && declaration.children.map(e => e.role)).toEqual(['type', 'storedValue']);
  });

  it('does not treat the named external registry as ambient bound variables', () => {
    failure(buildStructuralDrawing(b(0), { sourceIdentity: 's', externalContext: externals }), 'malformed');
    failure(buildStructuralDrawing(lam('x', c('Nat'), b(1)), { sourceIdentity: 's', externalContext: externals }), 'malformed');
    const malformed = build(lam('x', c('Nat'), b(0)), externals);
    const ref = malformed.nodes.find(n => n.kind === 'bvar')!;
    ref.index = 1; ref.declarationId = malformed.externalDeclarationIds[1];
    failure(readStructuralDrawing(malformed), 'malformed');
  });

  it('rejects an absent, future, self or duplicate registry identity', () => {
    failure(buildStructuralDrawing(fv(firstId), { sourceIdentity: 's' }), 'malformed');
    const future: ExternalDeclarationInput[] = [{ ...externals[0], type: fv(secondId) }, externals[1]];
    failure(buildStructuralDrawing(c('True'), { sourceIdentity: 's', externalContext: future }), 'malformed');
    const self: ExternalDeclarationInput[] = [{ ...externals[0], type: fv(firstId) }];
    failure(buildStructuralDrawing(c('True'), { sourceIdentity: 's', externalContext: self }), 'malformed');
    failure(buildStructuralDrawing(c('True'), { sourceIdentity: 's', externalContext: [externals[0], externals[0]] }), 'malformed');
  });

  it('reports unsupported metadata as a drawing-profile boundary, not source admission failure', () => {
    for (const value of [fv(named('unregistered')), ['mvar', named('unsolved')]] as JsonValue[]) {
      const ext: ExternalDeclarationInput = { constructor: 'ldecl', index: 0, fvarId: firstId, userName: named('opaque'), type: c('Nat'), value, nondep: true, kind: 'default' };
      const outcome = buildStructuralDrawing(fv(firstId), { sourceIdentity: 's', externalContext: [ext] });
      failure(outcome, 'unsupported');
      if (!outcome.ok) expect(outcome.error.path.slice(0, 3)).toEqual(['externalContext', 0, 'value']);
    }
  });
});

describe('independent readback and explicit boundaries', () => {
  it('reads changed constructor fields instead of consulting a hidden source copy', () => {
    const drawing = build(nat(1)), leaf = drawing.nodes[0];
    if (leaf.kind !== 'lit') throw new Error('expected literal');
    leaf.literal = ['natVal', 2];
    expect(ok(readStructuralDrawing(drawing)).expression).toEqual(nat(2));
    const binder = build(lam('x', sort, b(0))), root = binder.nodes[0];
    if (root.kind !== 'lam') throw new Error('expected lambda');
    root.name = named('y'); root.binderInfo = 'implicit';
    expect(ok(readStructuralDrawing(binder)).expression).toEqual(['lam', named('y'), sort, b(0), 'implicit']);
  });

  it.each(['missingRole', 'reorderedRoles', 'sharedChild', 'cycle', 'orphan', 'duplicateId', 'extraField', 'wrongHome', 'wrongPath'])(
    'rejects graph mutation %s', mutation => {
      const d = build(app(c('f'), nat(2))), root = d.nodes[0];
      switch (mutation) {
        case 'missingRole': root.children.pop(); break;
        case 'reorderedRoles': root.children.reverse(); break;
        case 'sharedChild': root.children[1].nodeId = root.children[0].nodeId; break;
        case 'cycle': root.children[0].nodeId = root.id; break;
        case 'orphan': d.nodes.push({ ...d.nodes[1], id: 'unused' }); break;
        case 'duplicateId': d.nodes[1].id = root.id; break;
        case 'extraField': Object.assign(root, { sourceExpr: nat(99) }); break;
        case 'wrongHome': d.nodes[1].homeId = 'other-home'; break;
        case 'wrongPath': d.nodes[1].sourcePath = ['expression', 2]; break;
      }
      failure(readStructuralDrawing(d), 'malformed');
    });

  it('rejects reference retargeting and swapped domain/body homes despite identical labels', () => {
    const original = build(lam('x', sort, lam('x', b(0), app(b(1), b(0)))));
    const wrongReference = structuredClone(original), refs = wrongReference.nodes.filter(n => n.kind === 'bvar');
    refs[1].declarationId = refs[2].declarationId;
    failure(readStructuralDrawing(wrongReference), 'malformed');
    const wrongHome = structuredClone(original), inner = wrongHome.nodes.find(n => n.kind === 'lam' && n.id !== wrongHome.rootId)!;
    wrongHome.nodes.find(n => n.id === inner.children[0].nodeId)!.homeId = wrongHome.declarations.find(d => d.id === (inner.kind === 'lam' ? inner.declarationId : ''))!.bodyHomeId;
    failure(readStructuralDrawing(wrongHome), 'malformed');
    const free = build(app(fv(firstId), fv(secondId)), externals), reference = free.nodes.find(n => n.kind === 'fvar')!;
    reference.declarationId = free.externalDeclarationIds[1];
    failure(readStructuralDrawing(free), 'malformed');
  });

  it('cannot reinterpret opaque metadata as a defining equation by changing its edge label', () => {
    const ext: ExternalDeclarationInput = { constructor: 'ldecl', index: 0, fvarId: firstId, userName: named('x'), type: sort, value: sort, nondep: true, kind: 'default' };
    const d = build(fv(firstId), [ext]), declaration = d.declarations[0];
    if (declaration.kind !== 'external') throw new Error('expected external');
    declaration.children[1].role = 'definitionValue';
    failure(readStructuralDrawing(d), 'malformed');
  });

  it.each([
    ['mvar', named('m')], ['mdata', {}, c('x')], ['sort', ['mvar', named('u')]], ['unknown', c('x')],
  ].map(expression => ({ expression: expression as JsonValue })))('has an explicit unsupported result for $expression', ({ expression }) => {
    failure(buildStructuralDrawing(expression, { sourceIdentity: 's' }), 'unsupported');
  });

  it('rejects sparse constructor, role and universe arrays without throwing or dropping holes', () => {
    const expression = ['const', named('C'), Array(1)] as JsonValue;
    failure(buildStructuralDrawing(expression, { sourceIdentity: 's' }), 'malformed');
    const missingRoles = build(app(c('f'), nat(1)));
    missingRoles.nodes[0].children = Array(2);
    failure(readStructuralDrawing(missingRoles), 'malformed');
    const missingUniverse = build(c('C'));
    if (missingUniverse.nodes[0].kind !== 'const') throw new Error('expected constant');
    missingUniverse.nodes[0].levels = Array(1);
    failure(readStructuralDrawing(missingUniverse), 'malformed');
    const extra = ['sort', ['zero']] as unknown as JsonValue[] & { extra?: boolean };
    extra.extra = true;
    failure(buildStructuralDrawing(extra, { sourceIdentity: 's' }), 'malformed');
  });

  it('bounds constructor depth, whole drawing data, text expansion and external declarations', () => {
    let expression = c('x');
    for (let i = 0; i < 280; i++) expression = app(c('f'), expression);
    failure(buildStructuralDrawing(expression, { sourceIdentity: 's' }), 'limit');
    failure(buildStructuralDrawing(c('x'), { sourceIdentity: 's', limits: { maxNodes: 2 } }), 'limit');
    failure(buildStructuralDrawing(c('x'), { sourceIdentity: 'long-identity', limits: { maxText: 10 } }), 'limit');
    failure(buildStructuralDrawing(c('x'), { sourceIdentity: 's', externalContext: externals, limits: { maxExternalDeclarations: 1 } }), 'limit');
    failure(readStructuralDrawing(build(c('x')), { maxNodes: 2 }), 'limit');
    const cyclic = build(c('x'));
    (cyclic.nodes[0].sourcePath as unknown[]).push(cyclic.nodes[0].sourcePath);
    failure(readStructuralDrawing(cyclic), 'limit');
  });
});

describe('version 2 structural natural fields', () => {
  const big = '9007199254740992', next = '9007199254740993';
  const exact = (digits: string): TaggedNatural => ['nat', digits];
  const numeric = (digits: string): StructuralName => ['num', named('same'), exact(digits)];
  const bound = (index: string): JsonValue => ['bvar', exact(index)];
  const registry: ExternalDeclarationInput[] = [
    { constructor: 'cdecl', index: exact(big), fvarId: numeric(big), userName: named('same'), type: c('Nat'), binderInfo: 'implicit', kind: 'default' },
    { constructor: 'ldecl', index: exact(next), fvarId: numeric(next), userName: named('same'), type: c('Nat'),
      value: ['lit', ['natVal', exact(next)]], nondep: true, kind: 'auxDecl' },
  ];
  const universes: JsonValue[] = [['zero'], ['succ', ['zero']], ['max', ['param', numeric(big)], ['zero']],
    ['imax', ['param', numeric(next)], ['succ', ['zero']]]];
  const expression: JsonValue = ['lam', numeric(big), ['sort', universes[3]],
    ['letE', named('same'), c('Nat'), app(fv(numeric(big)), ['lit', ['strVal', 'λ\n"']]),
      ['forallE', named('same'), app(['const', numeric(next), universes], ['lit', ['natVal', exact(big)]]),
        ['proj', numeric(big), exact(next), app(app(bound('2'), bound('0')), fv(numeric(next)))], 'strictImplicit'], true], 'instImplicit'];

  it('reconstructs every constructor and exact external metadata with tagged small and large naturals', () => {
    const drawing = ok(buildStructuralDrawing(expression, { sourceIdentity: 'v2:all', profile: 2, externalContext: registry }));
    expect(drawing.schema).toBe('definograph.structure.v2');
    expect(ok(readStructuralDrawing(drawing))).toEqual({ expression, externalContext: registry });
    expect(new Set(drawing.nodes.map(node => node.kind))).toEqual(new Set(['const', 'lit', 'lam', 'sort', 'letE', 'app', 'fvar', 'forallE', 'proj', 'bvar']));
    expect(drawing.nodes.filter(node => node.kind === 'bvar').map(node => node.index)).toEqual([2, 0]);
    expect(drawing.declarations.filter(d => d.kind === 'external').map(d => d.index)).toEqual([exact(big), exact(next)]);
    const opaque = drawing.declarations.find(d => d.kind === 'external' && d.constructor === 'ldecl');
    expect(opaque?.kind === 'external' && opaque.children.map(edge => edge.role)).toEqual(['type', 'storedValue']);
  });

  it('keeps adjacent large names and numeric-versus-string identity distinct', () => {
    const raw = app(app(['const', numeric(big), []], ['const', numeric(next), []]), ['const', ['str', named('same'), big], []]);
    const drawing = ok(buildStructuralDrawing(raw, { sourceIdentity: 'v2:names', profile: 2 }));
    expect(ok(readStructuralDrawing(drawing)).expression).toEqual(raw);
    const fields = drawing.nodes.filter(n => n.kind === 'const').map(n => n.name);
    expect(new Set(fields.map(field => JSON.stringify(field))).size).toBe(3);
    const duplicate = structuredClone(registry);
    duplicate[1].index = exact(big);
    failure(buildStructuralDrawing(c('Nat'), { sourceIdentity: 'duplicate', profile: 2, externalContext: duplicate }), 'malformed');
  });

  it('copies tagged semantic fields and independently reads edits without a hidden input', () => {
    const input: JsonValue = ['proj', numeric(big), exact(big), ['lit', ['natVal', exact(big)]]];
    const drawing = ok(buildStructuralDrawing(input, { sourceIdentity: 'v2:edited', profile: 2 }));
    const projection = drawing.nodes.find(n => n.kind === 'proj')!;
    if (!Array.isArray(projection.field)) throw new Error('expected tagged projection index');
    projection.field[1] = next;
    expect(ok(readStructuralDrawing(drawing)).expression).toEqual(['proj', numeric(big), exact(next), ['lit', ['natVal', exact(big)]]]);
    expect(input).toEqual(['proj', numeric(big), exact(big), ['lit', ['natVal', exact(big)]]]);
  });

  it('rejects bare semantic naturals in v2 and tagged fields in v1', () => {
    for (const raw of [nat(0), ['const', ['num', anonymous, 0], []], ['proj', named('Owner'), 0, c('x')],
      ['lam', named('x'), c('Nat'), b(0), 'default']] as JsonValue[])
      failure(buildStructuralDrawing(raw, { sourceIdentity: 'mixed', profile: 2 }), 'malformed');
    for (const raw of [['lit', ['natVal', exact('0')]], ['const', numeric(big), []],
      ['proj', named('Owner'), exact('0'), c('x')]] as JsonValue[])
      failure(buildStructuralDrawing(raw, { sourceIdentity: 'mixed', profile: 1 }), 'malformed');
    const wrongIndex = structuredClone(registry); wrongIndex[0].index = 0;
    failure(buildStructuralDrawing(c('Nat'), { sourceIdentity: 'mixed', profile: 2, externalContext: wrongIndex }), 'malformed');
    const drawing = ok(buildStructuralDrawing(expression, { sourceIdentity: 'v2:schema', profile: 2, externalContext: registry }));
    drawing.schema = 'definograph.structure.v1';
    failure(readStructuralDrawing(drawing), 'malformed');
    const legacy = build(['const', ['num', anonymous, 1], []]);
    legacy.schema = 'definograph.structure.v2';
    failure(readStructuralDrawing(legacy), 'malformed');
  });

  it('bounds source bvars before conversion while keeping drawing positions operational', () => {
    failure(buildStructuralDrawing(['lam', named('x'), c('Nat'), bound(big), 'default'], { sourceIdentity: 'bounds', profile: 2 }), 'malformed');
    failure(buildStructuralDrawing(bound('0'), { sourceIdentity: 'bounds', profile: 2, externalContext: registry }), 'malformed');
    failure(buildStructuralDrawing(['lam', named('x'), c('Nat'), bound('1'), 'default'], { sourceIdentity: 'bounds', profile: 2, externalContext: registry }), 'malformed');
    const d = ok(buildStructuralDrawing(['lam', named('x'), c('Nat'), bound('0'), 'default'], { sourceIdentity: 'bounds', profile: 2 }));
    const ref = d.nodes.find(n => n.kind === 'bvar')!;
    Object.assign(ref, { index: exact('0') });
    failure(readStructuralDrawing(d), 'malformed');
  });

  it('accepts bounded-length huge scalar fields without claiming projection typing', () => {
    const digits = '9'.repeat(MAX_NATURAL_DIGITS);
    const raw: JsonValue = ['proj', numeric(digits), exact(digits), ['lit', ['natVal', exact(digits)]]];
    const drawing = ok(buildStructuralDrawing(raw, { sourceIdentity: 'scalar-limit', profile: 2 }));
    expect(ok(readStructuralDrawing(drawing)).expression).toEqual(raw);
    failure(buildStructuralDrawing(['lit', ['natVal', exact(digits + '9')]], { sourceIdentity: 'scalar-limit', profile: 2 }), 'limit');
    failure(buildStructuralDrawing(bound(digits + '9'), { sourceIdentity: 'bound-limit', profile: 2 }), 'limit');
    for (const digits of ['01', '-1', '1.0', '1e2', '１２'])
      failure(buildStructuralDrawing(['lit', ['natVal', exact(digits)]], { sourceIdentity: 'malformed', profile: 2 }), 'malformed');
  });

  it('rejects unknown schemas and profiles and retains opaque metadata boundaries', () => {
    const d = build(c('Nat')); Object.assign(d, { schema: 'definograph.structure.v3' });
    failure(readStructuralDrawing(d), 'unsupported');
    failure(buildStructuralDrawing(c('Nat'), { sourceIdentity: 'unknown', profile: 3 as 2 }), 'unsupported');
    const opaque = structuredClone(registry);
    if (opaque[1].constructor !== 'ldecl') throw new Error('expected let');
    opaque[1].value = ['mvar', numeric(big)];
    failure(buildStructuralDrawing(fv(numeric(big)), { sourceIdentity: 'opaque', profile: 2, externalContext: opaque }), 'unsupported');
  });
});
