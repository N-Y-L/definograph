import { createHash } from 'node:crypto';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { expressionKey, formatExpression } from '../semantic/expression';
import { encodeNatural, type NaturalProfile } from './natural';
import { parsePacket, type JsonValue, type PacketEnvelope, type RecordRole } from './packet';
import { capturedPacketExpression, compilePacketRecord } from './semantic';
import { describeSelectedUse, PacketReading, selectedUseApplication, selectedUseObject, selectedUseSource } from './PacketReader';
import { buildStructuralDrawing, readStructuralDrawing } from './structure';
import { StructuralFieldValue, StructuralNodeFields, StructuralReading } from './StructuralReading';

const large = '9007199254740992', adjacent = '9007199254740993';
const name = (text: string): JsonValue => ['str', ['anonymous'], text];
const constant = (text: string): JsonValue => ['const', name(text), []];
const app = (fn: JsonValue, ...args: JsonValue[]): JsonValue => args.reduce<JsonValue>((f, arg) => ['app', f, arg], fn);
const nat = constant('Nat');

// Independent envelope bindings, as in packet.test.ts. These invented source
// controls make only unknown checking reports; hashing them does not add trust.
function canonical(value: JsonValue): string {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
  const keys = Object.keys(value).sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  return `{${keys.map(key => `${JSON.stringify(key)}:${canonical(value[key])}`).join(',')}}`;
}
const hash = (value: JsonValue): string => createHash('sha256').update(canonical(value)).digest('hex');
function boundEnvelope(envelope: PacketEnvelope): string {
  const { payload, request, basis } = envelope;
  const basisId = hash({ request, basis });
  const environments = [hash({ basis: basisId, initial: basis.env0 })];
  envelope.bindings = {
    payload: hash(payload),
    results: payload.results.map((result, i) => ({ pair: result.id,
      subject: hash({ basis: basisId, bank: hash(payload.bank), context: hash(payload.context), inputs: hash(payload.inputs[i]), candidate: hash(result.candidate) }),
      report: hash(result.report), records: { retained: hash(result.records.retained), derived: hash(result.records.derived) } })),
    checks: payload.checks.map(check => ({ id: check.id, receipt: hash(check), environmentBefore: environments[0], environmentAfter: environments[0] })),
    environments,
    uses: payload.uses.map(use => ({ id: [payload.attempt, use.pair, use.role, hash(payload.results.find(r => r.id === use.pair)!.records[use.role]), use.oid, use.path], entry: hash(use) })),
    audits: [],
  };
  const { digest: _digest, ...unsigned } = envelope;
  envelope.digest = hash(unsigned);
  return canonical(envelope);
}

async function consumerPacket(profile: NaturalProfile) {
  const encoded = (n: number): JsonValue => encodeNatural(n, profile);
  const first = profile === 2 ? ['nat', large] as JsonValue : 17;
  const second = profile === 2 ? ['nat', adjacent] as JsonValue : 18;
  const decimal = profile === 2 ? large : '17';
  const exactName: JsonValue = ['num', name('function'), first];
  const functionValue: JsonValue = ['const', exactName, [['param', ['num', name('u'), second]]]];
  const functionType: JsonValue = ['forallE', name('argument'), nat, nat, 'default'];
  const b = (index: number): JsonValue => ['bvar', encoded(index)];
  const body = app(b(0), b(2), b(1), ['lit', ['natVal', first]], ['lit', ['natVal', second]], ['lit', ['strVal', decimal]]);
  const raw: JsonValue = ['forallE', name('same'), nat, ['forallE', name('same'), nat,
    ['letE', name('supplier'), functionType, functionValue, body, false], 'default'], 'default'];
  const use = (offset: number): JsonValue => ['use', offset, 0, ['nil']];
  const path = ['fn', 'fn', 'fn', 'fn', 'fn'];
  const member = { entry: { e: 0, scope: [], path, use: { oid: first, src: use(0), view: use(0),
    acts: ['nil'], srcCert: ['exact'], viewCert: ['exact'] } }, sourceLevels: { tag: 'notApplicable' }, viewLevels: { tag: 'notApplicable' } };
  const owner: JsonValue = ['port', ['port', ['nil'], { name: name('same'), info: 'default' }, use(2)],
    { name: name('same'), info: 'default' }, use(2)];
  const record = { n: 2, owner, nodeName: name('supplier'), nodeTy: use(1), sup: use(0), uses: [member],
    table: { homes: [0, 0, 0], rows: [{ home: 0, row: nat },
      { home: 0, row: ['pi', { name: name('argument'), info: 'default' }, use(0), use(0)] }, { home: 0, row: functionValue }] } };
  const inputs = ['first', 'second'].map(id => ({ id, F: null, G: null }));
  const checks = inputs.flatMap(input => (['retained', 'derived'] as RecordRole[]).map(role => {
    const id = (input.id === 'first' ? 0 : 2) + Number(role === 'derived');
    const label = `${role === 'retained' ? 'laws' : 'law'}.reading`;
    const declaration = { kind: 'defnDecl', name: ['num', name('Check'), encoded(id)], type: ['sort', ['zero']], value: raw };
    return { id, pair: input.id, label, declaration, subject: { attempt: 'natural-consumer', pair: input.id, sequence: id, target: label + ' is a proposition', declaration },
      envBefore: 0, envAfter: 0, heartbeatBound: encoded(100), outcome: { tag: 'unknown', reason: 'synthetic source, not kernel evidence' } };
  }));
  const results = inputs.map(input => ({ id: input.id, candidate: null, records: { retained: record, derived: record },
    report: { formation: { tag: 'unknown' }, evidence: { tag: 'notFormed' }, checks: checks.filter(check => check.pair === input.id).map(check => [check.label, check.outcome]) } }));
  const envelope = { schema: profile, request: { id: 'natural-consumer', documentRevision: 'test', sourceSnapshot: 'test' },
    basis: { workerEpoch: 'test', env0: 'test', depsDigest: 'test', workerDigest: 'test', fixedUniverseInstance: [], policies: {} },
    payload: { schema: profile, attempt: 'natural-consumer', mode: 'constructor-control', bank: { exactEvidence: null }, context: {}, inputs, results, checks,
      uses: results.flatMap(result => (['retained', 'derived'] as RecordRole[]).map(role => ({ ...member, pair: result.id, role, oid: first, path }))), audits: [],
      coherence: { value: false, inputs, bankExact: false, admissions: [false, false] }, joint: { formation: 'notChecked', evidence: 'notConstructed' } },
    bindings: {}, digest: '',
  } as PacketEnvelope;
  return parsePacket(boundEnvelope(envelope));
}

describe('exact-natural consumer integration', () => {
  it('keeps v2 large naturals exact and distinct from identically spelled string literals', async () => {
    const packet = await consumerPacket(2), model = compilePacketRecord(packet, 0, 'retained');
    expect(model.profile).toBe(2); expect(model.document).toBeDefined();
    const literals = model.document!.objects.filter(o => o.expression?.kind === 'literal');
    const expressions = literals.map(o => o.expression!);
    expect(expressions).toHaveLength(3);
    expect(expressions.map(expression => expression.kind === 'literal' && expression.value)).toEqual([large, adjacent, large]);
    expect(expressions.map(formatExpression)).toEqual([large, adjacent, JSON.stringify(large)]);
    expect(new Set(expressions.map(expression => expressionKey(expression))).size).toBe(3);
    expect(new Set(literals.map(o => o.id)).size).toBe(3);
    expect(model.document!.source).toContain(adjacent);
  });

  it.each([1, 2] as const)('resolves selected supplier and shadowed bound references in profile %s', async profile => {
    const packet = await consumerPacket(profile), model = compilePacketRecord(packet, 0, 'retained');
    const sourceId = selectedUseSource(model, packet.payload.uses[0]);
    expect(sourceId).toBeDefined(); expect(model.supplierObjectId).toBeDefined();
    expect(selectedUseObject(model, sourceId)).toBe(model.supplierObjectId);
    const boundSources = Object.entries(model.sourceById).filter(([, source]) => Array.isArray(source.syntax) && source.syntax[0] === 'bvar');
    const targets = new Set(boundSources.map(([id]) => selectedUseObject(model, id)));
    expect(targets.has(undefined)).toBe(false); expect(targets.size).toBe(3);
    const call = selectedUseApplication(model, sourceId)!;
    expect(call.arguments).toHaveLength(5);
    expect(call.arguments.map(arg => arg.text).slice(0, 2)).toEqual(['same', 'same@2']);
    expect(call.arguments.map(arg => arg.text).slice(2)).toEqual(profile === 2 ? [large, adjacent, JSON.stringify(large)] : ['17', '18', '"17"']);
    const selected = describeSelectedUse(packet.payload.results[0].records.retained, packet.payload.uses[0], profile);
    expect(selected.scope.map(binding => binding.label)).toEqual(['same', 'same@2']);
    expect(selected.source).toContain(profile === 2 ? large : '17');
    if (profile === 1) {
      const { profile: _profile, ...legacy } = model;
      expect(selectedUseObject(legacy, sourceId)).toBe(model.supplierObjectId);
      expect(selectedUseApplication(legacy, sourceId)?.text).toBe(call.text);
      expect(describeSelectedUse(packet.payload.results[0].records.retained, packet.payload.uses[0])).toEqual(selected);
    }
  });

  it('rejects a wrong profile or unbounded selected index instead of rounding it to a binder', async () => {
    const packet = await consumerPacket(2), model = compilePacketRecord(packet, 0, 'retained');
    const sourceId = selectedUseSource(model, packet.payload.uses[0])!;
    expect(selectedUseObject({ ...model, profile: 1 }, sourceId)).toBeUndefined();
    const oversized = { ...model, sourceById: { ...model.sourceById,
      [sourceId]: { ...model.sourceById[sourceId], syntax: ['bvar', ['nat', large]] as JsonValue } } };
    expect(selectedUseObject(oversized, sourceId)).toBeUndefined();
  });

  it.each([1, 2] as const)('renders both packet views using the captured profile %s', async profile => {
    const packet = await consumerPacket(profile);
    for (const initialView of ['guided', 'structure'] as const) {
      const html = renderToStaticMarkup(createElement(PacketReading, { packet, initialView }));
      expect(html).toContain('Unverified imported packet');
      expect(html).not.toContain('Source structure unavailable');
      expect(html).not.toContain('Readable use unavailable');
      expect(html).not.toContain('Application reading unavailable');
      expect(html).toContain(profile === 2 ? adjacent : '18');
      expect(html).toContain('recorded heartbeat bound 100');
      expect(html).toContain(`local use ${profile === 2 ? large : '17'}`);
      if (initialView === 'structure') expect(html).toContain('aria-label="Exact source structure"');
    }
    const captured = capturedPacketExpression(packet, 0, 'retained')!;
    const drawing = buildStructuralDrawing(captured.syntax, { sourceIdentity: 'consumer', profile });
    expect(drawing.ok).toBe(true);
    if (drawing.ok) expect(readStructuralDrawing(drawing.value)).toEqual({ ok: true, value: { expression: captured.syntax, externalContext: [] } });
  });

  it('renders large projection, literal, name, universe and external-index fields as exact decimal data', () => {
    const numeric: JsonValue = ['num', name('component'), ['nat', adjacent]];
    const raw: JsonValue = ['proj', numeric, ['nat', large], ['app', ['const', numeric, [['param', numeric]]], ['lit', ['natVal', ['nat', adjacent]]]]];
    const drawing = buildStructuralDrawing(raw, { sourceIdentity: 'all-fields', profile: 2 });
    expect(drawing.ok).toBe(true);
    if (!drawing.ok) return;
    const html = renderToStaticMarkup(createElement(StructuralReading, { drawing: drawing.value, initialNodeLimit: 200 }));
    expect(html).toContain(`field ${large}`); expect(html).toContain(adjacent); expect(html).not.toContain('nat,');
    const fields = drawing.value.nodes.map(node => renderToStaticMarkup(createElement(StructuralNodeFields, { node }))).join('');
    expect(fields).toContain('Exact natural number'); expect(fields).toContain('Decimal digits');
    expect(fields).toContain('Numeric name component'); expect(fields).toContain('Named universe parameter'); expect(fields).toContain('Natural literal');
    expect(fields).toContain(large); expect(fields).toContain(adjacent);
    const externalIndex = renderToStaticMarkup(createElement(StructuralFieldValue, { value: { index: ['nat', adjacent] } }));
    expect(externalIndex).toContain('Index'); expect(externalIndex).toContain(adjacent); expect(externalIndex).toContain('Exact natural number');
  });
});
