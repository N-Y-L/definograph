import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, PacketError, parsePacket, validatePacketNaturalRoles, type JsonObject, type JsonValue } from './packet';
import { parseRawSourceText, RawImportError } from './raw-import';
import { readRawInspection } from './raw';

const name = (text: string): JsonValue => ['str', ['anonymous'], text];
const nat = (text: string): JsonValue => ['nat', text];
const prop: JsonValue = ['sort', ['zero']];
const metadataValue = (text = 'source'): JsonValue => ['mdata', ['mdataEntries', [
  [name('same'), ['ofString', text]], [name('same'), ['ofNat', nat('9007199254740993')]],
]], ['mvar', name('unresolved')]];
const local = (value = metadataValue()): JsonObject => ({ constructor: 'ldecl', index: nat('0'),
  fvarId: name('local'), userName: name('same'), type: prop, value, nondep: true, kind: 'default' });
const frame = (): JsonObject => ({ schema: 'definograph.raw-frame.v1', naturalProfile: 2,
  originalDeclarations: [local()], sourceTerm: ['bvar', nat('9007199254740993')], sourceType: prop });

// Independent identity oracle: UTF-8 ordering agrees with Unicode scalar order.
function canonical(value: JsonValue): string {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return '[' + value.map(canonical).join(',') + ']';
  return '{' + Object.keys(value).sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))
    .map(key => JSON.stringify(key) + ':' + canonical(value[key])).join(',') + '}';
}
const hash = (value: JsonValue): string => createHash('sha256').update(canonical(value)).digest('hex');
const binding = (): JsonObject => ({ schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1',
  sourceKind: 'named', context: { originalDeclarations: [local()] }, sourceTerm: ['bvar', nat('0')], sourceType: prop });

// A fully bound synthetic envelope reports no successful admission. Binding
// changes are rehashed independently so refusal tests exercise semantic roles.
function packetText(sourceBinding: JsonObject): string {
  const request = { id: 'raw-import-control', documentRevision: 'test', sourceSnapshot: 'test' };
  const basis = { workerEpoch: 'test', env0: 'test', depsDigest: 'test', workerDigest: 'test', fixedUniverseInstance: [], policies: {} };
  const inputs = ['first', 'second'].map(id => ({ id, F: null, G: null }));
  const results = inputs.map((input, i) => ({ id: input.id, candidate: null, records: { retained: null, derived: null },
    report: { formation: { tag: i === 0 ? 'unknown' : 'refused' }, evidence: { tag: 'notFormed' }, checks: [] } }));
  const payload = { schema: 2, attempt: request.id, mode: 'raw-import-control', bank: { exactEvidence: null }, context: { sourceBinding },
    inputs, results, checks: [], uses: [], audits: [], coherence: { value: false, inputs, bankExact: false, admissions: [false, false] },
    joint: { formation: 'notChecked', evidence: 'notConstructed' } };
  const basisId = hash({ request, basis });
  const bindings = { payload: hash(payload), results: results.map((result, i) => ({ pair: result.id,
    subject: hash({ basis: basisId, bank: hash(payload.bank), context: hash(payload.context), inputs: hash(inputs[i]), candidate: hash(null) }),
    report: hash(result.report), records: { retained: hash(null), derived: hash(null) } })),
    environments: [hash({ basis: basisId, initial: basis.env0 })], checks: [], uses: [], audits: [] };
  const unsigned = { schema: 2, request, basis, payload, bindings };
  return canonical({ ...unsigned, digest: hash(unsigned) });
}

describe('raw source text import', () => {
  it('preserves unresolved references, ordered duplicate metadata, and original bytes without trust claims', async () => {
    const value = frame(), sourceText = '\n' + JSON.stringify(value, null, 2) + '\n';
    const imported = await parseRawSourceText(sourceText);
    expect(imported.identity).toBe(hash(value));
    expect(imported.sourceText).toBe(sourceText);
    expect(imported.value).toEqual(value);
    expect(Object.keys(imported).sort()).toEqual(['drawing', 'identity', 'sourceText', 'value']);
    expect(readRawInspection(imported.drawing)).toEqual({ ok: true, value: { family: 'frame', value } });
    expect(imported.drawing.sourceIdentity).toBe(imported.identity);
    expect(imported.drawing.sourcePath).toEqual([]);
    expect(imported.drawing.nodes.find(node => node.id === imported.drawing.rootId)?.sourcePath).toEqual([]);
    expect(imported.drawing.nodes.find(node => node.family === 'expression' && node.tag === 'bvar')?.sourcePath).toEqual(['sourceTerm']);
    expect(imported.drawing.nodes.find(node => node.family === 'metadata')?.sourcePath).toEqual(['originalDeclarations', 0, 'value', 1]);
    for (const node of imported.drawing.nodes) {
      let source: JsonValue = value;
      for (const part of node.sourcePath) source = (source as JsonObject)[part];
      expect(source, JSON.stringify(node.sourcePath)).toBeDefined();
    }
    expect(imported.drawing.nodes.some(node => node.tag === 'mvar')).toBe(true);
    expect(imported.drawing.nodes.filter(node => node.family === 'metadataEntry')).toHaveLength(2);
    expect(Object.isFrozen(imported)).toBe(true);
    expect(Object.isFrozen(imported.value)).toBe(true);
    expect(Object.isFrozen(imported.drawing.nodes[0].children)).toBe(true);
    expect(() => imported.drawing.nodes.push(imported.drawing.nodes[0])).toThrow();
  });

  it('uses canonical scalar ordering and exact Unicode without erasing metadata distinctions', async () => {
    const a = frame(); a.originalDeclarations = [local(metadataValue('é e\u0301 😀 \u202e'))];
    const b = structuredClone(a);
    const localB = (b.originalDeclarations as JsonObject[])[0];
    ((localB.value as JsonValue[])[1] as JsonValue[])[1] = (((localB.value as JsonValue[])[1] as JsonValue[])[1] as JsonValue[]).slice().reverse();
    const imported = await parseRawSourceText(JSON.stringify(a));
    expect(imported.identity).toBe(hash(a));
    expect((await parseRawSourceText(canonical(a))).identity).toBe(imported.identity);
    expect((await parseRawSourceText(JSON.stringify(b))).identity).not.toBe(imported.identity);
    const tools = createExactJsonTools();
    const ordering = { '\ue000': 1, '😀': 2, '1': 3, '01': 4 };
    expect(tools.canonical(ordering)).toBe('{"01":4,"1":3,"":1,"😀":2}');
    expect(await tools.hash(ordering)).toBe(hash(ordering));
  });

  it.each([
    ['duplicate decoded keys', '{"schema":1,"\\u0073chema":2}', /duplicate/],
    ['unsafe JSON integer', '{"index":9007199254740993}', /safe browser range/],
    ['decimal JSON number', '{"index":0.5}', /integers/],
    ['unpaired surrogate', '{"name":"\\ud800"}', /surrogate/],
    ['trailing content', '{} {}', /trailing/],
    ['deep JSON', '['.repeat(130) + '0' + ']'.repeat(130), /nesting/],
  ])('shares packet strict JSON rejection for %s', async (_label, text, pattern) => {
    await expect(parseRawSourceText(text as string)).rejects.toThrow(pattern as RegExp);
    await expect(parseRawSourceText(text as string)).rejects.toBeInstanceOf(PacketError);
  });

  it('rejects oversized raw text and bounded natural/text metadata before import completes', async () => {
    await expect(parseRawSourceText(' '.repeat(16 * 1024 * 1024 + 1))).rejects.toThrow(/byte limit/);
    const digits = frame(); digits.sourceTerm = ['bvar', nat('1'.repeat(10001))];
    await expect(parseRawSourceText(JSON.stringify(digits))).rejects.toMatchObject({ code: 'limit' });
    const text = frame(); text.originalDeclarations = [local(metadataValue('x'.repeat(2 * 1024 * 1024)))];
    await expect(parseRawSourceText(JSON.stringify(text))).rejects.toMatchObject({ code: 'limit' });
  });

  it.each([
    ['schema', 'definograph.raw-frame.v2'], ['naturalProfile', 1], ['extra', true],
  ] as [string, JsonValue][])('rejects unrecognized frame field/profile %s', async (key, value) => {
    const changed = frame(); changed[key] = value;
    await expect(parseRawSourceText(JSON.stringify(changed))).rejects.toBeInstanceOf(RawImportError);
  });

  it('rejects mixed natural forms and malformed or unknown raw constructor subtrees', async () => {
    for (const value of [['bvar', 0], ['lit', ['natVal', ['nat', '01']]], ['mdata', ['mdataEntries', [[name('key'), ['ofFuture', true]]]], prop],
      ['mdata', ['mdataEntries', [[name('key'), ['ofNat', ['nat', '2'], 'extra']]]], prop]] as JsonValue[]) {
      const changed = frame(); changed.originalDeclarations = [local(value)];
      await expect(parseRawSourceText(JSON.stringify(changed))).rejects.toBeInstanceOf(RawImportError);
    }
  });

  it('keeps independent readback sensitive to port tampering and imported values immutable', async () => {
    const imported = await parseRawSourceText(JSON.stringify(frame()));
    const changed = structuredClone(imported.drawing);
    const entry = changed.nodes.find(node => node.family === 'metadataEntry')!;
    entry.children[0].role = 'other';
    expect(readRawInspection(changed)).toMatchObject({ ok: false, error: { code: 'malformed' } });
    expect(readRawInspection(imported.drawing)).toMatchObject({ ok: true });
  });
});

describe('explicit raw source bindings inside packets', () => {
  it('accepts binding schema 3 under packet schema 2 while preserving unknown and refused reports', async () => {
    const imported = await parsePacket(packetText(binding()));
    expect(imported.value.schema).toBe(2);
    expect(imported.payload.results.map(result => result.report.formation.tag)).toEqual(['unknown', 'refused']);
    expect(imported.payload.results.every(result => result.candidate === null)).toBe(true);
    expect(imported.payload.joint).toEqual({ formation: 'notChecked', evidence: 'notConstructed' });
    expect(Object.keys(imported).sort()).toEqual(['identity', 'payload', 'sourceText', 'value']);
  });

  it.each([
    ['naturalProfile', 1], ['rawProfile', 'definograph.raw.v2'], ['schema', 4], ['schema', 2],
  ] as [string, JsonValue][])('rejects mismatched or reinterpreted binding %s even with repaired hashes', async (key, value) => {
    const changed = binding(); changed[key] = value;
    await expect(parsePacket(packetText(changed))).rejects.toBeInstanceOf(PacketError);
  });

  it('requires both explicit raw profile fields and the v2 packet natural profile', () => {
    for (const key of ['naturalProfile', 'rawProfile']) {
      const changed = binding(); delete changed[key];
      expect(() => validatePacketNaturalRoles({ sourceBinding: changed }, 2)).toThrow(PacketError);
    }
    expect(() => validatePacketNaturalRoles({ sourceBinding: binding() }, 1)).toThrow(PacketError);
    for (const profile of [1, 2] as const) {
      expect(() => validatePacketNaturalRoles({ sourceBinding: { schema: profile } }, profile)).not.toThrow();
      expect(() => validatePacketNaturalRoles({ sourceBinding: { schema: profile, naturalProfile: 2 } }, profile)).toThrow(PacketError);
    }
  });

  it('validates every retained raw metadata subtree and reports the exact original value path', async () => {
    const changed = binding();
    const declarations = (changed.context as JsonObject).originalDeclarations as JsonObject[];
    declarations.push(local(['mdata', ['mdataEntries', [[name('key'), ['ofNat', ['nat', '01']]]]], prop]));
    await expect(parsePacket(packetText(changed))).rejects.toMatchObject({ code: 'malformed',
      path: ['payload', 'context', 'sourceBinding', 'context', 'originalDeclarations', 1, 'value', 1, 1, 0, 1, 1] });
  });

  it('rejects missing ignored local values rather than treating them as absent metadata', async () => {
    const changed = binding();
    delete ((changed.context as JsonObject).originalDeclarations as JsonObject[])[0].value;
    await expect(parsePacket(packetText(changed))).rejects.toMatchObject({ code: 'malformed',
      path: ['payload', 'context', 'sourceBinding', 'context', 'originalDeclarations', 0, 'value'] });
  });

  it('charges raw metadata budgets across distinct opaque local values in the same binding', async () => {
    const changed = binding();
    (changed.context as JsonObject).originalDeclarations = [local(metadataValue('x'.repeat(1100000))), local(metadataValue('y'.repeat(1100000)))];
    await expect(parsePacket(packetText(changed))).rejects.toMatchObject({ code: 'limit' });
  });

  it('keeps ordinary semantic positions on their existing v2 validation path', () => {
    for (const key of ['sourceTerm', 'sourceType', 'positionalTerm', 'positionalType']) {
      const changed = binding(); changed[key] = ['bvar', 0];
      expect(() => validatePacketNaturalRoles({ sourceBinding: changed }, 2)).toThrow(/canonical decimal|tag|natural/i);
    }
    const changed = binding(); const declaration = ((changed.context as JsonObject).originalDeclarations as JsonObject[])[0];
    declaration.type = ['lit', ['natVal', 1]];
    expect(() => validatePacketNaturalRoles({ sourceBinding: changed }, 2)).toThrow(PacketError);
    // Unknown annotations are still opaque, and are never reinterpreted as raw data.
    expect(() => validatePacketNaturalRoles({ sourceBinding: binding(), annotation: { rawProfile: 'other', value: ['bvar', 0] } }, 2)).not.toThrow();
  });
});

// Generated by the configured producer, retained externally so public tests do
// not embed machine paths, source provenance, or private source captures.
const rawFramesFile = process.env.DEFINOGRAPH_RAW_SOURCE_FRAMES;
const actualFrames = rawFramesFile ? JSON.parse(readFileSync(rawFramesFile, 'utf8')) as { label: string; frame: JsonValue }[] : [];
describe.skipIf(!rawFramesFile)('actual raw source frame imports', () => {
  it.each(actualFrames)('imports $label with exact producer data and independent identity', async ({ frame: value }) => {
    const sourceText = JSON.stringify(value);
    const imported = await parseRawSourceText(sourceText);
    expect(imported.identity).toBe(hash(value));
    expect(imported.sourceText).toBe(sourceText);
    expect(imported.value).toEqual(value);
    expect(readRawInspection(imported.drawing)).toEqual({ ok: true, value: { family: 'frame', value } });
  });
});

const rawBindingsFile = process.env.DEFINOGRAPH_RAW_SOURCE_BINDINGS;
const actualBindings = rawBindingsFile ? JSON.parse(readFileSync(rawBindingsFile, 'utf8')) as {
  label: string; binding: JsonObject; checks: JsonValue[]; audits: JsonValue[]; outcome: JsonObject; environmentSnapshotCount: number;
}[] : [];
describe.skipIf(!rawBindingsFile)('actual retained-metadata source bindings', () => {
  it.each(actualBindings)('validates $label without changing source or receipts', record => {
    const before = canonical(record);
    validatePacketNaturalRoles({ sourceCapture: record }, 2);
    expect(canonical(record)).toBe(before);
    expect(record.binding.schema === 2 || record.binding.schema === 3).toBe(true);
    if (record.binding.schema === 3) {
      expect(record.binding.naturalProfile).toBe(2);
      expect(record.binding.rawProfile).toBe('definograph.raw.v1');
    }
  });

  it('includes successful and failed actions with retained exact receipts', () => {
    expect(actualBindings.filter(record => record.binding.schema === 3).length).toBeGreaterThanOrEqual(3);
    expect(actualBindings.some(record => record.binding.schema === 2)).toBe(true);
    expect(actualBindings.some(record => record.outcome.kind === 'completed' && record.checks.length > 0)).toBe(true);
    expect(actualBindings.some(record => record.outcome.kind === 'actionError' && record.checks.length > 0)).toBe(true);
  });

  it('retains different ignored values even when the source projection and actual checks agree', () => {
    const [first, second] = actualBindings.filter(record => record.binding.schema === 3 && record.outcome.kind === 'completed');
    expect(first).toBeDefined(); expect(second).toBeDefined();
    expect(first.checks).toEqual(second.checks);
    expect(first.audits).toEqual(second.audits);
    expect(first.binding.sourceTerm).toEqual(second.binding.sourceTerm);
    expect((first.binding.context as JsonObject).telescope).toEqual((second.binding.context as JsonObject).telescope);
    expect((first.binding.context as JsonObject).originalDeclarations).not.toEqual((second.binding.context as JsonObject).originalDeclarations);
    expect(hash(first.binding)).not.toBe(hash(second.binding));
  });
});
