import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import { parsePacket, PacketError, validatePacketNaturalRoles, type JsonObject, type JsonValue, type PacketEnvelope } from './packet';

// Independent test oracle: UTF-8 byte ordering equals scalar-value ordering.
// In particular, this avoids both JS object enumeration and UTF-16 key sorting.
function canonical(value: JsonValue): string {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
  const keys = Object.keys(value).sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  return `{${keys.map(key => `${JSON.stringify(key)}:${canonical(value[key])}`).join(',')}}`;
}
function digest(value: JsonValue): string { return createHash('sha256').update(canonical(value)).digest('hex'); }
function clone<T>(value: T): T { return structuredClone(value); }
function sign(envelope: PacketEnvelope): string {
  const { digest: _digest, ...unsigned } = envelope;
  envelope.digest = digest(unsigned);
  return canonical(envelope);
}
// Reference binding construction is only for synthetic mutation controls.
// Fixed Python-produced identities below and the optional real exports check
// that the importer and this helper cannot agree on a different wire contract.
function bind(envelope: PacketEnvelope): string {
  const { payload, request, basis } = envelope;
  const basisId = digest({ request, basis });
  const environments = [digest({ basis: basisId, initial: basis.env0 })];
  const checks = payload.checks.map(check => {
    if (check.outcome.tag === 'accepted') environments.push(digest({ parent: environments.at(-1)!, declaration: check.declaration }));
    return { id: check.id, receipt: digest(check), environmentBefore: environments[check.envBefore] ?? '', environmentAfter: environments[check.envAfter] ?? '' };
  });
  envelope.bindings = {
    payload: digest(payload),
    results: payload.results.map((result, index) => ({
      pair: result.id,
      subject: digest({ basis: basisId, bank: digest(payload.bank), context: digest(payload.context), inputs: digest(payload.inputs[index]), candidate: digest(result.candidate) }),
      report: digest(result.report),
      records: { derived: digest(result.records.derived), retained: digest(result.records.retained) },
    })),
    checks, environments,
    uses: payload.uses.map(use => ({
      id: [payload.attempt, use.pair, use.role, digest(payload.results.find(result => result.id === use.pair)!.records[use.role]), use.oid, use.path],
      entry: digest(use),
    })),
    audits: payload.audits.map(audit => ({ audit: digest(audit), subject: digest(audit.subject), environment: environments[audit.environment as number] ?? '' })),
  };
  return sign(envelope);
}

function fixture(): PacketEnvelope {
  const member = {
    entry: { use: { oid: 'u0', source: ['future-expression', 1] }, path: ['body'] },
    sourceLevels: { tag: 'available', values: [['succ', ['zero']]] },
    viewLevels: { tag: 'notApplicable' },
  };
  const inputs = ['operation-a', 'operation-b'].map(id => ({ id, F: { source: id }, G: { target: id } }));
  const checks = [
    { id: 0, pair: 'operation-a', label: 'reading', subject: { target: 'laws.reading', pair: 'operation-a' }, declaration: { name: ['str', ['anonymous'], 'first'], value: ['bvar', 0] }, envBefore: 0, envAfter: 1, outcome: { tag: 'accepted' }, heartbeatBound: 10 },
    { id: 1, pair: 'operation-a', label: 'reading', subject: { target: 'law.reading', pair: 'operation-a' }, declaration: { name: ['str', ['anonymous'], 'second'], value: ['future-expression', null] }, envBefore: 1, envAfter: 1, outcome: { tag: 'unknown', reason: 'budget' }, heartbeatBound: 20 },
    { id: 2, pair: 'operation-b', label: 'reading', subject: { target: 'laws.reading', pair: 'operation-b' }, declaration: { name: ['str', ['anonymous'], 'third'], value: ['lit', ['natVal', 2]] }, envBefore: 1, envAfter: 2, outcome: { tag: 'accepted' }, heartbeatBound: 30 },
  ];
  const results = inputs.map((input, index) => ({
    id: input.id, candidate: { expression: ['future-expression', index] },
    records: { retained: { uses: [clone(member)], annotation: `retained-${index}` }, derived: { uses: [clone(member)], annotation: `derived-${index}` } },
    report: { formation: { tag: 'formed' }, evidence: { tag: index === 0 ? 'unknown' : 'certified' }, checks: checks.filter(check => check.pair === input.id).map(check => [check.label, check.outcome]) },
  }));
  return {
    schema: 1,
    request: { id: 'synthetic-attempt', documentRevision: 'revision', sourceSnapshot: 'snapshot' },
    basis: { workerEpoch: 'epoch', env0: 'initial', depsDigest: 'dependencies', workerDigest: 'worker', fixedUniverseInstance: [], policies: { resources: { kernelHeartbeatBounds: checks.map(check => ({ checkId: check.id, bound: check.heartbeatBound })) } } },
    payload: {
      schema: 1, attempt: 'synthetic-attempt', mode: 'unfamiliar-mode', bank: { exactEvidence: null }, context: {}, inputs, results, checks,
      uses: results.flatMap(result => (['retained', 'derived'] as const).map(role => ({ ...clone(member), pair: result.id, role, oid: 'u0', path: ['body'] }))),
      audits: [
        { subject: checks[0].declaration, checkId: 0, category: 'declaration', environment: 1, result: { tag: 'available', axioms: [] } },
        { subject: checks[1].declaration, checkId: 1, category: 'declaration', environment: 1, result: { tag: 'unavailable', reason: 'not installed' } },
        { subject: checks[2].declaration, checkId: 2, category: 'declaration', environment: 2, result: { tag: 'available', axioms: [] } },
        { subject: { name: 'source' }, category: 'source', environment: 0, result: { tag: 'available', axioms: [['anonymous']] } },
      ],
      coherence: { value: true, inputs, bankExact: false, admissions: [true, true] },
      joint: { formation: 'notChecked', evidence: 'notConstructed' },
    },
    bindings: {}, digest: '',
  } as PacketEnvelope;
}

function setUseIds(value: PacketEnvelope, oid: JsonValue): void {
  for (const result of value.payload.results) for (const role of ['retained', 'derived'] as const)
    for (const member of result.records[role]!.uses) (member.entry.use as JsonObject).oid = clone(oid);
  for (const use of value.payload.uses) { use.oid = clone(oid); (use.entry.use as JsonObject).oid = clone(oid); }
}
function fixtureV2(): PacketEnvelope {
  const value = fixture(); value.schema = 2; value.payload.schema = 2;
  setUseIds(value, ['nat', '0']);
  value.payload.checks.forEach(check => { check.heartbeatBound = ['nat', String(check.heartbeatBound)]; });
  value.payload.checks[0].declaration.value = ['bvar', ['nat', '0']];
  value.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '2']]];
  ((value.basis.policies as JsonObject).resources as JsonObject).kernelHeartbeatBounds = value.payload.checks.map(check => ({ checkId: check.id, bound: check.heartbeatBound }));
  return value;
}

describe('packet import consistency', () => {
  it('matches Python canonical identity, retains exact source, and freezes the complete accepted packet', async () => {
    const value = fixture(), source = bind(value), imported = await parsePacket(source);
    // definograph.codec/client Python canonicalization and bind_payload oracle.
    expect(imported.identity).toBe('c57b670de838bd90fa5ada4611f8e050c1566a34cf4e33cfaf0b03d8276324e0');
    expect(imported.identity).toBe(digest(value));
    expect(imported.sourceText).toBe(source);
    expect(imported.payload).toBe(imported.value.payload);
    expect(imported.payload.mode).toBe('unfamiliar-mode');
    expect(imported.payload.checks[1].declaration.value).toEqual(['future-expression', null]);
    expect(Object.isFrozen(imported)).toBe(true);
    expect(Object.isFrozen(imported.payload.checks[0].declaration.value)).toBe(true);
    expect(() => { imported.payload.checks[0].envAfter = 9; }).toThrow(TypeError);
    const pretty = JSON.stringify(value, null, 2);
    expect((await parsePacket(pretty)).identity).toBe(imported.identity);
    expect((await parsePacket(pretty)).sourceText).toBe(pretty);
    expect(Object.keys(imported).sort()).toEqual(['identity', 'payload', 'sourceText', 'value']);
  });

  it('uses Unicode scalar ordering and exact UTF-8 escaping, including integer-looking and prototype keys', async () => {
    const value = fixture();
    value.payload.bank.metadata = JSON.parse('{"2":"two","10":"ten","\\ue000":"BMP","\\ud800\\udc00":"astral","__proto__":{"constructor":"ordinary data"},"text":"quotes \\\" slash \\\\ newline\\n\\t and \\u2028\\u2029","low":"\\u0000\\b\\f\\r"}') as JsonObject;
    const source = bind(value), imported = await parsePacket(source);
    expect(imported.identity).toBe('223e163e1cb46da8ebe14dbfd37fa370faea337f5a3e38f047cbab06702c7ce7');
    expect(imported.identity).toBe(digest(value));
    expect((imported.payload.bank.metadata as JsonObject).__proto__).toEqual({ constructor: 'ordinary data' });
    expect(Object.getPrototypeOf(imported.payload.bank.metadata)).toBeNull();
    expect(({} as Record<string, unknown>).constructor).toBe(Object);
  });

  it('keeps producer and certification statements as unverified imported data', async () => {
    const value = fixture();
    value.basis.workerEpoch = 'trustedCurrent';
    value.payload.producerProvenance = 'trustedCurrent';
    value.payload.currentlyCertified = true;
    const imported = await parsePacket(bind(value));
    expect(imported.payload.results[1].report.evidence.tag).toBe('certified');
    expect(imported).not.toHaveProperty('currentlyCertified');
    expect(imported).not.toHaveProperty('producerProvenance');
    expect(imported).not.toHaveProperty('jointlyCertified');
  });

  it.each(['1.0', '1e0', '1E+0', '9007199254740993', '-9007199254740993', 'NaN', 'Infinity', '01'])('rejects lossy or noninteger JSON number %s before semantic use', async token => {
    await expect(parsePacket(`{"schema":${token}}`)).rejects.toBeInstanceOf(PacketError);
  });

  it('preserves safe integer boundaries and Python integer negative-zero normalization', async () => {
    const value = fixture();
    value.payload.bank.integers = [Number.MIN_SAFE_INTEGER, Number.MAX_SAFE_INTEGER, 0];
    const source = bind(value), imported = await parsePacket(source);
    expect(imported.payload.bank.integers).toEqual([-9007199254740991, 9007199254740991, 0]);
    const negativeZero = source.replace('"envBefore":0', '"envBefore":-0');
    expect(negativeZero).not.toBe(source);
    expect((await parsePacket(negativeZero)).identity).toBe(imported.identity);
  });

  it.each(['{"schema":1,"schema":1}', '{"schema":1,"\\u0073chema":1}', '{"nested":{"x":1,"x":1}}'])('rejects duplicate decoded keys: %s', async source => {
    await expect(parsePacket(source)).rejects.toThrow('duplicate JSON object key');
  });

  it.each(['"\\ud800"', '"\\udc00"', '"\\ud800x"', '"\ud800"', '"\udc00"', '{"\\ud800":1}'])('rejects unpaired Unicode surrogates: %s', async source => {
    await expect(parsePacket(source)).rejects.toThrow('unpaired Unicode surrogate');
  });

  it.each(['{"a":1,}', '[1,]', 'true false', '"bad\nstring"', '"\\q"', '{"a" 1}', '\ufeff{}'])('rejects malformed JSON: %s', async source => {
    await expect(parsePacket(source)).rejects.toBeInstanceOf(PacketError);
  });

  it('declines browser resource boundaries explicitly', async () => {
    await expect(parsePacket(' '.repeat(16 * 1024 * 1024 + 1))).rejects.toThrow('byte limit');
    await expect(parsePacket('['.repeat(130) + 'null' + ']'.repeat(130))).rejects.toThrow('nesting');
    await expect(parsePacket('[' + '0,'.repeat(500_000) + '0]')).rejects.toThrow('node count');
  });

  it('distinguishes the whole packet identity from its unsigned envelope digest', async () => {
    const value = fixture();
    const imported = await parsePacket(bind(value));
    expect(imported.identity).not.toBe(value.digest);
    value.payload.bank.changed = true;
    await expect(parsePacket(canonical(value))).rejects.toThrow('packet digest');
    await expect(parsePacket(sign(value))).rejects.toThrow('attachment bindings');
  });

  it.each(['payload', 'results', 'checks', 'environments', 'uses', 'audits'])('checks the %s attachment even when the envelope digest was recomputed', async field => {
    const value = fixture(); bind(value);
    value.bindings[field] = field === 'payload' ? '0'.repeat(64) : [];
    await expect(parsePacket(sign(value))).rejects.toThrow('attachment bindings');
  });

  it.each([
    ['candidate', (v: PacketEnvelope) => { v.payload.results[0].candidate = null; }, 'formed result requires'],
    ['report order', (v: PacketEnvelope) => { v.payload.results[0].report.checks.reverse(); }, 'report checks differ'],
    ['environment', (v: PacketEnvelope) => { v.payload.checks[1].envAfter = 2; }, 'only accepted declarations'],
    ['boolean revision', (v: PacketEnvelope) => { (v.payload.checks[0] as JsonObject).envBefore = false; }, 'safe natural number'],
    ['audit subject', (v: PacketEnvelope) => { v.payload.audits[0].subject = { name: 'other' }; }, 'audit subject differs'],
    ['audit installation', (v: PacketEnvelope) => { v.payload.audits[0].environment = 0; }, 'follow declaration installation'],
    ['unknown audit', (v: PacketEnvelope) => { v.payload.audits[1].result = { tag: 'available', axioms: [] }; }, 'follow declaration installation'],
    ['unavailable audit', (v: PacketEnvelope) => { v.payload.audits[1].result = { tag: 'unavailable', reason: 'missing', axioms: [] }; }, 'not an empty axiom list'],
    ['duplicate use', (v: PacketEnvelope) => { v.payload.uses.push(clone(v.payload.uses[0])); }, 'duplicate qualified use'],
    ['use levels', (v: PacketEnvelope) => { v.payload.uses[0].sourceLevels.values = [['zero']]; }, 'not an exact record member'],
    ['use local id', (v: PacketEnvelope) => { v.payload.uses[0].oid = 'other'; }, 'local id differs'],
    ['use path', (v: PacketEnvelope) => { v.payload.uses[0].path = ['other']; }, 'path differs'],
    ['joint claim', (v: PacketEnvelope) => { (v.payload.joint as JsonObject).evidence = 'certified'; }, 'cannot claim joint'],
    ['request association', (v: PacketEnvelope) => { v.request.id = 'other'; }, 'another request'],
    ['heartbeat policy', (v: PacketEnvelope) => { ((v.basis.policies as JsonObject).resources as JsonObject).kernelHeartbeatBounds = []; }, 'resource policy differs'],
  ] as const)('rejects inconsistent %s despite fully recomputed hashes', async (_name, mutate, message) => {
    const value = fixture(); mutate(value);
    await expect(parsePacket(bind(value))).rejects.toThrow(message);
  });

  it('qualifies repeated local use IDs by their operation and record role', async () => {
    const imported = await parsePacket(bind(fixture()));
    const bindings = imported.value.bindings.uses as JsonObject[];
    expect(new Set(bindings.map(item => canonical(item.id))).size).toBe(4);
    expect(new Set(imported.payload.uses.map(use => use.oid)).size).toBe(1);
    const environments = imported.value.bindings.environments as string[];
    const checks = imported.value.bindings.checks as JsonObject[];
    expect(checks.map(check => check.environmentBefore)).toEqual([environments[0], environments[1], environments[1]]);
    expect(checks.map(check => check.environmentAfter)).toEqual([environments[1], environments[1], environments[2]]);
  });
});

describe('v2 packet natural roles', () => {
  it('accepts matched profiles and keeps large adjacent semantic values byte-distinct through every binding', async () => {
    const first = fixtureV2(), second = fixtureV2();
    first.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '9007199254740992']]];
    second.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '9007199254740993']]];
    const a = await parsePacket(bind(first)), b = await parsePacket(bind(second));
    expect(a.value.schema).toBe(2); expect(a.payload.schema).toBe(2);
    expect(a.identity).toBe(digest(first)); expect(b.identity).toBe(digest(second));
    expect(a.identity).not.toBe(b.identity);
    expect(a.value.bindings.payload).not.toBe(b.value.bindings.payload);
    expect((a.value.bindings.checks as JsonObject[])[2].receipt).not.toBe((b.value.bindings.checks as JsonObject[])[2].receipt);
    expect(a.payload.checks[2].declaration.value).toEqual(['lit', ['natVal', ['nat', '9007199254740992']]]);
    expect(b.payload.checks[2].declaration.value).toEqual(['lit', ['natVal', ['nat', '9007199254740993']]]);
    expect(a.payload.checks.map(check => check.id)).toEqual([0, 1, 2]);
    expect(a.payload.checks[0].heartbeatBound).toEqual(['nat', '10']);
    expect(a).not.toHaveProperty('currentlyCertified');
  });

  it('validates exact natural roles in names, universes, projections, DAG rows and source metadata', async () => {
    const value = fixtureV2(), huge = ['nat', '18446744073709551617'];
    value.payload.checks[0].declaration.name = ['num', ['anonymous'], huge];
    value.payload.checks[0].declaration.value = ['proj', ['num', ['anonymous'], huge], huge, ['bvar', ['nat', '0']]];
    value.basis.fixedUniverseInstance = [['param', ['num', ['anonymous'], huge]]];
    value.payload.bank.table = { homes: [1], rows: [{ home: 1, row: ['proj', ['anonymous'], huge, ['var', 0]] }] };
    value.payload.sourceBinding = { schema: 2, sourceKind: 'namedExtraction', sourceSteps: [['uniqueArg', huge], ['instActual', huge]], context: { arity: 1, originalDeclarations: [
      { constructor: 'cdecl', index: huge, fvarId: ['num', ['anonymous'], huge], userName: ['str', ['anonymous'], 'local'], type: ['sort', ['zero']], binderInfo: 'default', kind: 'default' },
    ] } };
    setUseIds(value, huge);
    const imported = await parsePacket(bind(value));
    expect(imported.payload.uses[0].oid).toEqual(huge);
    expect(imported.value.basis.fixedUniverseInstance).toEqual(value.basis.fixedUniverseInstance);
    expect(imported.identity).toBe(digest(value));
  });

  it.each([
    ['number in raw bvar', (v: PacketEnvelope) => { v.payload.checks[0].declaration.value = ['bvar', 0]; }],
    ['noncanonical literal', (v: PacketEnvelope) => { v.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '02']]]; }],
    ['numeric Name component', (v: PacketEnvelope) => { v.payload.checks[0].declaration.name = ['num', ['anonymous'], 3]; }],
    ['numeric universe parameter name', (v: PacketEnvelope) => { v.basis.fixedUniverseInstance = [['param', ['num', ['anonymous'], 3]]]; }],
    ['numeric raw projection', (v: PacketEnvelope) => { v.payload.checks[0].declaration.value = ['proj', ['anonymous'], 0, ['sort', ['zero']]]; }],
    ['numeric DAG projection', (v: PacketEnvelope) => { v.payload.bank.table = { homes: [0], rows: [{ home: 0, row: ['proj', ['anonymous'], 0, ['use', 0, 0, ['nil']]] }] }; }],
    ['numeric local use', (v: PacketEnvelope) => { setUseIds(v, 0); }],
    ['numeric LocalDecl index', (v: PacketEnvelope) => { v.payload.sourceBinding = { schema: 2, context: { originalDeclarations: [{ constructor: 'ldecl', index: 0 }] } }; }],
    ['numeric selected source step', (v: PacketEnvelope) => { v.payload.sourceBinding = { schema: 2, sourceSteps: [['uniqueArg', 0]] }; }],
    ['malformed selected source step', (v: PacketEnvelope) => { v.payload.sourceBinding = { schema: 2, path: [['instActual', ['nat', '+1']]] }; }],
    ['numeric heartbeat', (v: PacketEnvelope) => { v.payload.checks[0].heartbeatBound = 10; }],
    ['missing heartbeat', (v: PacketEnvelope) => { delete v.payload.checks[0].heartbeatBound; }],
    ['missing hole oid', (v: PacketEnvelope) => { v.payload.results[0].records.retained!.body = ['hole', { src: ['var', 0], view: ['var', 0] }]; }],
  ] as const)('rejects %s after every hash has been repaired', async (_label, mutate) => {
    const value = fixtureV2(); mutate(value);
    await expect(parsePacket(bind(value))).rejects.toThrow('v2 natural');
  });

  it.each([
    ['Fin variable', ['var', ['nat', '0']]],
    ['reference offset', ['use', ['nat', '0'], 0, ['nil']]],
    ['reference home', ['use', 0, ['nat', '0'], ['nil']]],
    ['instantiation count', ['inst', ['nat', '0'], ['var', 0], ['nil']]],
    ['certificate count', ['classB', ['anonymous'], ['nat', '0'], ['nil']]],
    ['scope depth', ['pi', ['nat', '0'], { name: ['anonymous'], info: 'default' }, ['var', 0]]],
  ] as [string, JsonValue][])('keeps the operational %s as a safe JSON number', async (_label, syntax) => {
    const value = fixtureV2(); value.payload.results[0].records.retained!.body = clone(syntax);
    await expect(parsePacket(bind(value))).rejects.toThrow('safe natural number');
  });

  it('requires matched versions, safe operational table positions and finite UInt32 hints', async () => {
    const mismatched = fixtureV2(); mismatched.payload.schema = 1;
    await expect(parsePacket(bind(mismatched))).rejects.toThrow('schemas must match');
    const binding = fixtureV2(); binding.payload.sourceBinding = { schema: 1 };
    await expect(parsePacket(bind(binding))).rejects.toThrow('source binding schema must match');
    const table = fixtureV2(); table.payload.bank.table = { homes: [['nat', '0']], rows: [] };
    await expect(parsePacket(bind(table))).rejects.toThrow('safe natural number');
    const hint = fixtureV2(); hint.payload.checks[0].declaration.hints = ['regular', 4294967296];
    await expect(parsePacket(bind(hint))).rejects.toThrow('UInt32');
    hint.payload.checks[0].declaration.hints = ['regular', 4294967295];
    await expect(parsePacket(bind(hint))).resolves.toHaveProperty('value.schema', 2);
  });

  it('requires positive v2 heartbeat bounds while preserving the legacy receipt boundary', async () => {
    const receipt = fixtureV2(); receipt.payload.checks[0].heartbeatBound = ['nat', '0'];
    await expect(parsePacket(bind(receipt))).rejects.toThrow('heartbeatBound must be positive');
    const policy = fixtureV2();
    const bounds = ((policy.basis.policies as JsonObject).resources as JsonObject).kernelHeartbeatBounds as JsonObject[];
    bounds[0].bound = ['nat', '0'];
    await expect(parsePacket(bind(policy))).rejects.toThrow('bound must be positive');
    const legacy = fixture(); legacy.payload.checks[0].heartbeatBound = 0;
    (((legacy.basis.policies as JsonObject).resources as JsonObject).kernelHeartbeatBounds as JsonObject[])[0].bound = 0;
    await expect(parsePacket(bind(legacy))).resolves.toHaveProperty('value.schema', 1);
  });

  it('does not reinterpret opaque annotations, unknown constructors or string literal contents', async () => {
    const value = fixtureV2();
    const opaque = [['num', ['anonymous'], 7], ['natVal', 7], ['nat', '01'], ['bvar', 7]];
    value.payload.bank.annotation = clone(opaque);
    value.basis.annotation = clone(opaque);
    value.payload.checks[0].declaration.value = ['future-expression', clone(opaque)];
    value.payload.checks[2].declaration.value = ['lit', ['strVal', '["num",["anonymous"],7]']];
    const imported = await parsePacket(bind(value));
    expect(imported.payload.bank.annotation).toEqual(opaque);
    expect(imported.identity).toBe(digest(value));
  });

  it('rejects v2 natural tags at known v1 roles while preserving opaque v1 data', async () => {
    const value = fixture(); value.payload.checks[0].declaration.value = ['bvar', ['nat', '0']];
    await expect(parsePacket(bind(value))).rejects.toThrow('v1 natural');
    const opaque = fixture(); opaque.payload.bank.annotation = ['bvar', ['nat', '0']];
    await expect(parsePacket(bind(opaque))).resolves.toHaveProperty('value.schema', 1);
  });

  it('enforces the decimal budget in packet roles without accepting unsafe JSON number tokens', async () => {
    const value = fixtureV2(); value.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '9'.repeat(10_000)]]];
    await expect(parsePacket(bind(value))).resolves.toHaveProperty('value.schema', 2);
    value.payload.checks[2].declaration.value = ['lit', ['natVal', ['nat', '9'.repeat(10_001)]]];
    await expect(parsePacket(bind(value))).rejects.toThrow('10000-digit');
    await expect(parsePacket('{"schema":2,"unsafe":9007199254740993}')).rejects.toThrow('safe browser range');
  });

  it('uses the same contextual natural rules on source-capture bindings', () => {
    expect(() => validatePacketNaturalRoles({ binding: { schema: 2, sourceTerm: ['bvar', 0] } }, 2)).toThrow('v2 natural');
    expect(() => validatePacketNaturalRoles({ binding: { schema: 2, sourceTerm: ['bvar', ['nat', '0']], annotation: ['bvar', 0] } }, 2)).not.toThrow();
  });
});

// Optional integration evidence remains external to the public repository.
// Set DEFINOGRAPH_PACKET_FIXTURES to a directory with worker-packets/ and
// import-controls/. Absence is reported as skipped, never as verified.
const fixtureRoot = process.env.DEFINOGRAPH_PACKET_FIXTURES;
describe.skipIf(!fixtureRoot)('external real packet exports and independent controls', () => {
  const read = (folder: string, name: string): string => readFileSync(join(fixtureRoot!, folder, name), 'utf8');
  it.each([
    ['certified-route-universe', ['formed', 'formed'], ['certified', 'certified'], true, 10],
    ['let-context', ['formed', 'formed'], ['certified', 'certified'], true, 10],
    ['missing', ['formed', 'formed'], ['missing', 'certified'], true, 10],
    ['incoherent', ['formed', 'formed'], ['certified', 'certified'], false, 10],
    ['refused', ['refused', 'formed'], ['notFormed', 'certified'], true, 5],
    ['timeout', ['unknown', 'unknown'], ['notFormed', 'notFormed'], true, 10],
  ])('preserves %s outcomes, source, identities and all attachment bindings', async (name, formations, evidence, coherent, useCount) => {
    const source = read('worker-packets', `${name}.packet.json`), imported = await parsePacket(source);
    expect(imported.payload.results.map(result => result.report.formation.tag)).toEqual(formations);
    expect(imported.payload.results.map(result => result.report.evidence.tag)).toEqual(evidence);
    expect(imported.payload.coherence.value).toBe(coherent);
    expect(imported.payload.uses).toHaveLength(useCount as number);
    expect(imported.identity).toBe(digest(JSON.parse(source) as JsonObject));
    expect(imported.sourceText).toBe(source);
    expect(imported).not.toHaveProperty('currentlyCertified');
    expect(imported).not.toHaveProperty('jointlyCertified');
    expect(imported.payload.joint).toEqual({ formation: 'notChecked', evidence: 'notConstructed' });
    if (name === 'refused') {
      expect(imported.payload.results[0].candidate).toBeNull();
      expect(imported.payload.results[0].records).toEqual({ retained: null, derived: null });
    }
    if (name === 'timeout') expect(imported.payload.results.every(result => result.candidate !== null)).toBe(true);
  });

  it.each(['ordinary-canonical', 'pretty-import', 'canonical-key-order', 'renamed-with-repeated-labels', 'rebound-producer-claim'])('accepts structurally consistent %s without promoting imported trust', async name => {
    const source = read('import-controls', `${name}.json`), imported = await parsePacket(source);
    expect(imported.identity).toBe(digest(JSON.parse(source) as JsonObject));
    expect(Object.keys(imported).sort()).toEqual(['identity', 'payload', 'sourceText', 'value']);
    if (name === 'pretty-import') expect(imported.identity).toBe((await parsePacket(read('import-controls', 'ordinary-canonical.json'))).identity);
  });

  it.each([
    ['unsafe-integer', 'safe browser range'], ['rehashed-stale-bindings', 'attachment bindings'],
    ['duplicate-key', 'duplicate JSON object key'], ['float-token', 'integers'],
  ])('declines %s for its exact failure reason', async (name, reason) => {
    await expect(parsePacket(read('import-controls', `${name}.json`))).rejects.toThrow(reason);
  });
});
