import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import type { JsonObject, JsonValue } from '../packets/packet';
import { readRawInspection } from '../packets/raw';
import { sourceSnapshotDrawings, SourceSnapshotError, validateSourceSnapshot } from './source-snapshot';

const anonymous: JsonValue = ['anonymous'];
const name = (part: string, parent: JsonValue = anonymous): JsonValue => ['str', parent, part];
const nat = (digits: string | number): JsonValue => ['nat', String(digits)];
const c = (part: string): JsonValue => ['const', name(part), []];
const b = (index: number): JsonValue => ['bvar', nat(index)];
const id = '550e8400-e29b-41d4-a716-446655440000';
const prefix = name(id, name('SourceSnapshot', name('StatementLens')));
const unavailable = (phase = 'source-capture', kind = 'unsupported'): JsonObject => ({ status: 'unavailable', kind, phase, reason: 'Retained diagnostic.' });
const frame = (term: JsonValue = c('True'), type: JsonValue = ['sort', ['zero']], originalDeclarations: JsonValue[] = []): JsonObject => ({
  schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations, sourceTerm: term, sourceType: type,
});
function snapshot(): JsonObject {
  return {
    schema: 'definograph.source-snapshot.v1',
    selection: { startByte: 2, endByte: 8, requestedStartByte: 3, requestedEndByte: 7, parentDeclaration: name('example') },
    policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: nat(200000), retainedMetadata: 'definograph.raw.v1' },
    expectedType: { status: 'absent' },
    original: { status: 'available', typeOrigin: 'inferred', frame: frame() },
    prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame: frame(), checkerUniverseParams: [] },
    checking: { ...unavailable(), attempted: true },
  };
}
const obj = (value: JsonValue): JsonObject => value as JsonObject;
const arr = (value: JsonValue): JsonValue[] => value as JsonValue[];
function captured(): JsonObject {
  const s = snapshot();
  const declarations: JsonValue[] = [
    { constructor: 'cdecl', index: nat(9), fvarId: name('a'), userName: name('x'), type: c('Nat'), binderInfo: 'implicit', kind: 'default' },
    { constructor: 'ldecl', index: nat(2), fvarId: name('l'), userName: name('x'), type: c('Nat'), value: ['fvar', name('a')], nondep: false, kind: 'auxDecl' },
    { constructor: 'ldecl', index: nat(2), fvarId: name('o'), userName: name('x'), type: c('Nat'),
      value: ['mdata', ['mdataEntries', [[name('key'), ['ofInt', ['negSucc', nat('9007199254740993')]]]]], ['sort', ['param', name('ignored')]]], nondep: true, kind: 'implDetail' },
  ];
  const f = frame(['fvar', name('o')], c('Nat'), declarations);
  obj(s.original).frame = structuredClone(f); obj(s.prepared).frame = f;
  const telescope: JsonValue = ['port', ['letE', ['port', ['nil'], { name: name('x'), info: 'implicit' }, c('Nat')],
    name('x'), false, c('Nat'), b(0)], { name: name('x'), info: 'default' }, c('Nat')];
  const binding: JsonObject = {
    schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt: id, operation: 'editor-source', sourceKind: 'namedComponent',
    declarationPrefix: prefix, universeParams: [], initialEnvironment: 0,
    context: { arity: 3, telescope, registry: [name('o'), name('l'), name('a')], registryOrder: 'mostRecentFirst',
      originalDeclarations: declarations, originalDeclarationOrder: 'oldestFirst' },
    sourceTerm: ['fvar', name('o')], sourceType: c('Nat'), positionalTerm: b(0), positionalType: c('Nat'),
  };
  const closed = (tag: string, body: JsonValue): JsonValue => [tag, name('x'), c('Nat'),
    ['letE', name('x'), c('Nat'), b(0), [tag, name('x'), c('Nat'), body, 'default'], false], 'implicit'];
  const checks: JsonValue[] = [], audits: JsonValue[] = [];
  for (const [i, label] of ['context', 'component'].entries()) {
    const declName = name(label, prefix);
    const declaration: JsonObject = {
      kind: i === 0 ? 'thmDecl' : 'defnDecl', name: declName, levelParams: [], all: [declName],
      type: closed('forallE', i === 0 ? c('True') : c('Nat')),
      value: closed('lam', i === 0 ? ['const', name('intro', name('True')), []] : b(0)),
      ...(i === 0 ? {} : { hints: ['abbrev'], safety: 'safe' }),
    };
    checks.push({ id: i, pair: 'editor-source', label, displayLabel: label, declaration,
      subject: { attempt: id, pair: 'editor-source', sequence: i, target: label, declaration },
      envBefore: i, envAfter: i + 1, heartbeatBound: nat(200000), outcome: { tag: 'accepted' } });
    audits.push({ checkId: i, category: 'declarationCheck', subject: declaration, environment: i + 1, result: { tag: 'available', axioms: [] } });
  }
  s.checking = { status: 'captured', action: { status: 'completed' }, binding, checks, audits, environmentSnapshotCount: 3 };
  return s;
}
function rejects(value: unknown, expression?: RegExp): void {
  expect(() => validateSourceSnapshot(value)).toThrow(SourceSnapshotError);
  if (expression) expect(() => validateSourceSnapshot(value)).toThrow(expression);
}

describe('immutable source snapshot structure', () => {
  it('validates independent original, prepared and expected-type raw drawings', () => {
    const s = snapshot(); s.expectedType = { status: 'available', expression: ['mvar', name('expectation')] };
    obj(s.original).frame = frame(['mdata', ['mdataEntries', []], ['mvar', name('term')]], ['mvar', name('type')]);
    const validated = validateSourceSnapshot(s), drawings = sourceSnapshotDrawings(validated);
    expect(drawings.original).toBeDefined(); expect(drawings.prepared).toBeDefined(); expect(drawings.expectedType).toBeDefined();
    expect(readRawInspection(drawings.original).ok).toBe(true);
    expect(sourceSnapshotDrawings(validated)).toBe(drawings);
    expect(Object.isFrozen(validated)).toBe(true); expect(Object.isFrozen(validated.selection)).toBe(true);
    expect(Object.isFrozen(drawings.original!.nodes[0].children)).toBe(true);
    obj(s.original).frame = frame(c('Changed'));
    expect(validated.original.status === 'available' && validated.original.frame.sourceTerm).not.toEqual(c('Changed'));
  });

  it('validates a complete two-receipt action with genuine lets and opaque retained metadata', () => {
    const s = validateSourceSnapshot(captured());
    expect(s.checking.status).toBe('captured');
    if (s.checking.status === 'captured') { expect(s.checking.checks).toHaveLength(2); expect(s.checking.environmentSnapshotCount).toBe(3); }
    expect(sourceSnapshotDrawings(s).prepared?.nodes.some(n => n.family === 'integer' && n.tag === 'negSucc')).toBe(true);
  });

  it.each(['unsupported', 'error', 'limit', 'prerequisite'])('preserves unavailable %s phases and attempted flag', kind => {
    const s = snapshot();
    s.expectedType = unavailable('expected-type', kind); s.original = unavailable('original-serialization', kind);
    s.prepared = unavailable('preparation', kind); s.checking = { ...unavailable('checking-prerequisite', kind), attempted: false };
    const v = validateSourceSnapshot(s);
    expect(v).toEqual(s); expect(sourceSnapshotDrawings(v)).toEqual({});
  });

  it('preserves a prepared frame when original serialization fails', () => {
    const s = snapshot(); s.original = unavailable('original-serialization', 'limit');
    const v = validateSourceSnapshot(s); expect(sourceSnapshotDrawings(v).prepared).toBeDefined();
  });

  it('blocks a prepared frame after an original inference failure', () => {
    const s = snapshot(); s.original = unavailable('original-inference', 'error');
    rejects(s, /inference failure blocks/);
    s.prepared = unavailable('preparation', 'prerequisite');
    s.checking = { ...unavailable('checking-prerequisite', 'prerequisite'), attempted: false };
    validateSourceSnapshot(s);
  });

  it('enforces the placeholder guard on captured semantic fields while retaining ignored values', () => {
    const semantic = captured();
    obj(obj(semantic.prepared).frame).sourceTerm = c('sorryAx');
    obj(obj(semantic.original).frame).sourceTerm = c('sorryAx');
    obj(obj(semantic.checking).binding).sourceTerm = c('sorryAx');
    rejects(semantic, /placeholder policy/);
    const opaque = captured();
    for (const section of ['original', 'prepared']) {
      obj(arr(obj(obj(opaque[section]).frame).originalDeclarations)[2]).value = c('sorryAx');
    }
    validateSourceSnapshot(opaque);
  });

  it('reconstructs owned binders independently of the external free-variable registry', () => {
    const s = captured(), input = obj(obj(s.prepared).frame), binding = obj(obj(s.checking).binding);
    const source: JsonValue = ['lam', name('owned'), c('Nat'),
      ['letE', name('inside'), c('Nat'), ['fvar', name('a')], b(1), true], 'default'];
    const positional: JsonValue = ['lam', name('owned'), c('Nat'),
      ['letE', name('inside'), c('Nat'), b(3), b(1), true], 'default'];
    const type: JsonValue = ['forallE', name('owned'), c('Nat'), c('Nat'), 'default'];
    input.sourceTerm = source; input.sourceType = type;
    obj(s.original).frame = structuredClone(input);
    binding.sourceTerm = source; binding.sourceType = type;
    binding.positionalTerm = positional; binding.positionalType = type;
    const declaration = obj(obj(arr(obj(s.checking).checks)[1]).declaration);
    // The fixture's original context closes three chronological declarations:
    // a parameter, a genuine let, and an opaque parameter.
    arr(arr(arr(declaration.value)[3])[4])[3] = positional;
    arr(arr(arr(declaration.type)[3])[4])[3] = type;
    validateSourceSnapshot(s);
    arr(arr(positional)[3])[3] = b(2);
    rejects(s, /association/);
  });

  it('rejects bare bound variables and unregistered identities even with external declarations', () => {
    for (const [source, message] of [[b(0), /out-of-scope bound/], [['fvar', name('missing')], /unregistered free/]] as [JsonValue, RegExp][]) {
      const s = captured();
      obj(obj(s.prepared).frame).sourceTerm = source;
      obj(obj(s.original).frame).sourceTerm = source;
      obj(obj(s.checking).binding).sourceTerm = source;
      rejects(s, message);
    }
  });

  it('preserves empty diagnostic strings and bounds reasons by Unicode characters', () => {
    const s = snapshot(); obj(s.checking).reason = ''; validateSourceSnapshot(s);
    obj(s.checking).reason = '😀'.repeat(4096); validateSourceSnapshot(s);
    obj(s.checking).reason = '😀'.repeat(4097); rejects(s, /4096 characters/);
  });

  it.each([0, 1, 2])('retains action error after %s receipts without inferring success', count => {
    const s = captured(), checking = obj(s.checking);
    checking.action = { status: 'error', reason: 'Action stopped after captured callbacks.' };
    checking.checks = arr(checking.checks).slice(0, count); checking.audits = arr(checking.audits).slice(0, count); checking.environmentSnapshotCount = count + 1;
    const v = validateSourceSnapshot(s);
    expect(v.checking.status === 'captured' && v.checking.action.status).toBe('error');
  });

  it.each([{ tag: 'unknown', message: 'Heartbeat budget exhausted.' }, { tag: 'rejected', kind: 'notConvertible' },
    { tag: 'rejected', kind: 'typeError', detail: 'type mismatch' }] as JsonObject[])('retains nonaccepted outcome $tag with an unchanged environment', outcome => {
    const s = captured(), checking = obj(s.checking), checks = arr(checking.checks), audits = arr(checking.audits);
    obj(checks[0]).outcome = outcome; obj(checks[0]).envAfter = 0;
    obj(checks[1]).envBefore = 0; obj(checks[1]).envAfter = 1;
    obj(audits[0]).environment = 0; obj(audits[0]).result = { tag: 'unavailable', reason: 'declaration was not installed' };
    obj(audits[1]).environment = 1; checking.environmentSnapshotCount = 2;
    expect(validateSourceSnapshot(s).checking).toEqual(checking);
  });

  it('collects exact universe parameters in first occurrence order, excluding opaque data', () => {
    const s = snapshot();
    const term: JsonValue = ['const', name('term'), [['max', ['param', name('u')], ['param', name('v')]], ['param', name('u')]]];
    const f = frame(term, ['sort', ['param', name('w')]], [{ constructor: 'ldecl', index: nat(0), fvarId: name('x'),
      userName: anonymous, type: ['sort', ['param', name('first')]], value: ['sort', ['param', name('ignored')]], nondep: true, kind: 'default' }]);
    obj(s.original).frame = structuredClone(f); obj(s.prepared).frame = f;
    obj(s.prepared).checkerUniverseParams = ['first', 'u', 'v', 'w'].map(n => name(n));
    validateSourceSnapshot(s);
    obj(s.prepared).checkerUniverseParams = ['first', 'u', 'w', 'v'].map(n => name(n)); rejects(s, /association/);
  });
});

describe('snapshot linkage and malformed inputs', () => {
  it.each(['binding term', 'binding type', 'binding declarations', 'params', 'prefix', 'attempt', 'registry', 'arity', 'telescope', 'positional', 'order'])(
    'rejects modified %s', change => {
      const s = captured(), binding = obj(obj(s.checking).binding), context = obj(binding.context);
      switch (change) {
        case 'binding term': binding.sourceTerm = c('False'); break;
        case 'binding type': binding.sourceType = c('False'); break;
        case 'binding declarations': context.originalDeclarations = []; break;
        case 'params': binding.universeParams = [name('u')]; break;
        case 'prefix': binding.declarationPrefix = name(id); break;
        case 'attempt': binding.attempt = 'public-hash-is-not-a-capture-id'; break;
        case 'registry': context.registry = arr(context.registry).slice().reverse(); break;
        case 'arity': context.arity = 4; break;
        case 'telescope': context.telescope = ['nil']; break;
        case 'positional': binding.positionalTerm = b(1); break;
        case 'order': context.originalDeclarationOrder = 'mostRecentFirst'; break;
      }
      rejects(s);
    });

  it.each(['id', 'pair', 'label', 'displayLabel', 'subject', 'declaration', 'envBefore', 'envAfter', 'heartbeatBound', 'outcome', 'audit subject', 'audit result', 'audit environment', 'audit checkId', 'audit category', 'environment count', 'missing audit', 'zero completed'])(
    'rejects receipt/audit mutation %s', change => {
      const s = captured(), checking = obj(s.checking), receipt = obj(arr(checking.checks)[0]), audit = obj(arr(checking.audits)[0]);
      switch (change) {
        case 'subject': receipt.subject = { ...obj(receipt.subject), attempt: '550e8400-e29b-41d4-a716-446655440001' }; break;
        case 'declaration': receipt.declaration = { ...obj(receipt.declaration), type: c('False') }; break;
        case 'envBefore': receipt.envBefore = 1; break;
        case 'envAfter': receipt.envAfter = 0; break;
        case 'heartbeatBound': receipt.heartbeatBound = nat(200001); break;
        case 'outcome': receipt.outcome = { tag: 'success' }; break;
        case 'audit subject': audit.subject = { ...obj(audit.subject), value: c('False') }; break;
        case 'audit result': audit.result = { tag: 'unavailable', reason: 'declaration was not installed' }; break;
        case 'audit environment': audit.environment = 0; break;
        case 'audit checkId': audit.checkId = 1; break;
        case 'audit category': audit.category = 'certificate'; break;
        case 'environment count': checking.environmentSnapshotCount = 4; break;
        case 'missing audit': checking.audits = []; break;
        case 'zero completed': checking.checks = []; checking.audits = []; checking.environmentSnapshotCount = 1; break;
        default: receipt[change] = change === 'id' ? 1 : 'other';
      }
      rejects(s);
    });

  it('preserves exact opaque values and original declaration identities across preparation', () => {
    for (const key of ['value', 'index', 'fvarId', 'userName', 'kind', 'nondep']) {
      const s = captured(), d = obj(arr(obj(obj(s.prepared).frame).originalDeclarations)[2]);
      d[key] = key === 'value' ? c('True') : key === 'index' ? nat(3) : key === 'kind' ? 'default' : key === 'nondep' ? false : name('changed');
      rejects(s);
    }
  });

  it('rejects captured checks without a prepared frame and wrong capture profiles', () => {
    const s = captured(); s.prepared = unavailable('prepared-serialization', 'limit'); rejects(s);
    for (const [key, value] of [['schema', 2], ['naturalProfile', 1], ['rawProfile', 'other'], ['sourceKind', 'namedExtraction'], ['operation', 'other']] as [string, JsonValue][]) {
      const s = captured(); obj(obj(s.checking).binding)[key] = value; rejects(s);
    }
  });

  it('rejects unsafe or mixed natural roles, unknown branches and unknown fields', () => {
    const cases: JsonObject[] = [];
    const unsafe = snapshot(); obj(unsafe.selection).startByte = 9007199254740992; cases.push(unsafe);
    const negative = snapshot(); obj(negative.selection).startByte = -1; cases.push(negative);
    const semantic = snapshot(); obj(obj(semantic.original).frame).sourceTerm = ['bvar', 0]; cases.push(semantic);
    const numericName = snapshot(); obj(numericName.selection).parentDeclaration = ['num', anonymous, 7]; cases.push(numericName);
    const outOfRange = snapshot(); obj(outOfRange.selection).requestedEndByte = 9; cases.push(outOfRange);
    const wrong = snapshot(); obj(wrong.policy).heartbeatBound = 200000; cases.push(wrong);
    const unknown = snapshot(); unknown.expectedType = { status: 'pending' }; cases.push(unknown);
    const extra = snapshot(); extra.authorized = true; cases.push(extra);
    const malformed = snapshot(); malformed.checking = null; cases.push(malformed);
    const phase = snapshot(); obj(phase.checking).phase = 'x'.repeat(65); cases.push(phase);
    cases.forEach(s => rejects(s));
  });

  it('rejects accessors without invoking them, cycles, sparse arrays and hidden properties', () => {
    const getter = snapshot(); Object.defineProperty(getter, 'checking', { get() { throw new Error('getter must not run'); }, enumerable: true }); rejects(getter);
    const cycle = snapshot(); obj(cycle.checking).reason = cycle; rejects(cycle);
    const sparse = snapshot(); obj(sparse.prepared).checkerUniverseParams = new Array(1); rejects(sparse);
    const symbol = snapshot(); Object.defineProperty(symbol, Symbol('hidden'), { value: true }); rejects(symbol);
    const nonenumerable = snapshot(); Object.defineProperty(nonenumerable, 'hidden', { value: true }); rejects(nonenumerable);
    const extended = snapshot(); Object.assign(obj(extended.prepared).checkerUniverseParams!, { hidden: true }); rejects(extended);
  });

  it('enforces section text/depth/node/natural and aggregate output ceilings', () => {
    const text = snapshot(); text.expectedType = { status: 'available', expression: ['lit', ['strVal', '😀'.repeat(32768)]] }; rejects(text, /limit/);
    const digits = snapshot(); obj(obj(digits.original).frame).sourceTerm = ['lit', ['natVal', nat('9'.repeat(10001))]]; rejects(digits, /limit/);
    const depth = snapshot(); let expr: JsonValue = c('True'); for (let i = 0; i < 96; i++) expr = ['lam', anonymous, c('True'), expr, 'default'];
    obj(obj(depth.original).frame).sourceTerm = expr; rejects(depth, /limit/);
    const nodes = snapshot(); obj(obj(nodes.original).frame).sourceTerm = ['const', name('wide'), Array.from({ length: 11000 }, () => ['zero'])]; rejects(nodes, /limit/);
    const checking = captured(); obj(arr(obj(checking.checking).audits)[0]).result = { tag: 'available', axioms: Array.from({ length: 800 }, () => name('x'.repeat(1000))) }; rejects(checking, /limit/);
    const total = snapshot(); obj(total.checking).reason = 'x'.repeat(1536 * 1024); rejects(total, /limit/);
  });

  it('independently validates a foreign snapshot before exposing drawings', () => {
    const invalid = snapshot(); obj(obj(invalid.prepared).frame).sourceTerm = ['invalid'];
    expect(() => sourceSnapshotDrawings(invalid as never)).toThrow(SourceSnapshotError);
  });
});

describe.runIf(!!process.env.DEFINOGRAPH_SOURCE_SNAPSHOT_FIXTURES)('actual native source snapshots', () => {
  it('validates every retained native attachment and independently reads its drawings', () => {
    const cases: { sourceSnapshot?: unknown; snapshot?: unknown; response?: { sourceSnapshot?: unknown } }[] = JSON.parse(readFileSync(process.env.DEFINOGRAPH_SOURCE_SNAPSHOT_FIXTURES!, 'utf8'));
    expect(cases.length).toBeGreaterThan(0);
    for (const item of cases) {
      const snapshot = validateSourceSnapshot(item.response?.sourceSnapshot ?? item.sourceSnapshot ?? item.snapshot ?? item);
      for (const drawing of Object.values(sourceSnapshotDrawings(snapshot))) expect(readRawInspection(drawing).ok).toBe(true);
    }
  });
});
