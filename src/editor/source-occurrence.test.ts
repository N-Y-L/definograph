import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import type { JsonObject, JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { validateSourceSnapshot, type SourceSnapshot } from './source-snapshot';
import { isSourceOccurrencePath, sourceOccurrencePath, validateSourceOccurrence } from './source-occurrence';

const anon: JsonValue = ['anonymous'];
const name = (part: string, parent: JsonValue = anon): JsonValue => ['str', parent, part];
const n = (value: number): JsonValue => ['nat', String(value)];
const b = (value: number): JsonValue => ['bvar', n(value)];
const c = (value: string): JsonValue => ['const', value.split('.').reduce<JsonValue>((p, s) => name(s, p), anon), []];
const nat = c('Nat');
const parentCaptureId = '550e8400-e29b-41d4-a716-446655440000';
const captureId = '550e8400-e29b-41d4-a716-446655440001';
const prefix = name(captureId, name('SourceOccurrence', name('StatementLens')));
const object = (v: JsonValue): JsonObject => v as JsonObject;
const array = (v: JsonValue): JsonValue[] => v as JsonValue[];
const unavailable: JsonObject = { status: 'unavailable', kind: 'unsupported', phase: 'source-capture', reason: 'Retained source.', attempted: true };
const source: JsonValue = ['lam', name('x'), nat,
  ['letE', name('x'), nat, ['fvar', name('n')], ['app', c('Nat.succ'), b(0)], true], 'default'];
const positional: JsonValue = ['lam', name('x'), nat,
  ['letE', name('x'), nat, b(2), ['app', c('Nat.succ'), b(0)], true], 'default'];
// A reducible supplied type deliberately differs from the inferred arrow.
const supplied: JsonValue = ['letE', name('T'), ['sort', ['succ', ['zero']]], nat,
  ['forallE', name('x'), b(0), b(1), 'default'], true];
const inferred: JsonValue = ['forallE', name('x'), nat, nat, 'default'];
const locals: JsonValue[] = [
  { constructor: 'cdecl', index: n(3), fvarId: name('n'), userName: name('x'), type: nat, binderInfo: 'implicit', kind: 'default' },
  { constructor: 'ldecl', index: n(3), fvarId: name('opaque'), userName: name('x'), type: nat, nondep: true, kind: 'implDetail',
    value: ['mdata', ['mdataEntries', [[name('k'), ['ofInt', ['negSucc', ['nat', '9007199254740993']]]]]], ['mvar', name('ignored')]] },
];
const external: JsonValue = ['port', ['port', ['nil'], { name: name('x'), info: 'implicit' }, nat], { name: name('x'), info: 'default' }, nat];
const selectedHome: JsonValue = ['letE', ['port', external, { name: name('x'), info: 'default' }, nat], name('x'), true, nat, b(2)];
const externalClose = (body: JsonValue, tag: string): JsonValue => [tag, name('x'), nat, [tag, name('x'), nat, body, 'default'], 'implicit'];
const selectedClose = (body: JsonValue, tag: string): JsonValue => externalClose([tag, name('x'), nat,
  ['letE', name('x'), nat, b(2), body, true], 'default'], tag);

function rawSnapshot(term: JsonValue = source, type: JsonValue = supplied): JsonObject {
  const frame = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: locals, sourceTerm: term, sourceType: type };
  return structuredClone({ schema: 'definograph.source-snapshot.v1',
    selection: { startByte: 1, endByte: 10, requestedStartByte: 1, requestedEndByte: 10, parentDeclaration: null },
    policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' },
    expectedType: { status: 'absent' }, original: { status: 'available', typeOrigin: 'inferred', frame: structuredClone(frame) },
    prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame, checkerUniverseParams: [] }, checking: unavailable });
}
function fixture(): { snapshot: SourceSnapshot; value: JsonObject } {
  const snapshot = validateSourceSnapshot(rawSnapshot());
  const checks: JsonValue[] = [], audits: JsonValue[] = [];
  const pairs: [JsonValue, JsonValue, JsonValue, typeof externalClose][] = [
    [name('source', prefix), supplied, positional, externalClose],
    [name('root', name('extraction', prefix)), inferred, positional, externalClose],
    [name('selected', name('extraction', prefix)), nat, b(0), selectedClose],
  ];
  for (const [base, type, term, close] of pairs) for (const label of ['context', 'component']) {
    const id = checks.length, declarationName = name(label, base), component = label === 'component';
    const declaration: JsonObject = { kind: component ? 'defnDecl' : 'thmDecl', name: declarationName, levelParams: [],
      type: close(component ? type : c('True'), 'forallE'), value: close(component ? term : c('True.intro'), 'lam'), all: [declarationName],
      ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
    checks.push({ id, pair: 'editor-occurrence', label, displayLabel: label, declaration,
      subject: { attempt: captureId, pair: 'editor-occurrence', sequence: id, target: label, declaration },
      envBefore: id, envAfter: id + 1, heartbeatBound: n(200000), outcome: { tag: 'accepted' } });
    audits.push({ checkId: id, subject: declaration, environment: id + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } });
  }
  return { snapshot, value: structuredClone({ schema: 'definograph.source-occurrence.v1', parentCaptureId, captureId,
    path: ['lamBody', 'letBody', 'appArg'], policy: { id: 'named-extraction-v1', operation: 'editor-occurrence',
      preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' },
    checking: { status: 'captured', action: { status: 'completed' }, binding: {
      schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt: captureId, operation: 'editor-occurrence', sourceKind: 'namedExtraction',
      declarationPrefix: prefix, universeParams: [], initialEnvironment: 0,
      context: { arity: 2, telescope: external, registry: [name('opaque'), name('n')], registryOrder: 'mostRecentFirst',
        originalDeclarations: locals, originalDeclarationOrder: 'oldestFirst' },
      sourceTerm: source, sourceType: supplied, positionalTerm: positional, positionalType: supplied, path: [['lamBody'], ['letBody'], ['appArg']],
    }, selected: { home: { arity: 4, telescope: selectedHome }, term: b(0), type: nat }, checks, audits, environmentSnapshotCount: 7 } }) };
}
function failedPrefix(value: JsonObject, count: number): void {
  const checking = object(value.checking);
  checking.action = { status: 'error', reason: 'Retained action error.' }; checking.selected = null;
  checking.checks = array(checking.checks).slice(0, count); checking.audits = array(checking.audits).slice(0, count); checking.environmentSnapshotCount = count + 1;
}

describe('exact prepared occurrence associations', () => {
  it('validates six independent receipts, inferred type differences, repeated names and owned nondep lets', () => {
    const { snapshot, value } = fixture(), validated = validateSourceOccurrence(value, snapshot);
    expect(validated.checking.status).toBe('captured'); expect(Object.isFrozen(validated)).toBe(true);
    expect(Object.isFrozen(validated.path)).toBe(true);
    object(value.checking).selected = null;
    expect(validated.checking.status === 'captured' && validated.checking.selected?.home.arity).toBe(4);
  });

  it.each([0, 1, 2, 3, 4, 5, 6])('retains exactly %s receipts on an action error with no selected result', count => {
    const { snapshot, value } = fixture(); failedPrefix(value, count);
    expect(validateSourceOccurrence(value, snapshot)).toEqual(value);
  });

  it('allows an invalid ordinary path after the actual two source checks, without inventing an extraction', () => {
    const { snapshot, value } = fixture(); failedPrefix(value, 2);
    value.path = ['appFun']; object(object(value.checking).binding).path = [['appFun']];
    validateSourceOccurrence(value, snapshot);
    const original = fixture().value;
    object(value.checking).checks = array(object(original.checking).checks).slice(0, 3);
    object(value.checking).audits = array(object(original.checking).audits).slice(0, 3);
    object(value.checking).environmentSnapshotCount = 4;
    expect(() => validateSourceOccurrence(value, snapshot)).toThrow(/invalid path/);
  });

  it.each(['unknown', 'notConvertible', 'typeError'])('keeps source %s independent of later accepted outcomes', kind => {
    const { snapshot, value } = fixture(), checking = object(value.checking), checks = array(checking.checks), audits = array(checking.audits);
    object(checks[1]).outcome = kind === 'unknown' ? { tag: 'unknown', message: 'budget' }
      : kind === 'typeError' ? { tag: 'rejected', kind, detail: 'mismatch' } : { tag: 'rejected', kind };
    object(checks[1]).envAfter = 1;
    object(audits[1]).result = { tag: 'unavailable', reason: 'declaration was not installed' };
    for (let i = 1; i < 6; i++) {
      object(audits[i]).environment = i;
      if (i > 1) { object(checks[i]).envBefore = i - 1; object(checks[i]).envAfter = i; }
    }
    checking.environmentSnapshotCount = 6; validateSourceOccurrence(value, snapshot);
  });

  it.each(['unsupported', 'error', 'limit', 'prerequisite'])('preserves unavailable %s without requiring a matching prepared frame', kind => {
    const { value } = fixture(), raw = rawSnapshot();
    raw.prepared = { status: 'unavailable', kind: 'limit', phase: 'preparation', reason: 'not retained' };
    value.checking = { status: 'unavailable', kind, phase: 'parent-match', reason: '', attempted: false };
    expect(validateSourceOccurrence(value, validateSourceSnapshot(raw))).toEqual(value);
  });

  it('retains the native explicit refusal of a reused capture identity', () => {
    const { value, snapshot } = fixture(); value.captureId = parentCaptureId;
    value.checking = { status: 'unavailable', kind: 'prerequisite', phase: 'parent-match', reason: 'Fresh capture identity required.', attempted: false };
    expect(validateSourceOccurrence(value, snapshot)).toEqual(value);
    for (const [key, replacement] of [['kind', 'error'], ['phase', 'occurrence-capture'], ['attempted', true]] as [string, JsonValue][]) {
      const changed = structuredClone(value); object(changed.checking)[key] = replacement;
      expect(() => validateSourceOccurrence(changed, snapshot)).toThrow(/fresh capture identity/);
    }
  });

  it.each(['home arity', 'home flag', 'home value', 'term', 'type', 'selected on error', 'missing selected', 'completed prefix',
    'binding frame', 'binding path', 'binding registry', 'binding prefix', 'binding profile', 'id', 'capture identity', 'policy'])(
    'rejects %s mutation', mutation => {
      const { snapshot, value } = fixture(), checking = object(value.checking), selected = object(checking.selected), binding = object(checking.binding);
      switch (mutation) {
        case 'home arity': object(selected.home).arity = 3; break;
        case 'home flag': array(object(selected.home).telescope)[3] = false; break;
        case 'home value': array(object(selected.home).telescope)[5] = b(1); break;
        case 'term': selected.term = b(1); break;
        case 'type': selected.type = c('Bool'); break;
        case 'selected on error': checking.action = { status: 'error', reason: '' }; break;
        case 'missing selected': checking.selected = null; break;
        case 'completed prefix': checking.checks = array(checking.checks).slice(0, 5); break;
        case 'binding frame': binding.sourceType = inferred; break;
        case 'binding path': binding.path = [['lamBody']]; break;
        case 'binding registry': object(binding.context).registry = [name('n'), name('opaque')]; break;
        case 'binding prefix': binding.declarationPrefix = name('wrong'); break;
        case 'binding profile': binding.schema = 2; break;
        case 'id': value.parentCaptureId = 'unverified-public-hash'; break;
        case 'capture identity': value.captureId = parentCaptureId; break;
        case 'policy': object(value.policy).heartbeatBound = n(2); break;
      }
      expect(() => validateSourceOccurrence(value, snapshot)).toThrow();
    });

  it.each(['label', 'subject', 'audit', 'environment', 'heartbeat', 'owned flag', 'closure name', 'closure info', 'closure value',
    'inferred bvar', 'inferred fvar', 'inferred mvar', 'inferred universe', 'inferred metadata'])(
    'checks receipt/audit and exact closure mutation %s even in a partial error', mutation => {
      const { snapshot, value } = fixture(); failedPrefix(value, 6);
      const checking = object(value.checking), receipt = object(array(checking.checks)[5]), declaration = object(receipt.declaration);
      // Remove exactly the two external ports and owned lambda port to reach
      // the source let wrapper, leaving inferred type constructors untouched.
      const outer = array(declaration.type), second = array(outer[3]), owned = array(second[3]), letNode = array(owned[3]);
      switch (mutation) {
        case 'label': receipt.label = 'extraction.selected.component'; break;
        case 'subject': object(receipt.subject).sequence = 3; break;
        case 'audit': object(array(checking.audits)[5]).checkId = 4; break;
        case 'environment': receipt.envBefore = 0; break;
        case 'heartbeat': receipt.heartbeatBound = 200000; break;
        case 'owned flag': letNode[5] = false; break;
        case 'closure name': outer[1] = name('another'); break;
        case 'closure info': second[4] = 'implicit'; break;
        case 'closure value': letNode[3] = b(1); break;
        case 'inferred bvar': letNode[4] = b(4); break;
        case 'inferred fvar': letNode[4] = ['fvar', name('n')]; break;
        case 'inferred mvar': letNode[4] = ['mvar', name('m')]; break;
        case 'inferred universe': letNode[4] = ['sort', ['mvar', name('u')]]; break;
        case 'inferred metadata': letNode[4] = ['mdata', ['mdataEntries', []], nat]; break;
      }
      expect(() => validateSourceOccurrence(value, snapshot)).toThrow();
    });

  it('does not strip binders belonging to the inferred root type', () => {
    const { snapshot, value } = fixture(); failedPrefix(value, 4);
    validateSourceOccurrence(value, snapshot);
    const declaration = object(object(array(object(value.checking).checks)[3]).declaration);
    const inferredArrow = array(array(array(declaration.type)[3])[3]);
    inferredArrow[3] = b(3); // Its own binder plus two external ports permit only indices 0..2.
    expect(() => validateSourceOccurrence(value, snapshot)).toThrow(/less than 3/);
  });
});

describe('constructor path mapping and bounds', () => {
  const root: RawPath = ['prepared', 'frame', 'sourceTerm'];
  const tree: JsonValue = ['lam', name('x'), nat, ['forallE', name('x'), nat,
    ['letE', name('x'), ['sort', ['zero']], ['proj', name('Pair'), n(0), ['app', c('id'), ['fvar', name('n')]]],
      ['app', b(0), b(1)], false], 'default'], 'default'];
  it.each([
    [[], []], [[2], ['lamDomain']], [[3], ['lamBody']], [[3, 2], ['lamBody', 'piDomain']],
    [[3, 3], ['lamBody', 'piBody']], [[3, 3, 2], ['lamBody', 'piBody', 'letType']],
    [[3, 3, 3], ['lamBody', 'piBody', 'letValue']], [[3, 3, 4], ['lamBody', 'piBody', 'letBody']],
    [[3, 3, 3, 3], ['lamBody', 'piBody', 'letValue', 'projValue']],
    [[3, 3, 3, 3, 1], ['lamBody', 'piBody', 'letValue', 'projValue', 'appFun']],
    [[3, 3, 3, 3, 2], ['lamBody', 'piBody', 'letValue', 'projValue', 'appArg']],
  ])('maps only actual prepared expression edges %j', (suffix, expected) => {
    const raw = rawSnapshot(tree); object(object(raw.original).frame).sourceTerm = ['fvar', name('n')];
    expect(sourceOccurrencePath(validateSourceSnapshot(raw), [...root, ...suffix])).toEqual(expected);
  });

  it('rejects scalar/name/universe/metadata positions and every other source section', () => {
    const snapshot = validateSourceSnapshot(rawSnapshot(tree));
    for (const path of [[...root, 0], [...root, 1], [...root, 2, 1], [...root, 2, 2], [...root, 3, 3, 3, 2],
      ['original', 'frame', 'sourceTerm'], ['prepared', 'frame', 'sourceType'], ['prepared', 'frame', 'originalDeclarations', 0, 'type'],
      [...root, '3'], [...root, 9]] as RawPath[]) expect(sourceOccurrencePath(snapshot, path)).toBeUndefined();
    const metadata = validateSourceSnapshot(rawSnapshot(['mdata', ['mdataEntries', []], tree]));
    expect(sourceOccurrencePath(metadata, root)).toBeUndefined(); expect(sourceOccurrencePath(metadata, [...root, 2])).toBeUndefined();
  });

  it('strictly validates path arrays without invoking accessors', () => {
    expect(isSourceOccurrencePath([])).toBe(true); expect(isSourceOccurrencePath(Array(64).fill('lamBody'))).toBe(true);
    const getter = ['lamBody']; Object.defineProperty(getter, 0, { get() { throw Error('must not run'); } });
    for (const value of [getter, new Array(1), Object.assign([], { extra: true }), ['uniqueArg'], ['instBody'], ['mdataBody'],
      Array(65).fill('lamBody'), { 0: 'lamBody', length: 1 }, [1], [['lamBody']]]) expect(isSourceOccurrencePath(value)).toBe(false);
  });

  it('rejects malformed, extra, unsafe, cyclic and oversized records before readback', () => {
    const changes: ((v: JsonObject) => void)[] = [
      v => { v.schema = 'unknown'; }, v => { v.extra = true; }, v => { v.path = new Array(1); },
      v => { object(v.checking).environmentSnapshotCount = 9007199254740992; },
      v => { v.checking = v; }, v => { v.path = Array(65).fill('lamBody'); },
      v => { v.checking = { ...unavailable, reason: 'x'.repeat(4097) }; },
      v => { object(v.checking).extra = 'x'.repeat(768 * 1024); },
      v => { let deep: JsonValue = null; for (let i = 0; i < 121; i++) deep = [deep]; v.checking = deep; },
    ];
    for (const mutate of changes) { const { value, snapshot } = fixture(); mutate(value); expect(() => validateSourceOccurrence(value, snapshot)).toThrow(); }
  });
});

describe.runIf(!!process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_FIXTURES)('actual native occurrence captures', () => {
  it('validates every complete native occurrence attachment against its fresh snapshot', () => {
    const cases = JSON.parse(readFileSync(process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_FIXTURES!, 'utf8'));
    expect(cases.length).toBeGreaterThan(0);
    for (const item of cases) {
      const response = item.response ?? item;
      const snapshot = validateSourceSnapshot(response.sourceSnapshot ?? response.snapshot);
      validateSourceOccurrence(response.sourceOccurrence ?? response.occurrence, snapshot);
    }
  });
});
