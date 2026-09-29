import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import { validateSourceSnapshot } from './source-snapshot';
import { validateSourceOccurrence } from './source-occurrence';
import { validateSourceHeadExposure, type HeadExposureTarget } from './source-head-exposure';
const name = (s: string, prefix: JsonValue = ['anonymous']): JsonValue => ['str', prefix, s];
const c = (s: string, levels: JsonValue[] = []): JsonValue => ['const', name(s), levels];
const n = (v: number): JsonValue => ['nat', String(v)];
const b = (i: number): JsonValue => ['bvar', n(i)];
const app = (fn: JsonValue, ...args: JsonValue[]): JsonValue => args.reduce<JsonValue>((f, a) => ['app', f, a], fn);
const object = (v: JsonValue) => v as JsonObject;
const array = (v: JsonValue) => v as JsonValue[];
const older = '550e8400-e29b-41d4-a716-446655440000', parentId = '550e8400-e29b-41d4-a716-446655440001', freshId = '550e8400-e29b-41d4-a716-446655440002';
const prefix = (kind: string, id: string) => name(id, name(kind, name('StatementLens')));
const nat = c('Nat'), arrow: JsonValue = ['forallE', name('x'), nat, nat, 'default'];
const lam = (type: JsonValue, body: JsonValue): JsonValue => ['lam', name('x'), type, body, 'default'];
const port = (previous: JsonValue, type: JsonValue): JsonValue => ['port', previous, { name: name('same'), info: 'default' }, type];
const home = { arity: 3, telescope: ['letE', port(port(['nil'], arrow), nat), name('same'), false, nat, b(0)] as JsonValue };
// This independent fixture closure is intentionally explicit rather than calling
// the production close/reconstruction helpers. Receipts here are test data only.
const close = (value: JsonValue, tag: 'forallE' | 'lam'): JsonValue => [tag, name('same'), arrow,
  [tag, name('same'), nat, ['letE', name('same'), nat, b(0), value, false], 'default'], 'default'];
const truth = c('True'), intro: JsonValue = ['const', name('intro', name('True')), []];
function declaration(base: JsonValue, label: string, type: JsonValue, value: JsonValue, component = label === 'component'): JsonObject {
  const declarationName = name(label, base);
  return { kind: component ? 'defnDecl' : 'thmDecl', name: declarationName, levelParams: [], type: close(type, 'forallE'), value: close(value, 'lam'), all: [declarationName],
    ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
}
function attach(checking: JsonObject, declarations: JsonObject[], captureId: string, operation: string) {
  checking.checks = declarations.map((d, id) => {
    const label = id === 8 ? 'conversion' : id % 2 ? 'component' : 'context';
    return { id, pair: operation, label, displayLabel: label, declaration: d,
      subject: { attempt: captureId, pair: operation, sequence: id, target: label, declaration: d },
      envBefore: id, envAfter: id + 1, heartbeatBound: n(200000), outcome: { tag: 'accepted' } };
  });
  checking.audits = declarations.map((subject, checkId) => ({ checkId, subject, environment: checkId + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } }));
  checking.environmentSnapshotCount = declarations.length + 1;
}
function baseDeclarations(base: JsonValue, term: JsonValue, type: JsonValue): JsonObject[] {
  return [name('source', base), name('root', name('extraction', base)), name('selected', name('extraction', base))]
    .flatMap(p => [declaration(p, 'context', truth, intro), declaration(p, 'component', type, term)]);
}
function fixture(target: HeadExposureTarget = 'term') {
  const term = target === 'term' ? app(c('ForeignWrapper'), b(2), b(0)) : c('ForeignValue');
  const type = target === 'term' ? nat : c('ForeignType');
  const sourceTerm = target === 'term' ? app(c('ForeignWrapper'), ['fvar', name('f')], ['fvar', name('k')]) : term;
  const originals: JsonValue[] = [
    { constructor: 'cdecl', index: n(0), fvarId: name('f'), userName: name('same'), type: arrow, binderInfo: 'default', kind: 'default' },
    { constructor: 'cdecl', index: n(1), fvarId: name('n'), userName: name('same'), type: nat, binderInfo: 'default', kind: 'default' },
    { constructor: 'ldecl', index: n(2), fvarId: name('k'), userName: name('same'), type: nat, value: ['fvar', name('n')], nondep: false, kind: 'default' },
  ];
  const frame = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: originals, sourceTerm, sourceType: type };
  const snapshot = validateSourceSnapshot({ schema: 'definograph.source-snapshot.v1',
    selection: { startByte: 0, endByte: 1, requestedStartByte: 0, requestedEndByte: 1, parentDeclaration: null },
    policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' },
    expectedType: { status: 'absent' }, original: { status: 'available', typeOrigin: 'inferred', frame },
    prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame, checkerUniverseParams: [] },
    checking: { status: 'unavailable', kind: 'unsupported', phase: 'test', reason: 'Independent test data.', attempted: false } });
  const binding = (attempt: string, kind: string, operation: string): JsonObject => ({ schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt, operation,
    sourceKind: kind === 'SourceOccurrence' ? 'namedExtraction' : 'namedHeadExposure', declarationPrefix: prefix(kind, attempt), universeParams: [], initialEnvironment: 0,
    context: { ...home, registry: [name('k'), name('n'), name('f')], registryOrder: 'mostRecentFirst', originalDeclarations: originals, originalDeclarationOrder: 'oldestFirst' },
    sourceTerm, sourceType: type, positionalTerm: term, positionalType: type, path: [] });
  const selected = { home, term, type };
  const parentChecking: JsonObject = { status: 'captured', action: { status: 'completed' }, binding: binding(parentId, 'SourceOccurrence', 'editor-occurrence'), selected };
  attach(parentChecking, baseDeclarations(prefix('SourceOccurrence', parentId), term, type), parentId, 'editor-occurrence');
  const occurrence = validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1', parentCaptureId: older, captureId: parentId, path: [],
    policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' }, checking: parentChecking }, snapshot);
  const after = target === 'term' ? app(b(2), b(0)) : arrow;
  const carrier: JsonValue = target === 'term' ? nat : ['sort', ['succ', ['zero']]];
  const carrierSort: JsonValue = target === 'term' ? ['succ', ['zero']] : ['succ', ['succ', ['zero']]];
  const before = selected[target], headName = name(target === 'term' ? 'ForeignWrapper' : 'ForeignType');
  const exposure: JsonObject = { status: 'candidate', before, result: { home, term: after, type: carrier },
    definition: { name: headName, levelParams: [], type: target === 'term' ? ['forallE', name('x'), arrow, arrow, 'default'] : carrier,
      value: target === 'term' ? lam(arrow, lam(nat, app(b(1), b(0)))) : arrow, hints: ['regular', 3], safety: 'safe' },
    actualLevels: [], arguments: target === 'term' ? [b(2), b(0)] : [], betaApplications: target === 'term' ? 2 : 0, carrierSort, checking: { status: 'completed' } };
  const newPrefix = prefix('SourceHeadExposure', freshId);
  const declarations = [...baseDeclarations(newPrefix, term, type), declaration(name('result', newPrefix), 'context', truth, intro), declaration(name('result', newPrefix), 'component', carrier, after),
    declaration(newPrefix, 'conversion', app(c('Eq', [carrierSort]), carrier, before, after), app(['const', name('refl', name('Eq')), [carrierSort]], carrier, before), false)];
  const checking: JsonObject = { status: 'captured', action: { status: 'completed' }, binding: { ...binding(freshId, 'SourceHeadExposure', 'editor-head-exposure'), target, expectedSelected: selected }, selected, exposure };
  attach(checking, declarations, freshId, 'editor-head-exposure');
  const value: JsonObject = { schema: 'definograph.source-head-exposure.v1', parentCaptureId: parentId, captureId: freshId, path: [], target,
    policy: { id: 'safe-definition-head-v1', operation: 'editor-head-exposure', preparation: 'Lean.instantiateMVars', universeSubstitution: 'structural', reduction: 'original-lambda-spine', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' }, checking };
  return { value: JSON.parse(JSON.stringify(value)) as JsonObject, snapshot, parent: { snapshot, occurrence } };
}
function truncate(value: JsonObject, count: number) {
  const check = object(value.checking);
  check.checks = array(check.checks).slice(0, count); check.audits = array(check.audits).slice(0, count); check.environmentSnapshotCount = count + 1;
}
function replaceDeclaration(checking: JsonObject, i: number, transform: (declaration: JsonObject) => void) {
  const receipt = object(array(checking.checks)[i]), declaration = structuredClone(object(receipt.declaration)); transform(declaration);
  receipt.declaration = declaration; object(receipt.subject).declaration = declaration; object(array(checking.audits)[i]).subject = declaration;
}
function unwrap(value: JsonValue): JsonValue { return array(array(array(value)[3])[3])[4]; }
function replaceBody(value: JsonValue, body: JsonValue) { array(array(array(value)[3])[3])[4] = body; }

describe('fresh definition-head exposure record associations', () => {
  it.each(['term', 'type'] as const)('validates exact %s carrier, closed declarations and frozen source without mutating its parent', target => {
    const { value, snapshot, parent } = fixture(target), before = JSON.stringify(parent);
    const result = validateSourceHeadExposure(value, snapshot, parent);
    expect(result).toEqual(value); expect(Object.isFrozen(result)).toBe(true);
    expect(result.checking.status).toBe('captured'); expect(JSON.stringify(parent)).toBe(before);
    object(value.checking).selected = null;
    expect(result.checking.status === 'captured' && result.checking.selected).not.toBeNull();
  });
  it.each([0, 1, 2, 3, 4, 5, 6])('preserves a coherent base failure prefix of %s checks', count => {
    const { value, snapshot, parent } = fixture(); truncate(value, count);
    Object.assign(object(value.checking), { action: { status: 'error', reason: 'actual base error' }, selected: null, exposure: null });
    expect(validateSourceHeadExposure(value, snapshot, parent)).toEqual(value);
  });
  it.each([6, 7, 8, 9])('preserves candidate trace and every receipt after later error at %s checks', count => {
    const { value, snapshot, parent } = fixture(); truncate(value, count);
    object(object(value.checking).exposure).checking = { status: 'error', reason: 'actual later error' };
    expect(validateSourceHeadExposure(value, snapshot, parent)).toEqual(value);
  });
  it.each(['unknown', 'typeError', 'notConvertible'])('does not turn a source %s into acceptance after later success', tag => {
    const { value, snapshot, parent } = fixture(), checking = object(value.checking), checks = array(checking.checks), audits = array(checking.audits);
    object(checks[1]).outcome = tag === 'unknown' ? { tag, message: 'budget' } : tag === 'typeError' ? { tag: 'rejected', kind: tag, detail: 'source mismatch' } : { tag: 'rejected', kind: tag };
    object(checks[1]).envAfter = 1; object(audits[1]).result = { tag: 'unavailable', reason: 'declaration was not installed' };
    for (let i = 1; i < checks.length; i++) { object(audits[i]).environment = i; if (i > 1) { object(checks[i]).envBefore = i - 1; object(checks[i]).envAfter = i; } }
    checking.environmentSnapshotCount = 9;
    const result = validateSourceHeadExposure(value, snapshot, parent);
    expect(result.checking.status === 'captured' && result.checking.checks[1].outcome.tag).toBe(tag === 'unknown' ? tag : 'rejected');
  });
  it('retains a fresh selected-type mismatch only as its explicit prerequisite refusal', () => {
    const { value, snapshot, parent } = fixture(); truncate(value, 6); const checking = object(value.checking);
    object(checking.selected).type = c('Bool');
    replaceDeclaration(checking, 5, declaration => { declaration.type = close(c('Bool'), 'forallE'); });
    checking.exposure = { status: 'unavailable', kind: 'prerequisite', phase: 'selected-match', reason: 'fresh type changed' };
    validateSourceHeadExposure(value, snapshot, parent);
    object(checking.exposure).kind = 'unsupported'; expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow(/selected/);
  });
  it('permits fresh prepared-parent mismatch only as an unattempted parent-match refusal', () => {
    const { value, snapshot, parent } = fixture();
    const altered = structuredClone(snapshot); altered.selection.parentDeclaration = ['str', ['anonymous'], 'different'];
    value.checking = { status: 'unavailable', kind: 'prerequisite', phase: 'parent-match', reason: '', attempted: false };
    validateSourceHeadExposure(value, validateSourceSnapshot(altered), parent);
    object(value.checking).attempted = true; expect(() => validateSourceHeadExposure(value, validateSourceSnapshot(altered), parent)).toThrow(/parent/);
  });
  it('binds a same-id refusal to its exact unattempted parent-match status', () => {
    const { value, snapshot, parent } = fixture(); value.captureId = parentId;
    value.checking = { status: 'unavailable', kind: 'prerequisite', phase: 'parent-match', reason: '', attempted: false };
    validateSourceHeadExposure(value, snapshot, parent); object(value.checking).phase = 'preparation';
    expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow(/fresh/);
  });
  it.each(['candidate', 'arguments', 'beta', 'before', 'home', 'carrier', 'body', 'head', 'expected', 'selected', 'universe', 'target', 'parent', 'path', 'policy'])(
    'refuses %s mutation independently of repaired redundant receipt fields', mutation => {
      const { value, snapshot, parent } = fixture(), checking = object(value.checking), exposure = object(checking.exposure), result = object(exposure.result);
      switch (mutation) {
        case 'candidate':
          result.term = b(1);
          replaceDeclaration(checking, 7, declaration => { replaceBody(declaration.value, b(1)); });
          replaceDeclaration(checking, 8, declaration => { array(unwrap(declaration.type))[2] = b(1); }); break;
        case 'arguments': array(exposure.arguments).reverse(); break;
        case 'beta': exposure.betaApplications = 1; break;
        case 'before': exposure.before = app(c('ForeignWrapper'), b(1), b(0)); break;
        case 'home': object(result.home).arity = 2; break;
        case 'carrier': result.type = c('Bool'); break;
        case 'body': object(exposure.definition).value = lam(arrow, lam(nat, b(0))); break;
        case 'head': object(exposure.definition).name = name('another'); break;
        case 'expected': object(object(checking.binding).expectedSelected).term = b(0); break;
        case 'selected': object(checking.selected).type = c('Bool'); break;
        case 'universe': exposure.carrierSort = ['zero']; break;
        case 'target': value.target = 'type'; break;
        case 'parent': value.parentCaptureId = older; break;
        case 'path': value.path = ['appArg']; break;
        case 'policy': object(value.policy).universeSubstitution = 'smart'; break;
      }
      expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow();
    });
  it.each(['Eq left', 'Eq right', 'refl', 'kind', 'label', 'subject', 'closure flag', 'closure value', 'audit', 'env count', 'env before', 'env after', 'heartbeat', 'missing', 'completed prefix'])(
    'checks exact conversion and receipt lineage: %s', mutation => {
      const { value, snapshot, parent } = fixture(), checking = object(value.checking), checks = array(checking.checks);
      switch (mutation) {
        case 'Eq left': replaceDeclaration(checking, 8, d => { array(array(unwrap(d.type))[1])[2] = b(0); }); break;
        case 'Eq right': replaceDeclaration(checking, 8, d => { array(unwrap(d.type))[2] = b(0); }); break;
        case 'refl': replaceDeclaration(checking, 8, d => { array(unwrap(d.value))[2] = b(0); }); break;
        case 'kind': replaceDeclaration(checking, 8, d => { d.kind = 'defnDecl'; }); break;
        case 'label': object(checks[8]).label = 'component'; break;
        case 'subject': object(object(checks[8]).subject).attempt = parentId; break;
        case 'closure flag': replaceDeclaration(checking, 8, d => { array(array(array(d.type)[3])[3])[5] = true; }); break;
        case 'closure value': replaceDeclaration(checking, 8, d => { array(array(array(d.type)[3])[3])[3] = b(1); }); break;
        case 'audit': object(array(checking.audits)[8]).result = { tag: 'unavailable', reason: 'declaration was not installed' }; break;
        case 'env count': checking.environmentSnapshotCount = 11; break;
        case 'env before': object(checks[8]).envBefore = 7; break;
        case 'env after': object(checks[8]).envAfter = 8; break;
        case 'heartbeat': object(checks[8]).heartbeatBound = 200000; break;
        case 'missing': checks.splice(6, 1); break;
        case 'completed prefix': truncate(value, 8); break;
      }
      expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow();
    });
  it('requires succ of the actual Sort carrier in type mode, even after all universe copies are repaired', () => {
    const { value, snapshot, parent } = fixture('type'), checking = object(value.checking), exposure = object(checking.exposure);
    const wrong: JsonValue = ['succ', ['zero']]; exposure.carrierSort = wrong;
    replaceDeclaration(checking, 8, d => {
      array(array(array(array(unwrap(d.type))[1])[1])[1])[2] = [wrong];
      array(array(array(unwrap(d.value))[1])[1])[2] = [wrong];
    });
    expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow(/carrierSort/);
  });
  it.each(['extra', 'hidden', 'symbol', 'prototype', 'getter', 'sparse', 'cycle', 'unsafe', 'surrogate', 'oversize'])('refuses hostile %s input before accepting any data', mutation => {
    const { value, snapshot, parent } = fixture(); let invoked = false;
    switch (mutation) {
      case 'extra': value.extra = null; break;
      case 'hidden': Object.defineProperty(value, 'extra', { value: true }); break;
      case 'symbol': Object.assign(value, { [Symbol('extra')]: true }); break;
      case 'prototype': Object.setPrototypeOf(value, { inherited: true }); break;
      case 'getter': Object.defineProperty(value, 'checking', { enumerable: true, get() { invoked = true; return null; } }); break;
      case 'sparse': value.path = new Array(1); break;
      case 'cycle': value.checking = value; break;
      case 'unsafe': object(value.checking).environmentSnapshotCount = 9007199254740992; break;
      case 'surrogate': object(value.policy).id = '\ud800'; break;
      case 'oversize': value.extra = 'x'.repeat(1024 * 1024); break;
    }
    expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow(); expect(invoked).toBe(false);
  });
  it('validates the retained parent independently rather than trusting its type assertion', () => {
    const { value, snapshot, parent } = fixture(), corrupt = structuredClone(parent);
    if (corrupt.occurrence.checking.status === 'captured') corrupt.occurrence.checking.checks[5].envAfter = 3;
    expect(() => validateSourceHeadExposure(value, snapshot, corrupt)).toThrow(/environment/);
  });
  it('refuses an environment appended before a failed audit could append its receipt', () => {
    const { value, snapshot, parent } = fixture(); truncate(value, 8);
    const checking = object(value.checking);
    object(checking.exposure).checking = { status: 'error', reason: 'audit interrupted after environment append' };
    checking.environmentSnapshotCount = 10;
    expect(() => validateSourceHeadExposure(value, snapshot, parent)).toThrow(/snapshot count/);
  });
});

describe.runIf(!!process.env.DEFINOGRAPH_SOURCE_HEAD_EXPOSURE_FIXTURES)('actual native definition-head exposure records', () => {
  it('validates all actual records and preserves every outcome and original parent', () => {
    const rows = JSON.parse(readFileSync(process.env.DEFINOGRAPH_SOURCE_HEAD_EXPOSURE_FIXTURES!, 'utf8'));
    expect(rows.length).toBeGreaterThan(0); const { canonical } = createExactJsonTools();
    for (const row of rows) {
      const before = canonical(row), snapshot = validateSourceSnapshot(row.response.sourceSnapshot);
      const parentSnapshot = validateSourceSnapshot(row.parent.snapshot), occurrence = validateSourceOccurrence(row.parent.occurrence, parentSnapshot);
      const result = validateSourceHeadExposure(row.response.sourceHeadExposure, snapshot, { snapshot: parentSnapshot, occurrence });
      expect(canonical(result as unknown as JsonValue)).toBe(canonical(row.response.sourceHeadExposure)); expect(canonical(row)).toBe(before);
    }
  });
});
