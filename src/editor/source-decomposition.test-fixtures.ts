/** Constructed wire records for independent parser tests; these receipts are
 * synthetic data, not evidence that Lean checked the expressions. */
import type { JsonObject, JsonValue } from '../packets/packet';
import { validateSourceSnapshot } from './source-snapshot';
import { validateSourceOccurrence } from './source-occurrence';
import type { HeadExposureTarget } from './source-head-exposure';
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
export function headExposureFixture(target: HeadExposureTarget = 'term') {
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
