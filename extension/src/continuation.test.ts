import { test } from 'node:test';
import assert from 'node:assert/strict';
import { continuationCommand, requireContinuationParent } from './continuation.js';
import type { HeadExposureBundle } from '../../src/editor/source-history.js';
import type { SourceDecompositionBundle } from '../../src/editor/source-decomposition.js';

const command = { type: 'statementlens.focusExposedPart', parentCaptureId: 'parent', previousCaptureId: 'seed', parentStepIndex: 0, path: [] };
// Only the host eligibility layer is under test here. Full records and receipts
// are validated separately by the server and shared exact model.
const sort = ['sort', ['zero']];
const result = { home: { arity: 0, telescope: ['nil'] }, term: ['app', sort, sort], type: sort };
const candidate = { status: 'candidate', result, checking: { status: 'completed' } };
const seed = { record: { captureId: 'seed', checking: { status: 'captured', action: { status: 'completed' }, exposure: candidate } } } as HeadExposureBundle;
const step = (kind: 'focus' | 'expose', replay = 'matched') => ({ operation: kind === 'focus' ? { kind, path: [] } : { kind, target: 'term' }, output: candidate, replay });
const attempt = (steps: unknown[]) => ({ record: { captureId: 'attempt', checking: { status: 'captured', action: { status: 'completed' }, steps } } }) as SourceDecompositionBundle;

test('strict continuation commands carry only dense paths or an exact target', () => {
  assert.deepEqual(continuationCommand(command).operation, { kind: 'focus', path: [] });
  for (const value of [
    { ...command, expectedSelected: {} }, { ...command, path: Array(65).fill('appArg') }, { ...command, path: new Array(1) },
    { ...command, path: ['metadata'] }, { ...command, parentStepIndex: 8 }, { ...command, parentStepIndex: 0.5 },
    { ...command, previousCaptureId: {} }, { ...command, target: 'term' },
    { type: 'statementlens.exposeFocusedHead', parentCaptureId: 'parent', previousCaptureId: 'attempt', parentStepIndex: 1, target: 'body' },
  ]) assert.throws(() => continuationCommand(value));
  const hidden = { ...command }; Object.defineProperty(hidden, 'secret', { value: 1 }); assert.throws(() => continuationCommand(hidden));
  const symbol = { ...command, [Symbol('field')]: true }; assert.throws(() => continuationCommand(symbol));
  let accessed = false; const accessor = { ...command }; Object.defineProperty(accessor, 'path', { get() { accessed = true; return []; }, enumerable: true });
  assert.throws(() => continuationCommand(accessor)); assert.equal(accessed, false);
  const dense = ['appArg']; const parsed = continuationCommand({ ...command, path: dense }); dense[0] = 'metadata';
  assert.deepEqual(parsed.operation, { kind: 'focus', path: ['appArg'] });
});

test('completion and matching gate continuation independently of verdicts and later failures', () => {
  const focus = continuationCommand(command);
  requireContinuationParent(seed, [], focus);
  assert.throws(() => requireContinuationParent({ record: { ...seed.record, checking: { status: 'unavailable' } } } as HeadExposureBundle, [], focus));
  const value = attempt([step('expose'), step('focus', 'new')]);
  const expose = continuationCommand({ type: 'statementlens.exposeFocusedHead', parentCaptureId: 'parent', previousCaptureId: 'attempt', parentStepIndex: 1, target: 'type' });
  requireContinuationParent(seed, [value], expose);
  assert.throws(() => requireContinuationParent(seed, [attempt([step('expose'), step('focus', 'mismatch')])], expose));
  assert.throws(() => requireContinuationParent(seed, [attempt([step('expose'), step('focus', 'not-compared')])], expose));
  const earlier = { ...focus, previousCaptureId: 'attempt' };
  requireContinuationParent(seed, [attempt([step('expose'), step('focus', 'mismatch')])], earlier);
  requireContinuationParent(seed, [value], { ...focus, previousCaptureId: 'attempt', parentStepIndex: 1 });
  const withVerdicts = structuredClone(value) as unknown as Record<string, any>;
  withVerdicts.record.checking.checks = [{ outcome: { tag: 'rejected' } }, { outcome: { tag: 'unknown' } }];
  requireContinuationParent(seed, [withVerdicts as SourceDecompositionBundle], expose);
});

test('retention, operation and total path bounds reject before a process begins', () => {
  const focus = continuationCommand(command), value = attempt([step('expose'), step('focus')]);
  assert.throws(() => requireContinuationParent(seed, Array(8).fill(value), focus), /Eight/);
  requireContinuationParent(seed, Array(7).fill(value), focus);
  const long = continuationCommand({ ...command, path: Array(64).fill('appArg') });
  const deep = structuredClone(seed);
  if (deep.record.checking.status !== 'captured' || deep.record.checking.exposure?.status !== 'candidate') throw Error('missing control');
  deep.record.checking.exposure.result.term = Array.from({length:64}).reduce<any>(body => ['app', ['sort', ['zero']], body], ['sort', ['zero']]);
  requireContinuationParent(deep, [], long, Array(64).fill('appArg'));
  assert.throws(() => requireContinuationParent(seed, [], continuationCommand({...command,path:['lamBody']})), /does not address/);
  const withPrior = attempt([step('expose'), { ...step('focus'), operation: { kind: 'focus', path: ['appArg'] } }, step('expose')]);
  assert.throws(() => requireContinuationParent(seed, [withPrior], { ...long, previousCaptureId: 'attempt', parentStepIndex: 2 }, Array(64).fill('appArg')), /total constructor-path/);
  const full = attempt(Array.from({ length: 8 }, (_, i) => step(i % 2 ? 'focus' : 'expose')));
  const expose = continuationCommand({ type: 'statementlens.exposeFocusedHead', parentCaptureId: 'parent', previousCaptureId: 'attempt', parentStepIndex: 7, target: 'term' });
  assert.throws(() => requireContinuationParent(seed, [full], expose), /eight operations/);
});

test('v2 commands select an original pair or actual retained catalogue without supplying terms', () => {
  const fields = { type: 'statementlens.inspectFields', parentCaptureId: 'parent', previousCaptureId: 'parent', parentStepIndex: 0 };
  const original = { captureId: 'parent', checking: { status: 'captured', action: { status: 'completed' }, selected: result } } as import('../../src/editor/source-occurrence.js').SourceOccurrence;
  requireContinuationParent(null, [], continuationCommand(fields), [], original);
  for (const extra of [{ catalogue: {} }, { index: 0 }, { path: [] }, { expectedSelected: result }]) assert.throws(() => continuationCommand({ ...fields, ...extra }));
  const project = { ...fields, type: 'statementlens.projectField', previousCaptureId: 'attempt', index: 0 };
  const listed = attempt([{ operation: { kind: 'fields' }, output: { ...candidate, catalogue: { fields: [{ index: 0 }] } }, replay: 'new' }]);
  requireContinuationParent(null, [listed], continuationCommand(project), [], original);
  assert.throws(() => requireContinuationParent(null, [], continuationCommand({ ...project, previousCaptureId: 'parent' }), [], original), /catalogue/);
  assert.throws(() => requireContinuationParent(null, [listed], continuationCommand({ ...project, index: 1 }), [], original), /catalogue/);
  for (const index of [-1, 16, 0.5, '0']) assert.throws(() => continuationCommand({ ...project, index }));
  assert.throws(() => requireContinuationParent(null, [listed], continuationCommand({ ...fields, parentCaptureId: 'other' }), [], original), /association/);
  assert.throws(() => requireContinuationParent(null, [], continuationCommand({ ...fields, parentStepIndex: 1 }), [], original), /original/);
});

test('v3 type and logical commands carry only scalar history identifiers', () => {
  const original = { captureId: 'parent', checking: { status: 'captured', action: { status: 'completed' }, selected: result } } as import('../../src/editor/source-occurrence.js').SourceOccurrence;
  for (const [type, kind] of [['statementlens.inspectTypeComponent', 'typeComponent'], ['statementlens.inspectLogicalStructure', 'logical']]) {
    const request = { type, parentCaptureId: 'parent', previousCaptureId: 'parent', parentStepIndex: 0 };
    const action = continuationCommand(request);
    assert.deepEqual(action.operation, { kind });
    requireContinuationParent(null, [], action, [], original);
    for (const extra of [{ term: sort }, { inferredType: sort }, { descriptor: {} }, { frames: [] }, { path: [] }, { index: 0 }]) {
      assert.throws(() => continuationCommand({ ...request, ...extra }));
    }
    let accessed = false;
    const accessor = { ...request };
    Object.defineProperty(accessor, 'type', { enumerable: true, get() { accessed = true; return type; } });
    assert.throws(() => continuationCommand(accessor));
    assert.equal(accessed, false);
    assert.throws(() => requireContinuationParent(null, [], { ...action, parentCaptureId: 'other' }, [], original), /association/);
  }
});

test('v3 reserves four checks per logical step, uses the chosen prefix and counts a legacy seed once', () => {
  const logical = () => ({ operation: { kind: 'logical' }, output: candidate, replay: 'matched' });
  const action = continuationCommand({ type: 'statementlens.inspectLogicalStructure', parentCaptureId: 'parent', previousCaptureId: 'attempt', parentStepIndex: 4 });
  // Six non-forall inspections actually use fewer checks, but reserve 6 + 6*4 = 30.
  requireContinuationParent(null, [attempt(Array.from({ length: 5 }, logical))], action);
  const six = attempt(Array.from({ length: 6 }, logical));
  assert.throws(() => requireContinuationParent(null, [six], { ...action, parentStepIndex: 5 }), /reserved thirty-check/);
  requireContinuationParent(null, [six], action);
  const legacyPrefix = attempt([step('expose'), ...Array.from({ length: 4 }, logical),
    { operation: { kind: 'typeComponent' }, output: candidate, replay: 'matched' }]);
  const expose = continuationCommand({ type: 'statementlens.exposeFocusedHead', parentCaptureId: 'parent', previousCaptureId: 'attempt', parentStepIndex: 5, target: 'term' });
  // 6 + 3 + 4*4 + 2 + 3 = 30; the exposure already appears in the retained prefix.
  requireContinuationParent(seed, [legacyPrefix], expose);
});
