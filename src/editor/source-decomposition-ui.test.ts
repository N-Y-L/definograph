import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { initial, firstFocus, append, record as nextRecord, errorStop } from './source-decomposition-chain.test-fixtures';
import { validateSourceDecomposition, type SourceDecompositionBundle } from './source-decomposition';
import type { SourceSnapshotOrigin } from './source-origin';
import type { JsonObject, JsonValue } from '../packets/packet';
import type { HeadExposureCandidate } from './source-head-exposure';
import { parseEditorMessage, retainedDecompositionHistory, type HeadExposureBundle } from './host';
import { SOURCE_PRESENTATION_SCHEMA, SOURCE_PRESENTATION_NOTE } from './source-presentation';
import { assertSourceHistoryLimit, MAX_SOURCE_HISTORY_BYTES } from './source-history';
import { SourceSnapshotReading, savedSourceSnapshot } from './SourceSnapshotReading';
import { SourceDecompositionReading, canContinueDecompositionStep } from './SourceDecompositionReading';
import { SourceHeadExposureReading } from './SourceHeadExposureReading';

const document = { uri: 'file:///control.lean', fileName: '/control.lean', version: 3,
  selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } };
const origin = (captureId: string): SourceSnapshotOrigin => ({ kind: 'local-editor-process-snapshot', captureId, sourceSha256: '0'.repeat(64),
  engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
  project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
  document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' });
const object = (v: unknown) => v as JsonObject;
const array = (v: unknown) => v as JsonValue[];
function fixture() {
  const base = initial(), raw = firstFocus(base.history), decomposition = validateSourceDecomposition(raw, base.snapshot, base.history);
  const seed: HeadExposureBundle = { snapshot: base.snapshot, origin: origin(base.seed.captureId), record: base.seed };
  const first: SourceDecompositionBundle = { snapshot: base.snapshot, origin: origin(decomposition.captureId), record: decomposition };
  const message = { type: 'statementlens.error', requestId: '4', document, message: 'Guided source export unavailable.',
    sourceSnapshot: base.snapshot, sourceSnapshotOrigin: origin(base.history.occurrence.captureId), sourceOccurrence: base.history.occurrence,
    headExposure: seed, decompositions: [first] };
  return { ...base, raw, first, seed, message };
}
function secondExposure() {
  const f = fixture(), history = append(f.history, f.raw), checking = f.first.record.checking;
  if (checking.status !== 'captured' || checking.steps[1].output.status !== 'candidate') throw Error('missing control');
  const pair = checking.steps[1].output.result, name: JsonValue = ['str', ['anonymous'], 'Nat'];
  const carrier: JsonValue = ['sort', ['succ', ['zero']]], carrierSort: JsonValue = ['succ', ['succ', ['zero']]];
  const exposed: JsonValue = ['const', ['str', ['anonymous'], 'ExpandedNat'], []];
  const output: HeadExposureCandidate = { status: 'candidate', before: pair.type, result: { home: pair.home, term: exposed, type: carrier },
    definition: { name, levelParams: [], type: carrier, value: exposed, hints: ['abbrev'], safety: 'safe' },
    actualLevels: [], arguments: [], betaApplications: 0, carrierSort, checking: { status: 'completed' } };
  const raw = nextRecord(history, { kind: 'expose', target: 'type' }, output, { previous: f.first.record.captureId, index: 1 });
  const record = validateSourceDecomposition(raw, f.snapshot, history);
  const second: SourceDecompositionBundle = { snapshot: f.snapshot, origin: origin(record.captureId), record };
  return { ...f, second, secondRaw: raw, history };
}

describe('continuation host, retention and reading', () => {
  it('admits optional text only beside decomposition records and preserves raw branded histories on rejection', () => {
    const f = secondExposure(), checking = f.second.record.checking;
    if (checking.status !== 'captured' || checking.steps[2].output.status !== 'candidate') throw Error('Missing fixture.');
    const presentation = { schema: SOURCE_PRESENTATION_SCHEMA, captureId: f.second.record.captureId, status: 'available',
      stepIndex: 2, target: 'type', result: checking.steps[2].output.result, text: '<script>ExpandedNat</script>' };
    const exact = JSON.stringify(f.second.record);
    for (const sidecar of [presentation, { ...presentation, target: 'term' }, { ...presentation, text: 'x'.repeat(200_000) }, { ...presentation, extra: true }]) {
      const parsed = parseEditorMessage({ ...f.message, decompositions: [f.first, { ...f.second, presentation: sidecar }] });
      if (!parsed || parsed.type === 'statementlens.status' || !parsed.decompositions) throw Error('Lost valid raw history.');
      const bundle = parsed.decompositions[1], history = retainedDecompositionHistory(parsed.decompositions);
      expect(JSON.stringify(bundle.record)).toBe(exact); expect(history?.attempts[1].record).toBe(bundle.record);
      expect(bundle.presentation?.status).toBe(sidecar === presentation ? 'available' : 'unavailable');
      expect(Object.isFrozen(bundle.presentation)).toBe(true);
      const html = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: parsed.decompositions }));
      if (sidecar === presentation) { expect(html).toContain('&lt;script&gt;ExpandedNat&lt;/script&gt;'); expect(html).toContain(SOURCE_PRESENTATION_NOTE); expect(html).not.toContain('<script>'); }
      else expect(html).toContain('Readable Lean text was rejected');
    }
    expect(parseEditorMessage({ ...f.message, headExposure: { ...f.seed, presentation } })).toBeUndefined();
    expect(parseEditorMessage({ ...f.message, decompositions: [{ ...f.first, extra: true }] })).toBeUndefined();
    const extended = [f.first]; Object.assign(extended, { extra: true });
    expect(parseEditorMessage({ ...f.message, decompositions: extended })).toBeUndefined();
    const accessor = [f.first]; Object.defineProperty(accessor, 0, { get: () => { throw Error('Must not invoke'); }, enumerable: true });
    expect(parseEditorMessage({ ...f.message, decompositions: accessor })).toBeUndefined();
  });
  it('validates ordered bundles with separate immutable original and fresh origins', () => {
    const f = secondExposure(), message = { ...f.message, decompositions: [f.first, f.second] }, parsed = parseEditorMessage(message);
    expect(parsed?.type).toBe('statementlens.error');
    if (!parsed || parsed.type === 'statementlens.status') throw Error('missing response');
    expect(parsed.sourceOccurrence).toEqual(f.parent.occurrence); expect(parsed.headExposure).toEqual(f.seed);
    expect(parsed.decompositions).toEqual([f.first, f.second]);
    expect(Object.isFrozen(parsed.decompositions)).toBe(true); expect(Object.isFrozen(parsed.decompositions?.[1].origin.engine)).toBe(true);
    for (const mutate of [
      (v: typeof message) => { v.decompositions.reverse(); },
      (v: typeof message) => { v.decompositions[1].origin.sourceSha256 = 'f'.repeat(64); },
      (v: typeof message) => { v.decompositions[1].origin.captureId = v.decompositions[0].origin.captureId; },
      (v: typeof message) => { v.decompositions[1].origin.project.libraryPaths.push('/other'); },
      (v: typeof message) => { v.decompositions[1].record.parentStepIndex = 0; },
      (v: typeof message) => { const c = v.decompositions[1].record.checking; if (c.status === 'captured') c.checks[0].envAfter = 2; },
    ]) { const changed = structuredClone(message); mutate(changed); expect(parseEditorMessage(changed)).toBeUndefined(); }
    expect(parseEditorMessage({ ...message, headExposure: undefined })).toBeUndefined();
    const sparse = structuredClone(message); delete sparse.decompositions[0]; expect(parseEditorMessage(sparse)).toBeUndefined();
  });

  it('keeps original, seed and intermediate checks while exposing a real focused pair', () => {
    const f = fixture(); let calls = 0;
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: f.snapshot, origin: f.message.sourceSnapshotOrigin,
      occurrence: f.parent.occurrence, headExposure: f.seed, decompositions: [f.first], onContinue: () => { calls++; } }));
    expect(html).toContain('6 kernel outcomes retained'); expect(html).toContain('9 fresh kernel outcomes retained');
    expect(html).toContain('11 fresh kernel outcomes retained'); expect(html).toContain('Step 2 · Check part');
    expect(html).toContain('Expose definition head of term'); expect(html).toContain('Inferred type');
    expect(html).toContain('3 declarations'); expect(html).toContain('Exact input pair'); expect(calls).toBe(0);
    const saved = savedSourceSnapshot(f.snapshot, f.message.sourceSnapshotOrigin, f.parent.occurrence, f.seed, undefined, [f.first]);
    expect(saved.version).toBe(4); expect(saved.provenance).toBe('unverified-saved-record');
    expect(saved.decompositions).toEqual([f.first]); expect(saved.headExposure).toEqual(f.seed);
    expect(saved.occurrence).toEqual(f.parent.occurrence);
    const readOnly = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: f.snapshot, occurrence: f.parent.occurrence,
      headExposure: f.seed, decompositions: [f.first], onContinue: () => { calls++; } }));
    expect(readOnly).toContain('unverified origin'); expect(readOnly).not.toContain('Check chosen part');
    expect(readOnly).not.toContain('Expose definition head of term'); expect(calls).toBe(0);
  });

  it('offers result-term choice after type exposure and keeps the type annotation separate', () => {
    const f = secondExposure(); let calls = 0;
    const html = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [f.first, f.second], currentOrigin: true, onContinue: () => { calls++; } }));
    expect(html).toContain('attempt 1, step 2'); expect(html).toContain('Step 3 · Expose type');
    expect(html).toContain('Exposed type'); expect(html).toContain('Check chosen part');
    expect(html).toContain('No eligible part chosen'); expect(html).toContain('disabled=""');
    expect(html).toContain('Earlier continuations and current attempt (2)'); expect(calls).toBe(0);
    const before = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle: f.seed, original: f.parent.occurrence,
      initialSide: 'before', onFocusExposedPart: () => { calls++; } }));
    expect(before).not.toContain('Check chosen part'); expect(calls).toBe(0);
  });

  it('makes partial and mismatching candidates inspectable while retaining earlier eligible steps', () => {
    const f = fixture(), raw = structuredClone(f.raw); errorStop(raw, 1, 1);
    const record = validateSourceDecomposition(raw, f.snapshot, f.history);
    const bundle = { ...f.first, record };
    expect(canContinueDecompositionStep(record, 0)).toBe(true); expect(canContinueDecompositionStep(record, 1)).toBe(false);
    const html = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [bundle], onContinue: () => {} }));
    expect(html).toContain('callback failed'); expect(html).toContain('Checked part');
    expect(html).not.toContain('Expose definition head of term'); expect(html).toContain('Focused context');
    const mismatch = structuredClone(f.first.record);
    if (mismatch.checking.status !== 'captured') throw Error('missing checks');
    mismatch.checking.steps[1].replay = 'mismatch';
    // Rendering is independent of admission; the model suite checks complete mismatch records.
    expect(canContinueDecompositionStep(mismatch, 1)).toBe(false);
    expect(renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [{ ...f.first, record: mismatch }], onContinue: () => {} }))).toContain('This result changed');
  });

  it.each(['unknown', 'rejected'] as const)('keeps completed child actions after an earlier %s check', verdict => {
    const f = fixture(), raw = structuredClone(f.raw), check = object(raw.checking), checks = array(check.checks), audits = array(check.audits);
    object(checks[1]).outcome = verdict === 'unknown' ? { tag: 'unknown', message: 'timeout' } : { tag: 'rejected', kind: 'notConvertible' };
    object(checks[1]).envAfter = 1; object(audits[1]).result = { tag: 'unavailable', reason: 'declaration was not installed' };
    for (let i = 1; i < checks.length; i++) { object(audits[i]).environment = i; if (i > 1) { object(checks[i]).envBefore = i - 1; object(checks[i]).envAfter = i; } }
    check.environmentSnapshotCount = checks.length;
    const record = validateSourceDecomposition(raw, f.snapshot, f.history);
    expect(canContinueDecompositionStep(record, 1)).toBe(true);
    const html = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [{ ...f.first, record }], currentOrigin: true, onContinue: () => {} }));
    expect(html).toContain(`<span>${verdict}</span>`); expect(html).toContain('Expose definition head of term');
  });

  it('preserves history on an omission and enforces exact aggregate limits', () => {
    const f = fixture();
    expect(parseEditorMessage({ ...f.message, decompositionUnavailable: 'The output limit was reached.' })).toBeDefined();
    expect(parseEditorMessage({ ...f.message, decompositionUnavailable: 'x'.repeat(4097) })).toBeUndefined();
    const text = 'x'.repeat(MAX_SOURCE_HISTORY_BYTES - 2);
    expect(() => assertSourceHistoryLimit(text)).not.toThrow();
    expect(() => assertSourceHistoryLimit(text + 'x')).toThrow(/limit/);
    expect(() => assertSourceHistoryLimit(text, 20 * 1024)).toThrow(/limit/);
  });
});
