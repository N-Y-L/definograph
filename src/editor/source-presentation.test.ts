import { describe, expect, it } from 'vitest';
import type { JsonValue } from '../packets/packet';
import { initial, firstFocus, append, record as nextRecord } from './source-decomposition-chain.test-fixtures';
import { validateSourceDecomposition, type SourceDecompositionBundle } from './source-decomposition';
import { sourceSnapshotValidation } from './source-snapshot';
import { sanitizeSourcePresentation, sourceResultPresentation, fitSourcePresentationHistory, SOURCE_PRESENTATION_SCHEMA, SOURCE_PRESENTATION_BYTES } from './source-presentation';

function fixture() {
  const base = initial(), history = append(base.history, firstFocus(base.history));
  const first = history.attempts[0].record;
  if (first.checking.status !== 'captured' || first.checking.steps[1].output.status !== 'candidate') throw Error('Missing fixture result.');
  const pair = first.checking.steps[1].output.result;
  const carrier: JsonValue = ['sort', ['succ', ['zero']]], exposed: JsonValue = ['const', ['str', ['anonymous'], 'ExpandedNat'], []];
  const output = { status: 'candidate', before: pair.type, result: { home: pair.home, term: exposed, type: carrier },
    definition: { name: ['str', ['anonymous'], 'Nat'], levelParams: [], type: carrier, value: exposed, hints: ['abbrev'], safety: 'safe' },
    actualLevels: [], arguments: [], betaApplications: 0, carrierSort: ['succ', ['succ', ['zero']]], checking: { status: 'completed' } };
  const record = validateSourceDecomposition(nextRecord(history, { kind: 'expose', target: 'type' }, output,
    { previous: first.captureId, index: 1 }), base.snapshot, history);
  const presentation = { schema: SOURCE_PRESENTATION_SCHEMA, captureId: record.captureId, status: 'available',
    stepIndex: 2, target: 'type', result: structuredClone(output.result), text: 'ExpandedNat' };
  return { record, first, presentation, snapshot: base.snapshot };
}

describe('optional source result presentation', () => {
  it('associates only the last exposure, retaining its result term even for a type exposure', () => {
    const f = fixture(), bytes = JSON.stringify(f.record), checked = sanitizeSourcePresentation(f.presentation, f.record);
    expect(checked?.status).toBe('available'); expect(checked).toEqual(f.presentation);
    if (checked?.status !== 'available' || f.record.checking.status !== 'captured') throw Error('Missing presentation.');
    expect(checked.result).toBe((f.record.checking.steps[2].output as { result: unknown }).result);
    expect(Object.isFrozen(checked)).toBe(true); expect(Object.isFrozen(checked.result.home)).toBe(true);
    expect(JSON.stringify(f.record)).toBe(bytes);
    expect(sourceResultPresentation(f.record, 0, checked).status).toBe('unavailable');
    expect(sanitizeSourcePresentation(f.presentation, structuredClone(f.record))?.status).toBe('unavailable');
    expect(sanitizeSourcePresentation(undefined, f.record)).toBeUndefined();
    expect(sourceResultPresentation(f.record, 2, undefined)).toMatchObject({ status: 'unavailable', reason: expect.stringContaining('not retained') });
  });

  const malformed: [string, (v: ReturnType<typeof fixture>['presentation']) => unknown][] = [
    ['stale capture', v => ({ ...v, captureId: '550e8400-e29b-41d4-a716-446655440099' })],
    ['earlier step', v => ({ ...v, stepIndex: 0 })], ['wrong target', v => ({ ...v, target: 'term' })],
    ['extra presentation', v => ({ ...v, presentations: [v] })], ['array of presentations', v => [v]],
    ['wrong term', v => ({ ...v, result: { ...v.result, term: v.result.type } })],
    ['wrong type', v => ({ ...v, result: { ...v.result, type: v.result.term } })],
    ['wrong home', v => ({ ...v, result: { ...v.result, home: { ...v.result.home, arity: 0 } } })],
    ['extra result key', v => ({ ...v, result: { ...v.result, extra: true } })],
    ['extra home key', v => ({ ...v, result: { ...v.result, home: { ...v.result.home, extra: true } } })],
    ['oversized text', v => ({ ...v, text: 'x'.repeat(8193) })],
    ['oversized Unicode text', v => ({ ...v, text: '𝒙'.repeat(8193) })],
    ['oversized envelope', v => ({ ...v, result: { ...v.result, term: 'x'.repeat(SOURCE_PRESENTATION_BYTES) } })],
    ['null control', v => ({ ...v, text: 'x\0y' })], ['carriage return', v => ({ ...v, text: 'x\ry' })],
    ['bidi override', v => ({ ...v, text: 'x\u202ey' })], ['C1 control', v => ({ ...v, text: 'x\u0085y' })],
    ['unpaired surrogate', v => ({ ...v, text: '\ud800' })], ['empty text', v => ({ ...v, text: ' \n\t' })],
    ['accessor', v => Object.defineProperty({ ...v }, 'text', { get: () => { throw Error('Must not invoke'); }, enumerable: true })],
    ['symbol property', v => ({ ...v, [Symbol('extra')]: true })],
    ['non-enumerable property', v => Object.defineProperty({ ...v }, 'extra', { value: true })],
    ['cyclic data', v => { const result = { ...v } as Record<string, unknown>; result.extra = result; return result; }],
  ];
  it.each(malformed)('rejects %s locally without changing exact record', (_name, change) => {
    const f = fixture(), before = JSON.stringify(f.record);
    expect(sanitizeSourcePresentation(change(f.presentation), f.record)).toMatchObject({ captureId: f.record.captureId, status: 'unavailable', reason: expect.stringContaining('rejected') });
    expect(JSON.stringify(f.record)).toBe(before);
  });
  it('accepts exactly bounded Unicode and printer layout as text', () => {
    const f = fixture();
    for (const text of ['𝒙'.repeat(8192), 'fun x =>\n\tx', '<script>alert("x")</script>'])
      expect(sanitizeSourcePresentation({ ...f.presentation, text }, f.record)).toMatchObject({ status: 'available', text });
  });
  it('retains bounded native unavailability and rejects invalid reasons', () => {
    const f = fixture(), unavailable = { schema: SOURCE_PRESENTATION_SCHEMA, captureId: f.record.captureId, status: 'unavailable', reason: 'Printer budget exceeded.' };
    expect(sanitizeSourcePresentation(unavailable, f.record)).toEqual(unavailable);
    for (const reason of ['', 'x'.repeat(513), 'x\ny'])
      expect(sanitizeSourcePresentation({ ...unavailable, reason }, f.record)).toMatchObject({ status: 'unavailable', reason: expect.stringContaining('rejected') });
    expect(sanitizeSourcePresentation({ ...f.presentation, captureId: f.first.captureId }, f.first)?.status).toBe('unavailable');
  });
  it('counts display bytes and preserves all exact attempts when aggregate display cost must be removed', () => {
    const f = fixture(), presentation = sanitizeSourcePresentation({ ...f.presentation, text: 'x'.repeat(8192) }, f.record)!;
    // The origin is irrelevant to this aggregate-size control; host tests check it independently.
    const raw: SourceDecompositionBundle = { snapshot: f.snapshot, record: f.record, origin: {} as SourceDecompositionBundle['origin'] };
    const bundles = [{ ...raw, presentation }], bytes = new TextEncoder().encode(JSON.stringify([raw])).length;
    const before = JSON.stringify(bundles);
    const within = (limit: number) => (entries: SourceDecompositionBundle[]) => sourceSnapshotValidation.preflight(entries, limit, ['history']);
    expect(fitSourcePresentationHistory(bundles, within(bytes + 10_000))).toBe(bundles);
    const fallback = fitSourcePresentationHistory(bundles, within(bytes + 1000));
    expect(fallback[0].presentation).toMatchObject({ status: 'unavailable', reason: expect.stringContaining('retained-history display budget') });
    expect(fallback[0].record).toBe(raw.record); expect(fallback[0].snapshot).toBe(raw.snapshot);
    const exactOnly = fitSourcePresentationHistory(bundles, within(bytes));
    expect(exactOnly).toEqual([raw]); expect(exactOnly[0].record).toBe(raw.record);
    expect(() => fitSourcePresentationHistory(bundles, within(bytes - 1))).toThrow(/limit/);
    expect(() => fitSourcePresentationHistory(bundles, () => { throw Error('Unrelated raw failure'); })).toThrow('Unrelated raw failure');
    expect(JSON.stringify(bundles)).toBe(before);
  });
});
