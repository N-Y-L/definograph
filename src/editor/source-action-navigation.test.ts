import { describe, expect, it } from 'vitest';
import { followSourceStatus, sourceActionResultAnchor, type PendingSourceAction, type SourceActionResult } from './source-action-navigation';

const ORIGIN = 'c52c05ff-d114-4a9e-84cd-353f895a06e9', FRESH = '77b5bb42-0000-4000-8000-000000000001';
const PREVIOUS = 'ad5b470c-0000-4000-8000-000000000002', EARLIER = '117cf9d7-0000-4000-8000-000000000003';
const attempt = (previousCaptureId: string, parentStepIndex: number) => ({ record: { parentCaptureId: ORIGIN, previousCaptureId, parentStepIndex } });
// Three retained attempts; the user continues from step 3 (index 2) of the last one.
const history = [attempt(ORIGIN, 0), attempt(EARLIER, 0), attempt(EARLIER, 1)];
const continuation = (requestId?: string, attemptsBefore = history.length): PendingSourceAction =>
  ({ request: { kind: 'continuation', parentCaptureId: ORIGIN, previousCaptureId: PREVIOUS, parentStepIndex: 2, attemptsBefore }, requestId });
const answer = (extra: Partial<SourceActionResult>): SourceActionResult => ({ requestId: '5', sourceSnapshot: {}, sourceSnapshotOrigin: { captureId: ORIGIN }, ...extra });

describe('explicit source action lifecycle', () => {
  it('binds a posted action to the first analyzing status and keeps it for a repeated status', () => {
    const bound = followSourceStatus(continuation(), { requestId: '5', phase: 'analyzing' });
    expect(bound?.requestId).toBe('5');
    expect(followSourceStatus(bound, { requestId: '5', phase: 'analyzing' })).toBe(bound);
  });
  it('drops the action when another request supersedes it or the capture becomes stale', () => {
    expect(followSourceStatus(continuation('5'), { requestId: '6', phase: 'analyzing' })).toBeNull();
    expect(followSourceStatus(continuation('5'), { requestId: '5', phase: 'stale' })).toBeNull();
    expect(followSourceStatus(continuation(), { requestId: '5', phase: 'stale' })).toBeNull();
    expect(followSourceStatus(null, { requestId: '5', phase: 'analyzing' })).toBeNull();
  });
});

describe('answer to an explicit continuation', () => {
  it('shows the new attempt, including a stopped one, when exactly one attempt continues the requested step', () => {
    expect(sourceActionResultAnchor(continuation('5'), answer({ decompositions: [...history, attempt(PREVIOUS, 2)] }))).toBe('attempt');
  });
  it('shows the explicit unavailable notice when the history is unchanged', () => {
    const refused = answer({ decompositions: history, decompositionUnavailable: 'This result exceeds the retained-history limits (16 MiB total).' });
    expect(sourceActionResultAnchor(continuation('5'), refused)).toBe('continuation-unavailable');
  });
  it('does not mistake an earlier attempt with the same parent step for the answer', () => {
    const repeated = [...history, attempt(PREVIOUS, 2)];
    const pending = continuation('5', repeated.length);
    expect(sourceActionResultAnchor(pending, answer({ decompositions: repeated, decompositionUnavailable: 'refused' }))).toBe('continuation-unavailable');
    expect(sourceActionResultAnchor(pending, answer({ decompositions: repeated }))).toBeNull();
  });
  it('ignores results of other requests, fresh captures and host errors without a record', () => {
    const answered = { decompositions: [...history, attempt(PREVIOUS, 2)] };
    expect(sourceActionResultAnchor(continuation('5'), { ...answer(answered), requestId: '6' })).toBeNull();
    expect(sourceActionResultAnchor(continuation(), answer(answered))).toBeNull();
    expect(sourceActionResultAnchor(null, answer(answered))).toBeNull();
    expect(sourceActionResultAnchor(continuation('5'), answer({ ...answered, sourceSnapshotOrigin: { captureId: FRESH } }))).toBeNull();
    expect(sourceActionResultAnchor(continuation('5'), { requestId: '5' })).toBeNull();
  });
});

describe('answer to other explicit source actions', () => {
  const exposure: PendingSourceAction = { request: { kind: 'head-exposure', parentCaptureId: ORIGIN }, requestId: '5' };
  const occurrence: PendingSourceAction = { request: { kind: 'occurrence', parentCaptureId: ORIGIN, path: ['appArg', 'lamBody'] }, requestId: '5' };
  it('shows a definition-head exposure or its unavailable notice for the same parent capture only', () => {
    expect(sourceActionResultAnchor(exposure, answer({ headExposure: {} }))).toBe('head-exposure');
    expect(sourceActionResultAnchor(exposure, answer({ headExposureUnavailable: 'unsupported' }))).toBe('head-exposure-unavailable');
    expect(sourceActionResultAnchor(exposure, answer({ headExposure: {}, sourceSnapshotOrigin: { captureId: FRESH } }))).toBeNull();
  });
  it('shows a checked occurrence only for the requested parent and path', () => {
    const fresh = { sourceSnapshotOrigin: { captureId: FRESH } };
    expect(sourceActionResultAnchor(occurrence, answer({ ...fresh, sourceOccurrence: { parentCaptureId: ORIGIN, path: ['appArg', 'lamBody'] } }))).toBe('occurrence');
    expect(sourceActionResultAnchor(occurrence, answer({ ...fresh, sourceOccurrence: { parentCaptureId: ORIGIN, path: ['appArg'] } }))).toBeNull();
    expect(sourceActionResultAnchor(occurrence, answer({ ...fresh, sourceOccurrence: { parentCaptureId: FRESH, path: ['appArg', 'lamBody'] } }))).toBeNull();
    expect(sourceActionResultAnchor(occurrence, answer({ ...fresh, sourceOccurrenceUnavailable: 'unsupported position' }))).toBe('occurrence-unavailable');
    expect(sourceActionResultAnchor(occurrence, { requestId: '5', sourceOccurrenceUnavailable: 'no snapshot' })).toBeNull();
  });
});
