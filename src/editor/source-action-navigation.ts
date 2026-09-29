import type { SourceOccurrenceStep } from './source-occurrence';

/** An explicit inspection posted by this webview, kept only until the host answers it.
 * The posted request itself is unchanged; this record is local to the webview. */
export type SourceActionRequest =
  | { kind: 'continuation'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number; attemptsBefore: number }
  | { kind: 'head-exposure'; parentCaptureId: string }
  | { kind: 'occurrence'; parentCaptureId: string; path: readonly SourceOccurrenceStep[] };
export interface PendingSourceAction { request: SourceActionRequest; requestId?: string }
/** Where the answer to an explicit action is shown. Each value names one `data-source-result` element. */
export type SourceResultAnchor = 'attempt' | 'continuation-unavailable' | 'head-exposure' | 'head-exposure-unavailable' | 'occurrence' | 'occurrence-unavailable';
/** The parts of an accepted host result that identify what it answers. */
export interface SourceActionResult {
  requestId: string;
  sourceSnapshot?: unknown;
  sourceSnapshotOrigin?: { captureId: string };
  sourceOccurrence?: { parentCaptureId: string; path: readonly SourceOccurrenceStep[] };
  sourceOccurrenceUnavailable?: string;
  headExposure?: unknown;
  headExposureUnavailable?: string;
  decompositions?: readonly { record: { parentCaptureId: string; previousCaptureId: string; parentStepIndex: number } }[];
  decompositionUnavailable?: string;
}

/** The host posts one `analyzing` status for an accepted action before any Lean work.
 * A pending action binds to the first such status. Any other accepted status means the
 * request was refused before it started, superseded or made stale, so it is dropped. */
export function followSourceStatus(pending: PendingSourceAction | null, status: { requestId: string; phase: string }): PendingSourceAction | null {
  if (!pending || status.phase !== 'analyzing') return null;
  if (pending.requestId === undefined) return { ...pending, requestId: status.requestId };
  return pending.requestId === status.requestId ? pending : null;
}

/** The element to show after an accepted result, or null when the result does not answer
 * the pending action: another request, a fresh capture, or no record of this action. */
export function sourceActionResultAnchor(pending: PendingSourceAction | null, result: SourceActionResult): SourceResultAnchor | null {
  if (!pending || pending.requestId !== result.requestId) return null;
  const request = pending.request;
  if (request.kind === 'occurrence') {
    const occurrence = result.sourceOccurrence;
    if (occurrence) return occurrence.parentCaptureId === request.parentCaptureId && occurrence.path.length === request.path.length
      && occurrence.path.every((step, index) => step === request.path[index]) ? 'occurrence' : null;
    return result.sourceSnapshot !== undefined && typeof result.sourceOccurrenceUnavailable === 'string' ? 'occurrence-unavailable' : null;
  }
  // Continuations and exposures keep the parent capture's identity in their answer.
  if (result.sourceSnapshotOrigin?.captureId !== request.parentCaptureId) return null;
  if (request.kind === 'head-exposure')
    return result.headExposure !== undefined ? 'head-exposure' : typeof result.headExposureUnavailable === 'string' ? 'head-exposure-unavailable' : null;
  const attempts = result.decompositions ?? [], added = attempts.length === request.attemptsBefore + 1 ? attempts.at(-1)?.record : undefined;
  if (added && added.parentCaptureId === request.parentCaptureId && added.previousCaptureId === request.previousCaptureId
    && added.parentStepIndex === request.parentStepIndex) return 'attempt';
  return typeof result.decompositionUnavailable === 'string' ? 'continuation-unavailable' : null;
}

/** Scrolls the open drawer so the answer sits just below its sticky heading and moves keyboard
 * focus there. Does nothing when the drawer or its source-data view is no longer shown. */
export function revealSourceResult(anchor: SourceResultAnchor): boolean {
  const target = document.querySelector<HTMLElement>(`[data-source-result="${anchor}"]`);
  const drawer = target?.closest<HTMLElement>('.atlas-drawer');
  if (!target || !drawer) return false;
  const heading = drawer.querySelector<HTMLElement>('.drawer-heading');
  const offset = target.getBoundingClientRect().top - drawer.getBoundingClientRect().top + drawer.scrollTop;
  drawer.scrollTop = Math.max(0, offset - (heading?.offsetHeight ?? 0) - 12);
  target.focus({ preventScroll: true });
  return true;
}
