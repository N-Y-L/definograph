import { assertSourceHistoryLimit, type HeadExposureBundle } from './source-history';
import type { Analysis } from '../core';
import { validateSourceSnapshot, type SourceSnapshot } from './source-snapshot';
import { isSourceSnapshotOrigin, type SourceSnapshotOrigin } from './source-origin';
import { validateSourceOccurrence, type SourceOccurrence, type SourceOccurrenceStep } from './source-occurrence';
import { validateSourceHeadExposure, type HeadExposureTarget } from './source-head-exposure';
import { validateDecompositionHistory, type DecompositionHistory, type SourceDecompositionBundle } from './source-decomposition';
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { GUIDED_CONTEXT_CONTRACT, GUIDED_CONTEXT_MISMATCH } from './guided-context-contract';
import { sanitizeSourcePresentation, fitSourcePresentationHistory } from './source-presentation';

export interface EditorPosition { line: number; character: number }
export interface EditorRange { start: EditorPosition; end: EditorPosition }
export interface EditorDocument {
  uri: string;
  version: number;
  fileName: string;
  selection: EditorRange;
}
export type { HeadExposureBundle } from './source-history';
interface SourceAttachment {
  sourceSnapshot?: SourceSnapshot;
  sourceSnapshotOrigin?: SourceSnapshotOrigin;
  sourceSnapshotUnavailable?: string;
  sourceOccurrence?: SourceOccurrence;
  sourceOccurrenceUnavailable?: string;
  headExposure?: HeadExposureBundle;
  headExposureUnavailable?: string;
  decompositions?: SourceDecompositionBundle[];
  decompositionUnavailable?: string;
}
export type EditorMessage =
  | { type: 'statementlens.status'; requestId: string; phase: 'analyzing' | 'idle' | 'stale'; document: EditorDocument }
  | ({ type: 'statementlens.analysis'; requestId: string; document: EditorDocument; analysis: Analysis } & SourceAttachment)
  | ({ type: 'statementlens.error'; requestId: string; document: EditorDocument; message: string; code?: string; source?: string } & SourceAttachment);
export type EditorCommand = { type: 'statementlens.ready'; guidedContextContract: typeof GUIDED_CONTEXT_CONTRACT } | { type: 'statementlens.refresh'; expansion?: { constants: string[]; maxDepth: number } } | { type: 'statementlens.reveal'; range?: EditorRange }
  | { type: 'statementlens.checkOccurrence'; parentCaptureId: string; path: SourceOccurrenceStep[] }
  | { type: 'statementlens.exposeDefinitionHead'; parentCaptureId: string; target: HeadExposureTarget }
  | { type: 'statementlens.focusExposedPart'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number; path: SourceOccurrenceStep[] }
  | { type: 'statementlens.exposeFocusedHead'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number; target: HeadExposureTarget }
  | { type: 'statementlens.inspectTypeComponent'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number }
  | { type: 'statementlens.inspectLogicalStructure'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number }
  | { type: 'statementlens.inspectFields'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number }
  | { type: 'statementlens.projectField'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number; index: number };
export interface EditorHost { postMessage(message: EditorCommand): void }
declare global { interface Window { acquireVsCodeApi?: () => EditorHost } }
let acquiredHost: EditorHost | undefined;
export function getEditorHost(): EditorHost | undefined {
  if (typeof window === 'undefined' || !window.acquireVsCodeApi) return undefined;
  return acquiredHost ??= window.acquireVsCodeApi();
}

const record = (value: unknown): value is Record<string, unknown> => !!value && typeof value === 'object' && !Array.isArray(value);
/** Process-local witness: the validator-registered history behind the exact bundle array this parser produced.
 * Copies, saved data and hand-built arrays have none, so they can never acquire live provenance authority. */
const retainedHistories = new WeakMap<readonly SourceDecompositionBundle[], DecompositionHistory>();
export function retainedDecompositionHistory(decompositions: readonly SourceDecompositionBundle[]): DecompositionHistory | undefined {
  return retainedHistories.get(decompositions);
}
const position = (value: unknown): value is EditorPosition => record(value) && Number.isSafeInteger(value.line) && Number(value.line) >= 0 && Number.isSafeInteger(value.character) && Number(value.character) >= 0;
export { MAX_SOURCE_HISTORY_BYTES, assertSourceHistoryLimit } from './source-history';
function sameOriginInput(fresh: SourceSnapshotOrigin, original: SourceSnapshotOrigin): boolean {
  const { canonical } = createExactJsonTools();
  const same = (a: unknown, b: unknown) => canonical(a as JsonValue) === canonical(b as JsonValue);
  return fresh.sourceSha256 === original.sourceSha256 && same(fresh.engine, original.engine)
    && same(fresh.project, original.project) && same(fresh.document, original.document) && same(fresh.selection, original.selection);
}
function checkedBundle(value: unknown, original: SourceSnapshotOrigin, seen: Set<string>, allowPresentation = false) {
  const keys = record(value) && allowPresentation && Object.hasOwn(value, 'presentation')
    ? 'origin,presentation,record,snapshot' : 'origin,record,snapshot';
  if (!record(value) || Reflect.ownKeys(value).length !== keys.split(',').length || Object.keys(value).sort().join(',') !== keys
    || Object.values(Object.getOwnPropertyDescriptors(value)).some(d => !d.enumerable || !Object.hasOwn(d, 'value'))
    || !isSourceSnapshotOrigin(value.origin) || seen.has(value.origin.captureId) || !sameOriginInput(value.origin, original))
    throw new Error('Invalid continuation bundle association.');
  const snapshot = validateSourceSnapshot(value.snapshot);
  if (snapshot.checking.status === 'captured' && snapshot.checking.binding.attempt !== value.origin.captureId)
    throw new Error('The snapshot belongs to another process.');
  seen.add(value.origin.captureId);
  return { snapshot, origin: structuredClone(value.origin), record: value.record,
    ...(allowPresentation && Object.hasOwn(value, 'presentation') ? { presentation: value.presentation } : {}) };
}
/** The host already validates Lean's response; this rejects unrelated window messages. */
export function parseEditorMessage(value: unknown): EditorMessage | undefined {
  if (!record(value) || typeof value.requestId !== 'string' || !/^(0|[1-9][0-9]{0,19})$/.test(value.requestId) || !record(value.document)) return undefined;
  const doc = value.document;
  if (typeof doc.uri !== 'string' || typeof doc.fileName !== 'string' || !Number.isSafeInteger(doc.version) || Number(doc.version) < 0 || !record(doc.selection) || !position(doc.selection.start) || !position(doc.selection.end)) return undefined;
  if (value.type === 'statementlens.analysis' && record(value.analysis) && typeof value.analysis.source === 'string'
    && value.analysis.guidedContextContract !== GUIDED_CONTEXT_CONTRACT) {
    const { analysis, ...attachments } = value;
    // A future guided shape need not parse; raw attachments still receive every normal check.
    return parseEditorMessage({ ...attachments, type: 'statementlens.error',
      source: analysis.source, code: 'EDITOR_COMPATIBILITY', message: GUIDED_CONTEXT_MISMATCH });
  }
  if (value.type === 'statementlens.status' && ['analyzing', 'idle', 'stale'].includes(String(value.phase))) return value as unknown as EditorMessage;
  if ((value.type === 'statementlens.error' && typeof value.message === 'string')
    || (value.type === 'statementlens.analysis' && record(value.analysis) && typeof value.analysis.source === 'string' && record(value.analysis.tree) && typeof value.analysis.tree.id === 'string' && Array.isArray(value.analysis.tree.children) && record(value.analysis.expression))) {
    if (value.sourceSnapshotUnavailable !== undefined && (typeof value.sourceSnapshotUnavailable !== 'string' || [...value.sourceSnapshotUnavailable].length > 4096 || value.sourceSnapshot !== undefined)) return undefined;
    if (value.sourceOccurrenceUnavailable !== undefined && (typeof value.sourceOccurrenceUnavailable !== 'string' || [...value.sourceOccurrenceUnavailable].length > 4096 || value.sourceOccurrence !== undefined)) return undefined;
    if (value.headExposureUnavailable !== undefined && (typeof value.headExposureUnavailable !== 'string' || [...value.headExposureUnavailable].length > 4096 || value.headExposure !== undefined)) return undefined;
    if (value.decompositionUnavailable !== undefined && (typeof value.decompositionUnavailable !== 'string' || [...value.decompositionUnavailable].length > 4096)) return undefined;
    if ((value.decompositions !== undefined || value.decompositionUnavailable !== undefined) && value.sourceOccurrence === undefined) return undefined;
    if ((value.headExposure !== undefined || value.headExposureUnavailable !== undefined) && value.sourceOccurrence === undefined) return undefined;
    if (value.sourceOccurrence !== undefined && value.sourceSnapshot === undefined) return undefined;
    if (value.sourceSnapshot === undefined && value.sourceSnapshotOrigin === undefined) return value as unknown as EditorMessage;
    if (!isSourceSnapshotOrigin(value.sourceSnapshotOrigin)) return undefined;
    const origin = value.sourceSnapshotOrigin;
    if (origin.document?.uri !== doc.uri || origin.document.version !== doc.version
      || origin.selection.start.line !== doc.selection.start.line || origin.selection.start.character !== doc.selection.start.character
      || origin.selection.end.line !== doc.selection.end.line || origin.selection.end.character !== doc.selection.end.character) return undefined;
    try {
      const snapshot = validateSourceSnapshot(value.sourceSnapshot);
      if (snapshot.checking.status === 'captured' && snapshot.checking.binding.attempt !== origin.captureId) return undefined;
      if (value.sourceOccurrence !== undefined) {
        const occurrence = validateSourceOccurrence(value.sourceOccurrence, snapshot);
        if (occurrence.captureId !== origin.captureId) return undefined;
        if (value.headExposure !== undefined || value.headExposureUnavailable !== undefined || value.decompositions !== undefined || value.decompositionUnavailable !== undefined) {
          if (occurrence.checking.status !== 'captured' || !occurrence.checking.selected) return undefined;
          const seen = new Set([origin.captureId]), { freeze } = createExactJsonTools();
          let retainedExposure: HeadExposureBundle | undefined;
          if (value.headExposure !== undefined) {
            const seed = checkedBundle(value.headExposure, origin, seen);
            const exposure = validateSourceHeadExposure(seed.record, seed.snapshot, { snapshot, occurrence });
            if (exposure.captureId !== seed.origin.captureId || exposure.parentCaptureId !== origin.captureId) return undefined;
            retainedExposure = { snapshot: seed.snapshot, origin: seed.origin, record: exposure }; freeze(retainedExposure);
          }
          let decompositions: SourceDecompositionBundle[] | undefined;
          if (value.decompositions !== undefined) {
            if (!Array.isArray(value.decompositions) || value.decompositions.length > 8
              || Reflect.ownKeys(value.decompositions).length !== value.decompositions.length + 1) return undefined;
            const bundles = Array.from({ length: value.decompositions.length }, (_, index) => {
              const descriptor = Object.getOwnPropertyDescriptor(value.decompositions, index);
              if (!descriptor?.enumerable || !Object.hasOwn(descriptor, 'value')) throw new Error('Invalid continuation array.');
              return checkedBundle(descriptor.value, origin, seen, true);
            });
            const historyAttachments = (attempts: unknown) => ({ sourceSnapshot: snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: occurrence,
              ...(retainedExposure ? { headExposure: retainedExposure } : {}), decompositions: attempts,
              ...(value.decompositionUnavailable !== undefined ? { decompositionUnavailable: value.decompositionUnavailable } : {}) });
            // Optional display data cannot prevent admission of valid exact records.
            assertSourceHistoryLimit(historyAttachments(bundles.map(({ snapshot, origin, record }) => ({ snapshot, origin, record }))));
            const history = validateDecompositionHistory({ snapshot, occurrence,
              seed: retainedExposure ? { snapshot: retainedExposure.snapshot, record: retainedExposure.record } : null,
              attempts: bundles.map(item => ({ snapshot: item.snapshot, record: item.record })) });
            decompositions = history.attempts.map((item, i) => {
              if (item.record.captureId !== bundles[i].origin.captureId) throw new Error('Continuation origin does not match its record.');
              const presentation = sanitizeSourcePresentation(bundles[i].presentation, item.record);
              return { ...item, origin: bundles[i].origin, ...(presentation ? { presentation } : {}) };
            });
            decompositions = fitSourcePresentationHistory(decompositions, attempts => assertSourceHistoryLimit(historyAttachments(attempts)));
            freeze(decompositions); retainedHistories.set(decompositions, history);
          }
          if (decompositions === undefined) assertSourceHistoryLimit({ sourceSnapshot: snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: occurrence,
            ...(retainedExposure ? { headExposure: retainedExposure } : {}),
            ...(value.decompositionUnavailable !== undefined ? { decompositionUnavailable: value.decompositionUnavailable } : {}) });
          return { ...value, sourceSnapshot: snapshot, sourceOccurrence: occurrence,
            ...(retainedExposure ? { headExposure: retainedExposure } : {}), ...(decompositions ? { decompositions } : {}) } as unknown as EditorMessage;
        }
        return { ...value, sourceSnapshot: snapshot, sourceOccurrence: occurrence } as unknown as EditorMessage;
      }
      return { ...value, sourceSnapshot: snapshot } as unknown as EditorMessage;
    } catch { return undefined; }
  }
  return undefined;
}

export interface EditorSession { requestId: string; document: EditorDocument; phase: 'analyzing' | 'idle' | 'stale' | 'error' }
/** The extension numbers requests monotonically within a webview lifetime. */
export function acceptsEditorStatus(session: EditorSession | null, message: Extract<EditorMessage, { type: 'statementlens.status' }>): boolean {
  if (!session) return true;
  if (BigInt(message.requestId) < BigInt(session.requestId)) return false;
  if (message.requestId !== session.requestId) return true;
  if (message.document.uri !== session.document.uri || message.document.version < session.document.version) return false;
  return message.phase !== 'analyzing' || session.phase === 'analyzing';
}
/** A result can only fill the exact document/version requested by the current host session. */
export function acceptsEditorResult(session: EditorSession | null, message: EditorMessage): boolean {
  return !!session && session.phase === 'analyzing' && message.requestId === session.requestId && message.document.uri === session.document.uri && message.document.fileName === session.document.fileName && message.document.version === session.document.version && message.document.selection.start.line === session.document.selection.start.line && message.document.selection.start.character === session.document.selection.start.character && message.document.selection.end.line === session.document.selection.end.line && message.document.selection.end.character === session.document.selection.end.character;
}
