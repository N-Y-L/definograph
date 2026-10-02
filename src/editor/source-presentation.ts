/** Optional display text. Exact syntax, receipts and replay never depend on it. */
import { createExactJsonTools } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { isValidatedSourceDecomposition, type SourceDecomposition, type SourceDecompositionBundle } from './source-decomposition';
import { sourceSnapshotValidation, SourceSnapshotError } from './source-snapshot';

export const SOURCE_PRESENTATION_SCHEMA = 'definograph.source-presentation.v1';
export const SOURCE_PRESENTATION_BYTES = 128 * 1024;
export const SOURCE_PRESENTATION_TEXT_CHARACTERS = 8192;
export const SOURCE_PRESENTATION_TEXT_BYTES = 32768;
export const SOURCE_PRESENTATION_NOTE = 'Notation may hide implicit arguments; exact arguments and scope remain in details.';
export type SourcePresentation = {
  schema: typeof SOURCE_PRESENTATION_SCHEMA; captureId: string; status: 'available';
  stepIndex: number; target: 'term' | 'type'; result: PositionalStructuralInput; text: string;
} | { schema: typeof SOURCE_PRESENTATION_SCHEMA; captureId: string; status: 'unavailable'; reason: string };

const encoder = new TextEncoder();
// Lean's pretty printer uses LF and TAB as layout. Other controls and invisible
// directional overrides cannot be used to disguise the displayed expression.
const textControls = /[\u0000-\u0008\u000b-\u001f\u007f-\u009f\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/u;
const reasonControls = /[\u0000-\u001f\u007f-\u009f\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/u;
export function unavailableSourcePresentation(record: SourceDecomposition, reason: string): SourcePresentation {
  return Object.freeze({ schema: SOURCE_PRESENTATION_SCHEMA, captureId: record.captureId, status: 'unavailable', reason });
}

/** Requires an independently validated raw record; malformed optional data is
 * replaced locally and can never invalidate that record or its history. */
export function sanitizeSourcePresentation(value: unknown, record: SourceDecomposition): SourcePresentation | undefined {
  if (value === undefined) return undefined;
  const fallback = (reason: string) => unavailableSourcePresentation(record, reason);
  try {
    if (!isValidatedSourceDecomposition(record)) throw Error('Unvalidated record.');
    const { preflight, object, text, exact, UUID } = sourceSnapshotValidation;
    preflight(value, SOURCE_PRESENTATION_BYTES, ['presentation'], false, 128, SOURCE_PRESENTATION_BYTES);
    const v = object(value, typeof value === 'object' && value !== null && 'status' in value && value.status === 'available'
      ? ['schema', 'captureId', 'status', 'stepIndex', 'target', 'result', 'text']
      : ['schema', 'captureId', 'status', 'reason'], ['presentation']);
    if (v.schema !== SOURCE_PRESENTATION_SCHEMA || typeof v.captureId !== 'string' || !UUID.test(v.captureId)
      || v.captureId !== record.captureId) throw Error('Wrong capture.');
    if (v.status === 'unavailable') {
      const reason = text(v.reason, 512, ['presentation', 'reason']);
      if (reasonControls.test(reason)) throw Error('Invalid reason.');
      return fallback(reason);
    }
    if (v.status !== 'available') throw Error('Unknown presentation status.');
    const stepIndex = record.operations.length - 1;
    const step = record.checking.status === 'captured' ? record.checking.steps[stepIndex] : undefined;
    if (!step || record.checking.status !== 'captured' || record.checking.steps.length !== stepIndex + 1
      || v.stepIndex !== stepIndex || step.index !== stepIndex || step.operation.kind !== 'expose'
      || v.target !== step.operation.target || record.operations[stepIndex].kind !== 'expose'
      || step.output.status !== 'candidate' || !('definition' in step.output)) throw Error('Wrong result step.');
    exact(v.result, step.output.result, ['presentation', 'result']);
    const rendered = text(v.text, SOURCE_PRESENTATION_TEXT_CHARACTERS, ['presentation', 'text']);
    if (!rendered.trim() || encoder.encode(rendered).length > SOURCE_PRESENTATION_TEXT_BYTES || textControls.test(rendered))
      throw Error('Invalid presentation text.');
    const result: SourcePresentation = { schema: SOURCE_PRESENTATION_SCHEMA, captureId: record.captureId,
      status: 'available', stepIndex, target: step.operation.target, result: step.output.result, text: rendered };
    createExactJsonTools().freeze(result); return result;
  } catch {
    return fallback('Readable Lean text was rejected because its result association, format, or display budget was invalid. Exact result and scope remain available.');
  }
}

/** Recheck at the display boundary too: a TypeScript annotation is no witness. */
export function sourceResultPresentation(record: SourceDecomposition, stepIndex: number, value: unknown): SourcePresentation {
  const presentation = sanitizeSourcePresentation(value, record);
  if (stepIndex !== record.operations.length - 1)
    return unavailableSourcePresentation(record, 'Readable Lean text is unavailable for this earlier step. Exact result and scope remain available.');
  return presentation ?? unavailableSourcePresentation(record,
    'Readable Lean text was not retained or exceeded its display budget. Exact result and scope remain available.');
}

/** The aggregate history cap includes display sidecars. Relieve display cost
 * before giving up any exact attempt, including earlier optional sidecars. */
export function fitSourcePresentationHistory(bundles: SourceDecompositionBundle[], checkLimit: (bundles: SourceDecompositionBundle[]) => void): SourceDecompositionBundle[] {
  try { checkLimit(bundles); return bundles; }
  catch (error) {
    if (!(error instanceof SourceSnapshotError) || error.code !== 'limit' || !bundles.some(bundle => bundle.presentation)) throw error;
  }
  const fallback = bundles.map(({ presentation, ...bundle }) => ({ ...bundle, ...(presentation ? {
    presentation: unavailableSourcePresentation(bundle.record, 'Readable Lean text exceeded the retained-history display budget. Exact result and scope remain available.') } : {}) }));
  try { checkLimit(fallback); return fallback; }
  catch (error) { if (!(error instanceof SourceSnapshotError) || error.code !== 'limit') throw error; }
  const exactOnly = bundles.map(({ snapshot, origin, record }) => ({ snapshot, origin, record }));
  checkLimit(exactOnly); return exactOnly;
}
