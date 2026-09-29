import { isSourceOccurrencePath, type SourceOccurrence, type SourceOccurrenceStep } from '../../src/editor/source-occurrence.js';
import type { HeadExposureBundle } from '../../src/editor/source-history.js';
import { isDecompositionFocusPath, type DecompositionOperation, type DecompositionCandidate, type SourceDecompositionBundle } from '../../src/editor/source-decomposition.js';

export type ContinuationAction = { kind: 'decomposition'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number;
  operation: DecompositionOperation };

/** Only scalar identifiers and one bounded action cross the webview boundary. */
export function continuationCommand(value: unknown): ContinuationAction {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('Invalid continuation request.');
  const descriptors = Object.getOwnPropertyDescriptors(value);
  if (Reflect.ownKeys(value).some(key => typeof key !== 'string')
    || Object.values(descriptors).some(d => !d.enumerable || !Object.hasOwn(d, 'value'))) throw new Error('Invalid continuation request.');
  const v = value as Record<string, unknown>;
  let operation: DecompositionOperation, additional: string[];
  if (v.type === 'statementlens.focusExposedPart' && isSourceOccurrencePath(v.path)) {
    operation = { kind: 'focus', path: [...v.path] }; additional = ['path'];
  } else if (v.type === 'statementlens.exposeFocusedHead' && (v.target === 'term' || v.target === 'type')) {
    operation = { kind: 'expose', target: v.target }; additional = ['target'];
  } else if (v.type === 'statementlens.inspectTypeComponent') {
    operation = { kind: 'typeComponent' }; additional = [];
  } else if (v.type === 'statementlens.inspectLogicalStructure') {
    operation = { kind: 'logical' }; additional = [];
  } else if (v.type === 'statementlens.inspectFields') {
    operation = { kind: 'fields' }; additional = [];
  } else if (v.type === 'statementlens.projectField' && Number.isSafeInteger(v.index) && Number(v.index) >= 0 && Number(v.index) < 16) {
    operation = { kind: 'project', index: Number(v.index) }; additional = ['index'];
  } else throw new Error('Invalid continuation request.');
  if (Object.keys(v).sort().join(',') !== ['type', 'parentCaptureId', 'previousCaptureId', 'parentStepIndex', ...additional].sort().join(',')
    || typeof v.parentCaptureId !== 'string' || typeof v.previousCaptureId !== 'string'
    || !Number.isSafeInteger(v.parentStepIndex) || Number(v.parentStepIndex) < 0 || Number(v.parentStepIndex) > 7)
    throw new Error('Invalid continuation request.');
  return { kind: 'decomposition', parentCaptureId: v.parentCaptureId, previousCaptureId: v.previousCaptureId,
    parentStepIndex: Number(v.parentStepIndex), operation };
}

/** Server-validated immutable bundles only. Verdicts are deliberately not gates.
 * Live commands use v3 even when their retained parent is a legacy v1 result. */
export function requireContinuationParent(seed: HeadExposureBundle | null, attempts: SourceDecompositionBundle[], action: ContinuationAction,
  sourcePath: SourceOccurrenceStep[] = [], occurrence?: SourceOccurrence): void {
  if (attempts.length >= 8) throw new Error('Eight continuation attempts are retained. Save this history and Refresh to start another.');
  if (occurrence && action.parentCaptureId !== occurrence.captureId) throw new Error('The original source association changed.');
  let result: import('../../src/packets/structure.js').PositionalStructuralInput;
  let selectedOutput: DecompositionCandidate | undefined, previousKind: DecompositionOperation['kind'] | undefined;
  let pathSteps = sourcePath.length, prefixLength: number, reserved = 6;
  const cost = (operation: DecompositionOperation) => operation.kind === 'logical' ? 4 : operation.kind === 'fields' ? 0 : operation.kind === 'focus' || operation.kind === 'typeComponent' ? 2 : 3;
  if (occurrence && action.previousCaptureId === occurrence.captureId) {
    const c = occurrence.checking;
    if (action.parentStepIndex !== 0 || c.status !== 'captured' || c.action.status !== 'completed' || !c.selected)
      throw new Error('The original occurrence has no completed pair.');
    result = c.selected; prefixLength = 0;
  } else if (seed && action.previousCaptureId === seed.record.captureId) {
    const c = seed.record.checking;
    if (action.parentStepIndex !== 0 || c.status !== 'captured' || c.action.status !== 'completed'
      || c.exposure?.status !== 'candidate' || c.exposure.checking.status !== 'completed')
      throw new Error('This exposure did not complete. Refresh to start another source/exposure history.');
    result = c.exposure.result; prefixLength = 1; reserved += 3; previousKind = 'expose'; selectedOutput = c.exposure;
  } else {
    const previous = attempts.find(item => item.record.captureId === action.previousCaptureId)?.record;
    if (!previous || previous.checking.status !== 'captured' || previous.checking.action.status !== 'completed')
      throw new Error('The chosen continuation is not retained in this session.');
    const prefix = previous.checking.steps.slice(0, action.parentStepIndex + 1), selected = prefix[action.parentStepIndex];
    if (!selected || prefix.some(step => step.output.status !== 'candidate' || step.output.checking.status !== 'completed'
      || step.replay !== 'matched' && step.replay !== 'new')) throw new Error('Only a completed, matching continuation prefix can be replayed.');
    if (selected.output.status !== 'candidate') throw new Error('The selected step has no result.');
    selectedOutput = selected.output; previousKind = selected.operation.kind;
    result = selected.output.result; prefixLength = prefix.length;
    reserved += prefix.reduce((sum, step) => sum + cost(step.operation), 0);
    pathSteps += prefix.reduce((sum, step) => sum + (step.operation.kind === 'focus' ? step.operation.path.length : 0), 0);
  }
  if (reserved + cost(action.operation) > 30) throw new Error('This continuation exceeds the reserved thirty-check limit. Choose an earlier completed step or Refresh.');
  if (prefixLength >= 8) throw new Error('This continuation already has eight operations. Choose an earlier completed step or Refresh.');
  if (pathSteps + (action.operation.kind === 'focus' ? action.operation.path.length : 0) > 128) throw new Error('The selected history exceeds the total constructor-path limit.');
  if (action.operation.kind === 'project' && (previousKind !== 'fields' || !selectedOutput || !('catalogue' in selectedOutput)
    || !selectedOutput.catalogue.fields[action.operation.index])) throw new Error('Choose a field from the immediately preceding retained catalogue.');
  if (action.operation.kind === 'focus' && !isDecompositionFocusPath(result, action.operation.path)) throw new Error('The chosen path does not address an ordinary expression in this retained result.');
}
