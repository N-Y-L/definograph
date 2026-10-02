import type { Analysis } from '../core';
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { retainedDecompositionHistory, type EditorCommand, type EditorDocument, type EditorMessage } from './host';
import { followSourceStatus, sourceActionResultAnchor, type PendingSourceAction, type SourceActionRequest } from './source-action-navigation';
import type { SourceSnapshotOrigin } from './source-origin';
import { definitionOccurrences, definitionOccurrenceFocus, type DefinitionOccurrence } from './definition-occurrences';
import { DECOMPOSITION_MAX_ATTEMPTS, DECOMPOSITION_MAX_OPERATIONS, decompositionPlan, validateDecompositionHistory,
  type DecompositionOperation, type SourceDecomposition } from './source-decomposition';
import { sourceResultPresentation, type SourcePresentation } from './source-presentation';

type Result = Extract<EditorMessage, { type: 'statementlens.analysis' }>;
type Status = Extract<EditorMessage, { type: 'statementlens.status' }>;
type CatalogueSource = Parameters<typeof definitionOccurrences>[0];
export interface DefinitionWorkspaceAnchor {
  analysis: Analysis;
  document: EditorDocument;
  origin: SourceSnapshotOrigin;
  clause: string;
  proofType: boolean;
}
export interface DefinitionWorkspaceState {
  anchor: DefinitionWorkspaceAnchor;
  phase: 'preparing' | 'choosing' | 'focusing' | 'exposing' | 'complete' | 'unavailable';
  message: string;
  catalogue?: CatalogueSource;
  chosen?: DefinitionOccurrence;
  result?: SourceDecomposition;
  resultStep?: number;
  resultPresentation?: SourcePresentation;
}
function same(a: unknown, b: unknown): boolean {
  // Canonicalization budgets belong to one comparison, not the webview lifetime.
  const { canonical } = createExactJsonTools();
  return canonical(a as JsonValue) === canonical(b as JsonValue);
}
function sameBundle(a: { snapshot: unknown; origin: unknown; record: unknown }, b: typeof a): boolean {
  return same(a.snapshot, b.snapshot) && same(a.origin, b.origin) && same(a.record, b.record);
}
/** Parsing checks each reply internally. Its old attachments must additionally
 * remain the exact content from which this webview requested a continuation. */
function sameRetainedSource(previous: Result, next: Exclude<EditorMessage, Status>): boolean {
  for (const key of ['sourceSnapshot', 'sourceSnapshotOrigin', 'sourceOccurrence'] as const)
    if (!same(previous[key] ?? null, next[key] ?? null)) return false;
  if (previous.headExposure || next.headExposure) {
    if (!previous.headExposure || !next.headExposure || !sameBundle(previous.headExposure, next.headExposure)) return false;
  }
  const before = previous.decompositions ?? [], after = next.decompositions ?? [];
  return after.length >= before.length && before.every((bundle, index) => sameBundle(bundle, after[index]));
}
/** This is only a display-retention check. It grants no continuation authority. */
export function sameDefinitionWorkspaceInput(anchor: DefinitionWorkspaceAnchor, message: Result): boolean {
  const origin = message.sourceSnapshotOrigin;
  return !!origin && same(anchor.document, message.document)
    && anchor.origin.sourceSha256 === origin.sourceSha256
    && same(anchor.origin.engine, origin.engine) && same(anchor.origin.project, origin.project)
    && same(anchor.origin.selection, origin.selection) && same(anchor.origin.document, origin.document)
    && same(anchor.analysis.expression, message.analysis.expression)
    && same(anchor.analysis.tree, message.analysis.tree) && anchor.analysis.source === message.analysis.source;
}

/** A local explicit-action sequence using only the host's existing checked operations.
 * The original reading object stays mounted. Every answer must match the posted action,
 * unchanged input and retained host-validated history before another action is sent. */
export class DefinitionWorkspaceController {
  state: DefinitionWorkspaceState | null = null;
  private pending: PendingSourceAction | null = null;
  private capture: Result | null = null;
  private pendingOperation: DecompositionOperation | null = null;
  /** Only a source-associated result; rejected replies never replace this value. */
  get retainedCapture(): Result | null { return this.capture; }
  private stage: 'root' | 'type' | 'focus' | 'expose' | null = null;
  constructor(private readonly post: (request: SourceActionRequest, command: EditorCommand) => void,
    private readonly changed: (state: DefinitionWorkspaceState | null) => void) {}
  private publish(patch: Partial<DefinitionWorkspaceState>) {
    if (this.state) { this.state = { ...this.state, ...patch }; this.changed(this.state); }
  }
  cancel() { this.state = null; this.pending = null; this.pendingOperation = null; this.capture = null; this.stage = null; this.changed(null); }
  start(anchor: DefinitionWorkspaceAnchor, capture?: Result) {
    this.cancel();
    this.state = { anchor, phase: 'preparing', message: 'Checking the selected source and preparing its applications…' };
    this.changed(this.state);
    if (capture?.headExposure || capture?.decompositions !== undefined) {
      const bundles=capture.decompositions, history=bundles&&retainedDecompositionHistory(bundles);
      const record=bundles?.at(-1)?.record;
      const first=record?.checking.status==='captured'?record.checking.steps[0]:undefined;
      const matchesRoot=capture.sourceOccurrence?.path.length===0 && first && (anchor.proofType
        ? first.operation.kind==='typeComponent' : first.operation.kind==='focus'&&first.operation.path.length===0);
      if(!sameDefinitionWorkspaceInput(anchor,capture)||!matchesRoot||!history||!record){
        this.unavailable('This source has a different inspection history. Refresh from the editor to start another definition workspace.');return;
      }
      const catalogue={history,record,stepIndex:0};const model=definitionOccurrences(catalogue);
      if(model.status!=='available'){this.capture=capture;this.unavailable(`${model.reason} Refresh from the editor to start another inspection history.`);return;}
      this.capture=capture;this.publish({phase:'choosing',message:'Choose another application from the retained checked statement.',catalogue});return;
    }
    if (capture && sameDefinitionWorkspaceInput(anchor, capture)) this.capture = capture;
    this.stage = 'root';
    this.send({ kind: 'occurrence', parentCaptureId: anchor.origin.captureId, path: [] },
      { type: 'statementlens.checkOccurrence', parentCaptureId: anchor.origin.captureId, path: [] });
  }
  private send(request: SourceActionRequest, command: EditorCommand, operation: DecompositionOperation | null = null) {
    this.pending = { request }; this.pendingOperation = operation; this.post(request, command);
  }
  private continuation(previousCaptureId: string, parentStepIndex: number,
    command: Omit<Extract<EditorCommand, { type: 'statementlens.focusExposedPart' }>, 'parentCaptureId' | 'previousCaptureId' | 'parentStepIndex'>
      | { type: 'statementlens.inspectTypeComponent' } | { type: 'statementlens.exposeFocusedHead'; target: 'term' }) {
    const parentCaptureId = this.capture?.sourceSnapshotOrigin?.captureId;
    if (!parentCaptureId || !this.capture) { this.unavailable('The checked source is no longer available. Refresh from the editor.'); return; }
    const operation: DecompositionOperation = command.type === 'statementlens.focusExposedPart' ? { kind: 'focus', path: command.path }
      : command.type === 'statementlens.exposeFocusedHead' ? { kind: 'expose', target: command.target } : { kind: 'typeComponent' };
    try {
      const history = this.capture.decompositions ? retainedDecompositionHistory(this.capture.decompositions)
        : validateDecompositionHistory({ snapshot: this.capture.sourceSnapshot, occurrence: this.capture.sourceOccurrence,
          seed: this.capture.headExposure ? { snapshot: this.capture.headExposure.snapshot, record: this.capture.headExposure.record } : null, attempts: [] });
      if (!history) throw new Error('The checked inspection history is no longer retained.');
      decompositionPlan(history, previousCaptureId, parentStepIndex, operation, 3);
    } catch (error) {
      this.unavailable(`${error instanceof Error ? error.message : 'This continuation is unavailable.'} Refresh from the editor to start another inspection history.`); return;
    }
    this.send({ kind: 'continuation', parentCaptureId, previousCaptureId, parentStepIndex,
      attemptsBefore: this.capture.decompositions?.length ?? 0 }, { ...command, parentCaptureId, previousCaptureId, parentStepIndex }, operation);
  }
  /** False means the ordinary reader must discard its current data as usual. */
  status(message: Status): boolean {
    if (!this.state) return false;
    this.pending = followSourceStatus(this.pending, message);
    if (!this.pending || !same(message.document, this.state.anchor.document)) { this.cancel(); return false; }
    return true;
  }
  private unavailable(message: string) {
    this.pending = null; this.pendingOperation = null; this.stage = null; this.publish({ phase: 'unavailable', message });
  }
  result(message: Exclude<EditorMessage, Status>): boolean {
    if (!this.state) return false;
    const pending = this.pending, expectedOperation = this.pendingOperation, matched = sourceActionResultAnchor(pending, message);
    this.pending = null; this.pendingOperation = null;
    if (message.type === 'statementlens.error') {
      if (matched === 'continuation-unavailable' && this.capture && same(message.document, this.state.anchor.document)
        && sameRetainedSource(this.capture, message)
        && (message.decompositions?.length ?? 0) === (this.capture.decompositions?.length ?? 0)) {
        this.unavailable(message.decompositionUnavailable ?? message.message); return true;
      }
      this.cancel(); return false;
    }
    if (!matched || !sameDefinitionWorkspaceInput(this.state.anchor, message)) {
      this.cancel(); return false;
    }
    if (pending?.request.kind === 'continuation' && (!this.capture || !sameRetainedSource(this.capture, message))) {
      this.unavailable('The continuation changed its previously retained source or inspection history. Refresh from the editor before continuing.'); return true;
    }
    if (matched.endsWith('unavailable')) {
      if (matched === 'continuation-unavailable'
        && (message.decompositions?.length ?? 0) !== (this.capture?.decompositions?.length ?? 0)) {
        this.unavailable('The unavailable reply contains an unrequested inspection attempt. Refresh from the editor before continuing.'); return true;
      }
      this.capture = message;
      this.unavailable(message.decompositionUnavailable ?? message.sourceOccurrenceUnavailable ?? 'This inspection did not produce a checked result.'); return true;
    }
    if (this.stage === 'root') {
      this.capture = message;
      const occurrence = message.sourceOccurrence;
      if (occurrence?.checking.status !== 'captured' || occurrence.checking.action.status !== 'completed' || !occurrence.checking.selected) {
        this.unavailable('The selected source could not be checked. Details remain in Source data.'); return true;
      }
      this.stage = 'type';
      this.continuation(occurrence.captureId, 0, this.state.anchor.proofType
        ? { type: 'statementlens.inspectTypeComponent' }
        : { type: 'statementlens.focusExposedPart', path: [] });
      return true;
    }
    const bundles = message.decompositions, history = bundles && retainedDecompositionHistory(bundles);
    const record = bundles?.at(-1)?.record;
    if (!history || !record || !expectedOperation || !same(record.operations.at(-1), expectedOperation)) {
      this.unavailable('The continuation no longer matches the requested operation. Refresh from the editor before continuing.'); return true;
    }
    const requestedStep = record.checking.status === 'captured' ? record.checking.steps[record.operations.length - 1] : undefined;
    if (this.stage === 'focus' && requestedStep?.output.status === 'candidate') {
      const chosen = this.state.chosen;
      if (!chosen || !same(requestedStep.output.result.term, chosen.term) || !same(requestedStep.output.result.home, chosen.home)) {
        this.unavailable('The checked application no longer matches the chosen occurrence. Refresh from the editor before continuing.'); return true;
      }
    }
    // A stopped/refused attempt is still inspectable once its requested operation,
    // source, prior history and any returned chosen expression are associated.
    this.capture = message;
    if (record.checking.status !== 'captured' || record.checking.action.status !== 'completed' || record.checking.stop) {
      this.unavailable(record?.checking.status === 'captured' ? record.checking.stop?.reason ?? 'Checking did not complete. Details remain in Source data.'
        : record?.checking.reason ?? 'No checked continuation was retained.'); return true;
    }
    const stepIndex = record.checking.steps.length - 1, step = record.checking.steps[stepIndex];
    if (!step || step.output.status !== 'candidate' || step.output.checking.status !== 'completed'
      || !record.checking.steps.every(item => item.replay === 'matched' || item.replay === 'new')) {
      this.unavailable('This result did not reproduce the checked continuation. Details remain in Source data.'); return true;
    }
    if (this.stage === 'type') {
      const expected = this.state.anchor.proofType ? { kind: 'typeComponent' } : { kind: 'focus', path: [] };
      if (!same(step.operation, expected)) { this.unavailable('The continuation no longer matches the requested operation. Refresh from the editor before continuing.'); return true; }
      const catalogue = { history, record, stepIndex };
      const model = definitionOccurrences(catalogue);
      if (model.status !== 'available') { this.unavailable(`${model.reason} Refresh from the editor to start another inspection history.`); return true; }
      this.stage = null; this.publish({ phase: 'choosing', message: 'Choose an application in the selected statement.', catalogue });
    } else if (this.stage === 'focus') {
      const chosen = this.state.chosen;
      if (!chosen || step.operation.kind !== 'focus' || !same(step.operation.path, chosen.focusPath)
        || !same(step.output.result.term, chosen.term) || !same(step.output.result.home, chosen.home)) {
        this.unavailable('The checked application no longer matches the chosen occurrence.'); return true;
      }
      this.stage = 'expose'; this.publish({ phase: 'exposing', message: 'The exact application was checked. Opening its definition…' });
      this.continuation(record.captureId, stepIndex, { type: 'statementlens.exposeFocusedHead', target: 'term' });
    } else if (this.stage === 'expose') {
      if (step.operation.kind !== 'expose' || step.operation.target !== 'term' || !('definition' in step.output)) {
        this.unavailable('No definition exposure was retained.'); return true;
      }
      this.stage = null; this.publish({ phase: 'complete', message: 'Definition inspection completed in the application’s recorded scope. Check outcomes are shown below.', result: record, resultStep: stepIndex,
        resultPresentation: sourceResultPresentation(record, stepIndex, bundles?.at(-1)?.presentation) });
    } else { this.cancel(); return false; }
    return true;
  }
  inspect(chosen: DefinitionOccurrence) {
    const source = this.state?.catalogue;
    if (!source || this.pending || this.state?.phase !== 'choosing') return;
    const operation = definitionOccurrenceFocus(source, chosen);
    if (!operation) { this.unavailable('This application selection is no longer current. Refresh from the editor before continuing.'); return; }
    try {
      const plan = decompositionPlan(source.history, source.record.captureId, source.stepIndex, operation, 3);
      // The first plan already checks the actual focus and cumulative path budget.
      // Reserve the following exposure as well: one operation, three checks and
      // one additional attempt. These are the fixed v3 operation costs.
      const cost = (op: DecompositionOperation) => op.kind === 'logical' ? 4 : op.kind === 'fields' ? 0 : op.kind === 'focus' || op.kind === 'typeComponent' ? 2 : 3;
      if (source.history.attempts.length + 2 > DECOMPOSITION_MAX_ATTEMPTS
        || plan.operations.length + 1 > DECOMPOSITION_MAX_OPERATIONS
        || 6 + plan.operations.reduce((sum, op) => sum + cost(op), 0) + 3 > 30)
        throw new Error('This history has insufficient remaining capacity to check and expose the application.');
    } catch (error) {
      this.unavailable(`${error instanceof Error ? error.message : 'This inspection is unavailable.'} Refresh from the editor to start another inspection history.`); return;
    }
    this.stage = 'focus'; this.publish({ phase: 'focusing', message: 'Checking the exact application and its surrounding binders…', chosen });
    this.continuation(source.record.captureId, source.stepIndex, { type: 'statementlens.focusExposedPart', path: operation.path });
  }
}
