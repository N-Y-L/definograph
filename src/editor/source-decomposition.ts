/** Bounded, exact records of repeated head exposure and positional focus.
 * Validation establishes retained syntax associations, never native authority. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing, type PositionalStructuralInput } from '../packets/structure';
import { sourceSnapshotValidation as shared, type ClosureItem, type SnapshotAudit, type SnapshotBinding,
  type SnapshotReceipt, type SnapshotUnavailable, type SourceSnapshot } from './source-snapshot';
import { sourceOccurrenceValidation as occurrenceRules, isSourceOccurrencePath, validateSourceOccurrence,
  type SourceOccurrence, type SourceOccurrenceStep } from './source-occurrence';
import { headExposureValidation as headRules, validateSourceHeadExposure, type HeadExposureAction,
  type HeadExposureCandidate, type HeadExposureTarget, type SourceHeadExposure } from './source-head-exposure';
import { validateHeadExpression } from './head-exposure-replay';
import type { SourceSnapshotOrigin } from './source-origin';
import { validateLogicalCandidate, logicalDeclarations, type LogicalCandidate } from './logical-inspection-replay';
import { validateDirectFieldCatalogue, validateDirectFieldCandidate, directFieldDeclarations,
  type DirectFieldCatalogue, type DirectFieldEntry } from './field-inspection-replay';

export type DecompositionOperation = { kind: 'expose'; target: HeadExposureTarget } | { kind: 'focus'; path: SourceOccurrenceStep[] }
  | { kind: 'fields' } | { kind: 'project'; index: number } | { kind: 'typeComponent' } | { kind: 'logical' };
export type DecompositionCandidate = HeadExposureCandidate | LogicalCandidate | { status: 'candidate'; result: PositionalStructuralInput; checking: HeadExposureAction }
  | { status: 'candidate'; result: PositionalStructuralInput; catalogue: DirectFieldCatalogue; checking: { status: 'completed' } }
  | { status: 'candidate'; result: PositionalStructuralInput; field: DirectFieldEntry; primitive: JsonValue; carrierSort: JsonValue; checking: HeadExposureAction };
export interface DecompositionCheckpoint {
  operation: DecompositionOperation; input: PositionalStructuralInput;
  candidate: Omit<HeadExposureCandidate, 'checking'> | Omit<LogicalCandidate, 'checking'> | { status: 'candidate'; result: PositionalStructuralInput }
    | { status: 'candidate'; result: PositionalStructuralInput; catalogue: DirectFieldCatalogue }
    | { status: 'candidate'; result: PositionalStructuralInput; field: DirectFieldEntry; primitive: JsonValue; carrierSort: JsonValue };
}
export interface DecompositionStep {
  index: number; operation: DecompositionOperation; input: PositionalStructuralInput;
  output: DecompositionCandidate | SnapshotUnavailable; receiptStart: number; receiptCount: number;
  replay: 'new' | 'matched' | 'mismatch' | 'not-compared';
}
export interface SourceDecomposition {
  schema: 'definograph.source-decomposition.v1' | 'definograph.source-decomposition.v2' | 'definograph.source-decomposition.v3'; parentCaptureId: string; previousCaptureId: string; parentStepIndex: number;
  captureId: string; path: SourceOccurrenceStep[]; operations: DecompositionOperation[];
  policy: { id: 'bounded-decomposition-v1' | 'bounded-decomposition-v2' | 'bounded-decomposition-v3'; operation: 'editor-decomposition' | 'editor-decomposition-v2' | 'editor-decomposition-v3'; preparation: 'Lean.instantiateMVars';
    universeSubstitution: 'structural'; reduction: 'original-lambda-spine'; heartbeatBound: ['nat', string];
    retainedMetadata: 'definograph.raw.v1'; maxOperations: 8; maxChecks?: 30; maxFields?: 16; logicalInterpretation?: 'lean-standard-core-v1' };
  checking: (SnapshotUnavailable & { attempted: boolean }) | {
    status: 'captured'; action: HeadExposureAction;
    binding: Omit<SnapshotBinding, 'operation' | 'sourceKind'> & { operation: 'editor-decomposition' | 'editor-decomposition-v2' | 'editor-decomposition-v3'; sourceKind: 'namedDecomposition';
      path: [SourceOccurrenceStep][]; expectedSelected: PositionalStructuralInput; operations: DecompositionOperation[]; expectedHistory: DecompositionCheckpoint[] };
    selected: PositionalStructuralInput | null; steps: DecompositionStep[]; stop: SnapshotUnavailable | null;
    checks: SnapshotReceipt[]; audits: SnapshotAudit[]; environmentSnapshotCount: number;
  };
}
export interface SourceDecompositionBundle { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; record: SourceDecomposition }
export interface DecompositionHistory {
  snapshot: SourceSnapshot; occurrence: SourceOccurrence;
  seed: { snapshot: SourceSnapshot; record: SourceHeadExposure } | null;
  attempts: { snapshot: SourceSnapshot; record: SourceDecomposition }[];
}
export interface DecompositionParent {
  operation: DecompositionOperation | null; result: PositionalStructuralInput; catalogue?: DirectFieldCatalogue;
  operations: DecompositionOperation[]; expectedHistory: DecompositionCheckpoint[];
}
export const DECOMPOSITION_MAX_OPERATIONS = 8;
export const DECOMPOSITION_MAX_ATTEMPTS = 8;
export const DECOMPOSITION_HISTORY_BYTES = 16 * 1024 * 1024;
const RECORD_BYTES = 2 * 1024 * 1024;
const { bad, preflight, object, array, text, operational, exact, named, strName, constant, close, UUID } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const tools = createExactJsonTools();
const canonical = (value: JsonValue) => createExactJsonTools().canonical(value);
const same = (a: unknown, b: unknown) => canonical(a as JsonValue) === canonical(b as JsonValue);
const json = (value: unknown) => value as JsonValue;
const legacyPolicy: SourceDecomposition['policy'] = { id: 'bounded-decomposition-v1', operation: 'editor-decomposition', preparation: 'Lean.instantiateMVars',
  universeSubstitution: 'structural', reduction: 'original-lambda-spine', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1', maxOperations: 8 };
const fieldPolicy: SourceDecomposition['policy'] = { ...legacyPolicy, id: 'bounded-decomposition-v2', operation: 'editor-decomposition-v2', maxChecks: 30, maxFields: 16 };
const logicalPolicy: SourceDecomposition['policy'] = { ...fieldPolicy, id: 'bounded-decomposition-v3', operation: 'editor-decomposition-v3', logicalInterpretation: 'lean-standard-core-v1' };
const histories = new WeakSet<DecompositionHistory>();
const records = new WeakSet<SourceDecomposition>();

/** Internal consistency and exact receipt association, not native authority. */
export function isValidatedSourceDecomposition(value: SourceDecomposition): boolean { return records.has(value); }

function operation(value: unknown, path: RawPath): DecompositionOperation {
  requireThat(value !== null && typeof value === 'object' && !Array.isArray(value), 'expected an operation', path);
  const v = value as JsonObject;
  if (v.kind === 'expose') { object(v, ['kind', 'target'], path); requireThat(v.target === 'term' || v.target === 'type', 'invalid exposure target', path); }
  else if (v.kind === 'focus') { object(v, ['kind', 'path'], path); requireThat(isSourceOccurrencePath(v.path), 'invalid focus path', path); }
  else if (v.kind === 'fields' || v.kind === 'typeComponent' || v.kind === 'logical') object(v, ['kind'], path);
  else { object(v, ['kind', 'index'], path); requireThat(v.kind === 'project' && operational(v.index, [...path, 'index']) < 16, 'invalid direct field index', path); }
  return v as unknown as DecompositionOperation;
}
function recipe(value: unknown, seedPath: SourceOccurrenceStep[], version: 1 | 2 | 3): DecompositionOperation[] {
  const ops = array(value, ['operations']);
  requireThat(ops.length >= 1 && ops.length <= DECOMPOSITION_MAX_OPERATIONS, 'expected one to eight operations', ['operations']);
  let length = seedPath.length, reserved = 6;
  ops.forEach((v, i) => { const op = operation(v, ['operations', i]);
    if (version === 1) requireThat(op.kind === (i % 2 ? 'focus' : 'expose'), 'operations must alternate expose and focus', ['operations', i]);
    else if (op.kind === 'project') requireThat(i > 0 && (ops[i - 1] as JsonObject).kind === 'fields', 'projection requires its immediately preceding field catalogue', ['operations', i]);
    requireThat(version === 3 || (op.kind !== 'typeComponent' && op.kind !== 'logical'), 'type and logical inspection require version three', ['operations', i]);
    reserved += op.kind === 'logical' ? 4 : op.kind === 'fields' ? 0 : op.kind === 'focus' || op.kind === 'typeComponent' ? 2 : 3;
    if (op.kind === 'focus') length += op.path.length;
  });
  requireThat(version !== 3 || reserved <= 30, 'decomposition plan exceeds its reserved thirty-check limit', ['operations']);
  requireThat(length <= 128, 'combined ordinary paths exceed 128 steps', ['operations']);
  return ops as unknown as DecompositionOperation[];
}
/** Read an already structurally checked CTel directly, preserving genuine lets. */
function closureItems(input: PositionalStructuralInput): ClosureItem[] {
  const reversed: ClosureItem[] = []; let tel = input.home.telescope as JsonValue[];
  while (tel[0] !== 'nil') {
    if (tel[0] === 'port') { const port = tel[2] as JsonObject; reversed.push({ name: port.name, type: tel[3], info: port.info }); }
    else reversed.push({ name: tel[2], nondep: tel[3] as boolean, type: tel[4], value: tel[5] });
    tel = tel[1] as JsonValue[];
  }
  return reversed.reverse();
}
function triple(value: unknown, path: RawPath): PositionalStructuralInput {
  const v = object(value, ['home', 'term', 'type'], path), h = object(v.home, ['arity', 'telescope'], [...path, 'home']);
  requireThat(operational(h.arity, [...path, 'home', 'arity']) <= 128, 'positional home exceeds 128 entries', [...path, 'home']);
  const input = v as unknown as PositionalStructuralInput;
  const drawing = buildPositionalStructuralDrawing(input, { sourceIdentity: 'decomposition-validation', sourcePath: path });
  if (!drawing.ok) return bad(drawing.error.message, drawing.error.path, drawing.error.code);
  const read = readPositionalStructuralDrawing(drawing.value);
  if (!read.ok) return bad(read.error.message, read.error.path, read.error.code);
  exact(read.value, v, path);
  const items = closureItems(input);
  items.forEach((item, i) => { validateHeadExpression(item.type, i, [...path, 'home', 'telescope']);
    if (item.value !== undefined) validateHeadExpression(item.value, i, [...path, 'home', 'telescope']); });
  validateHeadExpression(input.term, items.length, [...path, 'term']);
  validateHeadExpression(input.type, items.length, [...path, 'type']);
  return input;
}
function checkpoint(operation: DecompositionOperation, input: PositionalStructuralInput, output: DecompositionCandidate): DecompositionCheckpoint {
  const { checking: _checking, ...candidate } = output; void _checking;
  return { operation, input, candidate };
}
function validated(history: DecompositionHistory): DecompositionHistory {
  return histories.has(history) ? history : validateDecompositionHistory(history);
}
/** Origins are checked by the host separately. Pass only snapshot/record bundle
 * projections here; saved data undergo the same bounded syntax validation. */
export function validateDecompositionHistory(value: unknown): DecompositionHistory {
  preflight(value, DECOMPOSITION_HISTORY_BYTES, ['history'], false, 128, DECOMPOSITION_HISTORY_BYTES);
  const v = object(value, ['snapshot', 'occurrence', 'seed', 'attempts'], ['history']);
  const snapshot = shared.validated(v.snapshot as unknown as SourceSnapshot);
  const occurrence = validateSourceOccurrence(v.occurrence, snapshot);
  requireThat(occurrence.checking.status === 'captured' && occurrence.checking.action.status === 'completed'
    && occurrence.checking.selected !== null, 'history requires a completed original selected occurrence', ['history', 'occurrence']);
  triple(occurrence.checking.selected, ['history', 'occurrence', 'checking', 'selected']);
  let seed: DecompositionHistory['seed'] = null;
  if (v.seed !== null) {
    const s = object(v.seed, ['snapshot', 'record'], ['history', 'seed']);
    const seedSnapshot = shared.validated(s.snapshot as unknown as SourceSnapshot);
    seed = { snapshot: seedSnapshot, record: validateSourceHeadExposure(s.record, seedSnapshot, { snapshot, occurrence }) };
  }
  const attempts = array(v.attempts, ['history', 'attempts']);
  requireThat(attempts.length <= DECOMPOSITION_MAX_ATTEMPTS, 'history exceeds eight attempts', ['history', 'attempts']);
  const history: DecompositionHistory = { snapshot, occurrence, seed, attempts: [] };
  for (let i = 0; i < attempts.length; i++) {
    const entry = object(attempts[i], ['snapshot', 'record'], ['history', 'attempts', i]);
    const fresh = shared.validated(entry.snapshot as unknown as SourceSnapshot);
    const record = validateRecord(entry.record, fresh, history);
    history.attempts.push({ snapshot: fresh, record });
  }
  tools.freeze(json(history)); histories.add(history); return history;
}
function parentIn(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number, version: 1 | 2 | 3): DecompositionParent {
  requireThat(UUID.test(text(previousCaptureId, 36, ['previousCaptureId'])), 'invalid previous capture identity', ['previousCaptureId']);
  operational(parentStepIndex, ['parentStepIndex']);
  if (previousCaptureId === history.occurrence.captureId) {
    requireThat(version >= 2 && parentStepIndex === 0, 'only v2 or later has an original empty operation prefix', ['parentStepIndex']);
    const c = history.occurrence.checking;
    requireThat(c.status === 'captured' && c.action.status === 'completed' && c.selected, 'original occurrence has no completed pair', ['previousCaptureId']);
    return { operation: null, result: c.selected, operations: [], expectedHistory: [] };
  }
  let checkpoints: DecompositionCheckpoint[];
  if (history.seed && previousCaptureId === history.seed.record.captureId) {
    requireThat(parentStepIndex === 0, 'a v1 seed has only step zero', ['parentStepIndex']);
    const c = history.seed.record.checking;
    requireThat(c.status === 'captured' && c.action.status === 'completed' && c.selected !== null
      && c.exposure?.status === 'candidate' && c.exposure.checking.status === 'completed', 'seed has no completed exposure candidate', ['previousCaptureId']);
    triple(c.exposure.result, ['seed', 'checking', 'exposure', 'result']);
    checkpoints = [checkpoint({ kind: 'expose', target: history.seed.record.target }, c.selected, c.exposure)];
  } else {
    const record = history.attempts.find(a => a.record.captureId === previousCaptureId)?.record;
    requireThat(record && record.checking.status === 'captured' && parentStepIndex < record.checking.steps.length,
      'unknown retained operation', ['parentStepIndex']);
    requireThat(version === 3 || (version === 2 && record.schema !== 'definograph.source-decomposition.v3') || record.schema === 'definograph.source-decomposition.v1', 'an older version cannot reinterpret a newer parent', ['previousCaptureId']);
    checkpoints = record.checking.steps.slice(0, parentStepIndex + 1).map(step => {
      requireThat(step.output.status === 'candidate' && step.output.checking.status === 'completed'
        && (step.replay === 'matched' || step.replay === 'new'), 'operation is not eligible for continuation', ['parentStepIndex']);
      return checkpoint(step.operation, step.input, step.output);
    });
  }
  const last = checkpoints[checkpoints.length - 1];
  return { operation: last.operation, result: last.candidate.result,
    ...(last.operation.kind === 'fields' && 'catalogue' in last.candidate ? { catalogue: last.candidate.catalogue } : {}),
    operations: checkpoints.map(c => c.operation), expectedHistory: checkpoints };
}
export function decompositionParent(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number, version: 1 | 2 | 3 = 1): DecompositionParent {
  const result = parentIn(validated(history), previousCaptureId, parentStepIndex, version); tools.freeze(json(result)); return result;
}
/** Test an actual term occurrence before a live request. The native/parser
 * boundary can still retain an explicit refusal for a nonexistent path. */
export function isDecompositionFocusPath(input: PositionalStructuralInput, path: unknown): path is SourceOccurrenceStep[] {
  try {
    preflight(input, RECORD_BYTES, ['result'], false, 120); preflight(path, 8192, ['path']);
    if (!isSourceOccurrencePath(path)) return false;
    const pair = triple(input, ['result']);
    return occurrenceRules.selectedAt(pair.term, pair.home.telescope, closureItems(pair), path) !== undefined;
  } catch { return false; }
}
function planIn(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number, next: DecompositionOperation, version: 1 | 2 | 3, requireActualFocus = false) {
  requireThat(history.attempts.length < DECOMPOSITION_MAX_ATTEMPTS, 'eight attempts already retained', ['attempts']);
  const parent = parentIn(history, previousCaptureId, parentStepIndex, version);
  const operations = recipe([...parent.operations, next], history.occurrence.path, version);
  requireThat(next.kind !== 'project' || parent.operation?.kind === 'fields' && parent.catalogue?.fields[next.index],
    'field choice is not in the retained predecessor catalogue', ['operation']);
  requireThat(!requireActualFocus || next.kind !== 'focus' || isDecompositionFocusPath(parent.result, next.path),
    'focus path does not address an ordinary occurrence of the retained result term', ['operation', 'path']);
  return { operations, expectedHistory: parent.expectedHistory };
}
export function decompositionPlan(history: DecompositionHistory, previousCaptureId: string, parentStepIndex: number, next: DecompositionOperation, version: 1 | 2 | 3 = 1) {
  preflight(next, 8192, ['operation']); operation(next, ['operation']);
  const result = planIn(validated(history), previousCaptureId, parentStepIndex, next, version, true);
  // Detach the caller's mutable newly appended operation before freezing.
  const copy = tools.parse(canonical(json(result))) as unknown as typeof result; tools.freeze(json(copy)); return copy;
}
function stopValue(value: JsonValue, path: RawPath): JsonObject {
  const result = object(value, ['status', 'kind', 'phase', 'reason'], path);
  shared.unavailable(result, path); return result;
}
function focusDeclarations(result: PositionalStructuralInput, items: ClosureItem[], prefix: JsonValue, params: JsonValue[],
  checks: JsonValue[], start: number, count: number, tag = 'focus'): JsonObject[] {
  return Array.from({ length: count }, (_, i): JsonObject => {
    const component = i === 1, name = strName(strName(prefix, tag), component ? 'component' : 'context');
    if (component) {
      const receipt = checks[start + i] as JsonObject;
      requireThat(receipt?.declaration !== null && typeof receipt?.declaration === 'object' && !Array.isArray(receipt.declaration),
        'invalid focus component declaration', ['checking', 'checks', start + i]);
      const inferred = occurrenceRules.inferredType(receipt.declaration as JsonObject, items, ['checking', 'checks', start + i, 'declaration', 'type']);
      exact(inferred, result.type, ['checking', 'checks', start + i, 'declaration', 'type']);
    }
    return { kind: component ? 'defnDecl' : 'thmDecl', name, levelParams: params,
      type: close(items, component ? result.type : constant('True'), 'forallE'),
      value: close(items, component ? result.term : ['const', strName(named('True'), 'intro'), []], 'lam'), all: [name],
      ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
  });
}
function validateRecord(value: unknown, fresh: SourceSnapshot, history: DecompositionHistory): SourceDecomposition {
  preflight(value, RECORD_BYTES, [], false, 120);
  const v = object(tools.parse(canonical(json(value))), ['schema', 'parentCaptureId', 'previousCaptureId', 'parentStepIndex',
    'captureId', 'path', 'operations', 'policy', 'checking'], []);
  requireThat(v.schema === 'definograph.source-decomposition.v1' || v.schema === 'definograph.source-decomposition.v2' || v.schema === 'definograph.source-decomposition.v3', 'unsupported decomposition schema', ['schema']);
  const version = v.schema === 'definograph.source-decomposition.v3' ? 3 : v.schema === 'definograph.source-decomposition.v2' ? 2 : 1;
  const policy = version === 1 ? legacyPolicy : version === 2 ? fieldPolicy : logicalPolicy;
  requireThat(version >= 2 || history.seed, 'v1 history requires its legacy exposure seed', ['history', 'seed']);
  for (const key of ['parentCaptureId', 'previousCaptureId', 'captureId']) requireThat(UUID.test(text(v[key], 36, [key])), 'capture identity must be a UUID', [key]);
  exact(v.parentCaptureId, history.occurrence.captureId, ['parentCaptureId']); exact(v.path, history.occurrence.path, ['path']);
  const attempt = v.captureId as string;
  requireThat(attempt !== history.occurrence.captureId && attempt !== history.seed?.record.captureId
    && !history.attempts.some(a => a.record.captureId === attempt), 'capture identity must be fresh and unique', ['captureId']);
  const operations = recipe(v.operations, history.occurrence.path, version);
  const plan = planIn(history, v.previousCaptureId as string, operational(v.parentStepIndex, ['parentStepIndex']), operations[operations.length - 1], version);
  exact(operations, plan.operations, ['operations']); exact(v.policy, policy, ['policy']);
  if (fresh.checking.status === 'captured') exact(fresh.checking.binding.attempt, attempt, ['captureId']);
  const checking = v.checking as JsonObject;
  requireThat(checking !== null && typeof checking === 'object' && !Array.isArray(checking), 'invalid checking section', ['checking']);
  const parentRefusal = checking.status === 'unavailable' && checking.kind === 'prerequisite' && checking.phase === 'parent-match' && checking.attempted === false;
  requireThat((same(fresh.selection, history.snapshot.selection) && same(fresh.prepared, history.snapshot.prepared)
    && same(fresh.policy, history.snapshot.policy)) || parentRefusal, 'decomposition ran against a changed prepared parent', ['checking']);
  if (checking.status === 'unavailable') shared.unavailable(checking, ['checking'], true);
  else {
    object(checking, ['status', 'action', 'binding', 'selected', 'steps', 'stop', 'checks', 'audits', 'environmentSnapshotCount'], ['checking']);
    requireThat(checking.status === 'captured' && fresh.prepared.status === 'available', 'captured decomposition requires a fresh prepared frame', ['checking']);
    const prepared = fresh.prepared;
    requireThat(prepared.frame.originalDeclarations.length <= 128, 'captured context exceeds 128 entries', ['checking']);
    const baseAction = headRules.action(checking.action, ['checking', 'action']);
    const positional = shared.positionalBinding(prepared.frame, ['checking', 'binding']);
    const original = history.occurrence.checking;
    requireThat(original.status === 'captured' && original.selected !== null, 'missing original selected triple', ['parentCaptureId']);
    const prefix = strName(strName(named('StatementLens'), 'SourceDecomposition'), attempt);
    exact(checking.binding, { schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt,
      operation: policy.operation, sourceKind: 'namedDecomposition', declarationPrefix: prefix,
      universeParams: prepared.checkerUniverseParams, initialEnvironment: 0,
      context: { arity: positional.items.length, telescope: positional.telescope, registry: positional.registry, registryOrder: 'mostRecentFirst',
        originalDeclarations: prepared.frame.originalDeclarations, originalDeclarationOrder: 'oldestFirst' },
      sourceTerm: prepared.frame.sourceTerm, sourceType: prepared.frame.sourceType, positionalTerm: positional.term, positionalType: positional.type,
      path: history.occurrence.path.map(step => [step]), expectedSelected: original.selected,
      operations, expectedHistory: plan.expectedHistory }, ['checking', 'binding']);
    const checks = array(checking.checks, ['checking', 'checks']), steps = array(checking.steps, ['checking', 'steps']);
    requireThat(checks.length <= (version === 1 ? 26 : 30) && steps.length <= operations.length, 'decomposition exceeds its bounded schedule', ['checking']);
    const selected = occurrenceRules.selectedAt(positional.term, positional.telescope, positional.items, history.occurrence.path);
    requireThat(selected || checks.length <= 2, 'invalid source path has extraction receipts', ['checking', 'checks']);
    let selectedType: JsonValue | undefined;
    const extraDeclarations: JsonObject[] = [], labels = ['context', 'component', 'context', 'component', 'context', 'component'].slice(0, checks.length);
    if (baseAction.status === 'error') {
      requireThat(checks.length <= 6 && checking.selected === null && steps.length === 0 && checking.stop === null,
        'base error must retain only its executed base prefix', ['checking']);
    } else {
      requireThat(selected && checks.length >= 6, 'completed extraction requires six base receipts', ['checking']);
      const payload = headRules.selectedTriple(checking.selected, selected, ['checking', 'selected']);
      let preceding = triple(payload, ['checking', 'selected']); selectedType = payload.type;
      if (!same(payload, original.selected)) {
        const stop = stopValue(checking.stop, ['checking', 'stop']);
        requireThat(stop.kind === 'prerequisite' && stop.phase === 'selected-match' && steps.length === 0 && checks.length === 6,
          'changed selected triple requires a selected-match refusal', ['checking', 'stop']);
      } else {
        requireThat(steps.length > 0, 'completed matching base requires its first operation or explicit operation refusal', ['checking', 'steps']);
        let offset = 6, stopped = false, catalogue: DirectFieldCatalogue | undefined;
        steps.forEach((rawStep, i) => {
          const p: RawPath = ['checking', 'steps', i];
          const step = object(rawStep, ['index', 'operation', 'input', 'output', 'receiptStart', 'receiptCount', 'replay'], p);
          requireThat(!stopped, 'step follows a stopped operation', p);
          exact(step.index, i, [...p, 'index']); exact(step.operation, operations[i], [...p, 'operation']); exact(step.input, preceding, [...p, 'input']);
          exact(step.receiptStart, offset, [...p, 'receiptStart']);
          const count = operational(step.receiptCount, [...p, 'receiptCount']), maximum = operations[i].kind === 'fields' ? 0 : operations[i].kind === 'logical' ? ((preceding.term as JsonValue[])[0] === 'forallE' ? 4 : 2) : operations[i].kind === 'focus' || operations[i].kind === 'typeComponent' ? 2 : 3;
          requireThat(count <= maximum && offset + count <= checks.length, 'invalid operation receipt span', p);
          const out = step.output as JsonObject, op = operations[i];
          requireThat(out !== null && typeof out === 'object' && !Array.isArray(out), 'missing operation output', [...p, 'output']);
          if (out.status === 'unavailable') {
            shared.unavailable(out, [...p, 'output']); requireThat(count === 0, 'unavailable operation has receipts', p);
            exact(step.replay, 'not-compared', [...p, 'replay']); exact(checking.stop, out, ['checking', 'stop']); stopped = true;
          } else {
            const stepPrefix = strName(prefix, `step${i}`), items = closureItems(preceding);
            let result: PositionalStructuralInput;
            if (op.kind === 'expose') {
              headRules.validateCandidate(out, json(preceding) as JsonObject, op.target, items, [...p, 'output'], attempt);
              result = triple(out.result, [...p, 'output', 'result']);
              extraDeclarations.push(...headRules.exposureDeclarations(out, items, stepPrefix, prepared.checkerUniverseParams, count));
              labels.push(...['context', 'component', 'conversion'].slice(0, count));
            } else if (op.kind === 'focus') {
              object(out, ['status', 'result', 'checking'], [...p, 'output']); requireThat(out.status === 'candidate', 'invalid focus status', p);
              const focus = occurrenceRules.selectedAt(preceding.term, preceding.home.telescope, items, op.path);
              requireThat(focus, 'focus candidate addresses a nonexistent ordinary occurrence', p);
              headRules.selectedTriple(out.result, focus, [...p, 'output', 'result']); result = triple(out.result, [...p, 'output', 'result']);
              // With zero/one receipts U remains scoped retained data. Only a real
              // component receipt can independently associate its inferred type.
              extraDeclarations.push(...focusDeclarations(result, focus.items, stepPrefix, prepared.checkerUniverseParams, checks, offset, count));
              labels.push(...['context', 'component'].slice(0, count));
            } else if (op.kind === 'typeComponent') {
              object(out, ['status', 'result', 'checking'], [...p, 'output']);
              requireThat(out.status === 'candidate', 'invalid type-component status', p);
              result = triple(out.result, [...p, 'output', 'result']);
              exact(result.home, preceding.home, [...p, 'output', 'result', 'home']);
              exact(result.term, preceding.type, [...p, 'output', 'result', 'term']);
              extraDeclarations.push(...focusDeclarations(result, items, stepPrefix, prepared.checkerUniverseParams, checks, offset, count, 'typeComponent'));
              labels.push(...['context', 'component'].slice(0, count));
            } else if (op.kind === 'logical') {
              const logical = validateLogicalCandidate(out, preceding, prepared.checkerUniverseParams, [...p, 'output']);
              result = preceding;
              extraDeclarations.push(...logicalDeclarations(logical, preceding, items, stepPrefix, prepared.checkerUniverseParams, count));
              labels.push(...['logical.root.context', 'logical.root.component', 'logical.domain.context', 'logical.domain.component'].slice(0, count));
            } else if (op.kind === 'fields') {
              object(out, ['status', 'result', 'catalogue', 'checking'], [...p, 'output']);
              requireThat(out.status === 'candidate', 'invalid catalogue status', [...p, 'output']);
              exact(out.result, preceding, [...p, 'output', 'result']); exact(out.checking, { status: 'completed' }, [...p, 'output', 'checking']);
              catalogue = validateDirectFieldCatalogue(out.catalogue, preceding, prepared.checkerUniverseParams, [...p, 'output', 'catalogue']);
              result = preceding;
            } else {
              requireThat(catalogue && operations[i - 1]?.kind === 'fields', 'projection lacks its immediate catalogue', p);
              validateDirectFieldCandidate(out, preceding, catalogue, op.index, prepared.checkerUniverseParams, [...p, 'output']);
              result = triple(out.result, [...p, 'output', 'result']);
              extraDeclarations.push(...directFieldDeclarations(out, items, stepPrefix, prepared.checkerUniverseParams, count));
              labels.push(...['context', 'component', 'conversion'].slice(0, count));
            }
            const state = headRules.action(out.checking, [...p, 'output', 'checking']);
            if (state.status === 'error') {
              exact(step.replay, 'not-compared', [...p, 'replay']);
              const stop = stopValue(checking.stop, ['checking', 'stop']);
              requireThat((stop.kind === 'error' || stop.kind === 'limit') && stop.phase === 'operation-checking', 'candidate error requires operation-checking stop', ['checking', 'stop']);
              stopped = true;
            } else {
              requireThat(count === maximum, 'completed operation lacks its full receipt schedule', p);
              if (i < plan.expectedHistory.length) {
                const matched = same(checkpoint(op, preceding, out as unknown as DecompositionCandidate), plan.expectedHistory[i]);
                exact(step.replay, matched ? 'matched' : 'mismatch', [...p, 'replay']);
                if (!matched) {
                  const stop = stopValue(checking.stop, ['checking', 'stop']);
                  requireThat(stop.kind === 'prerequisite' && stop.phase === 'history-match', 'historical semantic change requires history-match refusal', ['checking', 'stop']);
                  stopped = true;
                }
              } else exact(step.replay, 'new', [...p, 'replay']);
            }
            preceding = result;
            if (op.kind !== 'fields') catalogue = undefined;
          }
          offset += count;
        });
        requireThat(offset === checks.length, 'unassociated receipts follow the last operation', ['checking', 'checks']);
        if (!stopped) requireThat(steps.length === operations.length && checking.stop === null, 'incomplete operation sequence lacks explicit stop', ['checking']);
      }
    }
    const declarations = occurrenceRules.extractionDeclarations(checks.slice(0, 6), positional, selected, selectedType, prefix, prepared.checkerUniverseParams);
    declarations.push(...extraDeclarations);
    shared.validateReceipts(checking, attempt, policy.operation, declarations, { labels });
  }
  tools.freeze(v);
  const result = v as unknown as SourceDecomposition;
  records.add(result); return result;
}
export function validateSourceDecomposition(value: unknown, freshSnapshot: SourceSnapshot, history: DecompositionHistory): SourceDecomposition {
  return validateRecord(value, shared.validated(freshSnapshot), validated(history));
}
