/** Exact one-step exposure records. Validation checks syntax and retained
 * associations, not producer authority, present environment or admission. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing, type PositionalStructuralInput } from '../packets/structure';
import { sourceSnapshotValidation as shared, type SnapshotAudit, type SnapshotBinding, type SnapshotReceipt,
  type SnapshotUnavailable, type SourceSnapshot, type ClosureItem } from './source-snapshot';
import { isSourceOccurrencePath, sourceOccurrenceValidation as occurrenceRules, validateSourceOccurrence,
  type SourceOccurrence, type SourceOccurrenceStep } from './source-occurrence';
import { replayDefinitionHead, validateHeadExpression, validateHeadLevel, type HeadExposureDefinition } from './head-exposure-replay';

export type HeadExposureTarget = 'term' | 'type';
export type HeadExposureAction = { status: 'completed' } | { status: 'error'; reason: string };
export interface HeadExposureCandidate {
  status: 'candidate'; before: JsonValue; result: PositionalStructuralInput; definition: HeadExposureDefinition;
  actualLevels: JsonValue[]; arguments: JsonValue[]; betaApplications: number; carrierSort: JsonValue; checking: HeadExposureAction;
}
export interface SourceHeadExposure {
  schema: 'definograph.source-head-exposure.v1'; parentCaptureId: string; captureId: string;
  path: SourceOccurrenceStep[]; target: HeadExposureTarget;
  policy: { id: 'safe-definition-head-v1'; operation: 'editor-head-exposure'; preparation: 'Lean.instantiateMVars';
    universeSubstitution: 'structural'; reduction: 'original-lambda-spine'; heartbeatBound: ['nat', string]; retainedMetadata: 'definograph.raw.v1' };
  checking: (SnapshotUnavailable & { attempted: boolean }) | {
    status: 'captured'; action: HeadExposureAction;
    binding: Omit<SnapshotBinding, 'operation' | 'sourceKind'> & { operation: 'editor-head-exposure'; sourceKind: 'namedHeadExposure';
      path: [SourceOccurrenceStep][]; target: HeadExposureTarget; expectedSelected: PositionalStructuralInput };
    selected: PositionalStructuralInput | null; exposure: SnapshotUnavailable | HeadExposureCandidate | null;
    checks: SnapshotReceipt[]; audits: SnapshotAudit[]; environmentSnapshotCount: number;
  };
}
const { bad, requireThat: assertThat, preflight, object, array, text, exact, strName, named, constant, close, UUID } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = assertThat;
const policy: SourceHeadExposure['policy'] = { id: 'safe-definition-head-v1', operation: 'editor-head-exposure', preparation: 'Lean.instantiateMVars',
  universeSubstitution: 'structural', reduction: 'original-lambda-spine', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' };
const same = (a: unknown, b: unknown) => createExactJsonTools().canonical(a as JsonValue) === createExactJsonTools().canonical(b as JsonValue);
function action(value: unknown, path: RawPath): JsonObject {
  const a = value as JsonObject;
  requireThat(a !== null && typeof a === 'object' && !Array.isArray(a), 'invalid action status', path);
  if (a.status === 'completed') object(a, ['status'], path);
  else { object(a, ['status', 'reason'], path); requireThat(a.status === 'error', 'unsupported action status', path); text(a.reason, 4096, [...path, 'reason'], false); }
  return a;
}
function selectedTriple(value: JsonValue, selected: NonNullable<ReturnType<typeof occurrenceRules.selectedAt>>, path: RawPath): JsonObject {
  const payload = object(value, ['home', 'term', 'type'], path);
  exact(payload.home, { arity: selected.items.length, telescope: selected.telescope }, [...path, 'home']);
  exact(payload.term, selected.term, [...path, 'term']);
  occurrenceRules.core(payload.type, selected.items.length, [...path, 'type']);
  return payload;
}


/** Pure candidate replay shared by single and repeated exposure records. */
function validateCandidate(value: JsonValue, payload: JsonObject, target: HeadExposureTarget,
  items: ClosureItem[], p: RawPath, identity: string): JsonObject {
  const candidate = object(value, ['status', 'before', 'result', 'definition', 'actualLevels', 'arguments', 'betaApplications', 'carrierSort', 'checking'], p);
  requireThat(candidate.status === 'candidate', 'unsupported exposure result status', p);
  exact(candidate.before, payload[target], [...p, 'before']);
  const result = object(candidate.result, ['home', 'term', 'type'], [...p, 'result']);
  exact(result.home, payload.home, [...p, 'result', 'home']);
  validateHeadExpression(result.term, items.length, [...p, 'result', 'term']);
  validateHeadExpression(result.type, items.length, [...p, 'result', 'type']);
  validateHeadLevel(candidate.carrierSort, [...p, 'carrierSort']);
  if (target === 'term') exact(result.type, payload.type, [...p, 'result', 'type']);
  else {
    const carrier = array(result.type, [...p, 'result', 'type']);
    requireThat(carrier.length === 2 && carrier[0] === 'sort', 'type exposure requires a literal Sort carrier', [...p, 'result', 'type']);
    exact(candidate.carrierSort, ['succ', carrier[1]], [...p, 'carrierSort']);
  }
  const replay = replayDefinitionHead(candidate.before, candidate.definition as unknown as HeadExposureDefinition, items.length, p);
  exact(result.term, replay.term, [...p, 'result', 'term']);
  exact(candidate.actualLevels, replay.actualLevels, [...p, 'actualLevels']);
  exact(candidate.arguments, replay.arguments, [...p, 'arguments']);
  requireThat(candidate.betaApplications === replay.betaApplications, 'consumed lambda count differs', [...p, 'betaApplications']);
  const drawn = buildPositionalStructuralDrawing(result as unknown as PositionalStructuralInput, { sourceIdentity: identity, sourcePath: [...p, 'result'] });
  if (!drawn.ok) return bad(drawn.error.message, drawn.error.path, drawn.error.code);
  const read = readPositionalStructuralDrawing(drawn.value);
  if (!read.ok) return bad(read.error.message, read.error.path, read.error.code);
  exact(read.value, result, [...p, 'result']);
  action(candidate.checking, [...p, 'checking']);
  return candidate;
}

function exposureDeclarations(candidate: JsonObject, items: ClosureItem[], prefix: JsonValue,
  universeParams: JsonValue[], count: number): JsonObject[] {
  const result = candidate.result as JsonObject;
  return Array.from({ length: count }, (_, i): JsonObject => {
    const conversion = i === 2, component = i === 1;
    const name = conversion ? strName(prefix, 'conversion') : strName(strName(prefix, 'result'), component ? 'component' : 'context');
    const eq: JsonValue = ['const', named('Eq'), [candidate.carrierSort]], refl: JsonValue = ['const', strName(named('Eq'), 'refl'), [candidate.carrierSort]];
    const type: JsonValue = conversion ? ['app', ['app', ['app', eq, result.type], candidate.before], result.term] : component ? result.type : constant('True');
    const value: JsonValue = conversion ? ['app', ['app', refl, result.type], candidate.before] : component ? result.term : ['const', strName(named('True'), 'intro'), []];
    return { kind: component ? 'defnDecl' : 'thmDecl', name, levelParams: universeParams,
      type: close(items, type, 'forallE'), value: close(items, value, 'lam'), all: [name], ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
  });
}
export const headExposureValidation = Object.freeze({ action, selectedTriple, validateCandidate, exposureDeclarations });

export function validateSourceHeadExposure(value: unknown, freshSnapshot: SourceSnapshot,
  parent: { snapshot: SourceSnapshot; occurrence: SourceOccurrence }): SourceHeadExposure {
  preflight(value, 1024 * 1024, [], false, 120);
  preflight(parent, 3 * 1024 * 1024, ['parent']);
  object(parent, ['snapshot', 'occurrence'], ['parent']);
  const parentSnapshot = shared.validated(parent.snapshot), parentOccurrence = validateSourceOccurrence(parent.occurrence, parentSnapshot);
  const parentChecking = parentOccurrence.checking;
  requireThat(parentChecking.status === 'captured' && parentChecking.action.status === 'completed' && parentChecking.selected !== null,
    'head exposure requires a retained selected occurrence', ['parent', 'occurrence']);
  if (parentSnapshot.checking.status === 'captured') exact(parentSnapshot.checking.binding.attempt, parentOccurrence.captureId, ['parent', 'snapshot', 'checking', 'binding', 'attempt']);
  const expectedSelected = parentChecking.selected;
  const fresh = shared.validated(freshSnapshot), tools = createExactJsonTools();
  const v = object(tools.parse(tools.canonical(value as JsonValue)), ['schema', 'parentCaptureId', 'captureId', 'path', 'target', 'policy', 'checking'], []);
  if (v.schema !== 'definograph.source-head-exposure.v1') bad('unsupported source head exposure version', ['schema'], 'unsupported');
  for (const key of ['parentCaptureId', 'captureId']) requireThat(UUID.test(text(v[key], 36, [key])), 'capture identity must be a UUID', [key]);
  exact(v.parentCaptureId, parentOccurrence.captureId, ['parentCaptureId']);
  requireThat(isSourceOccurrencePath(v.path), 'expected at most 64 ordinary path steps', ['path']);
  exact(v.path, parentOccurrence.path, ['path']);
  requireThat(v.target === 'term' || v.target === 'type', 'exposure target must be term or type', ['target']);
  const target = v.target, attempt = v.captureId as string;
  exact(v.policy, policy, ['policy']);
  if (fresh.checking.status === 'captured') exact(fresh.checking.binding.attempt, attempt, ['captureId']);
  const checking = v.checking as JsonObject;
  requireThat(checking !== null && typeof checking === 'object' && !Array.isArray(checking), 'invalid exposure checking section', ['checking']);
  const parentRefusal = checking.status === 'unavailable' && checking.kind === 'prerequisite' && checking.phase === 'parent-match' && checking.attempted === false;
  requireThat(attempt !== v.parentCaptureId || parentRefusal, 'an exposure requires a fresh capture or explicit unattempted parent refusal', ['captureId']);
  const matchesParent = same(fresh.selection, parentSnapshot.selection) && same(fresh.prepared, parentSnapshot.prepared) && same(fresh.policy, parentSnapshot.policy);
  requireThat(matchesParent || parentRefusal, 'exposure checking ran against a changed prepared parent', ['checking']);
  if (checking.status === 'unavailable') shared.unavailable(checking, ['checking'], true);
  else {
    object(checking, ['status', 'action', 'binding', 'selected', 'exposure', 'checks', 'audits', 'environmentSnapshotCount'], ['checking']);
    requireThat(checking.status === 'captured', 'unsupported exposure checking status', ['checking']);
    requireThat(fresh.prepared.status === 'available', 'captured exposure requires its fresh prepared frame', ['checking']);
    const prepared = fresh.prepared;
    requireThat(prepared.frame.originalDeclarations.length <= 128, 'captured context exceeds 128 entries', ['checking']);
    const outerAction = action(checking.action, ['checking', 'action']);
    const positional = shared.positionalBinding(prepared.frame, ['checking', 'binding']);
    const prefix = strName(strName(named('StatementLens'), 'SourceHeadExposure'), attempt);
    exact(checking.binding, { schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt,
      operation: policy.operation, sourceKind: 'namedHeadExposure', declarationPrefix: prefix,
      universeParams: prepared.checkerUniverseParams, initialEnvironment: 0,
      context: { arity: positional.items.length, telescope: positional.telescope, registry: positional.registry, registryOrder: 'mostRecentFirst',
        originalDeclarations: prepared.frame.originalDeclarations, originalDeclarationOrder: 'oldestFirst' },
      sourceTerm: prepared.frame.sourceTerm, sourceType: prepared.frame.sourceType, positionalTerm: positional.term, positionalType: positional.type,
      path: (v.path as SourceOccurrenceStep[]).map(step => [step]), target, expectedSelected }, ['checking', 'binding']);
    const checks = array(checking.checks, ['checking', 'checks']);
    requireThat(checks.length <= 9, 'exposure has more than nine receipts', ['checking', 'checks']);
    const selected = occurrenceRules.selectedAt(positional.term, positional.telescope, positional.items, v.path as SourceOccurrenceStep[]);
    requireThat(selected || checks.length <= 2, 'invalid path cannot have extraction receipts', ['checking', 'checks']);
    let selectedType: JsonValue | undefined;
    let candidate: JsonObject | undefined;
    if (outerAction.status === 'error') {
      requireThat(checks.length <= 6 && checking.selected === null && checking.exposure === null, 'base action error must retain only its executed base prefix', ['checking']);
    } else {
      requireThat(selected && checks.length >= 6, 'completed base extraction requires its six receipts and selected source', ['checking']);
      const payload = selectedTriple(checking.selected, selected, ['checking', 'selected']); selectedType = payload.type;
      const exposure = checking.exposure as JsonObject, p: RawPath = ['checking', 'exposure'];
      requireThat(exposure !== null && typeof exposure === 'object' && !Array.isArray(exposure), 'missing exposure result', p);
      if (exposure.status === 'unavailable') {
        shared.unavailable(exposure, p);
        requireThat(checks.length === 6, 'unavailable exposure retains exactly six base checks', ['checking', 'checks']);
        requireThat(same(payload, expectedSelected) || (exposure.kind === 'prerequisite' && exposure.phase === 'selected-match'), 'changed selected triple requires its explicit prerequisite refusal', p);
      } else {
        exact(payload, expectedSelected, ['checking', 'selected']);
        candidate = validateCandidate(exposure, payload, target, selected.items, p, attempt);
        const candidateAction = action(candidate.checking, [...p, 'checking']);
        requireThat(candidateAction.status !== 'completed' || checks.length === 9, 'completed candidate requires all nine receipts', ['checking', 'checks']);
      }
    }
    const declarations = occurrenceRules.extractionDeclarations(checks.slice(0, 6), positional, selected, selectedType, prefix, prepared.checkerUniverseParams);
    if (candidate) declarations.push(...exposureDeclarations(candidate, selected!.items, prefix, prepared.checkerUniverseParams, checks.length - 6));
    shared.validateReceipts(checking, attempt, policy.operation, declarations, {
      labels: ['context', 'component', 'context', 'component', 'context', 'component', 'context', 'component', 'conversion'].slice(0, checks.length),
    });
  }
  tools.freeze(v); return v as unknown as SourceHeadExposure;
}
