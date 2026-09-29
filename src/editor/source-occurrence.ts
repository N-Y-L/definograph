/** Exact associations for a fresh source-occurrence checking record. These
 * immutable records neither authenticate their producer nor certify typing. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { validateExpr } from '../packets/syntax';
import { sourceSnapshotValidation as shared, type ClosureItem, type SnapshotAudit,
  type SnapshotBinding, type SnapshotReceipt, type SnapshotUnavailable, type SourceSnapshot } from './source-snapshot';

export type SourceOccurrenceStep = 'appFun' | 'appArg' | 'lamDomain' | 'lamBody' | 'piDomain'
  | 'piBody' | 'letType' | 'letValue' | 'letBody' | 'projValue';
export interface SourceOccurrence {
  schema: 'definograph.source-occurrence.v1'; parentCaptureId: string; captureId: string;
  path: SourceOccurrenceStep[];
  policy: { id: 'named-extraction-v1'; operation: 'editor-occurrence'; preparation: 'Lean.instantiateMVars';
    heartbeatBound: ['nat', string]; retainedMetadata: 'definograph.raw.v1' };
  checking: (SnapshotUnavailable & { attempted: boolean }) | {
    status: 'captured'; action: { status: 'completed' } | { status: 'error'; reason: string };
    binding: Omit<SnapshotBinding, 'operation' | 'sourceKind'> & {
      operation: 'editor-occurrence'; sourceKind: 'namedExtraction'; path: [SourceOccurrenceStep][];
    };
    selected: null | { home: { arity: number; telescope: JsonValue }; term: JsonValue; type: JsonValue };
    checks: SnapshotReceipt[]; audits: SnapshotAudit[]; environmentSnapshotCount: number;
  };
}
const { bad, object, array, text, exact, preflight, unavailable,
  strName, named, constant, UUID, positionalBinding, close, validateReceipts } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const EDGES: Record<string, Partial<Record<SourceOccurrenceStep, number>>> = {
  app: { appFun: 1, appArg: 2 }, lam: { lamDomain: 2, lamBody: 3 },
  forallE: { piDomain: 2, piBody: 3 }, letE: { letType: 2, letValue: 3, letBody: 4 }, proj: { projValue: 3 },
};
const STEPS = new Set(Object.values(EDGES).flatMap(value => Object.keys(value)));
const ORDINARY = new Set(['bvar', 'fvar', 'sort', 'const', 'app', 'lam', 'forallE', 'letE', 'lit', 'proj']);
const prefixFor = (id: string): JsonValue => strName(strName(named('StatementLens'), 'SourceOccurrence'), id);

export function isSourceOccurrencePath(value: unknown): value is SourceOccurrenceStep[] {
  try {
    if (!Array.isArray(value) || value.length > 64 || Reflect.ownKeys(value).length !== value.length + 1) return false;
    for (let i = 0; i < value.length; i++) {
      const property = Object.getOwnPropertyDescriptor(value, i);
      if (!property?.enumerable || !Object.hasOwn(property, 'value') || !STEPS.has(property.value)) return false;
    }
    return true;
  } catch { return false; }
}

/** Raw paths address actual prepared expression edges. Names, universes,
 * metadata, other frame fields and original-tree positions are never guessed. */
export function sourceOccurrencePath(snapshot: SourceSnapshot, rawPath: RawPath): SourceOccurrenceStep[] | undefined {
  const valid = shared.validated(snapshot);
  if (valid.prepared.status !== 'available' || !Array.isArray(rawPath)) return undefined;
  try { preflight(rawPath, 4096, []); } catch { return undefined; }
  if (rawPath.length < 3 || rawPath.length > 67 || rawPath[0] !== 'prepared'
    || rawPath[1] !== 'frame' || rawPath[2] !== 'sourceTerm') return undefined;
  let term = valid.prepared.frame.sourceTerm as JsonValue[];
  const result: SourceOccurrenceStep[] = [];
  for (const index of rawPath.slice(3)) {
    const edge = Object.entries(EDGES[String(term[0])] ?? {}).find(([, position]) => position === index);
    if (!edge) return undefined;
    result.push(edge[0] as SourceOccurrenceStep); term = term[index as number] as JsonValue[];
  }
  return ORDINARY.has(String(term[0])) ? result : undefined;
}

interface Selection { telescope: JsonValue; term: JsonValue; items: ClosureItem[] }
function selectedAt(root: JsonValue, initialTelescope: JsonValue, initialItems: ClosureItem[], path: SourceOccurrenceStep[]): Selection | undefined {
  let term = root, telescope = initialTelescope;
  const items = [...initialItems], frames: { parent: JsonValue[]; index: number }[] = [];
  for (const step of path) {
    const node = term as JsonValue[], index = EDGES[String(node[0])]?.[step];
    if (index === undefined) return undefined;
    if (step === 'lamBody' || step === 'piBody') {
      const item = { name: node[1], type: node[2], info: node[4] }; items.push(item);
      telescope = ['port', telescope, { name: item.name, info: item.info }, item.type];
    } else if (step === 'letBody') {
      const item = { name: node[1], type: node[2], value: node[3], nondep: node[5] as boolean }; items.push(item);
      telescope = ['letE', telescope, item.name, item.nondep, item.type, item.value];
    }
    frames.push({ parent: node, index }); term = node[index];
  }
  // Rebuild from addressed fields and sibling constructors, independently of
  // the emitted selected payload. This is syntax equality, not a proof flag.
  let rebuilt = term;
  for (const frame of frames.reverse()) { const parent = [...frame.parent]; parent[frame.index] = rebuilt; rebuilt = parent; }
  exact(rebuilt, root, ['path']);
  return { term, telescope, items };
}

/** Inferred receipt types can differ from the supplied source type. Require
 * complete Core syntax in this positional home, without performing inference. */
function core(value: JsonValue, arity: number, path: RawPath): void {
  try { validateExpr(value, arity, 2); } catch (error) { bad(error instanceof Error ? error.message : 'invalid Core expression', path); }
  const level = (value: JsonValue): void => {
    const node = value as JsonValue[];
    requireThat(node[0] !== 'mvar', 'Core type contains a universe metavariable', path);
    if (node[0] === 'succ') level(node[1]);
    else if (node[0] === 'max' || node[0] === 'imax') { level(node[1]); level(node[2]); }
  };
  const expression = (value: JsonValue): void => {
    const node = value as JsonValue[];
    requireThat(node[0] !== 'fvar' && node[0] !== 'mvar', 'Core type contains a named or unresolved variable', path);
    switch (node[0]) {
      case 'sort': level(node[1]); break;
      case 'const': (node[2] as JsonValue[]).forEach(level); break;
      case 'app': expression(node[1]); expression(node[2]); break;
      case 'lam': case 'forallE': expression(node[2]); expression(node[3]); break;
      case 'letE': expression(node[2]); expression(node[3]); expression(node[4]); break;
      case 'proj': expression(node[3]); break;
    }
  };
  expression(value);
}
function inferredType(declaration: JsonObject, items: ClosureItem[], path: RawPath): JsonValue {
  let type = declaration.type;
  for (const item of items) {
    const node = array(type, path);
    requireThat(node.length === (item.value === undefined ? 5 : 6), 'inferred declaration has the wrong closure shape', path);
    if (item.value === undefined) {
      exact([node[0], node[1], node[2], node[4]], ['forallE', item.name, item.type, item.info!], path); type = node[3];
    } else {
      exact([node[0], node[1], node[2], node[3], node[5]], ['letE', item.name, item.type, item.value, item.nondep ?? false], path); type = node[4];
    }
  }
  core(type, items.length, path); exact(declaration.type, close(items, type, 'forallE'), path); return type;
}

/** Reconstruct the six base declarations without inventing an occurrence record.
 * Record-specific prefix length, completion and selected-home rules remain with callers. */
function extractionDeclarations(checks: JsonValue[], positional: Selection & { type: JsonValue }, selected: Selection | undefined,
  selectedType: JsonValue | undefined, prefix: JsonValue, universeParams: JsonValue[]): JsonObject[] {
  return checks.map((receipt, i): JsonObject => {
      const selectedPair = i >= 4, component = i % 2 === 1;
      const items = selectedPair ? selected!.items : positional.items;
      const term = selectedPair ? selected!.term : positional.term;
      let declarationPrefix = strName(prefix, 'source');
      if (i >= 2) declarationPrefix = strName(strName(prefix, 'extraction'), selectedPair ? 'selected' : 'root');
      const name = strName(declarationPrefix, component ? 'component' : 'context');
      let type: JsonValue = constant('True');
      if (component) {
        if (i === 1) type = positional.type;
        else {
          requireThat(receipt !== null && typeof receipt === 'object' && !Array.isArray(receipt), 'invalid receipt', ['checking', 'checks', i]);
          const declaration = receipt.declaration as JsonObject;
          requireThat(declaration !== null && typeof declaration === 'object' && !Array.isArray(declaration), 'invalid inferred declaration', ['checking', 'checks', i, 'declaration']);
          type = inferredType(declaration, items, ['checking', 'checks', i, 'declaration', 'type']);
          if (i === 5 && selectedType !== undefined) exact(type, selectedType, ['checking', 'selected', 'type']);
        }
      }
      return { kind: component ? 'defnDecl' : 'thmDecl', name, levelParams: universeParams,
        type: close(items, type, 'forallE'),
        value: close(items, component ? term : ['const', strName(named('True'), 'intro'), []], 'lam'), all: [name],
        ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
    });
}

export function validateSourceOccurrence(value: unknown, snapshot: SourceSnapshot): SourceOccurrence {
  preflight(value, 768 * 1024, [], false, 120);
  const tools = createExactJsonTools();
  const v = object(tools.parse(tools.canonical(value as JsonValue)),
    ['schema', 'parentCaptureId', 'captureId', 'path', 'policy', 'checking'], []);
  if (v.schema !== 'definograph.source-occurrence.v1') bad('unsupported source occurrence version', ['schema'], 'unsupported');
  for (const key of ['parentCaptureId', 'captureId']) requireThat(UUID.test(text(v[key], 36, [key])), 'capture identity must be a UUID', [key]);
  requireThat(isSourceOccurrencePath(v.path), 'expected at most 64 ordinary constructor path steps', ['path']);
  const path = v.path as SourceOccurrenceStep[], attempt = v.captureId as string;
  exact(v.policy, { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars',
    heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' }, ['policy']);
  const valid = shared.validated(snapshot), checking = v.checking as JsonObject;
  requireThat(checking !== null && typeof checking === 'object' && !Array.isArray(checking), 'invalid occurrence checking section', ['checking']);
  requireThat(v.parentCaptureId !== v.captureId || (checking.status === 'unavailable' && checking.kind === 'prerequisite'
    && checking.phase === 'parent-match' && checking.attempted === false),
  'an occurrence requires a fresh capture identity or its explicit prerequisite refusal', ['captureId']);
  if (checking.status === 'unavailable') unavailable(checking, ['checking'], true);
  else {
    object(checking, ['status', 'action', 'binding', 'selected', 'checks', 'audits', 'environmentSnapshotCount'], ['checking']);
    requireThat(checking.status === 'captured', 'unsupported occurrence checking status', ['checking']);
    requireThat(valid.prepared.status === 'available', 'captured occurrence requires the exact fresh prepared frame', ['checking']);
    const prepared = valid.prepared;
    requireThat(prepared.frame.originalDeclarations.length <= 128, 'captured context exceeds 128 declarations', ['checking']);
    const action = checking.action as JsonObject;
    requireThat(action !== null && typeof action === 'object' && !Array.isArray(action), 'invalid capture action', ['checking', 'action']);
    if (action.status === 'completed') object(action, ['status'], ['checking', 'action']);
    else { object(action, ['status', 'reason'], ['checking', 'action']); requireThat(action.status === 'error', 'unsupported action status', ['checking', 'action']); text(action.reason, 4096, ['checking', 'action', 'reason'], false); }
    const binding = object(checking.binding, ['schema', 'naturalProfile', 'rawProfile', 'attempt', 'operation', 'sourceKind', 'declarationPrefix',
      'universeParams', 'initialEnvironment', 'context', 'sourceTerm', 'sourceType', 'positionalTerm', 'positionalType', 'path'], ['checking', 'binding']);
    const positional = positionalBinding(prepared.frame, ['checking', 'binding']);
    const prefix = prefixFor(attempt);
    exact(binding, { schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt,
      operation: 'editor-occurrence', sourceKind: 'namedExtraction', declarationPrefix: prefix,
      universeParams: prepared.checkerUniverseParams, initialEnvironment: 0,
      context: { arity: positional.items.length, telescope: positional.telescope, registry: positional.registry, registryOrder: 'mostRecentFirst',
        originalDeclarations: prepared.frame.originalDeclarations, originalDeclarationOrder: 'oldestFirst' },
      sourceTerm: prepared.frame.sourceTerm, sourceType: prepared.frame.sourceType, positionalTerm: positional.term, positionalType: positional.type,
      path: path.map(step => [step]) }, ['checking', 'binding']);
    const checks = array(checking.checks, ['checking', 'checks']);
    requireThat(checks.length <= 6 && (action.status !== 'completed' || checks.length === 6),
      'completed occurrence checking requires six receipts; errors retain only the executed prefix', ['checking', 'checks']);
    const selected = selectedAt(positional.term, positional.telescope, positional.items, path);
    requireThat(!!selected || checks.length <= 2, 'an invalid path cannot have extraction receipts', ['checking', 'checks']);
    let selectedType: JsonValue | undefined;
    if (action.status === 'completed') {
      requireThat(selected, 'completed occurrence requires an ordinary source path', ['path']);
      const payload = object(checking.selected, ['home', 'term', 'type'], ['checking', 'selected']);
      exact(payload.home, { arity: selected.items.length, telescope: selected.telescope }, ['checking', 'selected', 'home']);
      exact(payload.term, selected.term, ['checking', 'selected', 'term']);
      core(payload.type, selected.items.length, ['checking', 'selected', 'type']); selectedType = payload.type;
    } else requireThat(checking.selected === null, 'an action error retains no selected result', ['checking', 'selected']);
    const declarations = extractionDeclarations(checks, positional, selected, selectedType, prefix, prepared.checkerUniverseParams);
    validateReceipts(checking, attempt, 'editor-occurrence', declarations);
  }
  tools.freeze(v); return v as unknown as SourceOccurrence;
}

/** Pure exact-source helpers shared by fresh occurrence operations. */
export const sourceOccurrenceValidation = Object.freeze({ selectedAt, core, inferredType, extractionDeclarations });
