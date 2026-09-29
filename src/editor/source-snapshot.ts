/** Structural validation of editor capture data. A validated snapshot is an
 * immutable value, not proof of its producer, present environment or admission. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import { boundedNatural, type TaggedNatural } from '../packets/natural';
import { buildRawInspection, readRawInspection, type RawInspectionDrawing, type RawPath } from '../packets/raw';
import type { StructuralLocalKind, StructuralName } from '../packets/structure';

export type SnapshotUnavailableKind = 'unsupported' | 'error' | 'limit' | 'prerequisite';
export interface SnapshotUnavailable {
  status: 'unavailable'; kind: SnapshotUnavailableKind; phase: string; reason: string;
}
export interface SnapshotFrame {
  schema: 'definograph.raw-frame.v1'; naturalProfile: 2;
  originalDeclarations: JsonObject[]; sourceTerm: JsonValue; sourceType: JsonValue;
}
export type SnapshotOutcome = { tag: 'accepted' } | { tag: 'unknown'; message: string }
  | { tag: 'rejected'; kind: 'notConvertible' } | { tag: 'rejected'; kind: 'typeError'; detail: string };
export interface SnapshotReceipt {
  id: number; pair: string; label: string; displayLabel: string; declaration: JsonObject;
  subject: { attempt: string; pair: string; sequence: number; target: string; declaration: JsonObject };
  envBefore: number; envAfter: number; heartbeatBound: TaggedNatural; outcome: SnapshotOutcome;
}
export interface SnapshotAudit {
  checkId: number; subject: JsonObject; environment: number; category: 'declarationCheck';
  result: { tag: 'available'; axioms: StructuralName[] } | { tag: 'unavailable'; reason: string };
}
export interface SnapshotBinding {
  schema: 3; naturalProfile: 2; rawProfile: 'definograph.raw.v1'; attempt: string;
  operation: 'editor-source'; sourceKind: 'namedComponent'; declarationPrefix: StructuralName;
  universeParams: StructuralName[]; initialEnvironment: 0;
  context: { arity: number; telescope: JsonValue; registry: StructuralName[]; registryOrder: 'mostRecentFirst';
    originalDeclarations: JsonObject[]; originalDeclarationOrder: 'oldestFirst' };
  sourceTerm: JsonValue; sourceType: JsonValue; positionalTerm: JsonValue; positionalType: JsonValue;
}
/** The captured declarations, oldest first: each recorded name, which only checks alignment, and recorded kind. */
export function recordedContextEntries(binding: { context: { originalDeclarations: readonly JsonObject[] } }): { name: JsonValue; kind: StructuralLocalKind }[] {
  return binding.context.originalDeclarations.map(declaration => ({ name: declaration.userName, kind: declaration.kind as StructuralLocalKind }));
}
export type SnapshotChecking = (SnapshotUnavailable & { attempted: boolean }) | {
  status: 'captured'; action: { status: 'completed' } | { status: 'error'; reason: string };
  binding: SnapshotBinding; checks: SnapshotReceipt[]; audits: SnapshotAudit[]; environmentSnapshotCount: number;
};
export interface SourceSnapshot {
  schema: 'definograph.source-snapshot.v1';
  selection: { startByte: number; endByte: number; requestedStartByte: number; requestedEndByte: number; parentDeclaration: StructuralName | null };
  policy: { id: 'named-source-v1'; operation: 'editor-source'; preparation: 'Lean.instantiateMVars';
    heartbeatBound: TaggedNatural; retainedMetadata: 'definograph.raw.v1' };
  expectedType: { status: 'absent' } | { status: 'available'; expression: JsonValue } | SnapshotUnavailable;
  original: { status: 'available'; typeOrigin: 'inferred'; frame: SnapshotFrame } | SnapshotUnavailable;
  prepared: { status: 'available'; typeOrigin: 'inferred-instantiated'; frame: SnapshotFrame; checkerUniverseParams: StructuralName[] } | SnapshotUnavailable;
  checking: SnapshotChecking;
}
export interface SnapshotDrawings {
  original?: RawInspectionDrawing; prepared?: RawInspectionDrawing; expectedType?: RawInspectionDrawing;
}
export class SourceSnapshotError extends Error {
  constructor(readonly code: 'malformed' | 'unsupported' | 'limit', message: string, readonly path: RawPath = []) {
    super(`${path.length ? path.join('.') + ': ' : ''}${message}`); this.name = 'SourceSnapshotError';
  }
}
const SNAPSHOT_BYTES = 1536 * 1024;
const FRAME_BYTES = 256 * 1024;
const EXPECTED_BYTES = 128 * 1024;
const CHECKING_BYTES = 768 * 1024;
const RAW_NODES = 20_000, RAW_DEPTH = 96, RAW_TEXT = 128 * 1024;
const encoder = new TextEncoder();
const drawings = new WeakMap<SourceSnapshot, SnapshotDrawings>();
let occurrence = 0;
function bad(message: string, path: RawPath, code: SourceSnapshotError['code'] = 'malformed'): never {
  throw new SourceSnapshotError(code, message, [...path]);
}
function requireThat(condition: unknown, message: string, path: RawPath): asserts condition {
  if (!condition) bad(message, path);
}
function object(v: unknown, keys: string[], path: RawPath): JsonObject {
  requireThat(v !== null && typeof v === 'object' && !Array.isArray(v), 'expected an object', path);
  requireThat(Object.keys(v).length === keys.length && keys.every(k => Object.hasOwn(v, k)), 'unexpected or missing fields', path);
  return v as JsonObject;
}
function array(v: unknown, path: RawPath): JsonValue[] {
  requireThat(Array.isArray(v), 'expected an array', path); return v as JsonValue[];
}
function field(value: JsonObject, key: string): JsonValue { return value[key]; }
function text(v: unknown, maximum: number, path: RawPath, nonempty = true): string {
  requireThat(typeof v === 'string' && (!nonempty || v.length > 0), 'expected a string', path);
  if ([...v].length > maximum) bad(`string exceeds ${maximum} characters`, path, 'limit'); return v;
}
function operational(v: unknown, path: RawPath): number {
  requireThat(typeof v === 'number' && Number.isSafeInteger(v) && v >= 0, 'expected a nonnegative safe operational integer', path); return v;
}
function exact(a: JsonValue | unknown, b: JsonValue | unknown, path: RawPath): void {
  const { canonical } = createExactJsonTools();
  requireThat(canonical(a as JsonValue) === canonical(b as JsonValue), 'exact constructor association differs', path);
}
/** Before serialization, reject accessors, non-JSON properties, sparse arrays,
 * cycles and unsafe numbers. Count expanded occurrences, never object identity. */
function preflight(value: unknown, maxBytes: number, path: RawPath, raw = false, maximumDepth = raw ? RAW_DEPTH : 128, maximumNodes = raw ? RAW_NODES : 300_000): void {
  let bytes = 0, nodes = 0, textBytes = 0;
  const active = new Set<object>();
  const charge = (n: number, p: RawPath): void => { bytes += n; if (bytes > maxBytes) bad('serialized byte limit exceeded', p, 'limit'); };
  const string = (v: string, p: RawPath): void => {
    if (v.length > maxBytes) bad('string exceeds byte limit', p, 'limit');
    for (let i = 0; i < v.length; i++) {
      const c = v.charCodeAt(i);
      if (c >= 0xd800 && c <= 0xdbff) { const next = v.charCodeAt(++i); requireThat(next >= 0xdc00 && next <= 0xdfff, 'unpaired Unicode surrogate', p); }
      else requireThat(c < 0xdc00 || c > 0xdfff, 'unpaired Unicode surrogate', p);
    }
    textBytes += encoder.encode(v).length;
    if (raw && textBytes > RAW_TEXT) bad('raw cumulative UTF-8 text limit exceeded', p, 'limit');
    charge(encoder.encode(JSON.stringify(v)).length, p);
  };
  function visit(v: unknown, depth: number, p: RawPath): void {
    if (++nodes > maximumNodes || depth > maximumDepth) bad('JSON node or depth limit exceeded', p, 'limit');
    if (typeof v === 'string') { string(v, p); return; }
    if (v === null || typeof v === 'boolean') { charge(v === null ? 4 : v ? 4 : 5, p); return; }
    if (typeof v === 'number') { operational(v, p); charge(String(v).length, p); return; }
    requireThat(v !== null && typeof v === 'object', 'non-JSON value', p);
    requireThat(!active.has(v), 'cyclic value', p); active.add(v);
    const keys = Reflect.ownKeys(v);
    if (Array.isArray(v)) {
      requireThat(keys.length === v.length + 1, 'sparse or extended array', p);
      if (v.length > maximumNodes) bad('array exceeds node limit', p, 'limit');
      charge(2 + Math.max(0, v.length - 1), p);
      for (let i = 0; i < v.length; i++) {
        const d = Object.getOwnPropertyDescriptor(v, i);
        requireThat(d && d.enumerable && Object.hasOwn(d, 'value'), 'array must have dense data elements', [...p, i]);
        visit(d.value, depth + 1, [...p, i]);
      }
    } else {
      requireThat(Object.getPrototypeOf(v) === Object.prototype || Object.getPrototypeOf(v) === null, 'expected an ordinary JSON object', p);
      charge(2 + Math.max(0, keys.length - 1), p);
      for (const key of keys) {
        requireThat(typeof key === 'string', 'non-JSON property', p);
        const d = Object.getOwnPropertyDescriptor(v, key)!;
        requireThat(d.enumerable && Object.hasOwn(d, 'value'), 'object must have ordinary enumerable data properties', [...p, key]);
        // Keys count as JSON nodes, matching the native transport budget.
        visit(key, depth + 1, [...p, key]); charge(1, p); visit(d.value, depth + 1, [...p, key]);
      }
    }
    active.delete(v);
  }
  visit(value, 0, path);
}
function rawDrawing(value: JsonValue, family: 'frame' | 'expression' | 'dataValue', sourceIdentity: string, path: RawPath,
  cap = FRAME_BYTES): RawInspectionDrawing {
  preflight(value, cap, path, true);
  const built = buildRawInspection({ family, value }, { sourceIdentity, sourcePath: path,
    limits: { maxNodes: RAW_NODES, maxDepth: RAW_DEPTH, maxTextBytes: 2 * RAW_TEXT } });
  if (!built.ok) bad(built.error.message, built.error.path, built.error.code);
  const read = readRawInspection(built.value);
  if (!read.ok) bad(read.error.message, read.error.path, read.error.code);
  exact(read.value, { family, value }, path);
  return built.value;
}
function validName(v: JsonValue, path: RawPath): void {
  rawDrawing(['ofName', v], 'dataValue', 'snapshot-name', path, EXPECTED_BYTES);
}
function names(v: JsonValue, path: RawPath): StructuralName[] {
  const a = array(v, path); a.forEach((n, i) => validName(n, [...path, i])); return a as StructuralName[];
}
function unavailable(v: JsonObject, path: RawPath, checking = false): void {
  object(v, ['status', 'kind', 'phase', 'reason', ...(checking ? ['attempted'] : [])], path);
  requireThat(['unsupported', 'error', 'limit', 'prerequisite'].includes(String(v.kind)), 'unsupported unavailable kind', [...path, 'kind']);
  text(v.phase, 64, [...path, 'phase']); text(v.reason, 4096, [...path, 'reason'], false);
  if (checking) requireThat(typeof v.attempted === 'boolean', 'attempted must be a Boolean', [...path, 'attempted']);
}
function strName(parent: JsonValue, part: string): JsonValue { return ['str', parent, part]; }
const anon: JsonValue = ['anonymous'];
const named = (part: string): JsonValue => strName(anon, part);
const constant = (part: string): JsonValue => ['const', named(part), []];
const prefixFor = (id: string): JsonValue => strName(strName(named('StatementLens'), 'SourceSnapshot'), id);
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;

/** Deterministic parameter traversal mirrors Lean.collectLevelParams. Metadata
 * payloads and ignored original ldecl values do not contribute parameters. */
function universeParams(frame: SnapshotFrame): JsonValue[] {
  const found: JsonValue[] = [], seen = new Set<string>();
  const key = (value: JsonValue): string => JSON.stringify(value);
  const level = (value: JsonValue): void => {
    const a = value as JsonValue[];
    if (a[0] === 'param') { const k = key(a[1]); if (!seen.has(k)) { seen.add(k); found.push(a[1]); } }
    else if (a[0] === 'succ') level(a[1]);
    else if (a[0] === 'max' || a[0] === 'imax') { level(a[1]); level(a[2]); }
  };
  const expr = (value: JsonValue): void => {
    const a = value as JsonValue[];
    switch (a[0]) {
      case 'sort': level(a[1]); break;
      case 'const': (a[2] as JsonValue[]).forEach(level); break;
      case 'app': expr(a[1]); expr(a[2]); break;
      case 'lam': case 'forallE': expr(a[2]); expr(a[3]); break;
      case 'letE': expr(a[2]); expr(a[3]); expr(a[4]); break;
      case 'mdata': expr(a[2]); break;
      case 'proj': expr(a[3]); break;
    }
  };
  frame.originalDeclarations.forEach(d => { expr(d.type); if (field(d, 'constructor') === 'ldecl' && d.nondep === false) expr(d.value); });
  expr(frame.sourceTerm); expr(frame.sourceType); return found;
}
export interface ClosureItem { name: JsonValue; type: JsonValue; info?: JsonValue; value?: JsonValue; nondep?: boolean }
/** Reconstruct the exact named-to-positional syntax association. This verifies
 * neither the source environment nor dependent typing of that association. */
function positionalBinding(frame: SnapshotFrame, path: RawPath): {
  registry: JsonValue[]; telescope: JsonValue; term: JsonValue; type: JsonValue; items: ClosureItem[];
} {
  const registry: JsonValue[] = [], keys: string[] = [], items: ClosureItem[] = [];
  let telescope: JsonValue = ['nil'];
  const reify = (value: JsonValue, depth = 0): JsonValue => {
    const a = value as JsonValue[];
    switch (a[0]) {
      case 'fvar': {
        const index = keys.indexOf(JSON.stringify(a[1])); requireThat(index >= 0, 'captured source has an unregistered free variable', path);
        return ['bvar', ['nat', String(depth + index)]];
      }
      case 'bvar': try { boundedNatural(a[1], 2, depth); return a; } catch { return bad('captured source has an out-of-scope bound variable', path); }
      case 'mvar': case 'mdata': return bad('captured source lies outside the named checking profile', path);
      case 'sort': case 'const': {
        if (a[0] === 'const') requireThat(JSON.stringify(a[1]) !== JSON.stringify(named('sorryAx')),
          'captured source violates the placeholder policy', path);
        const visit = (u: JsonValue): void => { const l = u as JsonValue[]; requireThat(l[0] !== 'mvar', 'captured source contains a universe metavariable', path);
          if (l[0] === 'succ') visit(l[1]); else if (l[0] === 'max' || l[0] === 'imax') { visit(l[1]); visit(l[2]); } };
        if (a[0] === 'sort') visit(a[1]); else (a[2] as JsonValue[]).forEach(visit); return a;
      }
      case 'lit': return a;
      case 'app': return ['app', reify(a[1], depth), reify(a[2], depth)];
      case 'lam': case 'forallE': return [a[0], a[1], reify(a[2], depth), reify(a[3], depth + 1), a[4]];
      case 'letE': return ['letE', a[1], reify(a[2], depth), reify(a[3], depth), reify(a[4], depth + 1), a[5]];
      case 'proj': return ['proj', a[1], a[2], reify(a[3], depth)];
      default: return bad('unsupported captured source constructor', path);
    }
  };
  frame.originalDeclarations.forEach(d => {
    const key = JSON.stringify(d.fvarId); requireThat(!keys.includes(key), 'captured context has duplicate free-variable identities', path);
    const type = reify(d.type);
    if (field(d, 'constructor') === 'ldecl' && d.nondep === false) {
      const value = reify(d.value); items.push({ name: d.userName, type, value });
      telescope = ['letE', telescope, d.userName, false, type, value];
    } else {
      const info = field(d, 'constructor') === 'cdecl' ? d.binderInfo : 'default';
      items.push({ name: d.userName, type, info }); telescope = ['port', telescope, { name: d.userName, info }, type];
    }
    registry.unshift(d.fvarId); keys.unshift(key);
  });
  return { registry, telescope, term: reify(frame.sourceTerm), type: reify(frame.sourceType), items };
}
function close(items: ClosureItem[], body: JsonValue, binder: 'forallE' | 'lam'): JsonValue {
  return items.reduceRight<JsonValue>((value, item) => item.value !== undefined
    ? ['letE', item.name, item.type, item.value, value, item.nondep ?? false]
    : [binder, item.name, item.type, value, item.info!], body);
}
function checkOutcome(v: JsonValue, path: RawPath): string {
  requireThat(v !== null && typeof v === 'object' && !Array.isArray(v), 'invalid check outcome', path);
  if (v.tag === 'accepted') object(v, ['tag'], path);
  else if (v.tag === 'unknown') { object(v, ['tag', 'message'], path); text(v.message, 4096, [...path, 'message'], false); }
  else if (v.tag === 'rejected' && v.kind === 'notConvertible') object(v, ['tag', 'kind'], path);
  else if (v.tag === 'rejected' && v.kind === 'typeError') { object(v, ['tag', 'kind', 'detail'], path); text(v.detail, 4096, [...path, 'detail'], false); }
  else bad('unsupported check outcome', path, 'unsupported');
  return v.tag as string;
}

function validateChecking(value: JsonObject, prepared: SourceSnapshot['prepared']): void {
  const path: RawPath = ['checking'];
  requireThat(value !== null && typeof value === 'object' && !Array.isArray(value), 'invalid checking section', path);
  if (value.status === 'unavailable') { unavailable(value, path, true); return; }
  requireThat(value.status === 'captured', 'unsupported checking status', path);
  object(value, ['status', 'action', 'binding', 'checks', 'audits', 'environmentSnapshotCount'], path);
  preflight(value, CHECKING_BYTES, path);
  requireThat(prepared.status === 'available', 'captured checks require the exact prepared frame', path);
  requireThat(prepared.frame.originalDeclarations.length <= 128, 'captured context exceeds 128 declarations', path);
  const action = value.action as JsonObject;
  requireThat(action !== null && typeof action === 'object' && !Array.isArray(action), 'invalid capture action', [...path, 'action']);
  if (action.status === 'completed') object(action, ['status'], [...path, 'action']);
  else { object(action, ['status', 'reason'], [...path, 'action']); requireThat(action.status === 'error', 'unsupported action status', [...path, 'action']); text(action.reason, 4096, [...path, 'action', 'reason'], false); }
  const bpath = [...path, 'binding'];
  const binding = object(value.binding, ['schema', 'naturalProfile', 'rawProfile', 'attempt', 'operation', 'sourceKind', 'declarationPrefix',
    'universeParams', 'initialEnvironment', 'context', 'sourceTerm', 'sourceType', 'positionalTerm', 'positionalType'], bpath);
  requireThat(binding.schema === 3 && binding.naturalProfile === 2 && binding.rawProfile === 'definograph.raw.v1'
    && binding.operation === 'editor-source' && binding.sourceKind === 'namedComponent' && binding.initialEnvironment === 0,
  'unsupported source binding profile or policy', bpath);
  const attempt = text(binding.attempt, 36, [...bpath, 'attempt']); requireThat(UUID.test(attempt), 'capture attempt must be a UUID', [...bpath, 'attempt']);
  exact(binding.declarationPrefix, prefixFor(attempt), [...bpath, 'declarationPrefix']);
  exact(binding.universeParams, prepared.checkerUniverseParams, [...bpath, 'universeParams']);
  exact(binding.sourceTerm, prepared.frame.sourceTerm, [...bpath, 'sourceTerm']); exact(binding.sourceType, prepared.frame.sourceType, [...bpath, 'sourceType']);
  const ctx = object(binding.context, ['arity', 'telescope', 'registry', 'registryOrder', 'originalDeclarations', 'originalDeclarationOrder'], [...bpath, 'context']);
  requireThat(ctx.arity === prepared.frame.originalDeclarations.length && ctx.registryOrder === 'mostRecentFirst'
    && ctx.originalDeclarationOrder === 'oldestFirst', 'invalid captured context arity or order', [...bpath, 'context']);
  exact(ctx.originalDeclarations, prepared.frame.originalDeclarations, [...bpath, 'context', 'originalDeclarations']);
  const positional = positionalBinding(prepared.frame, bpath);
  exact(ctx.registry, positional.registry, [...bpath, 'context', 'registry']); exact(ctx.telescope, positional.telescope, [...bpath, 'context', 'telescope']);
  exact(binding.positionalTerm, positional.term, [...bpath, 'positionalTerm']); exact(binding.positionalType, positional.type, [...bpath, 'positionalType']);
  const checks = array(value.checks, [...path, 'checks']), audits = array(value.audits, [...path, 'audits']);
  requireThat(checks.length <= 2 && (action.status !== 'completed' || checks.length === 2),
    'completed named-source checking requires its two receipts; errors retain only the executed prefix', [...path, 'checks']);
  requireThat(audits.length === checks.length, 'every receipt requires its associated audit', [...path, 'audits']);
  const declarations = checks.map((_, i) => {
    const label = i === 0 ? 'context' : 'component';
    const declarationName = strName(binding.declarationPrefix, label);
    const declaration: JsonObject = { kind: i === 0 ? 'thmDecl' : 'defnDecl', name: declarationName, levelParams: prepared.checkerUniverseParams,
      type: close(positional.items, i === 0 ? constant('True') : positional.type, 'forallE'),
      value: close(positional.items, i === 0 ? ['const', strName(named('True'), 'intro'), []] : positional.term, 'lam'), all: [declarationName],
      ...(i === 0 ? {} : { hints: ['abbrev'], safety: 'safe' }) };
    return declaration;
  });
  validateReceipts(value, attempt, 'editor-source', declarations);
}

/** Validate the exact callback/audit prefix against independently reconstructed
 * declarations. Completion and sequence-length policy belong to the caller. */
function validateReceipts(value: JsonObject, attempt: string, operation: string, declarations: JsonObject[],
  options: { labels?: readonly string[]; path?: RawPath } = {}): void {
  const path: RawPath = options.path ?? ['checking'];
  requireThat(!options.labels || options.labels.length === declarations.length, 'receipt descriptor count differs', path);
  const checks = array(value.checks, [...path, 'checks']), audits = array(value.audits, [...path, 'audits']);
  requireThat(checks.length === declarations.length && audits.length === checks.length,
    'every receipt requires its reconstructed declaration and associated audit', path);
  let environment = 0;
  checks.forEach((item, i) => {
    const p = [...path, 'checks', i];
    const r = object(item, ['id', 'pair', 'label', 'displayLabel', 'declaration', 'subject', 'envBefore', 'envAfter', 'heartbeatBound', 'outcome'], p);
    const label = options.labels?.[i] ?? (i % 2 === 0 ? 'context' : 'component');
    requireThat(r.id === i && r.pair === operation && r.label === label && r.displayLabel === label, 'receipt sequence, operation or label differs', p);
    exact(r.heartbeatBound, ['nat', '200000'], [...p, 'heartbeatBound']);
    const declaration = declarations[i];
    exact(r.declaration, declaration, [...p, 'declaration']);
    exact(r.subject, { attempt, pair: operation, sequence: i, target: label, declaration }, [...p, 'subject']);
    const outcome = checkOutcome(r.outcome, [...p, 'outcome']);
    requireThat(r.envBefore === environment, 'receipt environment chain is discontinuous', [...p, 'envBefore']);
    if (outcome === 'accepted') environment++;
    requireThat(r.envAfter === environment, 'only an accepted check extends the environment chain', [...p, 'envAfter']);
    const ap = [...path, 'audits', i], audit = object(audits[i], ['checkId', 'subject', 'environment', 'category', 'result'], ap);
    requireThat(audit.checkId === i && audit.environment === environment && audit.category === 'declarationCheck', 'audit association differs', ap);
    exact(audit.subject, declaration, [...ap, 'subject']);
    if (outcome === 'accepted') {
      const result = object(audit.result, ['tag', 'axioms'], [...ap, 'result']); requireThat(result.tag === 'available', 'accepted declaration requires an available audit', ap);
      names(result.axioms, [...ap, 'result', 'axioms']);
    } else {
      exact(audit.result, { tag: 'unavailable', reason: 'declaration was not installed' }, [...ap, 'result']);
    }
  });
  requireThat(value.environmentSnapshotCount === environment + 1, 'environment snapshot count differs from receipt chain', [...path, 'environmentSnapshotCount']);
}

export function validateSourceSnapshot(value: unknown): SourceSnapshot {
  preflight(value, SNAPSHOT_BYTES, []);
  const tools = createExactJsonTools();
  const copy = tools.parse(tools.canonical(value as JsonValue));
  const v = object(copy, ['schema', 'selection', 'policy', 'expectedType', 'original', 'prepared', 'checking'], []);
  if (v.schema !== 'definograph.source-snapshot.v1') bad('unsupported source snapshot version', ['schema'], 'unsupported');
  const selection = object(v.selection, ['startByte', 'endByte', 'requestedStartByte', 'requestedEndByte', 'parentDeclaration'], ['selection']);
  const start = operational(selection.startByte, ['selection', 'startByte']), end = operational(selection.endByte, ['selection', 'endByte']);
  const requestedStart = operational(selection.requestedStartByte, ['selection', 'requestedStartByte']), requestedEnd = operational(selection.requestedEndByte, ['selection', 'requestedEndByte']);
  requireThat(start <= requestedStart && requestedStart <= requestedEnd && requestedEnd <= end, 'requested range must lie within the selected source range', ['selection']);
  if (selection.parentDeclaration !== null) validName(selection.parentDeclaration, ['selection', 'parentDeclaration']);
  exact(v.policy, { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars',
    heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' }, ['policy']);
  const id = `source-snapshot:${++occurrence}`, result: SnapshotDrawings = {};
  const expected = v.expectedType as JsonObject;
  requireThat(expected !== null && typeof expected === 'object' && !Array.isArray(expected), 'invalid expected-type section', ['expectedType']);
  if (expected.status === 'absent') object(expected, ['status'], ['expectedType']);
  else if (expected.status === 'unavailable') unavailable(expected, ['expectedType']);
  else {
    object(expected, ['status', 'expression'], ['expectedType']); requireThat(expected.status === 'available', 'unsupported expected-type status', ['expectedType']);
    result.expectedType = rawDrawing(expected.expression, 'expression', id + ':expectedType', ['expectedType', 'expression'], EXPECTED_BYTES);
  }
  for (const section of ['original', 'prepared'] as const) {
    const p = [section], item = v[section] as JsonObject;
    requireThat(item !== null && typeof item === 'object' && !Array.isArray(item), 'invalid frame section', p);
    if (item.status === 'unavailable') { unavailable(item, p); continue; }
    object(item, ['status', 'typeOrigin', 'frame', ...(section === 'prepared' ? ['checkerUniverseParams'] : [])], p);
    requireThat(item.status === 'available' && item.typeOrigin === (section === 'original' ? 'inferred' : 'inferred-instantiated'), 'unsupported frame status or type origin', p);
    result[section] = rawDrawing(item.frame, 'frame', id + ':' + section, [section, 'frame']);
    if (section === 'prepared') {
      names(item.checkerUniverseParams, [section, 'checkerUniverseParams']);
      exact(item.checkerUniverseParams, universeParams(item.frame as unknown as SnapshotFrame), [section, 'checkerUniverseParams']);
    }
  }
  const snapshot = v as unknown as SourceSnapshot;
  if (snapshot.original.status === 'unavailable' && snapshot.original.phase === 'original-inference') {
    requireThat(snapshot.prepared.status === 'unavailable', 'original inference failure blocks the prepared frame', ['prepared']);
  }
  if (snapshot.original.status === 'available' && snapshot.prepared.status === 'available') {
    const originals = snapshot.original.frame.originalDeclarations, prepared = snapshot.prepared.frame.originalDeclarations;
    requireThat(originals.length === prepared.length, 'preparation changed the original declaration count', ['prepared', 'frame', 'originalDeclarations']);
    originals.forEach((original, i) => {
      const next = prepared[i], p: RawPath = ['prepared', 'frame', 'originalDeclarations', i];
      for (const key of ['constructor', 'index', 'fvarId', 'userName', 'kind',
        ...(field(original, 'constructor') === 'cdecl' ? ['binderInfo'] : ['nondep'])]) exact(field(original, key), field(next, key), [...p, key]);
      if (field(original, 'constructor') === 'ldecl' && original.nondep === true) exact(original.value, next.value, [...p, 'value']);
    });
  }
  validateChecking(v.checking as JsonObject, snapshot.prepared);
  tools.freeze(snapshot); tools.freeze(result); drawings.set(snapshot, result);
  return snapshot;
}

/** Values created by the validator reuse their frozen drawings. Foreign callers
 * receive the same complete validation before any drawing is exposed. */
export function sourceSnapshotDrawings(snapshot: SourceSnapshot): SnapshotDrawings {
  const prior = drawings.get(snapshot); if (prior) return prior;
  return drawings.get(validateSourceSnapshot(snapshot))!;
}

/** Shared structural rules for source snapshots and their occurrence records.
 * These helpers check syntax and associations, never producer authority. */
export const sourceSnapshotValidation = Object.freeze({
  bad, requireThat, object, array, field, text, operational, exact, preflight,
  names, validName, unavailable, strName, named, constant, UUID, positionalBinding, close, validateReceipts,
  validated(snapshot: SourceSnapshot): SourceSnapshot {
    return drawings.has(snapshot) ? snapshot : validateSourceSnapshot(snapshot);
  },
});
