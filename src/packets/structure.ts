/** Constructor drawings and independent readback for the admitted exact source profile.
 * A drawing contains occurrence roles, fields and homes, never a saved Expr.
 * Structural readback establishes neither typing nor source certification.
 */
import type { JsonValue } from './packet';
import { boundedNatural, encodeNatural, naturalText, NaturalError, readNatural, type ExactNatural, type NaturalProfile } from './natural';

export type StructurePath = (string | number)[];
export type StructuralName = ['anonymous'] | ['str', StructuralName, string] | ['num', StructuralName, ExactNatural];
export type StructuralLevel = ['zero'] | ['succ', StructuralLevel]
  | ['max' | 'imax', StructuralLevel, StructuralLevel] | ['param', StructuralName];
export type StructuralBinderInfo = 'default' | 'implicit' | 'strictImplicit' | 'instImplicit';
export type StructuralLocalKind = 'default' | 'implDetail' | 'auxDecl';
export type StructuralRole = 'function' | 'argument' | 'domain' | 'body' | 'type' | 'value'
  | 'definitionValue' | 'storedValue';
export interface StructuralEdge { role: StructuralRole; nodeId: string }
interface Occurrence { id: string; sourcePath: StructurePath; homeId: string; children: StructuralEdge[] }
export type StructuralNode = Occurrence & (
  | { kind: 'bvar'; index: number; declarationId: string }
  | { kind: 'fvar'; fvarId: StructuralName; declarationId: string; externalHomeId: string }
  | { kind: 'sort'; level: StructuralLevel }
  | { kind: 'const'; name: StructuralName; levels: StructuralLevel[] }
  | { kind: 'lit'; literal: ['natVal', ExactNatural] | ['strVal', string] }
  | { kind: 'app' }
  | { kind: 'lam' | 'forallE'; name: StructuralName; binderInfo: StructuralBinderInfo; declarationId: string }
  | { kind: 'letE'; name: StructuralName; nondep: boolean; declarationId: string }
  | { kind: 'proj'; owner: StructuralName; field: ExactNatural }
);

/** Each home is either empty or one declaration extending its parent. */
export interface StructuralHome { id: string; parentId: string | null; declarationId: string | null }
export interface OwnedStructuralDeclaration {
  kind: 'binder' | 'let'; id: string; nodeId: string; homeId: string; bodyHomeId: string;
}
interface ExternalFields {
  index: ExactNatural; fvarId: StructuralName; userName: StructuralName; kind: StructuralLocalKind;
}
/** Exact original LocalDecl fields; order is oldest first. This named registry
 * supplies free references only, never ambient de Bruijn positions. Values with nondep=true
 * are retained metadata, not a defining equation. No context validity is inferred.
 * Stored metadata outside this module's expression profile returns unsupported,
 * even when the source itself was admitted; this is not an admission verdict.
 */
export type ExternalDeclarationInput = ExternalFields & (
  | { constructor: 'cdecl'; type: JsonValue; binderInfo: StructuralBinderInfo }
  | { constructor: 'ldecl'; type: JsonValue; value: JsonValue; nondep: boolean }
);
export type ExternalStructuralDeclaration = {
  kind: 'external'; id: string; homeId: string; bodyHomeId: string; sourcePath: StructurePath;
  index: ExactNatural; fvarId: StructuralName; userName: StructuralName; localKind: StructuralLocalKind;
  children: StructuralEdge[];
} & (
  | { constructor: 'cdecl'; binderInfo: StructuralBinderInfo }
  | { constructor: 'ldecl'; nondep: boolean }
);
export type StructuralDeclaration = OwnedStructuralDeclaration | ExternalStructuralDeclaration;
export interface StructuralDrawing {
  schema: 'definograph.structure.v1' | 'definograph.structure.v2'; sourceIdentity: string; sourcePath: StructurePath;
  rootId: string; rootHomeId: string; emptyHomeId: string;
  nodes: StructuralNode[]; homes: StructuralHome[]; declarations: StructuralDeclaration[];
  externalDeclarationIds: string[];
}
/** A positional source home has no original FVar identity or LocalDecl index.
 * Each CTel let retains its defining value, including nondep=true source haves. */
export type PositionalStructuralDeclaration = {
  kind: 'positional'; id: string; homeId: string; bodyHomeId: string; sourcePath: StructurePath;
  name: StructuralName; children: StructuralEdge[];
} & (
  | { constructor: 'port'; binderInfo: StructuralBinderInfo }
  | { constructor: 'letE'; nondep: boolean }
);
export interface PositionalStructuralInput {
  home: { arity: number; telescope: JsonValue }; term: JsonValue; type: JsonValue;
}
export interface PositionalStructuralDrawing {
  schema: 'definograph.structure.positional.v1'; sourceIdentity: string; sourcePath: StructurePath;
  rootId: string; typeRootId: string; rootHomeId: string; emptyHomeId: string; arity: number;
  nodes: StructuralNode[]; homes: StructuralHome[];
  declarations: (OwnedStructuralDeclaration | PositionalStructuralDeclaration)[];
  contextDeclarationIds: string[];
}
export interface PositionalStructuralDrawingOptions {
  sourceIdentity: string; sourcePath?: StructurePath; limits?: Partial<StructureLimits>;
}
/** maxExternalDeclarations bounds the ambient context in either source mode. */
export interface StructureLimits { maxNodes: number; maxDepth: number; maxText: number; maxExternalDeclarations: number }
export interface StructureError { code: 'malformed' | 'unsupported' | 'limit'; message: string; path: StructurePath }
export type StructureResult<T> = { ok: true; value: T } | { ok: false; error: StructureError };
export interface StructuralDrawingOptions {
  sourceIdentity: string; sourcePath?: StructurePath; externalContext?: ExternalDeclarationInput[];
  profile?: NaturalProfile;
  limits?: Partial<StructureLimits>;
}
export interface StructuralReadback { expression: JsonValue; externalContext: ExternalDeclarationInput[] }

const DEFAULT_LIMITS: StructureLimits = {
  maxNodes: 100_000, maxDepth: 256, maxText: 2_000_000, maxExternalDeclarations: 256,
};
class Failure extends Error {
  constructor(readonly detail: StructureError) { super(detail.message); }
}
function fail(message: string, path: StructurePath, code: StructureError['code'] = 'malformed'): never {
  throw new Failure({ code, message, path: [...path] });
}
function requireThat(condition: unknown, message: string, path: StructurePath): asserts condition {
  if (!condition) fail(message, path);
}
function result<T>(action: () => T): StructureResult<T> {
  try { return { ok: true, value: action() }; }
  catch (error) { if (error instanceof Failure) return { ok: false, error: error.detail }; throw error; }
}
class Budget {
  readonly limits: StructureLimits;
  private nodes = 0;
  private text = 0;
  constructor(limits: Partial<StructureLimits> = {}, readonly profile: NaturalProfile = 1) {
    if (profile !== 1 && profile !== 2) fail('unsupported natural profile', ['profile'], 'unsupported');
    this.limits = { ...DEFAULT_LIMITS };
    requireThat(limits !== null && typeof limits === 'object' && !Array.isArray(limits)
      && (Object.getPrototypeOf(limits) === Object.prototype || Object.getPrototypeOf(limits) === null),
    'resource limits must be an object', ['limits']);
    requireThat(Reflect.ownKeys(limits).every(key => typeof key === 'string'), 'symbol resource limits are not supported', ['limits']);
    for (const [key, descriptor] of Object.entries(Object.getOwnPropertyDescriptors(limits))) {
      requireThat(descriptor.enumerable && Object.hasOwn(descriptor, 'value'), 'hidden or accessor resource limit', ['limits', key]);
      const value = descriptor.value;
      requireThat(Object.hasOwn(DEFAULT_LIMITS, key), 'unknown resource limit', ['limits', key]);
      requireThat(typeof value === 'number' && Number.isSafeInteger(value) && value > 0
        && value <= DEFAULT_LIMITS[key as keyof StructureLimits], 'limit must be positive and within the implementation maximum', ['limits', key]);
      this.limits[key as keyof StructureLimits] = value;
    }
  }
  visit(depth: number, path: StructurePath): void {
    if (++this.nodes > this.limits.maxNodes || depth > this.limits.maxDepth) fail('drawing exceeds the node or depth limit', path, 'limit');
  }
  string(value: unknown, path: StructurePath): string {
    requireThat(typeof value === 'string', 'expected a string', path);
    if ((this.text += value.length) > this.limits.maxText) fail('drawing exceeds the text limit', path, 'limit');
    for (let i = 0; i < value.length; i++) {
      const char = value.charCodeAt(i);
      if (char >= 0xd800 && char <= 0xdbff) {
        const next = value.charCodeAt(++i);
        requireThat(next >= 0xdc00 && next <= 0xdfff, 'unpaired surrogate in string', path);
      } else requireThat(char < 0xdc00 || char > 0xdfff, 'unpaired surrogate in string', path);
    }
    return value;
  }
}
function array(value: unknown, path: StructurePath, length?: number): unknown[] {
  requireThat(Array.isArray(value) && (length === undefined || value.length === length), 'invalid constructor or collection shape', path);
  if (value.length > DEFAULT_LIMITS.maxNodes) fail('collection exceeds the node limit', path, 'limit');
  requireThat(Object.keys(value).length === value.length, 'sparse or extended arrays are not exact JSON arrays', path);
  for (let i = 0; i < value.length; i++) requireThat(Object.hasOwn(value, i), 'sparse array is not an exact JSON array', [...path, i]);
  return value;
}
function object(value: unknown, keys: string[], path: StructurePath): Record<string, unknown> {
  requireThat(value !== null && typeof value === 'object' && !Array.isArray(value), 'expected an object', path);
  requireThat(Object.keys(value).length === keys.length && keys.every(key => Object.hasOwn(value, key)), 'unexpected or missing fields', path);
  return value as Record<string, unknown>;
}
function natural(value: unknown, path: StructurePath): number {
  requireThat(typeof value === 'number' && Number.isSafeInteger(value) && value >= 0, 'expected a safe natural number', path);
  return value;
}
function semanticNatural(value: unknown, budget: Budget, path: StructurePath): ExactNatural {
  try {
    const exact = readNatural(value, budget.profile);
    if (Array.isArray(exact)) budget.string(exact[1], [...path, 1]);
    return exact;
  } catch (error) {
    if (error instanceof NaturalError) return fail(error.message, path, error.code);
    throw error;
  }
}
function boundIndex(value: unknown, budget: Budget, size: number, path: StructurePath, metadata: boolean): number {
  const exact = semanticNatural(value, budget, path);
  try { return boundedNatural(exact, budget.profile, size); }
  catch (error) {
    if (error instanceof NaturalError) return fail('bound reference is outside its home', path, metadata ? 'unsupported' : 'malformed');
    throw error;
  }
}
function boolean(value: unknown, path: StructurePath): boolean {
  requireThat(typeof value === 'boolean', 'expected a Boolean flag', path); return value;
}
function choice<T extends string>(value: unknown, choices: readonly T[], path: StructurePath): T {
  requireThat(typeof value === 'string' && choices.includes(value as T), 'unsupported field value', path); return value as T;
}
function binderInfo(value: unknown, path: StructurePath): StructuralBinderInfo {
  return choice(value, ['default', 'implicit', 'strictImplicit', 'instImplicit'], path);
}
function localKind(value: unknown, path: StructurePath): StructuralLocalKind {
  return choice(value, ['default', 'implDetail', 'auxDecl'], path);
}
function name(value: unknown, budget: Budget, path: StructurePath, depth = 0): StructuralName {
  budget.visit(depth, path);
  const a = array(value, path);
  switch (a[0]) {
    case 'anonymous': array(a, path, 1); return ['anonymous'];
    case 'str': array(a, path, 3); return ['str', name(a[1], budget, [...path, 1], depth + 1), budget.string(a[2], [...path, 2])];
    case 'num': array(a, path, 3); return ['num', name(a[1], budget, [...path, 1], depth + 1), semanticNatural(a[2], budget, [...path, 2])];
    default: return fail('unsupported Name constructor', path, 'unsupported');
  }
}
function level(value: unknown, budget: Budget, path: StructurePath, depth = 0): StructuralLevel {
  budget.visit(depth, path);
  const a = array(value, path);
  switch (a[0]) {
    case 'zero': array(a, path, 1); return ['zero'];
    case 'succ': array(a, path, 2); return ['succ', level(a[1], budget, [...path, 1], depth + 1)];
    case 'max': case 'imax': array(a, path, 3); return [a[0], level(a[1], budget, [...path, 1], depth + 1), level(a[2], budget, [...path, 2], depth + 1)];
    case 'param': array(a, path, 2); return ['param', name(a[1], budget, [...path, 1], depth + 1)];
    default: return fail('universe constructor is outside the admitted source profile', path, 'unsupported');
  }
}
function literal(value: unknown, budget: Budget, path: StructurePath): ['natVal', ExactNatural] | ['strVal', string] {
  const a = array(value, path, 2);
  if (a[0] === 'natVal') return ['natVal', semanticNatural(a[1], budget, [...path, 1])];
  requireThat(a[0] === 'strVal', 'unsupported literal kind', path);
  return ['strVal', budget.string(a[1], [...path, 1])];
}
function sourcePath(value: unknown, budget: Budget, path: StructurePath): StructurePath {
  const parts = array(value, path);
  if (parts.length > budget.limits.maxDepth) fail('source path exceeds the depth limit', path, 'limit');
  return parts.map((part, index) => typeof part === 'string' ? budget.string(part, [...path, index]) : natural(part, [...path, index]));
}
function same(a: unknown, b: unknown): boolean { return JSON.stringify(a) === JSON.stringify(b); }
function identity(value: unknown, budget: Budget, path: StructurePath): string {
  const id = budget.string(value, path); requireThat(id.length > 0, 'identity must be nonempty', path); return id;
}

/** Bound the whole serialized drawing, including repeated ids and paths. This
 * also rejects non-JSON/cyclic mutations before identity comparisons run. */
function checkDrawingSize(value: unknown, limits?: Partial<StructureLimits>): void {
  const budget = new Budget(limits);
  function visit(item: unknown, path: StructurePath, depth: number): void {
    budget.visit(depth, path);
    if (typeof item === 'string') { budget.string(item, path); return; }
    if (item === null || typeof item === 'boolean') return;
    if (typeof item === 'number') { natural(item, path); return; }
    if (Array.isArray(item)) { array(item, path).forEach((child, i) => visit(child, [...path, i], depth + 1)); return; }
    requireThat(typeof item === 'object', 'drawing contains a non-JSON field', path);
    for (const [key, child] of Object.entries(item)) {
      budget.string(key, path); visit(child, [...path, key], depth + 1);
    }
  }
  visit(value, [], 0);
}

function checkExactDrawingSize(value: unknown, limits?: Partial<StructureLimits>): void {
  const budget = new Budget(limits);
  const active = new Set<object>();
  function visit(item: unknown, path: StructurePath, depth: number): void {
    budget.visit(depth, path);
    if (typeof item === 'string') { budget.string(item, path); return; }
    if (item === null || typeof item === 'boolean') return;
    if (typeof item === 'number') { natural(item, path); return; }
    requireThat(typeof item === 'object', 'drawing contains a non-JSON field', path);
    requireThat(!active.has(item), 'cyclic data is not exact JSON', path);
    requireThat(Object.getPrototypeOf(item) === (Array.isArray(item) ? Array.prototype : Object.prototype)
      || !Array.isArray(item) && Object.getPrototypeOf(item) === null, 'data has a non-JSON prototype', path);
    active.add(item);
    if (Array.isArray(item)) array(item, path);
    const ownKeys = Reflect.ownKeys(item);
    if (ownKeys.length > budget.limits.maxNodes + (Array.isArray(item) ? 1 : 0)) fail('collection exceeds the node limit', path, 'limit');
    const descriptors = Object.getOwnPropertyDescriptors(item);
    requireThat(ownKeys.every(key => typeof key === 'string'), 'symbol fields are not exact JSON', path);
    for (const [key, descriptor] of Object.entries(descriptors)) {
      if (Array.isArray(item) && key === 'length') continue;
      requireThat(descriptor.enumerable && Object.hasOwn(descriptor, 'value'), 'accessors or hidden fields are not exact JSON', [...path, key]);
    }
    if (Array.isArray(item)) {
      array(item, path).forEach((child, i) => visit(child, [...path, i], depth + 1));
    } else for (const [key, descriptor] of Object.entries(descriptors)) {
      budget.string(key, path); visit(descriptor.value, [...path, key], depth + 1);
    }
    active.delete(item);
  }
  visit(value, [], 0);
}

type GraphDeclaration = StructuralDeclaration | PositionalStructuralDeclaration;

/** Shared constructor builder; source mode controls only reference namespaces. */
function structuralBuilder(budget: Budget, sourceIdentity: string, path: StructurePath, positional = false) {
    const nodes: StructuralNode[] = [], homes: StructuralHome[] = [], declarations: GraphDeclaration[] = [];
    const byHome = new Map<string, StructuralHome>();
    const byDeclaration = new Map<string, GraphDeclaration>();
    const id = (kind: string, index: number) => budget.string(`${sourceIdentity}:${kind}:${index}`, path);
    function home(parentId: string | null, declarationId: string | null): string {
      const item = { id: id('home', homes.length), parentId, declarationId };
      budget.visit(0, path); homes.push(item); byHome.set(item.id, item); return item.id;
    }
    function declare(item: GraphDeclaration): void { declarations.push(item); byDeclaration.set(item.id, item); }
    function inScope(homeId: string): GraphDeclaration[] {
      const found: GraphDeclaration[] = [];
      let cursor = byHome.get(homeId)!;
      while (cursor.declarationId !== null) {
        found.push(byDeclaration.get(cursor.declarationId)!); cursor = byHome.get(cursor.parentId!)!;
      }
      return found;
    }
    function draw(raw: unknown, homeId: string, at: StructurePath, depth: number, metadata = false): string {
      budget.visit(depth, at);
      const a = array(raw, at);
      const nodeId = id('node', nodes.length);
      // Reserve the occurrence before its children; no source value is retained.
      const common: Occurrence = { id: nodeId, sourcePath: [...at], homeId, children: [] };
      const slot = nodes.length; nodes.push(undefined as unknown as StructuralNode);
      const child = (role: StructuralRole, index: number, childHome = homeId) => {
        common.children.push({ role, nodeId: draw(a[index], childHome, [...at, index], depth + 1, metadata) });
      };
      let node: StructuralNode;
      switch (a[0]) {
        case 'bvar': {
          array(a, at, 2);
          const scope = inScope(homeId).filter(item => item.kind !== 'external');
          const index = boundIndex(a[1], budget, scope.length, [...at, 1], metadata), target = scope[index];
          node = { ...common, kind: 'bvar', index, declarationId: target.id }; break;
        }
        case 'fvar': {
          if (positional) fail('named free references are outside the positional Core profile', at, 'unsupported');
          array(a, at, 2); const fvarId = name(a[1], budget, [...at, 1], depth + 1);
          const target = inScope(homeId).find(item => item.kind === 'external' && same(item.fvarId, fvarId));
          if (target?.kind !== 'external') fail('free reference has no declaration in its external registry home', at, metadata ? 'unsupported' : 'malformed');
          node = { ...common, kind: 'fvar', fvarId, declarationId: target.id, externalHomeId: target.bodyHomeId }; break;
        }
        case 'sort': array(a, at, 2); node = { ...common, kind: 'sort', level: level(a[1], budget, [...at, 1], depth + 1) }; break;
        case 'const': {
          array(a, at, 3);
          node = { ...common, kind: 'const', name: name(a[1], budget, [...at, 1], depth + 1),
            levels: array(a[2], [...at, 2]).map((u, i) => level(u, budget, [...at, 2, i], depth + 1)) }; break;
        }
        case 'lit': array(a, at, 2); node = { ...common, kind: 'lit', literal: literal(a[1], budget, [...at, 1]) }; break;
        case 'app': array(a, at, 3); child('function', 1); child('argument', 2); node = { ...common, kind: 'app' }; break;
        case 'lam': case 'forallE': case 'letE': {
          const isLet = a[0] === 'letE'; array(a, at, isLet ? 6 : 5);
          const declarationId = id('declaration', declarations.length), bodyHomeId = home(homeId, declarationId);
          declare({ kind: isLet ? 'let' : 'binder', id: declarationId, nodeId, homeId, bodyHomeId });
          const exactName = name(a[1], budget, [...at, 1], depth + 1);
          if (isLet) {
            const nondep = boolean(a[5], [...at, 5]); child('type', 2); child('value', 3); child('body', 4, bodyHomeId);
            node = { ...common, kind: 'letE', name: exactName, nondep, declarationId };
          } else {
            const info = binderInfo(a[4], [...at, 4]); child('domain', 2); child('body', 3, bodyHomeId);
            node = { ...common, kind: a[0] as 'lam' | 'forallE', name: exactName, binderInfo: info, declarationId };
          }
          break;
        }
        case 'proj': array(a, at, 4); child('value', 3);
          node = { ...common, kind: 'proj', owner: name(a[1], budget, [...at, 1], depth + 1), field: semanticNatural(a[2], budget, [...at, 2]) }; break;
        default: return fail('expression constructor is outside the admitted source profile', at, 'unsupported');
      }
      nodes[slot] = node; return nodeId;
    }
    return { nodes, homes, declarations, id, home, declare, draw };
}

/** Build a general source drawing. Children are occurrence-specific; only declaration
 * references share identities. External context is exact, oldest first.
 */
export function buildStructuralDrawing(expression: JsonValue, options: StructuralDrawingOptions): StructureResult<StructuralDrawing> {
  return result(() => {
    const budget = new Budget(options.limits, options.profile ?? 1);
    const sourceIdentity = identity(options.sourceIdentity, budget, ['sourceIdentity']);
    const path = sourcePath(options.sourcePath ?? ['expression'], budget, ['sourcePath']);
    const { nodes, homes, declarations, id, home, declare, draw } = structuralBuilder(budget, sourceIdentity, path);
    const emptyHomeId = home(null, null);
    let rootHomeId = emptyHomeId;
    const externalDeclarationIds: string[] = [];
    const external = array(options.externalContext ?? [], ['externalContext']);
    if (external.length > budget.limits.maxExternalDeclarations) fail('external context exceeds the declaration limit', ['externalContext'], 'limit');
    const registered = new Set<string>();
    const indices = new Set<string>();
    external.forEach((input, index) => {
      const at: StructurePath = ['externalContext', index];
      const raw = input as Record<string, unknown>, ctor = (input as { constructor?: unknown } | null)?.constructor;
      requireThat(ctor === 'cdecl' || ctor === 'ldecl', 'unsupported external declaration constructor', at);
      const keys = ['constructor', 'index', 'fvarId', 'userName', 'type', 'kind', ...(ctor === 'cdecl' ? ['binderInfo'] : ['value', 'nondep'])];
      object(input, keys, at);
      const fvarId = name(raw.fvarId, budget, [...at, 'fvarId']);
      const registryId = JSON.stringify(fvarId), localIndex = semanticNatural(raw.index, budget, [...at, 'index']);
      const indexKey = naturalText(localIndex, budget.profile);
      requireThat(!registered.has(registryId) && !indices.has(indexKey), 'duplicate external identity or local index', at);
      registered.add(registryId); indices.add(indexKey);
      const declarationId = id('declaration', declarations.length), before = rootHomeId, bodyHomeId = home(before, declarationId);
      const fields = { kind: 'external' as const, id: declarationId, homeId: before, bodyHomeId, sourcePath: at,
        index: localIndex, fvarId, userName: name(raw.userName, budget, [...at, 'userName']), localKind: localKind(raw.kind, [...at, 'kind']), children: [] as StructuralEdge[] };
      const item: ExternalStructuralDeclaration = ctor === 'cdecl'
        ? { ...fields, constructor: ctor, binderInfo: binderInfo(raw.binderInfo, [...at, 'binderInfo']) }
        : { ...fields, constructor: ctor, nondep: boolean(raw.nondep, [...at, 'nondep']) };
      // Reserve identity before nested binders in its metadata. The declaration
      // itself is unavailable in its own preceding type/value home.
      declare(item);
      item.children.push({ role: 'type', nodeId: draw(raw.type, before, [...at, 'type'], 0) });
      if (item.constructor === 'ldecl') item.children.push({ role: item.nondep ? 'storedValue' : 'definitionValue',
        nodeId: draw(raw.value, before, [...at, 'value'], 0, item.nondep) });
      externalDeclarationIds.push(declarationId); rootHomeId = bodyHomeId;
    });
    const rootId = draw(expression, rootHomeId, path, 0);
    const drawing: StructuralDrawing = { schema: budget.profile === 1 ? 'definograph.structure.v1' : 'definograph.structure.v2', sourceIdentity, sourcePath: path, rootId, rootHomeId, emptyHomeId,
      nodes, homes, declarations: declarations as StructuralDeclaration[], externalDeclarationIds };
    checkDrawingSize(drawing, options.limits);
    return drawing;
  });
}

/** Independent graph reader: never calls either builder. */
function structuralReader(drawing: StructuralDrawing | PositionalStructuralDrawing, budget: Budget, positional = false) {
    function index<T extends { id: string }>(items: T[], at: string): Map<string, T> {
      const map = new Map<string, T>();
      for (const [i, item] of array(items, [at]).entries()) {
        budget.visit(0, [at, i]);
        requireThat(item !== null && typeof item === 'object' && !Array.isArray(item), 'invalid graph record', [at, i]);
        const key = identity((item as T).id, budget, [at, i, 'id']);
        requireThat(!map.has(key), 'duplicate graph identity', [at, i]); map.set(key, item as T);
      }
      return map;
    }
    const nodes = index(drawing.nodes, 'nodes'), homes = index(drawing.homes, 'homes'), declarations = index<GraphDeclaration>(drawing.declarations, 'declarations');
    const allIds = [...nodes.keys(), ...homes.keys(), ...declarations.keys()];
    requireThat(new Set(allIds).size === allIds.length, 'identity is shared by different graph record kinds', []);
    const seenNodes = new Set<string>(), seenHomes = new Set<string>(), seenDeclarations = new Set<string>();
    function home(homeId: string, parentId: string | null, declarationId: string | null, at: StructurePath): void {
      const h = homes.get(homeId); requireThat(h && !seenHomes.has(homeId), 'missing or multiply owned home', at);
      object(h, ['id', 'parentId', 'declarationId'], at);
      requireThat(h.parentId === parentId && h.declarationId === declarationId, 'home does not extend the required declaration', at); seenHomes.add(homeId);
    }
    function edges(value: unknown, roles: StructuralRole[], at: StructurePath): StructuralEdge[] {
      return array(value, at, roles.length).map((edge, i) => {
        const e = object(edge, ['role', 'nodeId'], [...at, i]);
        requireThat(e.role === roles[i], 'missing or out-of-order child role', [...at, i]);
        return { role: roles[i], nodeId: identity(e.nodeId, budget, [...at, i, 'nodeId']) };
      });
    }
    function declaration(declarationId: string, node: StructuralNode, isLet: boolean): OwnedStructuralDeclaration {
      const d = declarations.get(declarationId), at = node.sourcePath;
      requireThat(d && d.kind === (isLet ? 'let' : 'binder') && !seenDeclarations.has(declarationId), 'missing or multiply owned declaration', at);
      object(d, ['kind', 'id', 'nodeId', 'homeId', 'bodyHomeId'], at);
      const owned = d as OwnedStructuralDeclaration;
      requireThat(owned.nodeId === node.id && owned.homeId === node.homeId, 'declaration belongs to another occurrence or home', at);
      home(owned.bodyHomeId, node.homeId, declarationId, at); seenDeclarations.add(declarationId); return owned;
    }
    function read(nodeId: string, homeId: string, context: string[], at: StructurePath, depth: number): JsonValue {
      budget.visit(depth, at);
      const n = nodes.get(nodeId); requireThat(n && !seenNodes.has(nodeId), 'missing, shared or cyclic occurrence', at);
      seenNodes.add(nodeId);
      requireThat(n.homeId === homeId && same(n.sourcePath, at), 'occurrence has the wrong source path or home', at);
      const base = ['id', 'sourcePath', 'homeId', 'children', 'kind'];
      const fields = (keys: string[]) => object(n, [...base, ...keys], at);
      const children = (roles: StructuralRole[]) => edges(n.children, roles, [...at, 'children']);
      const recurse = (edge: StructuralEdge, rawIndex: number, childHome = homeId, childContext = context) =>
        read(edge.nodeId, childHome, childContext, [...at, rawIndex], depth + 1);
      switch (n.kind) {
        case 'bvar': {
          fields(['index', 'declarationId']); children([]); const i = natural(n.index, at);
          const boundContext = context.filter(id => declarations.get(id)?.kind !== 'external');
          requireThat(i < boundContext.length && boundContext[i] === n.declarationId, 'bound reference does not resolve to its recorded declaration', at);
          return ['bvar', encodeNatural(i, budget.profile)];
        }
        case 'fvar': {
          if (positional) fail('named free references are outside the positional Core profile', at, 'unsupported');
          fields(['fvarId', 'declarationId', 'externalHomeId']); children([]);
          const fvarId = name(n.fvarId, budget, [...at, 1], depth + 1), d = declarations.get(n.declarationId);
          requireThat(d?.kind === 'external' && context.includes(d.id) && same(d.fvarId, fvarId)
            && d.bodyHomeId === n.externalHomeId, 'free reference does not resolve in its registered external home', at);
          return ['fvar', fvarId];
        }
        case 'sort': fields(['level']); children([]); return ['sort', level(n.level, budget, [...at, 1], depth + 1)];
        case 'const': fields(['name', 'levels']); children([]);
          return ['const', name(n.name, budget, [...at, 1], depth + 1), array(n.levels, at).map((u, i) => level(u, budget, [...at, 2, i], depth + 1))];
        case 'lit': fields(['literal']); children([]); return ['lit', literal(n.literal, budget, [...at, 1])];
        case 'app': { fields([]); const c = children(['function', 'argument']); return ['app', recurse(c[0], 1), recurse(c[1], 2)]; }
        case 'lam': case 'forallE': {
          fields(['name', 'binderInfo', 'declarationId']); const c = children(['domain', 'body']);
          const d = declaration(n.declarationId, n, false);
          return [n.kind, name(n.name, budget, [...at, 1], depth + 1), recurse(c[0], 2), recurse(c[1], 3, d.bodyHomeId, [d.id, ...context]), binderInfo(n.binderInfo, at)];
        }
        case 'letE': {
          fields(['name', 'nondep', 'declarationId']); const c = children(['type', 'value', 'body']);
          const d = declaration(n.declarationId, n, true);
          return ['letE', name(n.name, budget, [...at, 1], depth + 1), recurse(c[0], 2), recurse(c[1], 3), recurse(c[2], 4, d.bodyHomeId, [d.id, ...context]), boolean(n.nondep, at)];
        }
        case 'proj': {
          fields(['owner', 'field']); const c = children(['value']);
          return ['proj', name(n.owner, budget, [...at, 1], depth + 1), semanticNatural(n.field, budget, [...at, 2]), recurse(c[0], 3)];
        }
        default: return fail('unsupported drawing constructor', at, 'unsupported');
      }
    }
    function complete(): void {
      requireThat(seenNodes.size === nodes.size && seenHomes.size === homes.size && seenDeclarations.size === declarations.size,
        'drawing contains unreachable or unowned records', []);
    }
    return { nodes, homes, declarations, seenDeclarations, home, edges, read, complete };
}

/** Reconstruct solely from drawing roles/fields. This reader deliberately does
 * not call the builder or consult the input expression. Unused, shared, cyclic,
 * misplaced or inconsistently scoped graph records are rejected.
 */
export function readStructuralDrawing(drawing: StructuralDrawing, limits?: Partial<StructureLimits>): StructureResult<StructuralReadback> {
  return result(() => {
    checkDrawingSize(drawing, limits);
    object(drawing, ['schema', 'sourceIdentity', 'sourcePath', 'rootId', 'rootHomeId', 'emptyHomeId', 'nodes', 'homes', 'declarations', 'externalDeclarationIds'], []);
    if (drawing.schema !== 'definograph.structure.v1' && drawing.schema !== 'definograph.structure.v2')
      fail('unsupported drawing schema', ['schema'], 'unsupported');
    const budget = new Budget(limits, drawing.schema === 'definograph.structure.v1' ? 1 : 2);
    identity(drawing.sourceIdentity, budget, ['sourceIdentity']);
    const path = sourcePath(drawing.sourcePath, budget, ['sourcePath']);
    const { declarations, seenDeclarations, home, edges, read, complete } = structuralReader(drawing, budget);
    home(drawing.emptyHomeId, null, null, ['emptyHomeId']);
    let currentHome = drawing.emptyHomeId;
    const context: string[] = [], externalContext: ExternalDeclarationInput[] = [];
    const registry = new Set<string>(), indices = new Set<string>();
    const externalIds = array(drawing.externalDeclarationIds, ['externalDeclarationIds']);
    if (externalIds.length > budget.limits.maxExternalDeclarations) fail('external context exceeds the declaration limit', ['externalDeclarationIds'], 'limit');
    externalIds.forEach((externalId, i) => {
      const at: StructurePath = ['externalContext', i];
      const d = declarations.get(identity(externalId, budget, at));
      requireThat(d?.kind === 'external' && !seenDeclarations.has(d.id), 'missing or repeated external declaration', at);
      requireThat(d.constructor === 'cdecl' || d.constructor === 'ldecl', 'unsupported external declaration constructor', at);
      object(d, ['kind', 'id', 'homeId', 'bodyHomeId', 'sourcePath', 'index', 'fvarId', 'userName', 'localKind', 'children', 'constructor',
        ...(d.constructor === 'cdecl' ? ['binderInfo'] : ['nondep'])], at);
      requireThat(d.homeId === currentHome && same(d.sourcePath, at), 'external declaration has the wrong preceding home or path', at);
      seenDeclarations.add(d.id); home(d.bodyHomeId, currentHome, d.id, at);
      const fvarId = name(d.fvarId, budget, [...at, 'fvarId']), key = JSON.stringify(fvarId), localIndex = semanticNatural(d.index, budget, [...at, 'index']);
      const indexKey = naturalText(localIndex, budget.profile);
      requireThat(!registry.has(key) && !indices.has(indexKey), 'duplicate external identity or local index', at);
      registry.add(key); indices.add(indexKey);
      const common = { index: localIndex, fvarId, userName: name(d.userName, budget, [...at, 'userName']), kind: localKind(d.localKind, at) };
      if (d.constructor === 'cdecl') {
        const c = edges(d.children, ['type'], at);
        externalContext.push({ ...common, constructor: 'cdecl', type: read(c[0].nodeId, currentHome, context, [...at, 'type'], 0), binderInfo: binderInfo(d.binderInfo, at) });
      } else {
        const nondep = boolean(d.nondep, at), c = edges(d.children, ['type', nondep ? 'storedValue' : 'definitionValue'], at);
        externalContext.push({ ...common, constructor: 'ldecl', nondep,
          type: read(c[0].nodeId, currentHome, context, [...at, 'type'], 0), value: read(c[1].nodeId, currentHome, context, [...at, 'value'], 0) });
      }
      currentHome = d.bodyHomeId; context.unshift(d.id);
    });
    requireThat(drawing.rootHomeId === currentHome, 'root does not use the completed external context home', ['rootHomeId']);
    const expression = read(drawing.rootId, currentHome, context, path, 0);
    complete();
    return { expression, externalContext };
  });
}

/** Build the exact open component and its inferred type in their shared CTel
 * home. Ambient declarations are positional slots, not a named FVar registry. */
export function buildPositionalStructuralDrawing(input: PositionalStructuralInput,
  options: PositionalStructuralDrawingOptions): StructureResult<PositionalStructuralDrawing> {
  return result(() => {
    requireThat(options !== null && typeof options === 'object' && !Array.isArray(options)
      && (Object.getPrototypeOf(options) === Object.prototype || Object.getPrototypeOf(options) === null),
    'invalid positional drawing options', ['options']);
    const optionFields: Record<string, unknown> = {};
    requireThat(Reflect.ownKeys(options).every(key => typeof key === 'string'), 'symbol options are not supported', ['options']);
    for (const [key, descriptor] of Object.entries(Object.getOwnPropertyDescriptors(options))) {
      requireThat(['sourceIdentity', 'sourcePath', 'limits'].includes(key) && descriptor.enumerable
        && Object.hasOwn(descriptor, 'value'), 'unknown, hidden or accessor option', ['options', key]);
      if (descriptor.value !== undefined || key === 'sourceIdentity') optionFields[key] = descriptor.value;
    }
    checkExactDrawingSize(optionFields);
    options = optionFields as unknown as PositionalStructuralDrawingOptions;
    // Check descriptors before accessing any caller-supplied expression field.
    checkExactDrawingSize(input, options.limits);
    object(input, ['home', 'term', 'type'], []);
    object(input.home, ['arity', 'telescope'], ['home']);
    const budget = new Budget(options.limits, 2);
    const sourceIdentity = identity(options.sourceIdentity, budget, ['sourceIdentity']);
    const path = sourcePath(options.sourcePath ?? ['selected'], budget, ['sourcePath']);
    const arity = natural(input.home.arity, ['home', 'arity']);
    if (arity > budget.limits.maxExternalDeclarations) fail('positional context exceeds the declaration limit', ['home', 'arity'], 'limit');
    const { nodes, homes, declarations, home, declare, draw } = structuralBuilder(budget, sourceIdentity, path, true);
    const emptyHomeId = home(null, null), contextDeclarationIds: string[] = [];
    let rootHomeId = emptyHomeId;
    const pending: { value: unknown[]; path: StructurePath }[] = [];
    let cursor: unknown = input.home.telescope, at: StructurePath = [...path, 'home', 'telescope'];
    while (true) {
      budget.visit(pending.length, at);
      const a = array(cursor, at);
      if (a[0] === 'nil') { array(a, at, 1); break; }
      requireThat(a[0] === 'port' || a[0] === 'letE', 'unsupported positional telescope constructor', at);
      array(a, at, a[0] === 'port' ? 4 : 6);
      if (pending.length >= budget.limits.maxExternalDeclarations) fail('positional context exceeds the declaration limit', at, 'limit');
      pending.push({ value: a, path: at }); cursor = a[1]; at = [...at, 1];
    }
    requireThat(pending.length === arity, 'positional arity does not match the telescope', ['home', 'arity']);
    for (const entry of pending.reverse()) {
      const a = entry.value, at = entry.path;
      const id = budget.string(`${sourceIdentity}:declaration:${declarations.length}`, at);
      const before = rootHomeId, bodyHomeId = home(before, id);
      let item: PositionalStructuralDeclaration;
      if (a[0] === 'port') {
        const attrs = object(a[2], ['name', 'info'], [...at, 2]);
        item = { kind: 'positional', id, homeId: before, bodyHomeId, sourcePath: at, constructor: 'port',
          name: name(attrs.name, budget, [...at, 2, 'name']), binderInfo: binderInfo(attrs.info, [...at, 2, 'info']), children: [] };
      } else {
        item = { kind: 'positional', id, homeId: before, bodyHomeId, sourcePath: at, constructor: 'letE',
          name: name(a[2], budget, [...at, 2]), nondep: boolean(a[3], [...at, 3]), children: [] };
      }
      // The identity is reserved before drawing nested binders, but its home
      // enters scope only after both type and defining value have been drawn.
      declare(item);
      const typeIndex = item.constructor === 'port' ? 3 : 4;
      item.children.push({ role: 'type', nodeId: draw(a[typeIndex], before, [...at, typeIndex], 0) });
      if (item.constructor === 'letE') item.children.push({ role: 'definitionValue', nodeId: draw(a[5], before, [...at, 5], 0) });
      contextDeclarationIds.push(id); rootHomeId = bodyHomeId;
    }
    const rootId = draw(input.term, rootHomeId, [...path, 'term'], 0);
    const typeRootId = draw(input.type, rootHomeId, [...path, 'type'], 0);
    const drawing: PositionalStructuralDrawing = {
      schema: 'definograph.structure.positional.v1', sourceIdentity, sourcePath: path, arity,
      rootId, typeRootId, rootHomeId, emptyHomeId, nodes, homes,
      declarations: declarations as (OwnedStructuralDeclaration | PositionalStructuralDeclaration)[], contextDeclarationIds,
    };
    checkExactDrawingSize(drawing, options.limits);
    return drawing;
  });
}

/** Reconstruct the CTel, open term and open type solely from the positional
 * drawing. This shares the independent constructor reader, never the builder. */
export function readPositionalStructuralDrawing(drawing: PositionalStructuralDrawing,
  limits?: Partial<StructureLimits>): StructureResult<PositionalStructuralInput> {
  return result(() => {
    checkExactDrawingSize(drawing, limits);
    object(drawing, ['schema', 'sourceIdentity', 'sourcePath', 'rootId', 'typeRootId', 'rootHomeId',
      'emptyHomeId', 'arity', 'nodes', 'homes', 'declarations', 'contextDeclarationIds'], []);
    if (drawing.schema !== 'definograph.structure.positional.v1') fail('unsupported positional drawing schema', ['schema'], 'unsupported');
    const budget = new Budget(limits, 2);
    identity(drawing.sourceIdentity, budget, ['sourceIdentity']);
    const path = sourcePath(drawing.sourcePath, budget, ['sourcePath']);
    const arity = natural(drawing.arity, ['arity']);
    const ids = array(drawing.contextDeclarationIds, ['contextDeclarationIds']);
    if (ids.length > budget.limits.maxExternalDeclarations) fail('positional context exceeds the declaration limit', ['contextDeclarationIds'], 'limit');
    requireThat(arity === ids.length, 'positional arity does not match its declarations', ['arity']);
    const { declarations, seenDeclarations, home, edges, read, complete } = structuralReader(drawing, budget, true);
    home(drawing.emptyHomeId, null, null, ['emptyHomeId']);
    let rootHomeId = drawing.emptyHomeId, telescope: JsonValue = ['nil'];
    const context: string[] = [];
    for (const [i, value] of ids.entries()) {
      const at: StructurePath = [...path, 'home', 'telescope', ...Array<number>(arity - i - 1).fill(1)];
      budget.visit(arity - i - 1, at);
      const id = identity(value, budget, ['contextDeclarationIds', i]);
      const d = declarations.get(id);
      requireThat(d?.kind === 'positional' && !seenDeclarations.has(id), 'missing or repeated positional declaration', at);
      requireThat(d.constructor === 'port' || d.constructor === 'letE', 'unsupported positional declaration constructor', at);
      object(d, ['kind', 'id', 'homeId', 'bodyHomeId', 'sourcePath', 'name', 'children', 'constructor',
        ...(d.constructor === 'port' ? ['binderInfo'] : ['nondep'])], at);
      requireThat(d.homeId === rootHomeId && same(d.sourcePath, at), 'positional declaration has the wrong prefix home or path', at);
      seenDeclarations.add(id); home(d.bodyHomeId, rootHomeId, id, at);
      if (d.constructor === 'port') {
        const c = edges(d.children, ['type'], at);
        telescope = ['port', telescope,
          { name: name(d.name, budget, [...at, 2, 'name']), info: binderInfo(d.binderInfo, [...at, 2, 'info']) },
          read(c[0].nodeId, rootHomeId, context, [...at, 3], 0)];
      } else {
        const c = edges(d.children, ['type', 'definitionValue'], at);
        telescope = ['letE', telescope, name(d.name, budget, [...at, 2]), boolean(d.nondep, [...at, 3]),
          read(c[0].nodeId, rootHomeId, context, [...at, 4], 0),
          read(c[1].nodeId, rootHomeId, context, [...at, 5], 0)];
      }
      rootHomeId = d.bodyHomeId; context.unshift(id);
    }
    requireThat(drawing.rootHomeId === rootHomeId, 'term/type do not use the complete positional home', ['rootHomeId']);
    const term = read(drawing.rootId, rootHomeId, context, [...path, 'term'], 0);
    const type = read(drawing.typeRootId, rootHomeId, context, [...path, 'type'], 0);
    complete();
    return { home: { arity, telescope }, term, type };
  });
}
