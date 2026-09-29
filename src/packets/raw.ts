/** Exact constructor inspection. References and byte positions are retained fields;
 * this representation resolves no references and makes no typing or context claim.
 * Readback uses only the exposed fields and ordered child roles of the drawing.
 */
import type { JsonValue } from './packet';
import { NaturalError, readNatural, type TaggedNatural } from './natural';
import type { StructuralBinderInfo, StructuralLocalKind, StructuralName } from './structure';

export type RawPath = (string | number)[];
export type RawFamily = 'expression' | 'level' | 'literal' | 'metadata' | 'dataValue' | 'integer'
  | 'syntax' | 'sourceInfo' | 'substring' | 'preresolved' | 'localDeclaration' | 'frame'
  | 'expressions' | 'levels' | 'syntaxList' | 'preresolutions' | 'strings' | 'declarations'
  | 'metadataEntries' | 'metadataEntry' | 'string';
export type RawField = { role: string } & (
  | { kind: 'name'; value: StructuralName }
  | { kind: 'natural'; value: TaggedNatural }
  | { kind: 'string'; value: string }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'binderInfo'; value: StructuralBinderInfo }
  | { kind: 'localKind'; value: StructuralLocalKind }
);
export interface RawEdge { role: string; nodeId: string; ordinal?: number }
export interface RawNode {
  id: string; family: RawFamily; tag: string; sourcePath: RawPath;
  fields: RawField[]; children: RawEdge[];
}
export interface RawInspectionDrawing {
  schema: 'definograph.raw-inspection.v1'; naturalProfile: 2;
  sourceIdentity: string; sourcePath: RawPath; family: RawFamily; rootId: string; nodes: RawNode[];
}
export interface RawLimits {
  maxNodes: number; maxDepth: number; maxTextBytes: number; maxOutputBytes: number; maxNaturalDigits: number;
}
export interface RawError { code: 'malformed' | 'unsupported' | 'limit'; message: string; path: RawPath }
export type RawResult<T> = { ok: true; value: T } | { ok: false; error: RawError };
export interface RawInspectionSource { family: RawFamily; value: JsonValue }
export interface RawInspectionOptions { sourceIdentity: string; sourcePath?: RawPath; limits?: Partial<RawLimits> }
export interface RawReadOptions { limits?: Partial<RawLimits> }

const DEFAULT_LIMITS: RawLimits = {
  maxNodes: 100_000, maxDepth: 128, maxTextBytes: 2 * 1024 * 1024,
  maxOutputBytes: 16 * 1024 * 1024, maxNaturalDigits: 10_000,
};
const FAMILIES: readonly RawFamily[] = ['expression', 'level', 'literal', 'metadata', 'dataValue', 'integer',
  'syntax', 'sourceInfo', 'substring', 'preresolved', 'localDeclaration', 'frame', 'expressions', 'levels', 'syntaxList',
  'preresolutions', 'strings', 'declarations', 'metadataEntries', 'metadataEntry', 'string'];
const COLLECTIONS: Partial<Record<RawFamily, RawFamily>> = {
  expressions: 'expression', levels: 'level', syntaxList: 'syntax', preresolutions: 'preresolved', strings: 'string',
  declarations: 'localDeclaration', metadataEntries: 'metadataEntry',
};
class Failure extends Error {
  constructor(readonly detail: RawError) { super(detail.message); }
}
function fail(message: string, path: RawPath, code: RawError['code'] = 'malformed'): never {
  throw new Failure({ code, message, path: [...path] });
}
function requireThat(test: unknown, message: string, path: RawPath): asserts test {
  if (!test) fail(message, path);
}
function result<T>(action: () => T): RawResult<T> {
  try { return { ok: true, value: action() }; }
  catch (error) { if (error instanceof Failure) return { ok: false, error: error.detail }; throw error; }
}
function array(value: unknown, path: RawPath, length?: number): unknown[] {
  requireThat(Array.isArray(value) && (length === undefined || value.length === length), 'invalid constructor or collection shape', path);
  if (value.length > DEFAULT_LIMITS.maxNodes) fail('collection exceeds implementation limit', path, 'limit');
  const keys = Reflect.ownKeys(value);
  requireThat(keys.length === value.length + 1, 'sparse or extended array', path);
  for (let i = 0; i < value.length; i++) {
    const descriptor = Object.getOwnPropertyDescriptor(value, i);
    requireThat(descriptor && descriptor.enumerable && Object.hasOwn(descriptor, 'value'), 'array must have ordinary dense elements', [...path, i]);
  }
  return value;
}
function object(value: unknown, keys: readonly string[], path: RawPath): Record<string, unknown> {
  requireThat(value !== null && typeof value === 'object' && !Array.isArray(value), 'expected an object', path);
  const prototype = Object.getPrototypeOf(value);
  requireThat(prototype === Object.prototype || prototype === null, 'expected an ordinary JSON object', path);
  requireThat(Reflect.ownKeys(value).length === keys.length, 'unexpected or missing object fields', path);
  for (const key of keys) {
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    requireThat(descriptor && descriptor.enumerable && Object.hasOwn(descriptor, 'value'), 'unexpected, missing or non-data object field', [...path, key]);
  }
  return value as Record<string, unknown>;
}
/** Count UTF-8 and conservative JSON string bytes without slicing, normalization,
 * or allocating an unbounded encoded copy. Lean strings contain Unicode scalars. */
function stringBytes(value: string, path: RawPath): { text: number; json: number } {
  let text = 0, json = 2;
  for (let i = 0; i < value.length; i++) {
    const c = value.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff) {
      const next = value.charCodeAt(++i);
      requireThat(next >= 0xdc00 && next <= 0xdfff, 'unpaired surrogate in string', path);
      text += 4; json += 4;
    } else {
      requireThat(c < 0xdc00 || c > 0xdfff, 'unpaired surrogate in string', path);
      const bytes = c < 0x80 ? 1 : c < 0x800 ? 2 : 3;
      text += bytes; json += c < 0x20 ? 6 : c === 34 || c === 92 ? 2 : bytes;
    }
  }
  return { text, json };
}
class Budget {
  readonly limits = { ...DEFAULT_LIMITS };
  private count = 0;
  private text = 0;
  constructor(limits: Partial<RawLimits> = {}) {
    requireThat(limits !== null && typeof limits === 'object' && !Array.isArray(limits), 'invalid resource limits', ['limits']);
    for (const key of Reflect.ownKeys(limits)) {
      requireThat(typeof key === 'string' && Object.hasOwn(DEFAULT_LIMITS, key), 'unknown resource limit', ['limits']);
      const value = limits[key as keyof RawLimits];
      requireThat(typeof value === 'number' && Number.isSafeInteger(value) && value > 0
        && value <= DEFAULT_LIMITS[key as keyof RawLimits], 'limit must be positive and within the implementation maximum', ['limits', key]);
      this.limits[key as keyof RawLimits] = value;
    }
  }
  depth(depth: number, path: RawPath): void {
    if (depth > this.limits.maxDepth) fail('raw inspection exceeds depth limit', path, 'limit');
  }
  node(depth: number, path: RawPath): void {
    this.depth(depth, path);
    if (++this.count > this.limits.maxNodes) fail('raw inspection exceeds node limit', path, 'limit');
  }
  string(value: unknown, path: RawPath): string {
    requireThat(typeof value === 'string', 'expected a string', path);
    if (value.length > this.limits.maxTextBytes) fail('raw inspection exceeds text limit', path, 'limit');
    this.text += stringBytes(value, path).text;
    if (this.text > this.limits.maxTextBytes) fail('raw inspection exceeds text limit', path, 'limit');
    return value;
  }
}
/** Shape/cycle/output audit runs before either consumer examines untrusted fields.
 * It bounds generated paths and IDs as well as mathematical payload fields. */
function auditJson(value: unknown, budget: Budget, basePath: RawPath = []): number {
  let bytes = 0;
  const active = new Set<object>();
  function add(amount: number, path: RawPath): void {
    bytes += amount;
    if (bytes > budget.limits.maxOutputBytes) fail('raw inspection exceeds serialized output limit', path, 'limit');
  }
  function visit(v: unknown, depth: number, path: RawPath): void {
    if (depth > budget.limits.maxDepth * 4 + 32) fail('JSON nesting exceeds implementation limit', path, 'limit');
    if (typeof v === 'string') {
      if (v.length > budget.limits.maxOutputBytes) fail('string exceeds serialized output limit', path, 'limit');
      add(stringBytes(v, path).json, path); return;
    }
    if (v === null || typeof v === 'boolean') { add(v === null ? 4 : v ? 4 : 5, path); return; }
    if (typeof v === 'number') {
      requireThat(Number.isFinite(v), 'non-finite JSON number', path); add(String(v).length, path); return;
    }
    requireThat(typeof v === 'object' && v !== null, 'non-JSON field', path);
    requireThat(!active.has(v), 'cyclic JSON value', path); active.add(v);
    if (Array.isArray(v)) {
      const a = array(v, path); add(2 + Math.max(0, a.length - 1), path);
      for (let i = 0; i < a.length; i++) visit(a[i], depth + 1, [...path, i]);
    } else {
      const keys = Reflect.ownKeys(v);
      requireThat(keys.every(k => typeof k === 'string'), 'non-JSON object key', path);
      const o = object(v, keys as string[], path); add(2 + Math.max(0, keys.length - 1), path);
      for (const key of keys as string[]) {
        add(stringBytes(key, [...path, key]).json + 1, path); visit(o[key], depth + 1, [...path, key]);
      }
    }
    active.delete(v);
  }
  visit(value, 0, basePath);
  return bytes;
}
function sourcePath(value: unknown, budget: Budget, location: RawPath, countText: boolean): RawPath {
  const a = array(value, location);
  if (a.length > budget.limits.maxDepth * 4 + 32) fail('source path exceeds depth limit', location, 'limit');
  return a.map((part, i) => {
    if (typeof part === 'string') return countText ? budget.string(part, [...location, i]) : part;
    requireThat(typeof part === 'number' && Number.isSafeInteger(part) && part >= 0, 'invalid source path component', [...location, i]);
    return part;
  });
}
function family(value: unknown, path: RawPath): RawFamily {
  if (typeof value !== 'string' || !FAMILIES.includes(value as RawFamily)) fail('unsupported raw family', path, 'unsupported');
  return value as RawFamily;
}
function natural(value: unknown, budget: Budget, path: RawPath): TaggedNatural {
  try {
    const n = readNatural(value, 2) as TaggedNatural;
    if (n[1].length > budget.limits.maxNaturalDigits) fail('natural exceeds digit limit', path, 'limit');
    budget.string(n[1], [...path, 1]); return n;
  } catch (error) { if (error instanceof NaturalError) fail(error.message, path, error.code); throw error; }
}
function name(value: unknown, budget: Budget, path: RawPath, depth: number): StructuralName {
  budget.depth(depth, path);
  const a = array(value, path);
  switch (a[0]) {
    case 'anonymous': array(a, path, 1); return ['anonymous'];
    case 'str': array(a, path, 3); return ['str', name(a[1], budget, [...path, 1], depth + 1), budget.string(a[2], [...path, 2])];
    case 'num': array(a, path, 3); return ['num', name(a[1], budget, [...path, 1], depth + 1), natural(a[2], budget, [...path, 2])];
    default: return fail('unsupported Name constructor', path, 'unsupported');
  }
}
function scalar(kind: RawField['kind'], value: unknown, budget: Budget, path: RawPath, depth: number): RawField['value'] {
  switch (kind) {
    case 'name': return name(value, budget, path, depth);
    case 'natural': return natural(value, budget, path);
    case 'string': return budget.string(value, path);
    case 'boolean': requireThat(typeof value === 'boolean', 'expected a Boolean flag', path); return value;
    case 'binderInfo': requireThat(typeof value === 'string' && ['default', 'implicit', 'strictImplicit', 'instImplicit'].includes(value), 'invalid binder information', path); return value as StructuralBinderInfo;
    case 'localKind': requireThat(typeof value === 'string' && ['default', 'implDetail', 'auxDecl'].includes(value), 'invalid local declaration kind', path); return value as StructuralLocalKind;
  }
}

/** Construct one occurrence node per compound constructor or collection item.
 * Repeated underlying JavaScript objects become distinct occurrences. */
export function buildRawInspection(source: RawInspectionSource, options: RawInspectionOptions): RawResult<RawInspectionDrawing> {
  return result(() => {
    const budget = new Budget(options.limits);
    const input = object(source, ['family', 'value'], []), rootFamily = family(input.family, ['family']);
    const identity = budget.string(options.sourceIdentity, ['sourceIdentity']);
    requireThat(identity.length > 0, 'source identity must not be empty', ['sourceIdentity']);
    const path = sourcePath(options.sourcePath ?? ['value'], budget, ['sourcePath'], true);
    auditJson(input.value, budget, path);
    const nodes: RawNode[] = [];
    let outputBytes = 0;
    function draw(f: RawFamily, value: unknown, p: RawPath, depth: number): string {
      budget.node(depth, p);
      const n: RawNode = { id: `raw:${nodes.length}`, family: f, tag: '', sourcePath: [...p], fields: [], children: [] };
      nodes.push(n);
      const complete = (): string => {
        // Charge each finished occurrence before its parent can add another
        // sibling. Width times source-path depth cannot accumulate unchecked.
        outputBytes += auditJson(n, budget) + 1;
        if (outputBytes > budget.limits.maxOutputBytes) fail('raw inspection exceeds serialized output limit', p, 'limit');
        return n.id;
      };
      const field = (role: string, kind: RawField['kind'], v: unknown, suffix: string | number): void => {
        n.fields.push({ role, kind, value: scalar(kind, v, budget, [...p, suffix], depth + 1) } as RawField);
      };
      const child = (role: string, cf: RawFamily, v: unknown, suffix: string | number): void => {
        n.children.push({ role, nodeId: draw(cf, v, [...p, suffix], depth + 1) });
      };
      const itemFamily = COLLECTIONS[f];
      if (itemFamily) {
        n.tag = 'list';
        const items = array(value, p);
        for (let i = 0; i < items.length; i++) n.children.push({ role: 'item', ordinal: i, nodeId: draw(itemFamily, items[i], [...p, i], depth + 1) });
        return complete();
      }
      if (f === 'string') { n.tag = 'value'; n.fields.push({ role: 'value', kind: 'string', value: budget.string(value, p) }); return complete(); }
      if (f === 'frame') {
        const v = object(value, ['schema', 'naturalProfile', 'originalDeclarations', 'sourceTerm', 'sourceType'], p);
        if (v.schema !== 'definograph.raw-frame.v1' || v.naturalProfile !== 2) fail('unsupported raw frame version', p, 'unsupported');
        n.tag = 'frame'; child('originalDeclarations', 'declarations', v.originalDeclarations, 'originalDeclarations');
        child('sourceTerm', 'expression', v.sourceTerm, 'sourceTerm'); child('sourceType', 'expression', v.sourceType, 'sourceType');
        return complete();
      }
      if (f === 'localDeclaration') {
        requireThat(value !== null && typeof value === 'object' && !Array.isArray(value), 'expected a local declaration', p);
        const descriptor = Object.getOwnPropertyDescriptor(value, 'constructor');
        requireThat(descriptor && Object.hasOwn(descriptor, 'value'), 'missing local declaration constructor', p);
        const tag = descriptor.value;
        if (tag !== 'cdecl' && tag !== 'ldecl') fail('unsupported local declaration constructor', p, 'unsupported');
        const v = object(value, tag === 'cdecl'
          ? ['constructor', 'index', 'fvarId', 'userName', 'type', 'binderInfo', 'kind']
          : ['constructor', 'index', 'fvarId', 'userName', 'type', 'value', 'nondep', 'kind'], p);
        n.tag = tag; field('index', 'natural', v.index, 'index'); field('fvarId', 'name', v.fvarId, 'fvarId');
        field('userName', 'name', v.userName, 'userName');
        if (tag === 'cdecl') field('binderInfo', 'binderInfo', v.binderInfo, 'binderInfo');
        else field('nondep', 'boolean', v.nondep, 'nondep');
        field('kind', 'localKind', v.kind, 'kind'); child('type', 'expression', v.type, 'type');
        if (tag === 'ldecl') child('value', 'expression', v.value, 'value');
        return complete();
      }
      if (f === 'metadataEntry') {
        const v = array(value, p, 2); n.tag = 'entry'; field('key', 'name', v[0], 0); child('value', 'dataValue', v[1], 1); return complete();
      }
      const a = array(value, p);
      requireThat(typeof a[0] === 'string', 'missing constructor tag', p);
      n.tag = a[0];
      const length = (size: number): void => { array(a, p, size); };
      const sf = (role: string, kind: RawField['kind'], i: number): void => field(role, kind, a[i], i);
      const ch = (role: string, cf: RawFamily, i: number): void => child(role, cf, a[i], i);
      switch (f) {
        case 'expression': switch (n.tag) {
          case 'bvar': length(2); sf('index', 'natural', 1); break;
          case 'fvar': case 'mvar': length(2); sf('id', 'name', 1); break;
          case 'sort': length(2); ch('level', 'level', 1); break;
          case 'const': length(3); sf('name', 'name', 1); ch('levels', 'levels', 2); break;
          case 'app': length(3); ch('function', 'expression', 1); ch('argument', 'expression', 2); break;
          case 'lam': case 'forallE': length(5); sf('name', 'name', 1); sf('binderInfo', 'binderInfo', 4); ch('domain', 'expression', 2); ch('body', 'expression', 3); break;
          case 'letE': length(6); sf('name', 'name', 1); sf('nondep', 'boolean', 5); ch('type', 'expression', 2); ch('value', 'expression', 3); ch('body', 'expression', 4); break;
          case 'lit': length(2); ch('literal', 'literal', 1); break;
          case 'mdata': length(3); ch('metadata', 'metadata', 1); ch('expression', 'expression', 2); break;
          case 'proj': length(4); sf('owner', 'name', 1); sf('field', 'natural', 2); ch('expression', 'expression', 3); break;
          default: fail('unsupported Expr constructor', p, 'unsupported');
        } break;
        case 'level': switch (n.tag) {
          case 'zero': length(1); break;
          case 'succ': length(2); ch('of', 'level', 1); break;
          case 'max': case 'imax': length(3); ch('left', 'level', 1); ch('right', 'level', 2); break;
          case 'param': case 'mvar': length(2); sf('name', 'name', 1); break;
          default: fail('unsupported Level constructor', p, 'unsupported');
        } break;
        case 'literal': length(2); if (n.tag === 'natVal') sf('value', 'natural', 1);
          else if (n.tag === 'strVal') sf('value', 'string', 1); else fail('unsupported Literal constructor', p, 'unsupported'); break;
        case 'metadata': if (n.tag !== 'mdataEntries') fail('unsupported MData constructor', p, 'unsupported');
          length(2); ch('entries', 'metadataEntries', 1); break;
        case 'dataValue': length(2); switch (n.tag) {
          case 'ofString': sf('value', 'string', 1); break;
          case 'ofBool': sf('value', 'boolean', 1); break;
          case 'ofName': sf('value', 'name', 1); break;
          case 'ofNat': sf('value', 'natural', 1); break;
          case 'ofInt': ch('value', 'integer', 1); break;
          case 'ofSyntax': ch('value', 'syntax', 1); break;
          default: fail('unsupported DataValue constructor', p, 'unsupported');
        } break;
        case 'integer': if (n.tag !== 'ofNat' && n.tag !== 'negSucc') fail('unsupported Int constructor', p, 'unsupported');
          length(2); sf('magnitude', 'natural', 1); break;
        case 'syntax': switch (n.tag) {
          case 'missing': length(1); break;
          case 'node': length(4); sf('kind', 'name', 2); ch('info', 'sourceInfo', 1); ch('arguments', 'syntaxList', 3); break;
          case 'atom': length(3); sf('value', 'string', 2); ch('info', 'sourceInfo', 1); break;
          case 'ident': length(5); sf('name', 'name', 3); ch('info', 'sourceInfo', 1); ch('rawValue', 'substring', 2); ch('preresolved', 'preresolutions', 4); break;
          default: fail('unsupported Syntax constructor', p, 'unsupported');
        } break;
        case 'sourceInfo': switch (n.tag) {
          case 'none': length(1); break;
          case 'original': length(5); sf('position', 'natural', 2); sf('endPosition', 'natural', 4); ch('leading', 'substring', 1); ch('trailing', 'substring', 3); break;
          case 'synthetic': length(4); sf('position', 'natural', 1); sf('endPosition', 'natural', 2); sf('canonical', 'boolean', 3); break;
          default: fail('unsupported SourceInfo constructor', p, 'unsupported');
        } break;
        case 'substring': if (n.tag !== 'substring') fail('unsupported Substring constructor', p, 'unsupported');
          length(4); sf('backingString', 'string', 1); sf('startPosition', 'natural', 2); sf('stopPosition', 'natural', 3); break;
        case 'preresolved': switch (n.tag) {
          case 'namespace': length(2); sf('name', 'name', 1); break;
          case 'decl': length(3); sf('name', 'name', 1); ch('fields', 'strings', 2); break;
          default: fail('unsupported Preresolved constructor', p, 'unsupported');
        } break;
        default: fail('unsupported raw family', p, 'unsupported');
      }
      return complete();
    }
    const rootId = draw(rootFamily, input.value, path, 0);
    const drawing: RawInspectionDrawing = { schema: 'definograph.raw-inspection.v1', naturalProfile: 2,
      sourceIdentity: identity, sourcePath: path, family: rootFamily, rootId, nodes };
    auditJson(drawing, budget);
    return drawing;
  });
}

/** This decoder has no source argument and does not call the drawing builder.
 * Every reconstructed constructor is assembled from checked scalar fields and
 * individually checked role children. Unused, shared and cyclic nodes fail. */
export function readRawInspection(drawing: unknown, options: RawReadOptions = {}): RawResult<RawInspectionSource> {
  return result(() => {
    const budget = new Budget(options.limits);
    auditJson(drawing, budget);
    const d = object(drawing, ['schema', 'naturalProfile', 'sourceIdentity', 'sourcePath', 'family', 'rootId', 'nodes'], []);
    if (d.schema !== 'definograph.raw-inspection.v1' || d.naturalProfile !== 2) fail('unsupported raw drawing version', [], 'unsupported');
    requireThat(budget.string(d.sourceIdentity, ['sourceIdentity']).length > 0, 'source identity must not be empty', ['sourceIdentity']);
    const rootFamily = family(d.family, ['family']), rootPath = sourcePath(d.sourcePath, budget, ['sourcePath'], true);
    const ns = array(d.nodes, ['nodes']);
    if (ns.length > budget.limits.maxNodes) fail('raw inspection exceeds node limit', ['nodes'], 'limit');
    const indexed = new Map<string, Record<string, unknown>>();
    for (let i = 0; i < ns.length; i++) {
      const n = object(ns[i], ['id', 'family', 'tag', 'sourcePath', 'fields', 'children'], ['nodes', i]);
      requireThat(typeof n.id === 'string' && n.id.length > 0 && !indexed.has(n.id), 'missing or duplicate occurrence ID', ['nodes', i, 'id']);
      indexed.set(n.id, n);
    }
    const used = new Set<string>();
    function read(id: unknown, expectedFamily: RawFamily, expectedPath: RawPath, depth: number): JsonValue {
      budget.node(depth, expectedPath);
      requireThat(typeof id === 'string' && indexed.has(id), 'missing child occurrence', expectedPath);
      requireThat(!used.has(id), 'shared or cyclic child occurrence', expectedPath); used.add(id);
      const n = indexed.get(id)!;
      requireThat(family(n.family, expectedPath) === expectedFamily, 'wrong child family', expectedPath);
      const path = sourcePath(n.sourcePath, budget, expectedPath, false);
      requireThat(path.length === expectedPath.length && path.every((v, i) => v === expectedPath[i]), 'child source path does not match its constructor position', expectedPath);
      requireThat(typeof n.tag === 'string', 'missing constructor tag', path);
      const fields = array(n.fields, [...path, 'fields']), children = array(n.children, [...path, 'children']);
      let fi = 0, ci = 0;
      const sf = (role: string, kind: RawField['kind'], suffix: string | number): JsonValue => {
        requireThat(fi < fields.length, 'missing scalar field', [...path, suffix]);
        const f = object(fields[fi++], ['role', 'kind', 'value'], [...path, suffix]);
        requireThat(f.role === role && f.kind === kind, 'wrong scalar field role or kind', [...path, suffix]);
        return scalar(kind, f.value, budget, [...path, suffix], depth + 1) as JsonValue;
      };
      const ch = (role: string, cf: RawFamily, suffix: string | number): JsonValue => {
        requireThat(ci < children.length, 'missing constructor child', [...path, suffix]);
        const edge = object(children[ci++], ['role', 'nodeId'], [...path, suffix]);
        requireThat(edge.role === role, 'wrong constructor child role', [...path, suffix]);
        return read(edge.nodeId, cf, [...path, suffix], depth + 1);
      };
      const finish = (value: JsonValue): JsonValue => {
        requireThat(fi === fields.length && ci === children.length, 'unexpected scalar fields or constructor children', path); return value;
      };
      const itemFamily = COLLECTIONS[expectedFamily];
      if (itemFamily) {
        requireThat(n.tag === 'list' && fields.length === 0, 'invalid collection node', path);
        return children.map((edgeValue, i) => {
          const edge = object(edgeValue, ['role', 'nodeId', 'ordinal'], [...path, i]);
          requireThat(edge.role === 'item' && edge.ordinal === i, 'wrong collection role or ordinal', [...path, i]);
          return read(edge.nodeId, itemFamily, [...path, i], depth + 1);
        });
      }
      if (expectedFamily === 'string') {
        requireThat(n.tag === 'value', 'invalid string item tag', path);
        return finish(sf('value', 'string', 'value'));
      }
      if (expectedFamily === 'metadataEntry') {
        requireThat(n.tag === 'entry', 'invalid metadata entry tag', path);
        return finish([sf('key', 'name', 0), ch('value', 'dataValue', 1)]);
      }
      if (expectedFamily === 'frame') {
        requireThat(n.tag === 'frame', 'invalid frame tag', path);
        return finish({ schema: 'definograph.raw-frame.v1', naturalProfile: 2,
          originalDeclarations: ch('originalDeclarations', 'declarations', 'originalDeclarations'),
          sourceTerm: ch('sourceTerm', 'expression', 'sourceTerm'), sourceType: ch('sourceType', 'expression', 'sourceType') });
      }
      if (expectedFamily === 'localDeclaration') {
        if (n.tag !== 'cdecl' && n.tag !== 'ldecl') fail('unsupported local declaration constructor', path, 'unsupported');
        const index = sf('index', 'natural', 'index'), fvarId = sf('fvarId', 'name', 'fvarId'), userName = sf('userName', 'name', 'userName');
        if (n.tag === 'cdecl') {
          const binderInfo = sf('binderInfo', 'binderInfo', 'binderInfo'), kind = sf('kind', 'localKind', 'kind');
          return finish({ constructor: 'cdecl', index, fvarId, userName, type: ch('type', 'expression', 'type'), binderInfo, kind });
        }
        const nondep = sf('nondep', 'boolean', 'nondep'), kind = sf('kind', 'localKind', 'kind');
        return finish({ constructor: 'ldecl', index, fvarId, userName, type: ch('type', 'expression', 'type'),
          value: ch('value', 'expression', 'value'), nondep, kind });
      }
      let value: JsonValue;
      switch (expectedFamily) {
        case 'expression': switch (n.tag) {
          case 'bvar': value = ['bvar', sf('index', 'natural', 1)]; break;
          case 'fvar': case 'mvar': value = [n.tag, sf('id', 'name', 1)]; break;
          case 'sort': value = ['sort', ch('level', 'level', 1)]; break;
          case 'const': value = ['const', sf('name', 'name', 1), ch('levels', 'levels', 2)]; break;
          case 'app': value = ['app', ch('function', 'expression', 1), ch('argument', 'expression', 2)]; break;
          case 'lam': case 'forallE': {
            const nm = sf('name', 'name', 1), info = sf('binderInfo', 'binderInfo', 4);
            value = [n.tag, nm, ch('domain', 'expression', 2), ch('body', 'expression', 3), info]; break;
          }
          case 'letE': {
            const nm = sf('name', 'name', 1), nondep = sf('nondep', 'boolean', 5);
            value = ['letE', nm, ch('type', 'expression', 2), ch('value', 'expression', 3), ch('body', 'expression', 4), nondep]; break;
          }
          case 'lit': value = ['lit', ch('literal', 'literal', 1)]; break;
          case 'mdata': value = ['mdata', ch('metadata', 'metadata', 1), ch('expression', 'expression', 2)]; break;
          case 'proj': value = ['proj', sf('owner', 'name', 1), sf('field', 'natural', 2), ch('expression', 'expression', 3)]; break;
          default: return fail('unsupported Expr constructor', path, 'unsupported');
        } break;
        case 'level': switch (n.tag) {
          case 'zero': value = ['zero']; break;
          case 'succ': value = ['succ', ch('of', 'level', 1)]; break;
          case 'max': case 'imax': value = [n.tag, ch('left', 'level', 1), ch('right', 'level', 2)]; break;
          case 'param': case 'mvar': value = [n.tag, sf('name', 'name', 1)]; break;
          default: return fail('unsupported Level constructor', path, 'unsupported');
        } break;
        case 'literal': if (n.tag !== 'natVal' && n.tag !== 'strVal') return fail('unsupported Literal constructor', path, 'unsupported');
          value = [n.tag, sf('value', n.tag === 'natVal' ? 'natural' : 'string', 1)]; break;
        case 'metadata': if (n.tag !== 'mdataEntries') return fail('unsupported MData constructor', path, 'unsupported');
          value = ['mdataEntries', ch('entries', 'metadataEntries', 1)]; break;
        case 'dataValue': switch (n.tag) {
          case 'ofString': value = ['ofString', sf('value', 'string', 1)]; break;
          case 'ofBool': value = ['ofBool', sf('value', 'boolean', 1)]; break;
          case 'ofName': value = ['ofName', sf('value', 'name', 1)]; break;
          case 'ofNat': value = ['ofNat', sf('value', 'natural', 1)]; break;
          case 'ofInt': value = ['ofInt', ch('value', 'integer', 1)]; break;
          case 'ofSyntax': value = ['ofSyntax', ch('value', 'syntax', 1)]; break;
          default: return fail('unsupported DataValue constructor', path, 'unsupported');
        } break;
        case 'integer': if (n.tag !== 'ofNat' && n.tag !== 'negSucc') return fail('unsupported Int constructor', path, 'unsupported');
          value = [n.tag, sf('magnitude', 'natural', 1)]; break;
        case 'syntax': switch (n.tag) {
          case 'missing': value = ['missing']; break;
          case 'node': { const kind = sf('kind', 'name', 2); value = ['node', ch('info', 'sourceInfo', 1), kind, ch('arguments', 'syntaxList', 3)]; break; }
          case 'atom': { const text = sf('value', 'string', 2); value = ['atom', ch('info', 'sourceInfo', 1), text]; break; }
          case 'ident': { const nm = sf('name', 'name', 3); value = ['ident', ch('info', 'sourceInfo', 1), ch('rawValue', 'substring', 2), nm, ch('preresolved', 'preresolutions', 4)]; break; }
          default: return fail('unsupported Syntax constructor', path, 'unsupported');
        } break;
        case 'sourceInfo': switch (n.tag) {
          case 'none': value = ['none']; break;
          case 'original': {
            const position = sf('position', 'natural', 2), end = sf('endPosition', 'natural', 4);
            value = ['original', ch('leading', 'substring', 1), position, ch('trailing', 'substring', 3), end]; break;
          }
          case 'synthetic': value = ['synthetic', sf('position', 'natural', 1), sf('endPosition', 'natural', 2), sf('canonical', 'boolean', 3)]; break;
          default: return fail('unsupported SourceInfo constructor', path, 'unsupported');
        } break;
        case 'substring': if (n.tag !== 'substring') return fail('unsupported Substring constructor', path, 'unsupported');
          value = ['substring', sf('backingString', 'string', 1), sf('startPosition', 'natural', 2), sf('stopPosition', 'natural', 3)]; break;
        case 'preresolved': switch (n.tag) {
          case 'namespace': value = ['namespace', sf('name', 'name', 1)]; break;
          case 'decl': value = ['decl', sf('name', 'name', 1), ch('fields', 'strings', 2)]; break;
          default: return fail('unsupported Preresolved constructor', path, 'unsupported');
        } break;
        default: return fail('unsupported raw family', path, 'unsupported');
      }
      return finish(value);
    }
    const value = read(d.rootId, rootFamily, rootPath, 0);
    requireThat(used.size === indexed.size, 'orphaned occurrence nodes', ['nodes']);
    return { family: rootFamily, value };
  });
}
