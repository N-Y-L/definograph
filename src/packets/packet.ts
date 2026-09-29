/** Imported packet consistency. Hashes establish byte identity, never trusted production. */
import { naturalText, readNatural, type NaturalProfile } from './natural';
import { buildRawInspection, type RawError, type RawPath } from './raw';
export type JsonValue = null | boolean | number | string | JsonValue[] | JsonObject;
export interface JsonObject { [key: string]: JsonValue }
export type RecordRole = 'retained' | 'derived';
export type TaggedValue = JsonObject & { tag: string };
export type UseMember = JsonObject & { entry: JsonObject; sourceLevels: TaggedValue; viewLevels: TaggedValue };
export type RecordPayload = JsonObject & { uses: UseMember[] };
export type CheckReceipt = JsonObject & {
  id: number; pair: string; label: string; subject: JsonObject; declaration: JsonObject;
  envBefore: number; envAfter: number; outcome: TaggedValue;
};
export type SelectedUse = UseMember & { pair: string; role: RecordRole; oid: JsonValue; path: JsonValue };
export type PacketResult = JsonObject & {
  id: string; candidate: JsonValue;
  records: JsonObject & { retained: RecordPayload | null; derived: RecordPayload | null };
  report: JsonObject & { formation: TaggedValue; evidence: TaggedValue; checks: JsonValue[] };
};
export type PacketPayload = JsonObject & {
  schema: NaturalProfile; attempt: string; mode: string; bank: JsonObject; context: JsonObject;
  inputs: (JsonObject & { id: string; F: JsonValue; G: JsonValue })[];
  results: PacketResult[]; checks: CheckReceipt[]; uses: SelectedUse[]; audits: JsonObject[];
  coherence: JsonObject & { value: boolean; inputs: JsonValue[]; admissions: boolean[] };
  joint: JsonObject & { formation: 'notChecked'; evidence: 'notConstructed' };
};
export type PacketEnvelope = JsonObject & {
  schema: NaturalProfile; request: JsonObject & { id: string; documentRevision: string; sourceSnapshot: string };
  basis: JsonObject; payload: PacketPayload; bindings: JsonObject; digest: string;
};
/** Values are deeply frozen on return. Source text remains available for exact inspection. */
export interface ImportedPacket {
  readonly value: PacketEnvelope;
  readonly payload: PacketPayload;
  readonly identity: string;
  readonly sourceText: string;
}

export class PacketError extends Error {
  readonly code?: RawError['code'];
  readonly path?: RawPath;
  constructor(message: string, detail?: Pick<RawError, 'code' | 'path'>) {
    super(message); this.name = 'PacketError';
    if (detail) { this.code = detail.code; this.path = [...detail.path]; }
  }
}
const MAX_BYTES = 16 * 1024 * 1024;
const MAX_DEPTH = 128;
// Bound both the input graph and repeated consistency work on untrusted imports.
// These browser limits may decline a structurally valid larger Python packet.
const MAX_JSON_NODES = 500_000;
const MAX_CANONICAL_NODES = 4_000_000;
const MAX_CANONICAL_CHARACTERS = 128 * 1024 * 1024;
const encoder = new TextEncoder();
const FORMATION = ['unsupported', 'refused', 'rejected', 'unknown', 'formed'];
const EVIDENCE = ['notFormed', 'missing', 'rejected', 'unknown', 'certified'];
const OUTCOMES = ['accepted', 'rejected', 'unknown'];
const ROLES: RecordRole[] = ['retained', 'derived'];

function requirePacket(condition: unknown, message: string): asserts condition {
  if (!condition) throw new PacketError(message);
}
function object(value: JsonValue | undefined, label: string): JsonObject {
  requirePacket(value !== null && typeof value === 'object' && !Array.isArray(value), `${label} must be an object`);
  return value;
}
function array(value: JsonValue | undefined, label: string): JsonValue[] {
  requirePacket(Array.isArray(value), `${label} must be an array`); return value;
}
function nonempty(value: JsonValue | undefined, label: string): string {
  requirePacket(typeof value === 'string' && value.length > 0, `${label} must be a nonempty string`); return value;
}
function natural(value: JsonValue | undefined, label: string): number {
  requirePacket(typeof value === 'number' && Number.isSafeInteger(value) && value >= 0, `${label} must be a safe natural number`); return value;
}
function tag(value: JsonValue | undefined, allowed: string[], label: string): string {
  const result = object(value, label).tag;
  requirePacket(typeof result === 'string' && allowed.includes(result), `invalid ${label} tag`); return result;
}
function get(value: JsonObject, key: string): JsonValue { return Object.hasOwn(value, key) ? value[key] : null; }
function scalarString(value: string): void {
  for (let i = 0; i < value.length; i++) {
    const unit = value.charCodeAt(i);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = value.charCodeAt(++i);
      requirePacket(next >= 0xdc00 && next <= 0xdfff, 'JSON strings contain an unpaired Unicode surrogate');
    } else requirePacket(unit < 0xdc00 || unit > 0xdfff, 'JSON strings contain an unpaired Unicode surrogate');
  }
}

/** JSON.parse alone loses duplicate keys and rounds large integers before validation. */
function parseExactJson(source: string): JsonValue {
  requirePacket(typeof source === 'string', 'JSON source must be text');
  requirePacket(source.length <= MAX_BYTES && encoder.encode(source).length <= MAX_BYTES, 'packet exceeds the byte limit');
  let cursor = 0, nodes = 0;
  function countNode(): void {
    requirePacket(++nodes <= MAX_JSON_NODES, 'JSON node count exceeds the browser packet limit');
  }
  function whitespace(): void { while (cursor < source.length && /[\x20\t\r\n]/.test(source[cursor])) cursor++; }
  function string(): string {
    requirePacket(source[cursor] === '"', 'expected JSON string');
    const start = cursor++;
    while (cursor < source.length) {
      const next = source[cursor++];
      if (next === '"') {
        let result: unknown;
        try { result = JSON.parse(source.slice(start, cursor)); } catch { throw new PacketError('invalid JSON string'); }
        requirePacket(typeof result === 'string', 'invalid JSON string'); scalarString(result); return result;
      }
      if (next === '\\') cursor++;
    }
    throw new PacketError('unterminated JSON string');
  }
  function value(depth: number): JsonValue {
    countNode(); requirePacket(depth <= MAX_DEPTH, 'JSON nesting exceeds the packet limit'); whitespace();
    const next = source[cursor];
    if (next === '"') return string();
    if (next === '{') {
      cursor++; whitespace(); const result: JsonObject = Object.create(null);
      if (source[cursor] === '}') { cursor++; return result; }
      while (cursor < source.length) {
        requirePacket(depth + 1 <= MAX_DEPTH, 'JSON nesting exceeds the packet limit');
        countNode();
        const key = string(); requirePacket(!Object.hasOwn(result, key), 'duplicate JSON object key: ' + key);
        whitespace(); requirePacket(source[cursor++] === ':', 'expected colon after JSON key');
        result[key] = value(depth + 1); whitespace();
        const delimiter = source[cursor++]; if (delimiter === '}') return result;
        requirePacket(delimiter === ',', 'expected comma or closing object'); whitespace();
      }
      throw new PacketError('unterminated JSON object');
    }
    if (next === '[') {
      cursor++; whitespace(); const result: JsonValue[] = [];
      if (source[cursor] === ']') { cursor++; return result; }
      while (cursor < source.length) {
        result.push(value(depth + 1)); whitespace();
        const delimiter = source[cursor++]; if (delimiter === ']') return result;
        requirePacket(delimiter === ',', 'expected comma or closing array');
      }
      throw new PacketError('unterminated JSON array');
    }
    for (const [literal, result] of [['true', true], ['false', false], ['null', null]] as const) {
      if (source.startsWith(literal, cursor)) { cursor += literal.length; return result; }
    }
    if (next === '-' || (next >= '0' && next <= '9')) {
      const start = cursor;
      if (source[cursor] === '-') cursor++;
      requirePacket(source[cursor] >= '0' && source[cursor] <= '9', 'invalid JSON integer');
      if (source[cursor] === '0') cursor++;
      else while (source[cursor] >= '0' && source[cursor] <= '9') cursor++;
      requirePacket(!['.', 'e', 'E'].includes(source[cursor]), 'packets require integers, not decimal or exponent numbers');
      const lexeme = source.slice(start, cursor);
      requirePacket(lexeme.length <= 17, 'packet integer exceeds the safe browser range; retain the original source text');
      const parsed = Number(lexeme);
      requirePacket(Number.isSafeInteger(parsed), 'packet integer exceeds the safe browser range; retain the original source text');
      return parsed;
    }
    throw new PacketError('invalid JSON value');
  }
  const result = value(0); whitespace(); requirePacket(cursor === source.length, 'unexpected trailing JSON content'); return result;
}

/** Python sorts Unicode code points; JavaScript's default sort orders UTF-16 units. */
function compareKeys(a: string, b: string): number {
  const left = Array.from(a), right = Array.from(b);
  for (let i = 0; i < Math.min(left.length, right.length); i++) {
    const difference = left[i].codePointAt(0)! - right[i].codePointAt(0)!;
    if (difference) return difference;
  }
  return left.length - right.length;
}
function createCanonicalizer(): (value: JsonValue) => string {
  let nodes = 0, characters = 0;
  function charge(text: string): string {
    characters += text.length;
    requirePacket(characters <= MAX_CANONICAL_CHARACTERS, 'consistency work exceeds the browser packet limit');
    return text;
  }
  return function canonical(value: JsonValue): string {
    requirePacket(++nodes <= MAX_CANONICAL_NODES, 'consistency work exceeds the browser packet limit');
    if (value === null || typeof value !== 'object') return charge(JSON.stringify(value));
    if (Array.isArray(value)) {
      charge('[]');
      return '[' + value.map(item => { charge(','); return canonical(item); }).join(',') + ']';
    }
    charge('{}');
    return '{' + Object.keys(value).sort(compareKeys).map(key => {
      const encodedKey = charge(JSON.stringify(key)); charge(':,');
      return encodedKey + ':' + canonical(value[key]);
    }).join(',') + '}';
  };
}
function createHasher(canonical: (value: JsonValue) => string): (value: JsonValue) => Promise<string> {
  const cached = new WeakMap<object, Promise<string>>();
  return function hash(value: JsonValue): Promise<string> {
    if (value !== null && typeof value === 'object') { const previous = cached.get(value); if (previous) return previous; }
    const bytes = encoder.encode(canonical(value));
    requirePacket(bytes.length <= MAX_BYTES, 'canonical value exceeds the packet byte limit');
    requirePacket(globalThis.crypto?.subtle, 'Web Crypto is unavailable; packet consistency cannot be checked');
    const result = globalThis.crypto.subtle.digest('SHA-256', bytes).then(buffer =>
      Array.from(new Uint8Array(buffer), byte => byte.toString(16).padStart(2, '0')).join(''));
    if (value !== null && typeof value === 'object') cached.set(value, result);
    return result;
  };
}
function levels(value: JsonValue | undefined): void {
  const item = object(value, 'certificate universe metadata');
  const kind = tag(item, ['available', 'unavailable', 'notApplicable'], 'certificate universe metadata');
  if (kind === 'available') array(item.values, 'available certificate levels');
  else requirePacket(!Object.hasOwn(item, 'values'), 'non-available certificate metadata cannot contain levels');
  if (kind === 'unavailable') nonempty(item.reason, 'unavailable certificate metadata reason');
}
function members(value: JsonValue): JsonObject[] {
  return array(object(value, 'record').uses, 'worker-enumerated record uses').map(member => {
    const item = object(member, 'record use'); object(item.entry, 'UseEntry'); levels(item.sourceLevels); levels(item.viewLevels); return item;
  });
}
function checkProjection(value: JsonValue | undefined): JsonObject[] {
  return array(value, 'report checks').map(item => {
    const [label, outcome] = Array.isArray(item) && item.length === 2 ? item :
      [object(item, 'report check').label, object(item, 'report check').outcome];
    nonempty(label, 'check label'); tag(outcome, OUTCOMES, 'check outcome'); return { label, outcome };
  });
}

/** Validate only documented semantic positions. Annotation keys and unknown
 * constructors remain opaque; strings are never reparsed as source syntax. */
export function validatePacketNaturalRoles(root: JsonValue, profile: NaturalProfile): void {
  const rawOpaqueDeclarations = new WeakSet<JsonObject>();
  function semantic(value: JsonValue | undefined, label: string): void {
    // v1 historically imported unknown semantic forms. Preserve that boundary,
    // while preventing new tags from masquerading as legacy natural positions.
    if (profile === 1 && !(Array.isArray(value) && value[0] === 'nat')) return;
    try { readNatural(value, profile); }
    catch (error) { throw new PacketError(`${label}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  function heartbeat(value: JsonValue | undefined, label: string): void {
    semantic(value, label);
    if (profile === 2) requirePacket(naturalText(value, profile) !== '0', label + ' must be positive');
  }
  const operational = (value: JsonValue | undefined, label: string) => { if (profile === 2 || (Array.isArray(value) && value[0] === 'nat')) natural(value, label); };
  const syntaxFields = new Set(['name', 'fvarId', 'userName', 'nodeName', 'yName', 'declarationPrefix', 'theorem',
    'type', 'value', 'term', 'sourceTerm', 'sourceType', 'positionalTerm', 'positionalType', 'hints',
    'owner', 'ctx', 'telescope', 'nodeTy', 'sup', 'body', 'row', 'src', 'view', 'acts', 'srcCert', 'viewCert',
    'ports', 'srcPorts', 'sigma', 'base', 'occurrence', 'inOwner', 'inTy', 'inSup', 'inBody', 'outOwner', 'outTy', 'outSup', 'outBody', 'u', 'v']);
  const syntaxLists = new Set(['levels', 'levelParams', 'all', 'registry', 'universeParams', 'fixedUniverseInstance', 'lv', 'sorts', 'images', 'axioms', 'values']);
  const objects = new Set(['payload', 'basis', 'bank', 'context', 'sourceContext', 'targetContext', 'table', 'F', 'G', 'candidate',
    'records', 'retained', 'derived', 'report', 'subject', 'declaration', 'entry', 'use', 'sourceLevels', 'viewLevels',
    'result', 'exactEvidence', 'ev', 'binding', 'sourceBinding', 'sourceCapture', 'coherence', 'policies', 'resources', 'x', 'a', 'b', 'z', 'h']);
  const objectLists = new Set(['inputs', 'results', 'checks', 'audits', 'uses', 'rows', 'certs', 'originalDeclarations']);
  function syntax(value: JsonValue | undefined, path: string, location: RawPath): void {
    if (value === undefined || value === null || typeof value !== 'object') return;
    if (!Array.isArray(value)) { wire(value, path, false, location); return; }
    const kind = value[0];
    if (typeof kind !== 'string') return;
    switch (kind) {
      case 'num': semantic(value[2], path + '.Name.num'); break;
      case 'natVal': semantic(value[1], path + '.Literal.natVal'); return;
      case 'bvar': semantic(value[1], path + '.Expr.bvar'); return;
      case 'proj': semantic(value[2], path + '.projection index'); break;
      case 'uniqueArg': case 'instActual': semantic(value[1], path + '.' + kind); return;
      case 'var': operational(value[1], path + '.Fin variable'); return;
      case 'use': operational(value[1], path + '.reference offset'); operational(value[2], path + '.reference home'); break;
      case 'inst': operational(value[1], path + '.instantiation arity'); break;
      case 'classB': operational(value[2], path + '.certificate arity'); break;
      case 'regular':
        operational(value[1], path + '.reducibility hint');
        if (profile === 2) requirePacket((value[1] as number) <= 0xffffffff, path + '.reducibility hint must fit UInt32');
        return;
      case 'pi':
        if (value[2] !== null && typeof value[2] === 'object' && !Array.isArray(value[2]) && Object.hasOwn(value[2], 'name')) operational(value[1], path + '.scope depth');
        break;
      case 'letE':
        if (typeof value[3] === 'boolean' && !(Array.isArray(value[1]) && ['nil', 'port', 'letE'].includes(String(value[1][0])))) operational(value[1], path + '.scope depth');
        break;
      case 'strVal': case 'anonymous': case 'zero': case 'nil': case 'exact': return;
      case 'str': case 'succ': case 'max': case 'imax': case 'param': case 'mvar': case 'fvar': case 'sort':
      case 'const': case 'lit': case 'app': case 'lam': case 'forallE': case 'unique': case 'port': case 'cons': case 'leaf': case 'hole': break;
      default: return; // Unknown constructor contents are not reinterpreted.
    }
    value.slice(1).forEach((child, index) => {
      // The constant's universe instances are a list rather than a constructor.
      if (kind === 'const' && index === 1 && Array.isArray(child)) child.forEach((level, position) => syntax(level, `${path}[2][${position}]`, [...location, 2, position]));
      else syntax(child, `${path}[${index + 1}]`, [...location, index + 1]);
    });
  }
  function rawBinding(value: JsonObject, location: RawPath): void {
    const context = value.context;
    if (!context || typeof context !== 'object' || Array.isArray(context) || !Array.isArray(context.originalDeclarations)) return;
    const values: JsonValue[] = [], paths: RawPath[] = [];
    context.originalDeclarations.forEach((declaration, index) => {
      if (!declaration || typeof declaration !== 'object' || Array.isArray(declaration)
        || get(declaration, 'constructor') !== 'ldecl' || declaration.nondep !== true) return;
      values.push(get(declaration, 'value'));
      paths.push([...location, 'context', 'originalDeclarations', index, 'value']);
      rawOpaqueDeclarations.add(declaration);
    });
    if (values.length === 0) return;
    // One ordered collection shares node, text, depth and output budgets across
    // every ignored local value. Its index maps back to the supplied declaration.
    const result = buildRawInspection({ family: 'expressions', value: values }, { sourceIdentity: 'packet-source-binding', sourcePath: [] });
    if (!result.ok) {
      const [index, ...suffix] = result.error.path;
      const originalPath = typeof index === 'number' && paths[index] ? [...paths[index], ...suffix] : location;
      throw new PacketError(`${pathLabel(originalPath)}: ${result.error.message}`, { ...result.error, path: originalPath });
    }
  }
  function pathLabel(location: RawPath): string { return 'packet' + location.map(part => typeof part === 'number' ? `[${part}]` : `.${part}`).join(''); }
  function wire(value: JsonValue | undefined, path: string, sourceBinding = false, location: RawPath = []): void {
    if (value === undefined || value === null || typeof value !== 'object' || Array.isArray(value)) return;
    if (sourceBinding || Object.hasOwn(value, 'sourceKind')) {
      if (value.schema === 3) {
        requirePacket(profile === 2 && value.naturalProfile === 2 && value.rawProfile === 'definograph.raw.v1', path + '.source binding schema 3 requires natural profile 2 and raw profile definograph.raw.v1');
        rawBinding(value, location);
      } else {
        requirePacket(!Object.hasOwn(value, 'naturalProfile') && !Object.hasOwn(value, 'rawProfile'), path + '.source binding uses an unsupported mixed raw profile');
        if (Object.hasOwn(value, 'schema')) requirePacket(value.schema === profile, path + '.source binding schema must match the packet');
      }
    }
    const constructor = get(value, 'constructor');
    if (constructor === 'cdecl' || constructor === 'ldecl') semantic(value.index, path + '.LocalDecl.index');
    if (Object.hasOwn(value, 'oid') || (Object.hasOwn(value, 'src') && Object.hasOwn(value, 'view')) || (Object.hasOwn(value, 'pair') && Object.hasOwn(value, 'role') && Object.hasOwn(value, 'entry'))) semantic(value.oid, path + '.use oid');
    if (Object.hasOwn(value, 'heartbeatBound') || (Object.hasOwn(value, 'id') && Object.hasOwn(value, 'envBefore') && Object.hasOwn(value, 'declaration'))) heartbeat(value.heartbeatBound, path + '.heartbeatBound');
    for (const [key, child] of Object.entries(value)) {
      const at = `${path}.${key}`, childLocation = [...location, key];
      if (key === 'value' && rawOpaqueDeclarations.has(value)) continue;
      if (syntaxFields.has(key)) syntax(child, at, childLocation);
      else if (syntaxLists.has(key) && Array.isArray(child)) child.forEach((item, index) => syntax(item, `${at}[${index}]`, [...childLocation, index]));
      else if (objects.has(key)) wire(child, at, key === 'binding' || key === 'sourceBinding', childLocation);
      else if (objectLists.has(key) && Array.isArray(child)) child.forEach((item, index) => wire(item, `${at}[${index}]`, false, [...childLocation, index]));
      else if (['n', 'm', 'arity', 'home', 'e', 'sequence', 'initialEnvironment'].includes(key)) operational(child, at);
      else if (key === 'homes' && Array.isArray(child)) child.forEach((item, index) => operational(item, `${at}[${index}]`));
      else if ((key === 'scope' || key === 'sourceSteps' || key === 'path') && Array.isArray(child)) child.forEach((item, index) => syntax(item, `${at}[${index}]`, [...childLocation, index]));
      else if (key === 'kernelHeartbeatBounds' && Array.isArray(child)) child.forEach((item, index) => {
        const entry = object(item, `${at}[${index}]`); operational(entry.checkId, at + '.checkId'); heartbeat(entry.bound, at + '.bound');
      });
    }
  }
  wire(root, 'packet');
}

function validatePayload(raw: JsonObject, canonical: (value: JsonValue) => string, profile: NaturalProfile): PacketPayload {
  const same = (left: JsonValue, right: JsonValue): boolean => canonical(left) === canonical(right);
  requirePacket(raw.schema === profile, 'packet and worker schemas must match'); nonempty(raw.attempt, 'worker attempt'); nonempty(raw.mode, 'worker fixture mode');
  const bank = object(raw.bank, 'bank'); requirePacket(Object.hasOwn(bank, 'exactEvidence'), 'bank exactness evidence must be explicit');
  object(raw.context, 'owner context');
  const inputs = array(raw.inputs, 'inputs'), results = array(raw.results, 'results');
  requirePacket(inputs.length === 2 && results.length === 2, 'this profile requires exactly two operation pairs');
  const inputIds = inputs.map(item => {
    const input = object(item, 'input pair'); requirePacket(Object.hasOwn(input, 'F') && Object.hasOwn(input, 'G'), 'input pair must retain F and G');
    return nonempty(input.id, 'input pair id');
  });
  requirePacket(new Set(inputIds).size === 2, 'operation pair ids must be distinct');
  const byPair = new Map<string, JsonObject>();
  results.forEach((item, index) => {
    const result = object(item, 'result'); requirePacket(result.id === inputIds[index], 'result order and identity must match inputs');
    requirePacket(Object.hasOwn(result, 'candidate'), 'result must explicitly retain candidate or null');
    const report = object(result.report, 'report');
    const formation = tag(report.formation, FORMATION, 'formation'), evidence = tag(report.evidence, EVIDENCE, 'evidence');
    if (formation === 'formed') {
      requirePacket(result.candidate !== null, 'formed result requires its exact candidate');
      requirePacket(evidence !== 'notFormed', 'formed result cannot have notFormed evidence');
    } else requirePacket(evidence === 'notFormed', 'unformed result must have notFormed evidence');
    const records = object(result.records, 'result records');
    requirePacket(same(Object.keys(records).sort(), ['derived', 'retained']), 'retain separate retained and derived record slots');
    for (const role of ROLES) if (records[role] !== null) members(records[role]);
    checkProjection(report.checks); byPair.set(inputIds[index], result);
  });
  const checks = array(raw.checks, 'check receipts').map(item => object(item, 'check receipt'));
  let revision = 0;
  checks.forEach((check, sequence) => {
    requirePacket(check.id === sequence, 'receipt ids must be consecutive and preserve check order');
    requirePacket(typeof check.pair === 'string' && byPair.has(check.pair), 'check receipt names an unknown operation pair');
    nonempty(check.label, 'check receipt label'); object(check.subject, 'semantic check subject'); object(check.declaration, 'exact declaration');
    requirePacket(natural(check.envBefore, 'environment before') === revision, 'check environment lineage is discontinuous');
    const accepted = tag(check.outcome, OUTCOMES, 'check outcome') === 'accepted';
    requirePacket(natural(check.envAfter, 'environment after') === revision + Number(accepted), 'only accepted declarations extend the environment');
    revision = check.envAfter as number;
  });
  for (const [pair, result] of byPair) {
    const expected = checks.filter(check => check.pair === pair).map(check => ({ label: check.label, outcome: check.outcome }));
    requirePacket(same(checkProjection(object(result.report, 'report').checks), expected), 'report checks differ from exact ordered receipts');
  }
  for (const value of array(raw.audits, 'audits')) {
    const audit = object(value, 'audit'), subject = object(audit.subject, 'audit subject declaration');
    const environment = natural(audit.environment, 'audit environment'); requirePacket(environment <= revision, 'audit names an environment outside this attempt');
    nonempty(audit.category, 'audit category'); const availability = tag(audit.result, ['available', 'unavailable'], 'audit result');
    const auditResult = object(audit.result, 'audit result');
    if (availability === 'available') array(auditResult.axioms, 'exact axiom names');
    else { requirePacket(!Object.hasOwn(auditResult, 'axioms'), 'unavailable audit is not an empty axiom list'); nonempty(auditResult.reason, 'unavailable audit reason'); }
    const checkId = get(audit, 'checkId');
    if (checkId !== null) {
      const index = natural(checkId, 'audit check id'); requirePacket(index < checks.length, 'audit names an absent check');
      const check = checks[index]; requirePacket(same(subject, check.declaration), 'audit subject differs from its checked declaration');
      if (availability === 'available') requirePacket(object(check.outcome, 'check outcome').tag === 'accepted' && environment >= (check.envAfter as number), 'available audit must follow declaration installation');
      else requirePacket(environment >= (check.envBefore as number), 'audit predates its check environment');
    }
  }
  const identities = new Set<string>(), recordMembers = new Map<JsonValue, Set<string>>();
  for (const value of array(raw.uses, 'qualified selected uses')) {
    const use = object(value, 'qualified use'), pair = use.pair, role = use.role;
    requirePacket(typeof pair === 'string' && byPair.has(pair) && typeof role === 'string' && ROLES.includes(role as RecordRole), 'qualified use has an unknown operation or record role');
    const record = object(byPair.get(pair)!.records, 'records')[role]; requirePacket(record !== null, 'qualified use names an unavailable record');
    const member = { entry: get(use, 'entry'), sourceLevels: get(use, 'sourceLevels'), viewLevels: get(use, 'viewLevels') };
    let indexedMembers = recordMembers.get(record);
    if (!indexedMembers) {
      indexedMembers = new Set(members(record).map(canonical)); recordMembers.set(record, indexedMembers);
    }
    requirePacket(indexedMembers.has(canonical(member)), 'qualified use is not an exact record member with its certificate levels');
    const entry = object(use.entry, 'UseEntry'), selected = object(entry.use, 'selected use');
    requirePacket(Object.hasOwn(use, 'oid') && Object.hasOwn(use, 'path'), 'qualified use must retain its local id and path');
    requirePacket(same(use.oid, get(selected, 'oid')), 'qualified use local id differs from its entry');
    requirePacket(same(use.path, get(entry, 'path')), 'qualified use path differs from its entry');
    // Pair and role already select exactly one record, so this is equivalent to including its digest.
    const identity = canonical([raw.attempt, pair, role, use.oid, use.path]);
    requirePacket(!identities.has(identity), 'duplicate qualified use identity'); identities.add(identity);
  }
  const coherence = object(raw.coherence, 'coordination');
  requirePacket(typeof coherence.value === 'boolean', 'coherence result must be explicit');
  requirePacket(same(get(coherence, 'inputs'), inputs), 'coherence must bind the same ordered four inputs');
  requirePacket(Object.hasOwn(coherence, 'bankExact'), 'bank exactness cannot be inferred from coherence');
  const admissions = array(coherence.admissions, 'structural admissions');
  requirePacket(admissions.length === 2 && admissions.every(value => typeof value === 'boolean'), 'separate local structural admissions must be explicit');
  requirePacket(same(get(raw, 'joint'), { formation: 'notChecked', evidence: 'notConstructed' }), 'this profile cannot claim joint formation or evidence');
  return raw as PacketPayload;
}

async function bindings(payload: PacketPayload, request: JsonObject, basis: JsonObject, hash: ReturnType<typeof createHasher>): Promise<JsonObject> {
  const [basisId, bankId, contextId] = await Promise.all([hash({ request, basis }), hash(payload.bank), hash(payload.context)]);
  const results = await Promise.all(payload.results.map(async (result, index) => ({
    pair: result.id,
    subject: await hash({ basis: basisId, bank: bankId, context: contextId, inputs: await hash(payload.inputs[index]), candidate: await hash(result.candidate) }),
    report: await hash(result.report),
    records: { derived: await hash(result.records.derived), retained: await hash(result.records.retained) },
  })));
  const environments: string[] = [await hash({ basis: basisId, initial: basis.env0 })];
  const checks: JsonObject[] = [];
  for (const check of payload.checks) {
    if (check.outcome.tag === 'accepted') environments.push(await hash({ parent: environments[environments.length - 1], declaration: check.declaration }));
    checks.push({ id: check.id, receipt: await hash(check), environmentBefore: environments[check.envBefore], environmentAfter: environments[check.envAfter] });
  }
  const uses = await Promise.all(payload.uses.map(async use => ({
    id: [payload.attempt, use.pair, use.role, await hash(payload.results.find(result => result.id === use.pair)!.records[use.role]), use.oid, use.path],
    entry: await hash(use),
  })));
  const audits = await Promise.all(payload.audits.map(async audit => ({ audit: await hash(audit), subject: await hash(audit.subject), environment: environments[audit.environment as number] })));
  return { payload: await hash(payload), results, checks, environments, uses, audits };
}
function deepFreeze(value: unknown): void {
  if (value === null || typeof value !== 'object') return;
  for (const child of Object.values(value)) deepFreeze(child);
  Object.freeze(value);
}

/** One bounded canonicalization/hash session for an exact JSON import. Other
 * source formats share the byte and identity boundary without becoming packets. */
export function createExactJsonTools() {
  const canonical = createCanonicalizer();
  return { parse: parseExactJson, canonical, hash: createHasher(canonical), freeze: deepFreeze };
}

/** Validate imported bytes and attachments without making any producer or proof claim. */
export async function parsePacket(sourceText: string): Promise<ImportedPacket> {
  requirePacket(typeof sourceText === 'string', 'packet source must be text');
  const { parse, canonical, hash } = createExactJsonTools();
  const value = object(parse(sourceText), 'packet');
  const same = (left: JsonValue, right: JsonValue): boolean => canonical(left) === canonical(right);
  requirePacket(same(Object.keys(value).sort(), ['basis', 'bindings', 'digest', 'payload', 'request', 'schema']), 'invalid packet envelope fields');
  requirePacket(value.schema === 1 || value.schema === 2, 'unsupported packet schema');
  const unsigned: JsonObject = Object.create(null);
  for (const [key, item] of Object.entries(value)) if (key !== 'digest') unsigned[key] = item;
  requirePacket(value.digest === await hash(unsigned), 'packet digest does not bind the exact supplied bytes');
  const request = object(value.request, 'request'), basis = object(value.basis, 'basis');
  for (const key of ['id', 'documentRevision', 'sourceSnapshot']) nonempty(request[key], 'request ' + key);
  for (const key of ['workerEpoch', 'env0', 'depsDigest', 'workerDigest']) nonempty(basis[key], 'basis ' + key);
  const policies = object(basis.policies, 'checking policies'); array(basis.fixedUniverseInstance, 'fixed universe instance');
  const profile = value.schema as NaturalProfile;
  const payload = validatePayload(object(value.payload, 'worker payload'), canonical, profile);
  validatePacketNaturalRoles({ payload, basis }, profile);
  requirePacket(payload.attempt === request.id, 'worker response belongs to another request');
  const resources = policies.resources;
  if (resources !== null && typeof resources === 'object' && !Array.isArray(resources) && Object.hasOwn(resources, 'kernelHeartbeatBounds')) {
    requirePacket(same(resources.kernelHeartbeatBounds, payload.checks.map(check => ({ checkId: check.id, bound: get(check, 'heartbeatBound') }))), 'kernel resource policy differs from ordered receipt budgets');
  }
  requirePacket(same(get(value, 'bindings'), await bindings(payload, request, basis, hash)), 'attachment bindings do not match their subjects');
  const identity = await hash(value); deepFreeze(value);
  return Object.freeze({ value: value as PacketEnvelope, payload, identity, sourceText });
}

/** Plain JSON data read only through own data descriptors, so no accessor is evaluated: null, booleans, finite
 * numbers, strings, dense arrays and plain objects, bounded in depth and size. Used before comparing supplied names. */
export function plainJsonData(value: unknown, budget = { nodes: 1024 }, depth = 0): value is JsonValue {
  if (depth > 128 || --budget.nodes < 0) return false;
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return true;
  if (typeof value === 'number') return Number.isFinite(value);
  if (typeof value !== 'object') return false;
  const keys = Reflect.ownKeys(value), descriptors = Object.getOwnPropertyDescriptors(value);
  if (keys.some(key => typeof key !== 'string') || Object.values(descriptors).some(descriptor => !Object.hasOwn(descriptor, 'value'))) return false;
  if (Array.isArray(value)) {
    const length = descriptors.length.value as number;
    return Object.getPrototypeOf(value) === Array.prototype && keys.length === length + 1
      && Object.entries(descriptors).every(([key, descriptor]) => key === 'length'
        || /^(0|[1-9][0-9]*)$/.test(key) && Number(key) < length && descriptor.enumerable && plainJsonData(descriptor.value, budget, depth + 1));
  }
  return [Object.prototype, null].includes(Object.getPrototypeOf(value))
    && Object.values(descriptors).every(descriptor => descriptor.enumerable && plainJsonData(descriptor.value, budget, depth + 1));
}
