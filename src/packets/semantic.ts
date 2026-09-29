/** Exact presentation of packet expressions and positional components. This
 * module neither checks Lean declarations nor uses the legacy semantic compiler. */
import type { Binder, Expr, StatementNode } from '../core/types';
import { contextEntryTitle } from '../core/context-entry';
import { SEMANTIC_DOCUMENT_VERSION } from '../semantic/types';
import type { FragmentCoverage, OpaqueRegion, Provenance, QuantifierChoice, SemanticDocument, SemanticObject, SemanticRelation, SemanticScope } from '../semantic/types';
import { plainJsonData, type CheckReceipt, type ImportedPacket, type JsonObject, type JsonValue, type RecordRole } from './packet';
import { boundedNatural, naturalText, type NaturalProfile } from './natural';
import { formatExpr, levelText, nameText, PacketSyntax, PacketSyntaxError, validateExpr } from './syntax';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing, type PositionalStructuralInput, type StructuralLocalKind } from './structure';
import { recordedName } from './recorded-name';

export interface PacketSource {
  readonly syntax: JsonValue;
  readonly path: (string | number)[];
  /** Lexical introduction order, oldest first. */
  readonly scopeBinderIds: string[];
}
export interface PacketRecordReading {
  readonly profile?: NaturalProfile;
  readonly document?: SemanticDocument;
  readonly reason?: string;
  readonly record: JsonValue;
  readonly source: { checkId?: number; label: string; outcome?: string; association: 'reading' | 'source' | 'unavailable' };
  readonly checks: readonly CheckReceipt[];
  readonly sourceById: Record<string, PacketSource>;
  readonly supplierObjectId?: string;
}
export interface PositionalComponentReading {
  readonly target: 'term' | 'type';
  readonly sourceById: Record<string, PacketSource>;
  readonly contextNodeIds: string[];
  readonly targetNodeId?: string;
  readonly document?: SemanticDocument;
  readonly reason?: string;
  /** Recorded kinds were given but could not be matched to the context, so every entry reads neutrally. */
  readonly recordedKindsUnmatched?: true;
}
export interface PositionalComponentOptions {
  readonly sourceIdentity: string;
  readonly sourcePath?: (string | number)[];
  readonly sourceOrigin?: 'selected-occurrence' | 'definition-head-exposure' | 'decomposition-result';
  readonly target: 'term' | 'type';
  /** Local presentation instruction supplied after exact formation association.
   * This compiler does not authenticate receipts or a native environment. */
  readonly logicalRoot?: PositionalLogicalRoot;
  /** The captured declarations, oldest first: exact recorded name and recorded kind. Entries added by selection
   * or continuation have no recorded declaration kind here. */
  readonly recordedContext?: readonly RecordedContextDeclaration[];
}
/** A captured declaration: its exact recorded name, used only to check alignment, and its recorded kind. */
export interface RecordedContextDeclaration { readonly name: JsonValue; readonly kind: StructuralLocalKind }
export interface PositionalLogicalRoot {
  readonly form: 'forall' | 'implies' | 'eq' | 'and' | 'or' | 'iff' | 'not' | 'exists' | 'true' | 'false' | 'unexpanded';
  readonly proofBinder?: boolean;
  readonly bodyUsesBinder?: boolean;
}

type Path = (string | number)[];
type Environment = readonly Binder[]; // Lean de Bruijn order: newest first.
interface Located { raw: JsonValue; path: Path }
interface Capture { check: CheckReceipt; path: Path; raw: JsonValue; association: 'reading' | 'source' }
type PresentationSource = Located & { association?: Capture['association'] };
export interface CapturedPacketExpression extends PacketSource {
  checkId: number;
  association: 'reading' | 'source';
  outcome: string;
}
const MAX_NODES = 30_000;
const MAX_DEPTH = 128;
const SAME_SOURCE = 'The diagram presents imported syntax only; it does not establish the declaration or any law as currently checked.';

function isObject(value: JsonValue | undefined): value is JsonObject {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
function same(a: JsonValue | undefined, b: JsonValue | undefined): boolean {
  // The compared values here are exact constructor arrays, or a bound copy of
  // the same declaration. Object key order is not an expression identity.
  if (a === b) return true;
  if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((v, i) => same(v, b[i]));
  if (isObject(a) && isObject(b)) return Object.keys(a).length === Object.keys(b).length && Object.keys(a).every(k => Object.hasOwn(b, k) && same(a[k], b[k]));
  return false;
}
/** Plain, dense data for at most 128 declarations (the captured-context bound), each name itself plain JSON data.
 * Accessors are never evaluated, and alignment with the context is decided separately. */
function recordedContextShape(value: unknown): value is RecordedContextDeclaration[] {
  const data = (candidate: object, keys: readonly string[]) => Reflect.ownKeys(candidate).length === keys.length
    && Reflect.ownKeys(candidate).every(key => typeof key === 'string' && keys.includes(key))
    && Object.entries(Object.getOwnPropertyDescriptors(candidate)).every(([key, descriptor]) => Object.hasOwn(descriptor, 'value')
      && (descriptor.enumerable || key === 'length' && Array.isArray(candidate)));
  if (!Array.isArray(value) || Object.getPrototypeOf(value) !== Array.prototype || value.length > 128 || Reflect.ownKeys(value).length !== value.length + 1
    || !data(value, ['length', ...Array.from({ length: value.length }, (_, index) => String(index))])) return false;
  return Object.entries(Object.getOwnPropertyDescriptors(value)).every(([key, descriptor]) => {
    if (key === 'length') return true;
    const entry = descriptor.value as unknown;
    return entry !== null && typeof entry === 'object' && !Array.isArray(entry) && [Object.prototype, null].includes(Object.getPrototypeOf(entry))
      && data(entry, ['name', 'kind']) && ['default', 'auxDecl', 'implDetail'].includes(Object.getOwnPropertyDescriptor(entry, 'kind')!.value)
      && plainJsonData(Object.getOwnPropertyDescriptor(entry, 'name')!.value);
  });
}
function fields(raw: JsonValue): JsonValue[] {
  if (!Array.isArray(raw)) throw new PacketSyntaxError('expected an exact Expr constructor');
  return raw;
}
function pathKey(path: Path): string { return path.map(part => encodeURIComponent(String(part))).join('/'); }
function constructorIs(raw: JsonValue, kind: string, length: number): boolean {
  return Array.isArray(raw) && raw.length === length && raw[0] === kind;
}
function application(raw: JsonValue, path: Path): { head: Located; args: Located[] } {
  const args: Located[] = [];
  let head = { raw, path };
  while (constructorIs(head.raw, 'app', 3)) {
    const part = fields(head.raw);
    args.unshift({ raw: part[2], path: [...head.path, 2] });
    head = { raw: part[1], path: [...head.path, 1] };
  }
  return { head, args };
}
function builtIn(raw: JsonValue, name: 'And' | 'Eq' | 'Or' | 'Iff' | 'Not' | 'Exists' | 'True' | 'False', arity: number, path: Path): Located[] | undefined {
  const parts = application(raw, path);
  return constructorIs(parts.head.raw, 'const', 3) && same(fields(parts.head.raw)[1], ['str', ['anonymous'], name]) &&
    Array.isArray(fields(parts.head.raw)[2]) && (fields(parts.head.raw)[2] as JsonValue[]).length === (name === 'Eq' || name === 'Exists' ? 1 : 0) && parts.args.length === arity
    ? parts.args : undefined;
}

/** Resolve only references to surrounding binders; locally bound indices stay
 * in the raw constructors, including their Names and BinderInfo annotations. */
function ambientReferences(raw: JsonValue, profile: NaturalProfile, bound = 0, result = new Set<number>()): Set<number> {
  const f = fields(raw);
  switch (f[0]) {
    case 'bvar': { const index = boundedNatural(f[1], profile, Number.MAX_SAFE_INTEGER); if (index >= bound) result.add(index - bound); break; }
    case 'app': ambientReferences(f[1], profile, bound, result); ambientReferences(f[2], profile, bound, result); break;
    case 'forallE': case 'lam': ambientReferences(f[2], profile, bound, result); ambientReferences(f[3], profile, bound + 1, result); break;
    case 'letE': ambientReferences(f[2], profile, bound, result); ambientReferences(f[3], profile, bound, result); ambientReferences(f[4], profile, bound + 1, result); break;
    case 'proj': ambientReferences(f[3], profile, bound, result); break;
  }
  return result;
}

function captures(packet: ImportedPacket, pair: string, role: RecordRole, association: 'reading' | 'source'): Capture[] {
  // These are protocol subject targets, not theorem, user record or display labels.
  const target = `${role === 'retained' ? 'laws' : 'law'}.${association} is a proposition`;
  return packet.payload.checks.flatMap((check, index) => {
    const subject = check.subject, declaration = check.declaration;
    if (check.pair !== pair || subject.target !== target || subject.pair !== pair || subject.sequence !== check.id ||
      subject.attempt !== packet.payload.attempt || !same(subject.declaration, declaration) || declaration.kind !== 'defnDecl' ||
      !same(declaration.type, ['sort', ['zero']]) || !Object.hasOwn(declaration, 'value')) return [];
    return [{ check, raw: declaration.value, path: ['payload', 'checks', index, 'declaration', 'value'], association }];
  });
}

/** Select a uniquely bound captured expression independently of the specialized
 * guided-reading compiler. A display limitation there must not erase the input
 * to the general structural drawing. Outcomes remain imported reports. */
export function capturedPacketExpression(packet: ImportedPacket, operationIndex: number, role: RecordRole,
  preferredCheckId?: number): CapturedPacketExpression | undefined {
  if (!Number.isSafeInteger(operationIndex) || operationIndex < 0 || operationIndex >= packet.payload.results.length ||
    !['retained', 'derived'].includes(role)) return;
  const result = packet.payload.results[operationIndex];
  if (!isObject(result.records[role])) return;
  const candidates = (['reading', 'source'] as const).flatMap(association => {
    const matches = captures(packet, result.id, role, association);
    return matches.length === 1 ? matches : [];
  });
  const selected = candidates.find(capture => capture.check.id === preferredCheckId) ?? candidates[0];
  if (!selected) return;
  return { syntax: selected.raw, path: [...selected.path], scopeBinderIds: [], checkId: selected.check.id,
    association: selected.association, outcome: selected.check.outcome.tag };
}

/** Find the designated supplier by its captured constructor position and exact
 * record fields. A binder called "h" elsewhere has no special status. */
function supplierPath(record: JsonObject, raw: JsonValue, rootPath: Path, profile: NaturalProfile): Path | undefined {
  try {
    if (typeof record.n !== 'number' || !Number.isSafeInteger(record.n) || record.n < 0 || record.table === undefined || record.owner === undefined) return;
    const syntax = new PacketSyntax(record.table, profile), owner = syntax.owner(record.owner);
    if (owner.length !== record.n) return;
    let current = raw, path = rootPath;
    for (const binding of owner) {
      const f = fields(current);
      if (binding.value !== undefined) {
        if (!constructorIs(current, 'letE', 6) || !same(f[1], binding.name) || !same(f[2], binding.type) || !same(f[3], binding.value) || f[5] !== binding.nondep) return;
        current = f[4]; path = [...path, 4];
      } else {
        if (!constructorIs(current, 'forallE', 5) || !same(f[1], binding.name) || !same(f[2], binding.type) || f[4] !== binding.info) return;
        current = f[3]; path = [...path, 3];
      }
    }
    const f = fields(current);
    if (record.nodeName === undefined || record.nodeTy === undefined || record.sup === undefined || !constructorIs(current, 'letE', 6)) return;
    if (same(f[1], record.nodeName) && same(f[2], syntax.occ(record.nodeTy, record.n)) && same(f[3], syntax.occ(record.sup, record.n))) return path;
  } catch { /* A decodable captured expression can still be read without a supplier association. */ }
}

class RecordCompiler {
  private visits = 0;
  private readonly expressions = new Map<string, Expr>();
  private readonly binders = new Map<string, Binder>();
  private readonly objects = new Map<string, SemanticObject & { provenance: Provenance[] }>();
  private readonly objectKeys = new Map<string, string>();
  private readonly objectDisplayNames = new Map<string, Set<string>>();
  private readonly relations: SemanticRelation[] = [];
  private readonly scopes: SemanticScope[] = [];
  private readonly choices: QuantifierChoice[] = [];
  private readonly opaqueRegions: OpaqueRegion[] = [];
  private readonly coverage: FragmentCoverage[] = [];
  private readonly unresolved = new Map<string, { raw: JsonValue; path: Path; env: Environment }>();
  private readonly statementPaths = new Map<string, StatementNode>();
  private readonly diagnostics: string[];
  supplierObjectId?: string;

  constructor(private readonly base: string, private readonly capture: PresentationSource,
    private readonly sourceById: Record<string, PacketSource>, private readonly profile: NaturalProfile, private readonly supplier?: Path,
    private readonly componentTarget?: 'term' | 'type',
    private readonly componentOrigin: 'selected-occurrence' | 'definition-head-exposure' | 'decomposition-result' = 'selected-occurrence',
    private readonly logicalRoot?: PositionalLogicalRoot) {
    this.diagnostics = [componentTarget ? 'This partial presentation follows the exact selected expression and its positional context. Structural readback belongs to the separate complete source drawing; this guide establishes no typing or truth.' : SAME_SOURCE,
      'Function applications retain every argument in source order. No numerical model or mathematical property is inferred.'];
  }

  private visit(depth: number): void {
    if (++this.visits > MAX_NODES || depth > MAX_DEPTH) throw new PacketSyntaxError(`the ${this.componentTarget ? 'component' : 'packet'} diagram exceeds its node or depth limit; exact source is retained`);
  }
  private id(kind: string, path: Path): string { return `${this.base}:${kind}:${pathKey(path)}`; }
  private logicalAt(path: Path): PositionalLogicalRoot | undefined {
    return this.componentTarget === 'term' && pathKey(path) === pathKey(this.capture.path) ? this.logicalRoot : undefined;
  }
  private source(id: string, raw: JsonValue, path: Path, env: Environment): void {
    if (!Object.hasOwn(this.sourceById, id)) this.sourceById[id] = { syntax: raw, path: [...path], scopeBinderIds: env.map(b => b.id).reverse() };
  }
  private identity(raw: JsonValue, env: Environment): string {
    const references = [...ambientReferences(raw, this.profile)].sort((a, b) => a - b).map(index => [index, env[index]?.id]);
    return JSON.stringify([this.base, raw, references]);
  }
  private text(raw: JsonValue, env: Environment): string { return formatExpr(raw, env.map(b => b.name), this.profile); }
  private provenance(nodeId: string, expressionPath: string): Provenance {
    return { nodeId, expressionPath, origin: this.componentTarget ? this.componentOrigin : 'imported-packet' };
  }

  private binder(raw: JsonValue, path: Path, env: Environment, role: Binder['role'], depth: number): Binder {
    const f = fields(raw);
    return this.bind(raw, path, f[1], { raw: f[2], path: [...path, 2] }, env, role, depth,
      f[0] === 'letE' ? { raw: f[3], path: [...path, 3], nondep: f[5] as boolean } : undefined);
  }

  /** Register declaration fields directly; CTel entries are not fake Expr binders. */
  private bind(raw: JsonValue, path: Path, rawName: JsonValue, type: Located, env: Environment,
    role: Binder['role'], depth: number, value?: Located & { nondep: boolean }, contextName?: string): Binder {
    const id = this.id('binder', path), existing = this.binders.get(id);
    if (existing) return existing;
    const baseName = contextName ?? (this.componentTarget ? recordedName(rawName, 'binder') : nameText(rawName));
    let name = baseName, suffix = 1;
    while (env.some(b => b.name === name)) name = `${baseName}@${++suffix}`;
    const dependencies = new Set(ambientReferences(type.raw, this.profile));
    if (value) ambientReferences(value.raw, this.profile, 0, dependencies);
    const binder: Binder = { id, name, type: this.text(type.raw, env), role,
      dependsOn: env.filter((_, index) => dependencies.has(index)).map(b => b.id).reverse(),
      typeExpression: this.expression(type.raw, type.path, env, depth + 1) };
    if (value) binder.definition = { value: this.expression(value.raw, value.path, env, depth + 1), nondep: value.nondep };
    this.binders.set(id, binder); this.source(id, raw, path, env);
    return binder;
  }

  private expression(raw: JsonValue, path: Path, env: Environment, depth: number): Expr {
    const cacheKey = pathKey(path), cached = this.expressions.get(cacheKey);
    if (cached) return cached;
    this.visit(depth);
    const f = fields(raw), exactIdentity = this.identity(raw, env);
    let expression: Expr;
    switch (f[0]) {
      case 'bvar': {
        const binder = env[boundedNatural(f[1], this.profile, env.length)];
        if (!binder) throw new PacketSyntaxError('an expression references a binder outside its lexical scope');
        expression = { kind: 'var', id: binder.id, name: binder.name, type: binder.type, exactIdentity: `${this.base}:bound:${binder.id}` }; break;
      }
      case 'const': {
        const name = nameText(f[1]);
        expression = { kind: 'const', name: env.some(b => b.name === name) ? `global(${name})` : name, levels: (f[2] as JsonValue[]).map(levelText), exactIdentity }; break;
      }
      case 'sort': expression = { kind: 'sort', name: levelText(f[1]), exactIdentity }; break;
      case 'lit': {
        const literal = fields(f[1]);
        // The shared Expr type already supports exact decimal text. Source
        // identity and displayText retain the literal constructor distinction.
        const value = literal[0] === 'natVal' && this.profile === 2 ? naturalText(literal[1], this.profile) : literal[1] as string | number;
        expression = { kind: 'literal', value, exactIdentity }; break;
      }
      case 'app': {
        const parts = application(raw, path);
        expression = { kind: 'app', fn: this.expression(parts.head.raw, parts.head.path, env, depth + 1),
          args: parts.args.map(arg => this.expression(arg.raw, arg.path, env, depth + 1)), exactIdentity }; break;
      }
      case 'forallE': case 'lam': {
        const binder = this.binder(raw, path, env, f[0] === 'lam' ? 'lambda' : this.componentTarget ? 'parameter' : 'universal', depth);
        expression = { kind: f[0] === 'lam' ? 'lambda' : 'forall', binder, binderType: binder.typeExpression,
          body: this.expression(f[3], [...path, 3], [binder, ...env], depth + 1), exactIdentity }; break;
      }
      default:
        // The legacy Expr union has no faithful let/projection/free-variable
        // representation. Never turn these into a quantifier or an application.
        expression = { kind: 'opaque', text: this.text(raw, env), exactIdentity };
        this.unresolved.set(cacheKey, { raw, path, env });
    }
    expression.displayText = this.text(raw, env);
    this.expressions.set(cacheKey, expression);
    this.source(this.id('syntax', path), raw, path, env);
    return expression;
  }

  private object(raw: JsonValue, path: Path, env: Environment, scopeId: string, source: Provenance, expression = this.expression(raw, path, env, 0)): string {
    const binder = expression.kind === 'var' ? this.binders.get(expression.id) : undefined;
    const key = expression.exactIdentity!;
    const id = binder ? this.id('bound-object', [binder.id]) : this.objectKeys.get(key) ?? this.id('object', path);
    const existing = this.objects.get(id);
    if (existing) {
      if (!existing.provenance.some(p => p.nodeId === source.nodeId && p.expressionPath === source.expressionPath)) existing.provenance.push(source);
      if (!binder) {
        // A shared term can occur in several scopes with different shadowing.
        // Reserve all encountered display names after the real environment so
        // global names remain explicit in every occurrence. Extra names affect
        // formatting only; neither de Bruijn indices nor semantic scope change.
        const names = this.objectDisplayNames.get(id)!;
        env.forEach(binding => names.add(binding.name));
        const currentNames = env.map(binding => binding.name);
        const label = formatExpr(raw, [...currentNames, ...[...names].filter(name => !currentNames.includes(name))], this.profile);
        const displayExpression = { ...expression, displayText: label };
        if (displayExpression.kind === 'const' && names.has(nameText(fields(raw)[1]))) displayExpression.name = `global(${nameText(fields(raw)[1])})`;
        this.objects.set(id, { ...existing, label, expression: displayExpression });
      }
      return id;
    }
    this.objectKeys.set(key, id);
    if (!binder) this.objectDisplayNames.set(id, new Set(env.map(binding => binding.name)));
    const kind = expression.kind === 'var' ? 'variable' : expression.kind === 'const' ? 'symbol' : expression.kind === 'sort' ? 'type'
      : expression.kind === 'literal' ? 'literal' : expression.kind === 'lambda' ? 'function' : 'expression';
    this.objects.set(id, { id, kind, label: binder?.name ?? this.text(raw, env), type: binder?.type ?? '', expression, binder, scopeId, provenance: [source] });
    this.source(id, raw, path, env);
    return id;
  }

  private introduce(binder: Binder, raw: JsonValue, path: Path, env: Environment, nodeId: string): string {
    const expression: Expr = { kind: 'var', id: binder.id, name: binder.name, type: binder.type, exactIdentity: `${this.base}:bound:${binder.id}`, displayText: binder.name };
    const scopeId = `scope:${nodeId}`, id = this.object(raw, path, env, scopeId, this.provenance(nodeId, 'binder'), expression);
    const ordinary = env.filter(b => b.role !== 'auxiliary');
    const availableObjectIds = ordinary.map(b => this.id('bound-object', [b.id])).reverse();
    // Definition roles are deliberately distinct: their values are fixed by
    // the source expression, never choices or assumptions.
    const introductionId = this.id('introduction', path);
    if (binder.role !== 'auxiliary') this.choices.push({ id: introductionId, objectId: id, binderId: binder.id, nodeId, role: binder.role,
      // An existential candidate may use the whole earlier scope. References in
      // its declared type alone do not determine its allowed dependence.
      dependsOn: this.componentTarget && binder.role === 'existential' ? availableObjectIds : binder.dependsOn.filter(id => ordinary.some(b => b.id === id)).map(id => this.id('bound-object', [id])), availableObjectIds, scopeId,
      explanation: binder.role === 'definition' ? 'A local definition with the displayed value; no arbitrary choice or existence claim is introduced.'
        : binder.role === 'lambda' ? 'A function input, available only in this body.'
          : this.componentTarget && binder.role === 'existential' ? 'A candidate bound inside the existential statement; no witness is supplied.'
          : this.componentTarget && binder.role === 'universal' ? 'A universally bound input in this proposition; the body remains within that binding.'
          : this.componentTarget ? 'A parameter with the displayed declared type, available in this positional scope; no quantified proposition is inferred.'
            : 'An arbitrary input in the exact captured forall expression; no implication is inferred from its printed type.' });
    if (this.componentTarget) this.source(introductionId, raw, path, env);
    if (this.supplier && pathKey(this.supplier) === pathKey(path)) this.supplierObjectId = id;
    return id;
  }

  private boundary(raw: JsonValue, path: Path, env: Environment, nodeId: string, expressionPath: string, reason: string): string {
    const id = this.id('opaque', path), expression = this.expression(raw, path, env, 0);
    this.opaqueRegions.push({ id, nodeId, scopeId: `scope:${nodeId}`, expression, label: this.text(raw, env), reason,
      supportedRelationIds: [], provenance: this.provenance(nodeId, expressionPath) });
    this.source(id, raw, path, env); return id;
  }

  private leaf(raw: JsonValue, path: Path, env: Environment, nodeId: string): void {
    const relationStart = this.relations.length, opaqueStart = this.opaqueRegions.length, objectIds = new Set<string>();
    const scopeId = `scope:${nodeId}`, seen = new Set<string>();
    const walk = (raw: JsonValue, path: Path, expressionPath: string, depth: number): void => {
      this.visit(depth);
      const expression = this.expression(raw, path, env, depth), identity = expression.exactIdentity!;
      const ownId = this.object(raw, path, env, scopeId, this.provenance(nodeId, expressionPath), expression);
      objectIds.add(ownId);
      if (seen.has(identity)) return;
      seen.add(identity);
      const equality = this.componentTarget && this.logicalAt(path)?.form !== 'eq' ? undefined : builtIn(raw, 'Eq', 3, path);
      if (equality) {
        const roles = ['type', 'left', 'right'];
        const ports = equality.map((arg, i) => {
          const objectId = this.object(arg.raw, arg.path, env, scopeId, this.provenance(nodeId, `${expressionPath}.${roles[i]}`));
          objectIds.add(objectId); return { role: roles[i], objectId };
        });
        const id = this.id('equality', path);
        this.relations.push({ id, kind: 'equality', label: 'Equality', ports, expression, scopeId, nodeId, pluginId: 'packet-exact-constructors', fidelity: 'symbolic',
          provenance: this.provenance(nodeId, expressionPath), conditions: [SAME_SOURCE, 'The equality carrier is retained in the explicit type port.'] });
        this.source(id, raw, path, env);
        equality.forEach((arg, i) => walk(arg.raw, arg.path, `${expressionPath}.${roles[i]}`, depth + 1));
      } else if (expression.kind === 'app') {
        const parts = application(raw, path);
        const functionId = this.object(parts.head.raw, parts.head.path, env, scopeId, this.provenance(nodeId, `${expressionPath}.function`));
        objectIds.add(functionId);
        const ports = [{ role: 'function', objectId: functionId }, ...parts.args.map((arg, index) => {
          const objectId = this.object(arg.raw, arg.path, env, scopeId, this.provenance(nodeId, `${expressionPath}.input${index + 1}`));
          objectIds.add(objectId); return { role: `input ${index + 1}`, objectId };
        }), { role: 'output', objectId: ownId }];
        const id = this.id('application', path);
        this.relations.push({ id, kind: 'application', label: this.text(parts.head.raw, env), ports, expression, scopeId, nodeId,
          pluginId: 'packet-exact-application', fidelity: 'symbolic', provenance: this.provenance(nodeId, expressionPath),
          conditions: ['Ordered application structure only. All inputs remain explicit; no reduction, mathematical property, or proof is inferred.'] });
        this.source(id, raw, path, env);
        walk(parts.head.raw, parts.head.path, `${expressionPath}.function`, depth + 1);
        parts.args.forEach((arg, index) => walk(arg.raw, arg.path, `${expressionPath}.input${index + 1}`, depth + 1));
      } else if (expression.kind === 'opaque') {
        const tag = String(fields(raw)[0]);
        this.boundary(raw, path, env, nodeId, expressionPath, `The ${tag} constructor is retained in exact source; this expression has no supported diagram. Its binders are not introduced as choices.`);
      } else if (expression.kind === 'lambda' || expression.kind === 'forall') {
        this.boundary(raw, path, env, nodeId, expressionPath, 'This nested binding expression is retained exactly as a function or type. Its body is not evaluated or promoted to the surrounding scope.');
      } else if (expressionPath === 'expression') {
        this.boundary(raw, path, env, nodeId, expressionPath, this.logicalAt(path)
          ? 'The proposition is retained at this exact occurrence; no additional internal logical form is inferred.'
          : 'This source expression is retained symbolically; no logical or mathematical interpretation is inferred.');
      }
    };
    walk(raw, path, 'expression', 0);
    const relations = this.relations.slice(relationStart), opaque = this.opaqueRegions.slice(opaqueStart);
    this.coverage.push({ nodeId, status: opaque.length ? relations.length ? 'partial' : 'structural' : relations.length ? 'interpreted' : 'structural',
      relationIds: relations.map(r => r.id), sceneIds: [], opaqueRegionIds: opaque.map(r => r.id), objectIds: [...objectIds] });
  }

  private tree(raw: JsonValue, path: Path, env: Environment, parentId?: string, depth = 0): StatementNode {
    this.visit(depth);
    const f = fields(raw), id = this.id('node', path), scopeId = `scope:${id}`;
    const expression = this.expression(raw, path, env, depth), children: StatementNode[] = [];
    const node: StatementNode = { id, kind: 'predicate', label: this.text(raw, env), lean: this.text(raw, env), expression, children, scope: env.map(b => b.id).reverse() };
    this.statementPaths.set(pathKey(path), node);
    this.source(id, raw, path, env);
    const localObjects = env.map(b => this.id('bound-object', [b.id])).reverse();
    const logical = this.logicalAt(path);
    let nextEnv = env, body: Located | undefined, operands: Located[] | undefined;
    if (f[0] === 'forallE' || f[0] === 'lam' || f[0] === 'letE') {
      const universal = logical?.form === 'forall' || logical?.form === 'implies';
      const role = f[0] === 'letE' ? 'definition' : f[0] === 'lam' ? 'lambda' : universal || !this.componentTarget ? 'universal' : 'parameter';
      node.kind = f[0] === 'letE' ? 'definition' : f[0] === 'lam' || this.componentTarget && !universal ? 'parameter' : logical?.form === 'implies' ? 'implies' : 'forall';
      node.binder = this.binder(raw, path, env, role, depth);
      // expression() may have already registered this exact binder neutrally.
      // Only this explicitly associated root changes its presentation role.
      if (universal) node.binder.role = role;
      node.label = logical?.form === 'implies' ? 'If the first condition holds, then the second holds'
        : `${role === 'definition' ? 'Define' : role === 'lambda' ? 'Function input' : role === 'universal' ? `For every${logical?.proofBinder ? ' proof' : ''}` : 'Dependent function input'} ${node.binder.name}${universal ? ` : ${node.binder.type}` : ''}`;
      localObjects.push(this.introduce(node.binder, raw, path, env, id));
      nextEnv = [node.binder, ...env];
      const bodyIndex = f[0] === 'letE' ? 4 : 3;
      body = { raw: f[bodyIndex], path: [...path, bodyIndex] };
      if (logical?.form === 'implies') operands = [{ raw: f[2], path: [...path, 2] }];
    }
    const conjunction = this.componentTarget ? undefined : builtIn(raw, 'And', 2, path);
    if (conjunction) { node.kind = 'and'; node.label = 'Both statements'; }
    if (logical && ['and', 'or', 'iff', 'not'].includes(logical.form)) {
      const forms = { and: ['And', 'Both required conditions'], or: ['Or', 'Alternative conditions'],
        iff: ['Iff', 'Equivalent conditions'], not: ['Not', 'Negated condition'] } as const;
      const form = logical.form as keyof typeof forms;
      node.kind = form; node.label = forms[form][1];
      operands = builtIn(raw, forms[form][0], form === 'not' ? 1 : 2, path);
    } else if (logical?.form === 'exists') {
      const predicate = builtIn(raw, 'Exists', 2, path)![1], p = fields(predicate.raw);
      node.kind = 'exists'; node.label = 'Existential condition with an unexpanded predicate';
      if (p[0] === 'lam') {
        node.binder = this.binder(predicate.raw, predicate.path, env, 'existential', depth);
        node.binder.role = 'existential';
        node.label = `Candidate ${node.binder.name} : ${node.binder.type} within the existential statement`;
        localObjects.push(this.introduce(node.binder, predicate.raw, predicate.path, env, id));
        nextEnv = [node.binder, ...env]; body = { raw: p[3], path: [...predicate.path, 3] };
      }
    } else if (logical?.form === 'unexpanded') node.label = 'Unexpanded proposition';
    else if (logical?.form === 'true' || logical?.form === 'false') node.label = `${logical.form === 'true' ? 'True' : 'False'} proposition`;
    this.scopes.push({ id: scopeId, parentId, nodeId: id, kind: node.kind, label: node.label, objectIds: localObjects, assumptionNodeIds: [], context: [] });
    if (this.componentTarget) this.source(scopeId, raw, path, env);
    (operands ?? conjunction)?.forEach(arg => children.push(this.tree(arg.raw, arg.path, env, scopeId, depth + 1)));
    if (body) children.push(this.tree(body.raw, body.path, nextEnv, scopeId, depth + 1));
    if (!children.length) this.leaf(raw, path, env, id);
    return node;
  }

  compile(): SemanticDocument {
    validateExpr(this.capture.raw, 0, this.profile);
    const tree = this.tree(this.capture.raw, this.capture.path, []);
    return this.finish(tree, []);
  }

  /** The context is a sequence of declaration presentations, not a generated
   * lambda/forall closure. Type and value fields are compiled in their prefix. */
  compilePositional(input: PositionalStructuralInput, sourcePath: Path, recorded?: readonly RecordedContextDeclaration[]): {
    document: SemanticDocument; contextNodeIds: string[]; targetNodeId: string; recordedKindsUnmatched?: true;
  } {
    const entries: Located[] = [];
    let cursor = input.home.telescope, path: Path = [...sourcePath, 'home', 'telescope'];
    while (fields(cursor)[0] !== 'nil') {
      entries.push({ raw: cursor, path }); cursor = fields(cursor)[1]; path = [...path, 1];
    }
    let env: Environment = [], root: StatementNode | undefined, previous: StatementNode | undefined;
    const contextNodeIds: string[] = [];
    entries.reverse();
    const rawName = (entry: Located) => { const f = fields(entry.raw); return f[0] === 'letE' ? f[2] : (f[2] as JsonObject).name; };
    // Recorded kinds apply only when the leading entries carry exactly the recorded names, in order; the names check
    // this alignment and never choose a label. Without it no entry can be matched to its record, so every entry
    // reads as a neutral context entry.
    const aligned = !recorded || recorded.length <= entries.length && recorded.every((record, index) => same(rawName(entries[index]!), record.name));
    const kind = (index: number) => aligned ? recorded?.[index]?.kind : undefined;
    const neutral = (index: number) => !aligned || kind(index) === 'auxDecl' || kind(index) === 'implDetail';
    // Reserve ordinary names first so a recorded neutral entry cannot give a
    // later ordinary variable a duplicate suffix. Names never determine kinds.
    const names: string[] = [], usedNames = new Set<string>();
    for (const wantNeutral of [false, true]) entries.forEach((entry, index) => {
      if (neutral(index) !== wantNeutral) return;
      const baseName = recordedName(rawName(entry), 'context entry');
      let name = baseName, suffix = 1;
      while (usedNames.has(name)) name = `${baseName}@${++suffix}`;
      usedNames.add(name); names[index] = name;
    });
    for (const [index, entry] of entries.entries()) {
      this.visit(0);
      const f = fields(entry.raw), isLet = f[0] === 'letE';
      const attrs = isLet ? undefined : f[2] as JsonObject;
      const typeIndex = isLet ? 4 : 3;
      const binder = this.bind(entry.raw, entry.path, isLet ? f[2] : attrs!.name,
        { raw: f[typeIndex], path: [...entry.path, typeIndex] }, env, neutral(index) ? 'auxiliary' : isLet ? 'definition' : 'parameter', 0,
        isLet ? { raw: f[5], path: [...entry.path, 5], nondep: f[3] as boolean } : undefined, names[index]);
      const recordedKind = kind(index);
      if (recordedKind === 'auxDecl' || recordedKind === 'implDetail') binder.declarationKind = recordedKind;
      const id = this.id('node', entry.path), scopeId = `scope:${id}`;
      const objectId = this.introduce(binder, entry.raw, entry.path, env, id);
      const label = neutral(index) ? contextEntryTitle(binder) : `${isLet ? 'Context definition' : 'Context parameter'} ${binder.name}`;
      const lean = `${binder.name} : ${binder.type}${isLet ? ` := ${this.text(f[5], env)}` : ''}`;
      const node: StatementNode = {
        id, kind: neutral(index) ? 'auxiliary' : isLet ? 'definition' : 'parameter', label, lean, binder, children: [],
        // This is the introduced presentation object, not an invented Lean Expr
        // constructor. Its exact source association is the actual CTel entry.
        expression: this.objects.get(objectId)!.expression, scope: env.map(b => b.id).reverse(),
      };
      this.statementPaths.set(pathKey(entry.path), node);
      this.source(id, entry.raw, entry.path, env); this.source(scopeId, entry.raw, entry.path, env);
      this.scopes.push({ id: scopeId, parentId: previous ? `scope:${previous.id}` : undefined,
        nodeId: id, kind: node.kind, label, objectIds: [...env.map(b => this.id('bound-object', [b.id])).reverse(), objectId],
        assumptionNodeIds: [], context: [] });
      if (previous) previous.children.push(node); else root = node;
      previous = node; contextNodeIds.push(id); env = [binder, ...env];
    }
    const target = this.tree(this.capture.raw, this.capture.path, env, previous ? `scope:${previous.id}` : undefined);
    if (previous) previous.children.push(target); else root = target;
    const document = this.finish(root!, env);
    return { document: { ...document, presentation: { kind: 'component', target: this.componentTarget!,
      contextNodeIds, targetNodeId: target.id, ...(this.logicalRoot ? { logicalRootNodeId: target.id } : {}) } }, contextNodeIds, targetNodeId: target.id,
      ...(aligned ? {} : { recordedKindsUnmatched: true as const }) };
  }

  private finish(tree: StatementNode, env: Environment): SemanticDocument {
    // Unsupported constructors inside types and defining values also need an
    // explicit boundary, even though they are not reached by a clause diagram.
    const reported = new Set<string>();
    for (const [key, entry] of this.unresolved) {
      if (this.statementPaths.get(key)?.kind === 'definition') continue;
      const tag = String(fields(entry.raw)[0]);
      if (!reported.has(tag)) {
        this.diagnostics.push(`The ${tag} constructor has an exact-source presentation only where it occurs inside an expression; it is not flattened into additional choices.`);
        reported.add(tag);
      }
      const opaqueId = this.id('opaque', entry.path);
      if (this.opaqueRegions.some(region => region.id === opaqueId)) continue;
      const ancestor = [...entry.path];
      while (ancestor.length && !this.statementPaths.has(pathKey(ancestor))) ancestor.pop();
      const node = this.statementPaths.get(pathKey(ancestor));
      if (!node) continue;
      this.boundary(entry.raw, entry.path, entry.env, node.id, `source.${pathKey(entry.path.slice(ancestor.length))}`,
        `The ${tag} constructor inside this expression is retained in exact source without a diagram or additional binder choices.`);
      const coverageIndex = this.coverage.findIndex(fragment => fragment.nodeId === node.id), prior = this.coverage[coverageIndex];
      const coverage: FragmentCoverage = { nodeId: node.id, status: prior?.relationIds.length ? 'partial' : 'structural',
        relationIds: prior?.relationIds ?? [], sceneIds: [], objectIds: prior?.objectIds ?? [], opaqueRegionIds: [...(prior?.opaqueRegionIds ?? []), opaqueId] };
      if (coverageIndex < 0) this.coverage.push(coverage); else this.coverage[coverageIndex] = coverage;
    }
    if (this.capture.association === 'reading' && !this.supplierObjectId) this.diagnostics.push('The captured reading is available, but its designated supplier could not be associated with an exact record position.');
    return { schemaVersion: SEMANTIC_DOCUMENT_VERSION, prover: 'lean', source: formatExpr(this.capture.raw, env.map(b => b.name), this.profile), tree,
      objects: [...this.objects.values()], relations: this.relations, scopes: this.scopes, choices: this.choices,
      opaqueRegions: this.opaqueRegions, coverage: this.coverage, scenes: [], diagnostics: this.diagnostics };
  }
}

/** A partial guided presentation of one exact positional component. The complete
 * structural model validates and independently reconstructs the entire input;
 * this semantic presentation does not claim its own complete readback or typing. */
export function compilePositionalComponent(input: PositionalStructuralInput, options: PositionalComponentOptions): PositionalComponentReading {
  let target: 'term' | 'type' = 'term';
  const unavailable = (reason: string): PositionalComponentReading =>
    ({ target, sourceById: Object.create(null), contextNodeIds: [], reason });
  try {
    if (!options || typeof options !== 'object' || Array.isArray(options)
      || ![Object.prototype, null].includes(Object.getPrototypeOf(options))) throw new PacketSyntaxError('invalid positional presentation options');
    const descriptors = Object.getOwnPropertyDescriptors(options);
    if (Reflect.ownKeys(options).some(key => typeof key !== 'string' || !['sourceIdentity', 'sourcePath', 'sourceOrigin', 'target', 'logicalRoot', 'recordedContext'].includes(key))
      || Object.values(descriptors).some(d => !d.enumerable || !Object.hasOwn(d, 'value')))
      throw new PacketSyntaxError('unknown, hidden or accessor presentation option');
    const requested = descriptors.target?.value;
    if (requested !== 'term' && requested !== 'type') throw new PacketSyntaxError('the presentation target must be term or type');
    target = requested;
    const sourceIdentity = descriptors.sourceIdentity?.value;
    if (typeof sourceIdentity !== 'string') throw new PacketSyntaxError('the presentation source identity must be a string');
    const sourceOriginOption = descriptors.sourceOrigin?.value;
    const sourceOrigin = sourceOriginOption === undefined ? 'selected-occurrence' : sourceOriginOption;
    if (sourceOrigin !== 'selected-occurrence' && sourceOrigin !== 'definition-head-exposure' && sourceOrigin !== 'decomposition-result') throw new PacketSyntaxError('invalid positional presentation provenance');
    const sourcePathOption = descriptors.sourcePath?.value;
    const built = buildPositionalStructuralDrawing(input, { sourceIdentity,
      sourcePath: sourcePathOption === undefined ? ['checking', 'selected'] : sourcePathOption });
    if (!built.ok) return unavailable(`${built.error.code}: ${built.error.message}`);
    const readback = readPositionalStructuralDrawing(built.value);
    if (!readback.ok) return unavailable(`${readback.error.code}: ${readback.error.message}`);
    if (!same(input as unknown as JsonValue, readback.value as unknown as JsonValue))
      return unavailable('The structural drawing did not reconstruct the exact selected context, term and type.');
    const sourceById: Record<string, PacketSource> = Object.create(null);
    const sourcePath = built.value.sourcePath, capture = { raw: readback.value[target], path: [...sourcePath, target] };
    const logicalRoot = descriptors.logicalRoot?.value as PositionalLogicalRoot | undefined;
    if (logicalRoot !== undefined) {
      if (target !== 'term' || !logicalRoot || typeof logicalRoot !== 'object' || Array.isArray(logicalRoot)
        || ![Object.prototype, null].includes(Object.getPrototypeOf(logicalRoot))
        || Reflect.ownKeys(logicalRoot).some(key => typeof key !== 'string' || !['form', 'proofBinder', 'bodyUsesBinder'].includes(key))
        || Object.values(Object.getOwnPropertyDescriptors(logicalRoot)).some(d => !d.enumerable || !Object.hasOwn(d, 'value')))
        throw new PacketSyntaxError('invalid logical root presentation');
      if (!['forall', 'implies', 'eq', 'and', 'or', 'iff', 'not', 'exists', 'true', 'false', 'unexpanded'].includes(logicalRoot.form)
        || logicalRoot.proofBinder !== undefined && typeof logicalRoot.proofBinder !== 'boolean'
        || logicalRoot.bodyUsesBinder !== undefined && typeof logicalRoot.bodyUsesBinder !== 'boolean')
        throw new PacketSyntaxError('invalid logical root form');
      const raw = fields(capture.raw), builtins = { eq: ['Eq', 3], and: ['And', 2], or: ['Or', 2], iff: ['Iff', 2], not: ['Not', 1], exists: ['Exists', 2], true: ['True', 0], false: ['False', 0] } as const;
      if (logicalRoot.form === 'forall' || logicalRoot.form === 'implies') {
        if (raw[0] !== 'forallE' || logicalRoot.form === 'implies' && (!logicalRoot.proofBinder || logicalRoot.bodyUsesBinder !== false || ambientReferences(raw[3], 2).has(0)))
          throw new PacketSyntaxError('logical binder does not match its exact source');
      } else if (logicalRoot.form !== 'unexpanded') {
        const [name, count] = builtins[logicalRoot.form];
        if (!builtIn(capture.raw, name, count, capture.path)) throw new PacketSyntaxError('logical form does not match its exact source');
      }
    }
    const recorded = descriptors.recordedContext?.value;
    if (recorded !== undefined && !recordedContextShape(recorded)) throw new PacketSyntaxError('invalid recorded context declarations');
    const compiler = new RecordCompiler(`component:${built.value.sourceIdentity}`, capture, sourceById, 2, undefined, target, sourceOrigin, logicalRoot);
    return { target, sourceById, ...compiler.compilePositional(readback.value, sourcePath, recorded?.map(entry => ({ name: entry.name, kind: entry.kind }))) };
  } catch (error) {
    return unavailable(`The selected ${target} cannot be presented: ${error instanceof Error ? error.message : String(error)}.`);
  }
}

/** Each call owns its binders and supplier, even when operation labels or all
 * printed local names happen to be equal. Evidence remains an imported receipt. */
export function compilePacketRecord(packet: ImportedPacket, operationIndex: number, role: RecordRole): PacketRecordReading {
  const sourceById: Record<string, PacketSource> = Object.create(null);
  const unavailable = (record: JsonValue, checks: readonly CheckReceipt[], reason: string): PacketRecordReading =>
    ({ profile: packet.payload.schema, record, checks, reason, sourceById, source: { label: 'Exact source unavailable', association: 'unavailable' } });
  if (!Number.isSafeInteger(operationIndex) || operationIndex < 0 || operationIndex >= packet.payload.results.length || !['retained', 'derived'].includes(role))
    return unavailable(null, [], 'The requested operation or record role is unavailable.');
  const result = packet.payload.results[operationIndex], record = result.records[role];
  const checks = packet.payload.checks.filter(check => check.pair === result.id);
  const recordPath: Path = ['payload', 'results', operationIndex, 'records', role];
  const base = `packet:${packet.identity}:operation:${operationIndex}:${role}`;
  sourceById[`${base}:record`] = { syntax: record, path: recordPath, scopeBinderIds: [] };
  if (!isObject(record)) return unavailable(record, checks, 'This operation has no retained or derived record for the selected role. Its report and captured checks remain available.');
  const reasons: string[] = [];
  for (const association of ['reading', 'source'] as const) {
    const matches = captures(packet, result.id, role, association);
    if (matches.length !== 1) { reasons.push(`The ${association} capture has ${matches.length ? 'an ambiguous association' : 'no unique matching declaration'}.`); continue; }
    const capture = matches[0], captureBase = `${base}:check:${capture.check.id}`;
    sourceById[`${captureBase}:capture`] = { syntax: capture.raw, path: capture.path, scopeBinderIds: [] };
    try {
      const supplier = association === 'reading' ? supplierPath(record, capture.raw, capture.path, packet.payload.schema) : undefined;
      const compiler = new RecordCompiler(captureBase, capture, sourceById, packet.payload.schema, supplier), document = compiler.compile();
      return { profile: packet.payload.schema, document, record, checks, sourceById, supplierObjectId: compiler.supplierObjectId,
        reason: association === 'source' ? `${reasons.join(' ')} Showing the exact captured source statement; the chosen reading and supplier association are unavailable.` : undefined,
        source: { checkId: capture.check.id, label: capture.check.label, outcome: capture.check.outcome.tag, association } };
    } catch (error) {
      reasons.push(`The ${association} capture cannot be diagrammed: ${error instanceof Error ? error.message : String(error)}.`);
    }
  }
  return unavailable(record, checks, `${reasons.join(' ')} Exact packet syntax is retained for inspection.`);
}
