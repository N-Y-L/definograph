/** Exact, bounded decoding of contextual DAG occurrences into Lean Expr data.
 * References use their row's earlier prefix. No reduction or type inference is performed.
 */
import type { JsonObject, JsonValue } from './packet';
import { boundedNatural, encodeNatural, naturalText, NaturalError, type ExactNatural, type NaturalProfile } from './natural';

export type RawExpr = JsonValue;
export type RawName = JsonValue;
export interface OwnerBinding {
  name: RawName;
  info: string;
  type: RawExpr;
  value?: RawExpr;
  nondep?: boolean;
}

export class PacketSyntaxError extends Error {
  constructor(message: string) { super(message); this.name = 'PacketSyntaxError'; }
}

// Each operation either returns its full result or reports its resource boundary.
const MAX_NODES = 250_000;
const MAX_DEPTH = 256;
const MAX_CHARS = 2_000_000;
const RESERVED = new Set(['Sort', 'Type', 'Prop', 'fun', 'forall', 'let', 'in', 'if', 'then',
  'else', 'match', 'with', 'do', 'by', 'where', 'have', 'show', 'from', 'return']);
const BINDER_INFO = ['default', 'implicit', 'strictImplicit', 'instImplicit'];

function requireSyntax(condition: unknown, message: string): asserts condition {
  if (!condition) throw new PacketSyntaxError(message);
}
class Budget {
  private remaining = MAX_NODES;
  private copiedChars = 0;
  constructor(readonly profile?: NaturalProfile) {
    requireSyntax(profile === undefined || profile === 1 || profile === 2, 'unsupported natural profile');
  }
  visit(depth: number): void {
    requireSyntax(--this.remaining >= 0 && depth <= MAX_DEPTH, 'syntax exceeds the node or depth limit');
  }
  text(value: string): string {
    requireSyntax(value.length <= MAX_CHARS, 'syntax exceeds the text limit');
    return value;
  }
  copiedText(value: string): string {
    this.copiedChars += value.length;
    requireSyntax(this.copiedChars <= MAX_CHARS, 'expanded syntax exceeds the text limit');
    return this.text(value);
  }
}
function seq(value: JsonValue, length?: number): JsonValue[] {
  requireSyntax(Array.isArray(value) && (length === undefined || value.length === length), 'invalid constructor shape');
  return value;
}
function object(value: JsonValue, keys: string[]): JsonObject {
  requireSyntax(value !== null && typeof value === 'object' && !Array.isArray(value), 'invalid constructor attributes');
  requireSyntax(Object.keys(value).length === keys.length && keys.every(key => Object.hasOwn(value, key)), 'invalid constructor fields');
  return value;
}
function natural(value: JsonValue): number {
  requireSyntax(typeof value === 'number' && Number.isSafeInteger(value) && value >= 0, 'expected a safe natural number');
  return value;
}
function exactNatural<T>(action: () => T): T {
  try { return action(); }
  catch (error) {
    if (error instanceof NaturalError) throw new PacketSyntaxError(error.message);
    throw error;
  }
}
function semanticNatural(value: JsonValue, budget: Budget): string {
  return budget.text(exactNatural(() => naturalText(value, budget.profile)));
}
function boundIndex(value: JsonValue, profile: NaturalProfile, arity: number): number {
  return exactNatural(() => boundedNatural(value, profile, arity));
}
function encodedIndex(value: number, profile: NaturalProfile): ExactNatural {
  return exactNatural(() => encodeNatural(value, profile));
}
function flag(value: JsonValue): boolean {
  requireSyntax(typeof value === 'boolean', 'expected a Boolean flag');
  return value;
}
function info(value: JsonValue): string {
  requireSyntax(typeof value === 'string' && BINDER_INFO.includes(value), 'unsupported binder annotation');
  return value;
}
function copy(value: JsonValue, budget: Budget, depth = 0, output = true): JsonValue {
  budget.visit(depth);
  if (Array.isArray(value)) return value.map(item => copy(item, budget, depth + 1, output));
  if (value !== null && typeof value === 'object') {
    const result: JsonObject = Object.create(null);
    for (const [key, item] of Object.entries(value)) {
      result[output ? budget.copiedText(key) : budget.text(key)] = copy(item, budget, depth + 1, output);
    }
    return result;
  }
  if (typeof value === 'string') return output ? budget.copiedText(value) : budget.text(value);
  requireSyntax(value === null || typeof value === 'boolean' ||
    (typeof value === 'number' && Number.isSafeInteger(value)), 'non-JSON syntax value');
  return value;
}
function name(value: JsonValue, budget: Budget, depth = 0): string {
  budget.visit(depth);
  const fields = seq(value);
  if (fields.length === 1 && fields[0] === 'anonymous') return '<anonymous>';
  seq(fields, 3);
  const [tag, parent, component] = fields;
  requireSyntax(tag === 'str' || tag === 'num', 'unsupported Name constructor');
  const prefix = name(parent, budget, depth + 1);
  let part: string;
  if (tag === 'num') part = '#' + semanticNatural(component, budget);
  else {
    requireSyntax(typeof component === 'string', 'invalid string Name component');
    const identifier = component.replace(/'+$/u, '');
    part = /^[_\p{ID_Start}][_\p{ID_Continue}]*$/u.test(identifier) && !RESERVED.has(component)
      ? component
      : '«' + JSON.stringify(component).slice(1, -1).replaceAll('«', '\\u00ab').replaceAll('»', '\\u00bb') + '»';
  }
  return budget.text(prefix === '<anonymous>' ? part : prefix + '.' + part);
}
function level(value: JsonValue, budget: Budget, depth = 0): string {
  budget.visit(depth);
  const fields = seq(value);
  switch (fields[0]) {
    case 'zero': seq(fields, 1); return '0';
    case 'succ': seq(fields, 2); return budget.text('succ(' + level(fields[1], budget, depth + 1) + ')');
    case 'max': case 'imax':
      seq(fields, 3);
      return budget.text(fields[0] + '(' + level(fields[1], budget, depth + 1) + ', ' + level(fields[2], budget, depth + 1) + ')');
    case 'param': case 'mvar':
      seq(fields, 2); return budget.text(fields[0] + '(' + name(fields[1], budget, depth + 1) + ')');
    default: throw new PacketSyntaxError('unsupported universe constructor');
  }
}
function literal(value: JsonValue, budget: Budget): string {
  const [tag, body] = seq(value, 2);
  if (tag === 'natVal') return semanticNatural(body, budget);
  requireSyntax(tag === 'strVal' && typeof body === 'string', 'unsupported literal constructor');
  return budget.text(JSON.stringify(body));
}
function attrs(value: JsonValue, budget: Budget): { name: RawName; info: string } {
  const fields = object(value, ['name', 'info']);
  name(fields.name, budget);
  return { name: fields.name, info: info(fields.info) };
}

export function nameText(value: RawName): string { return name(value, new Budget()); }
export function levelText(value: JsonValue): string { return level(value, new Budget()); }

function validate(value: RawExpr, arity: number, budget: Budget, depth = 0): void {
  budget.visit(depth);
  const fields = seq(value);
  switch (fields[0]) {
    case 'bvar':
      seq(fields, 2); boundIndex(fields[1], budget.profile!, arity); return;
    case 'fvar': case 'mvar': seq(fields, 2); name(fields[1], budget, depth + 1); return;
    case 'sort': seq(fields, 2); level(fields[1], budget, depth + 1); return;
    case 'const':
      seq(fields, 3); name(fields[1], budget, depth + 1);
      for (const item of seq(fields[2])) level(item, budget, depth + 1);
      return;
    case 'lit': seq(fields, 2); literal(fields[1], budget); return;
    case 'app':
      seq(fields, 3); validate(fields[1], arity, budget, depth + 1); validate(fields[2], arity, budget, depth + 1); return;
    case 'lam': case 'forallE':
      seq(fields, 5); name(fields[1], budget, depth + 1); info(fields[4]);
      validate(fields[2], arity, budget, depth + 1); validate(fields[3], arity + 1, budget, depth + 1); return;
    case 'letE':
      seq(fields, 6); name(fields[1], budget, depth + 1); flag(fields[5]);
      validate(fields[2], arity, budget, depth + 1); validate(fields[3], arity, budget, depth + 1);
      validate(fields[4], arity + 1, budget, depth + 1); return;
    case 'proj':
      seq(fields, 4); name(fields[1], budget, depth + 1); semanticNatural(fields[2], budget);
      validate(fields[3], arity, budget, depth + 1); return;
    default: throw new PacketSyntaxError('unsupported expression constructor: ' + (typeof fields[0] === 'string' ? fields[0] : '<invalid>'));
  }
}
export function validateExpr(value: RawExpr, arity = 0, profile: NaturalProfile = 1): void {
  validate(value, natural(arity), new Budget(profile));
}

/** Environments contain distinct labels in newest-binder-first order. Text is never an identity key. */
export function formatExpr(value: RawExpr, env: string[] = [], profile: NaturalProfile = 1): string {
  requireSyntax(Array.isArray(env) && env.every(item => typeof item === 'string') && new Set(env).size === env.length,
    'ambient labels must be distinct strings, newest first');
  const budget = new Budget(profile);
  validate(value, env.length, budget);
  const used = new Set(env);
  function fresh(base: string): string {
    let result = base;
    for (let index = 2; used.has(result); index++) result = base + '@' + index;
    used.add(result); return result;
  }
  function render(expr: RawExpr, context: string[], depth: number): string {
    budget.visit(depth);
    const fields = seq(expr);
    switch (fields[0]) {
      case 'bvar': return budget.text(context[boundIndex(fields[1], profile, context.length)]);
      case 'fvar': case 'mvar': return budget.text(fields[0] + '(' + name(fields[1], budget) + ')');
      case 'sort': return budget.text('(Sort ' + level(fields[1], budget) + ')');
      case 'const': {
        const base = name(fields[1], budget);
        const universes = seq(fields[2]);
        const text = base + (universes.length ? '.{' + universes.map(item => level(item, budget)).join(', ') + '}' : '');
        return budget.text(context.includes(base) || context.includes(text) ? 'global(' + text + ')' : text);
      }
      case 'lit': return literal(fields[1], budget);
      case 'app': {
        const args: RawExpr[] = [];
        let head = fields;
        while (head[0] === 'app') {
          budget.visit(depth); args.push(head[2]); head = seq(head[1]);
        }
        return budget.text('(' + [render(head, context, depth + 1),
          ...args.reverse().map(arg => render(arg, context, depth + 1))].join(' ') + ')');
      }
      case 'lam': case 'forallE': {
        const domain = render(fields[2], context, depth + 1);
        const label = fresh(name(fields[1], budget));
        const delimiters: Record<string, [string, string]> = {
          default: ['(', ')'], implicit: ['{', '}'], strictImplicit: ['⦃', '⦄'], instImplicit: ['[', ']'],
        };
        const [left, right] = delimiters[info(fields[4])];
        const binder = left + label + ' : ' + domain + right;
        const body = render(fields[3], [label, ...context], depth + 1);
        return budget.text(fields[0] === 'lam' ? '(fun ' + binder + ' => ' + body + ')' : '(∀ ' + binder + ', ' + body + ')');
      }
      case 'letE': {
        const typ = render(fields[2], context, depth + 1), val = render(fields[3], context, depth + 1);
        const label = fresh(name(fields[1], budget));
        const body = render(fields[4], [label, ...context], depth + 1);
        return budget.text('(let[nondep=' + flag(fields[5]) + '] ' + label + ' : ' + typ + ' := ' + val + '; ' + body + ')');
      }
      case 'proj': return budget.text('proj[' + name(fields[1], budget) + '#' + semanticNatural(fields[2], budget) + '](' + render(fields[3], context, depth + 1) + ')');
      default: throw new PacketSyntaxError('unsupported expression constructor');
    }
  }
  return render(value, [...env], 0);
}

/** A resolver owns its table and never exposes a cached mutable node. */
export class PacketSyntax {
  private readonly rows: JsonObject[];
  private readonly cache = new Map<number, RawExpr>();
  constructor(table: JsonValue, private readonly profile: NaturalProfile = 1) {
    const budget = new Budget(profile);
    const fields = object(copy(table, budget, 0, false), ['rows', 'homes']);
    this.rows = seq(fields.rows).map(row => object(row, ['home', 'row']));
    const homes = seq(fields.homes);
    requireSyntax(homes.length === this.rows.length, 'table homes disagree with the ordered rows');
    this.rows.forEach((row, index) => {
      const home = natural(row.home);
      requireSyntax(natural(homes[homes.length - 1 - index]) === home, 'table homes disagree with the ordered rows');
    });
  }
  occ(value: JsonValue, arity: number): RawExpr {
    const budget = new Budget(this.profile);
    return copy(this.occurrence(value, this.rows.length, natural(arity), budget, 0), budget);
  }
  args(value: JsonValue, arity: number): RawExpr[] {
    const budget = new Budget(this.profile);
    return this.actuals(value, this.rows.length, natural(arity), budget, 0).map(expr => copy(expr, budget));
  }
  owner(value: JsonValue): OwnerBinding[] {
    const budget = new Budget(this.profile);
    const entries: JsonValue[][] = [];
    let current = value;
    while (true) {
      budget.visit(0);
      const fields = seq(current);
      if (fields.length === 1 && fields[0] === 'nil') break;
      requireSyntax(fields[0] === 'port' || fields[0] === 'letE', 'unsupported owner constructor');
      seq(fields, fields[0] === 'port' ? 4 : 6);
      entries.push(fields); current = fields[1];
    }
    return entries.reverse().map((fields, arity) => {
      const declaration = fields[0] === 'port' ? attrs(fields[2], budget) : { name: fields[2], info: 'default' };
      name(declaration.name, budget);
      const type = fields[0] === 'port' ? fields[3] : fields[4];
      const binding: OwnerBinding = {
        name: copy(declaration.name, budget), info: declaration.info,
        type: copy(this.occurrence(type, this.rows.length, arity, budget, 0), budget),
      };
      if (fields[0] === 'letE') {
        binding.nondep = flag(fields[3]);
        binding.value = copy(this.occurrence(fields[5], this.rows.length, arity, budget, 0), budget);
      }
      return binding;
    });
  }
  private actuals(value: JsonValue, prefix: number, arity: number, budget: Budget, depth: number): RawExpr[] {
    const result: RawExpr[] = [];
    let current = value;
    while (true) {
      budget.visit(depth);
      const fields = seq(current);
      if (fields.length === 1 && fields[0] === 'nil') return result;
      requireSyntax(fields.length === 3 && fields[0] === 'cons', 'invalid actual vector');
      result.push(this.occurrence(fields[1], prefix, arity, budget, depth + 1)); current = fields[2];
    }
  }
  private occurrence(value: JsonValue, prefix: number, arity: number, budget: Budget, depth: number): RawExpr {
    budget.visit(depth);
    const fields = seq(value);
    if (fields[0] === 'var') {
      seq(fields, 2);
      const index = natural(fields[1]);
      requireSyntax(index < arity, 'occurrence variable is outside its ambient scope');
      return ['bvar', encodedIndex(index, this.profile)];
    }
    requireSyntax(fields[0] === 'use', 'unsupported occurrence constructor');
    seq(fields, 4);
    const offset = natural(fields[1]), home = natural(fields[2]);
    requireSyntax(offset < prefix, 'reference is outside its earlier table prefix');
    const rowIndex = prefix - 1 - offset;
    requireSyntax(home === this.rows[rowIndex].home, 'reference home arity does not match its row');
    // Actuals belong to the caller's prefix, even when newer than the called row.
    const actuals = this.actuals(fields[3], prefix, arity, budget, depth + 1);
    requireSyntax(actuals.length === home, 'actual vector length does not match the reference home');
    return this.substitute(this.row(rowIndex, budget, depth + 1), actuals, budget, depth + 1);
  }
  private row(index: number, budget: Budget, depth: number): RawExpr {
    budget.visit(depth);
    const cached = this.cache.get(index);
    if (cached !== undefined) return cached;
    const entry = this.rows[index];
    const value = this.decodeRow(entry.row, natural(entry.home), index, budget, depth + 1);
    this.cache.set(index, value);
    return value;
  }
  private decodeRow(value: JsonValue, arity: number, prefix: number, budget: Budget, depth: number): RawExpr {
    budget.visit(depth);
    const fields = seq(value);
    const child = (expr: JsonValue, scope = arity) => this.occurrence(expr, prefix, scope, budget, depth + 1);
    switch (fields[0]) {
      case 'var': {
        seq(fields, 2); const index = natural(fields[1]);
        requireSyntax(index < arity, 'bound variable is outside its ambient scope'); return ['bvar', encodedIndex(index, this.profile)];
      }
      case 'sort': case 'const': case 'lit':
        validate(fields, arity, budget, depth + 1); return fields;
      case 'app': seq(fields, 3); return ['app', child(fields[1]), child(fields[2])];
      case 'lam': case 'pi': {
        seq(fields, 4); const binder = attrs(fields[1], budget);
        return [fields[0] === 'lam' ? 'lam' : 'forallE', binder.name, child(fields[2]), child(fields[3], arity + 1), binder.info];
      }
      case 'letE':
        seq(fields, 6); name(fields[1], budget); flag(fields[2]);
        return ['letE', fields[1], child(fields[3]), child(fields[4]), child(fields[5], arity + 1), fields[2]];
      case 'proj':
        seq(fields, 4); name(fields[1], budget); semanticNatural(fields[2], budget);
        return ['proj', fields[1], fields[2], child(fields[3])];
      case 'inst': {
        seq(fields, 4); const home = natural(fields[1]);
        const actuals = this.actuals(fields[3], prefix, arity, budget, depth + 1);
        requireSyntax(actuals.length === home, 'instantiation actual vector has the wrong arity');
        return this.substitute(child(fields[2], home), actuals, budget, depth + 1);
      }
      default: throw new PacketSyntaxError('unsupported contextual expression constructor: ' + (typeof fields[0] === 'string' ? fields[0] : '<invalid>'));
    }
  }
  private transform(expr: RawExpr, variable: (index: number, bound: number, depth: number) => RawExpr,
    bound: number, budget: Budget, depth: number): RawExpr {
    budget.visit(depth);
    const fields = seq(expr);
    const child = (value: RawExpr, cutoff = bound) => this.transform(value, variable, cutoff, budget, depth + 1);
    switch (fields[0]) {
      case 'bvar': return variable(boundIndex(fields[1], this.profile, Number.MAX_SAFE_INTEGER), bound, depth);
      case 'fvar': case 'mvar': case 'sort': case 'const': case 'lit': return fields;
      case 'app': return ['app', child(fields[1]), child(fields[2])];
      case 'lam': case 'forallE': return [fields[0], fields[1], child(fields[2]), child(fields[3], bound + 1), fields[4]];
      case 'letE': return ['letE', fields[1], child(fields[2]), child(fields[3]), child(fields[4], bound + 1), fields[5]];
      case 'proj': return ['proj', fields[1], fields[2], child(fields[3])];
      default: throw new PacketSyntaxError('unsupported expression during substitution');
    }
  }
  private substitute(expr: RawExpr, actuals: RawExpr[], budget: Budget, depth: number): RawExpr {
    return this.transform(expr, (index, bound, nesting) => {
      if (index < bound) return ['bvar', encodedIndex(index, this.profile)];
      const slot = index - bound;
      requireSyntax(slot < actuals.length, 'substitution encountered an unbound home variable');
      // Shift only the actual's free variables; its own binders remain unchanged.
      // Inserted actuals are not substituted again: all home variables change simultaneously.
      return this.transform(actuals[slot], (k, cutoff) => ['bvar', encodedIndex(k >= cutoff ? k + bound : k, this.profile)], 0, budget, nesting + 1);
    }, 0, budget, depth);
  }
}
