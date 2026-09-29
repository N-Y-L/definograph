/** Independent bounded replay of one retained definition-body exposure. This
 * establishes syntax consistency relative to the witness, never its authority. */
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { boundedNatural, encodeNatural, naturalText } from '../packets/natural';
import type { RawPath } from '../packets/raw';
import { sourceSnapshotValidation as shared } from './source-snapshot';
import { sourceOccurrenceValidation } from './source-occurrence';

export interface HeadExposureDefinition {
  name: JsonValue; levelParams: JsonValue[]; type: JsonValue; value: JsonValue;
  hints: JsonValue; safety: 'safe';
}
export interface HeadExposureReplay {
  term: JsonValue; actualLevels: JsonValue[]; arguments: JsonValue[]; betaApplications: number;
}
const { bad, array, object, exact, operational, preflight } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const key = (value: JsonValue) => createExactJsonTools().canonical(value);
const encoder = new TextEncoder();
const MAX_NODES = 20_000, MAX_DEPTH = 96, MAX_TEXT = 128 * 1024;
const sorry: JsonValue = ['str', ['anonymous'], 'sorryAx'];

/** Counts expanded Expr/Level occurrences, including duplicated actuals. Names
 * contribute their exact payload text, but are not Expr/Level constructors. */
class Budget {
  nodes = 0; bytes = 0;
  constructor(readonly path: RawPath) {}
  visit(depth: number): void {
    if (++this.nodes > MAX_NODES || depth > MAX_DEPTH) bad('head exposure expression node or depth limit exceeded', this.path, 'limit');
  }
  text(value: string): string {
    this.bytes += encoder.encode(value).length;
    if (this.bytes > MAX_TEXT) bad('head exposure expression text limit exceeded', this.path, 'limit');
    return value;
  }
  nat(value: JsonValue): JsonValue { return ['nat', this.text(naturalText(value, 2))]; }
  name(value: JsonValue): JsonValue {
    const n = value as JsonValue[];
    if (n[0] === 'anonymous') return ['anonymous'];
    return [n[0], this.name(n[1]), n[0] === 'str' ? this.text(n[2] as string) : this.nat(n[2])];
  }
}
function copyLevel(value: JsonValue, budget: Budget, depth: number, parameters?: Map<string, JsonValue>, allowed?: Set<string>): JsonValue {
  const l = value as JsonValue[];
  if (l[0] === 'param') {
    const id = key(l[1]);
    requireThat(!allowed || allowed.has(id), 'unbound definition universe parameter', budget.path);
    const replacement = parameters?.get(id);
    if (replacement !== undefined) return copyLevel(replacement, budget, depth);
  }
  budget.visit(depth);
  switch (l[0]) {
    case 'zero': return ['zero'];
    case 'succ': return ['succ', copyLevel(l[1], budget, depth + 1, parameters, allowed)];
    case 'max': case 'imax': return [l[0], copyLevel(l[1], budget, depth + 1, parameters, allowed), copyLevel(l[2], budget, depth + 1, parameters, allowed)];
    case 'param': return ['param', budget.name(l[1])];
    default: return bad('unsupported exposure universe constructor', budget.path);
  }
}
type Variable = (index: number, localDepth: number, outputDepth: number) => JsonValue | undefined;
function copyExpr(value: JsonValue, budget: Budget, depth = 0, localDepth = 0,
  variable?: Variable, parameters?: Map<string, JsonValue>, allowed?: Set<string>): JsonValue {
  const e = value as JsonValue[];
  if (e[0] === 'bvar' && variable) {
    const replacement = variable(boundedNatural(e[1], 2, Number.MAX_SAFE_INTEGER), localDepth, depth);
    if (replacement !== undefined) return replacement;
  }
  budget.visit(depth);
  const child = (index: number, binds = false) => copyExpr(e[index], budget, depth + 1, localDepth + Number(binds), variable, parameters, allowed);
  switch (e[0]) {
    case 'bvar': return ['bvar', budget.nat(e[1])];
    case 'sort': return ['sort', copyLevel(e[1], budget, depth + 1, parameters, allowed)];
    case 'const':
      requireThat(key(e[1]) !== key(sorry), 'exposure expression contains a placeholder', budget.path);
      return ['const', budget.name(e[1]), (e[2] as JsonValue[]).map(l => copyLevel(l, budget, depth + 1, parameters, allowed))];
    case 'lit': {
      const literal = e[1] as JsonValue[];
      return ['lit', [literal[0], literal[0] === 'natVal' ? budget.nat(literal[1]) : budget.text(literal[1] as string)]];
    }
    case 'app': return ['app', child(1), child(2)];
    case 'lam': case 'forallE': return [e[0], budget.name(e[1]), child(2), child(3, true), e[4]];
    case 'letE': return ['letE', budget.name(e[1]), child(2), child(3), child(4, true), e[5]];
    case 'proj': return ['proj', budget.name(e[1]), budget.nat(e[2]), child(3)];
    default: return bad('unsupported exposure expression constructor', budget.path);
  }
}

/** Validate finished Core and the exposure's tighter constructor/text policy. */
export function validateHeadExpression(value: JsonValue, arity: number, path: RawPath, parameters?: JsonValue[]): void {
  preflight(value, 1024 * 1024, path, false, 120);
  sourceOccurrenceValidation.core(value, arity, path);
  copyExpr(value, new Budget(path), 0, 0, undefined, undefined, parameters ? new Set(parameters.map(key)) : undefined);
}
export function validateHeadLevel(value: JsonValue, path: RawPath): void {
  preflight(value, 1024 * 1024, path, false, 120);
  sourceOccurrenceValidation.core(['sort', value], 0, path);
  copyLevel(value, new Budget(path), 0);
}

export function replayDefinitionHead(before: JsonValue, definition: HeadExposureDefinition, arity: number,
  path: RawPath = ['checking', 'exposure']): HeadExposureReplay {
  // Public callers may supply hostile JS values. Inspect descriptors before any
  // field access; the record validator has its own separate complete bound.
  preflight({ before, definition, arity }, 1024 * 1024, path, false, 120);
  operational(arity, [...path, 'home', 'arity']);
  const d = object(definition, ['name', 'levelParams', 'type', 'value', 'hints', 'safety'], [...path, 'definition']);
  shared.validName(d.name, [...path, 'definition', 'name']);
  const params = shared.names(d.levelParams, [...path, 'definition', 'levelParams']);
  requireThat(new Set(params.map(key)).size === params.length, 'duplicate definition universe parameter', path);
  requireThat(d.safety === 'safe', 'only safe definition bodies may be exposed', path);
  const hints = array(d.hints, [...path, 'definition', 'hints']);
  requireThat((hints.length === 1 && (hints[0] === 'abbrev' || hints[0] === 'opaque'))
    || (hints.length === 2 && hints[0] === 'regular' && typeof hints[1] === 'number' && Number.isSafeInteger(hints[1]) && hints[1] >= 0 && hints[1] <= 0xffffffff),
  'invalid definition reducibility hints', [...path, 'definition', 'hints']);
  validateHeadExpression(d.type, 0, [...path, 'definition', 'type'], params);
  validateHeadExpression(d.value, 0, [...path, 'definition', 'value'], params);
  validateHeadExpression(before, arity, [...path, 'before']);
  let head = before as JsonValue[];
  const args: JsonValue[] = [];
  while (head[0] === 'app') { args.push(head[2]); head = head[1] as JsonValue[]; }
  args.reverse();
  requireThat(head[0] === 'const', 'exposure requires a constant-headed application spine', [...path, 'before']);
  exact(head[1], d.name, [...path, 'definition', 'name']);
  const levels = head[2] as JsonValue[];
  requireThat(levels.length === params.length, 'actual and formal universe arities differ', path);
  const substitution = new Map(params.map((p, i) => [key(p), levels[i]]));
  const instantiated = copyExpr(d.value, new Budget([...path, 'instantiatedBody']), 0, 0, undefined, substitution, new Set(params.map(key)));
  let body = instantiated as JsonValue[], consumed = 0;
  while (consumed < args.length && body[0] === 'lam') { body = body[3] as JsonValue[]; consumed++; }
  const remaining = args.length - consumed, budget = new Budget([...path, 'result', 'term']);
  // Reserve the outer application spine before copying its nested function.
  for (let i = 0; i < remaining; i++) budget.visit(i);
  const substitute: Variable = (index, localDepth, outputDepth) => {
    if (index < localDepth) return undefined;
    const slot = index - localDepth;
    if (slot < consumed) {
      const actual = args[consumed - slot - 1];
      return copyExpr(actual, budget, outputDepth, 0, (argumentIndex, argumentDepth, argumentOutputDepth) => {
        if (argumentIndex < argumentDepth || localDepth === 0) return undefined;
        budget.visit(argumentOutputDepth);
        return ['bvar', budget.nat(encodeNatural(argumentIndex + localDepth, 2))];
      });
    }
    budget.visit(outputDepth);
    return ['bvar', budget.nat(encodeNatural(index - consumed, 2))];
  };
  let result = copyExpr(body, budget, remaining, 0, substitute);
  for (let i = consumed; i < args.length; i++) {
    const argumentDepth = args.length - i;
    result = ['app', result, copyExpr(args[i], budget, argumentDepth)];
  }
  validateHeadExpression(result, arity, [...path, 'result', 'term']);
  return { term: result, actualLevels: levels, arguments: args, betaApplications: consumed };
}
