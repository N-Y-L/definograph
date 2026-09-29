/** Exact formation/operand associations. A saved descriptor does not authenticate
 * standard-core semantics or the environment that produced it. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import { naturalText } from '../packets/natural';
import type { RawPath } from '../packets/raw';
import type { PositionalStructuralInput } from '../packets/structure';
import { sourceSnapshotValidation as shared, type ClosureItem } from './source-snapshot';
import { validateHeadExpression } from './head-exposure-replay';

export interface LogicalCandidate {
  status: 'candidate'; result: PositionalStructuralInput;
  formation: { inferredType: JsonValue }; domain: null | { term: JsonValue; inferredType: JsonValue };
  shape: JsonObject; checking: { status: 'completed' } | { status: 'error'; reason: string };
};
const { object, array, exact, preflight, close, named, strName, constant } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const key = (value: JsonValue) => createExactJsonTools().canonical(value);
const standard: Record<string, { name: string; module: string; universes: number; roles: string[] }> = {
  eq: { name: 'Eq', module: 'Prelude', universes: 1, roles: ['carrier', 'left', 'right'] },
  and: { name: 'And', module: 'Prelude', universes: 0, roles: ['required-left', 'required-right'] },
  or: { name: 'Or', module: 'Prelude', universes: 0, roles: ['alternative-left', 'alternative-right'] },
  iff: { name: 'Iff', module: 'Core', universes: 0, roles: ['equivalent-left', 'equivalent-right'] },
  not: { name: 'Not', module: 'Prelude', universes: 0, roles: ['negated'] },
  exists: { name: 'Exists', module: 'Core', universes: 1, roles: ['carrier', 'predicate'] },
  true: { name: 'True', module: 'Prelude', universes: 0, roles: [] },
  false: { name: 'False', module: 'Prelude', universes: 0, roles: [] },
};

/** Input has already passed bounded exact expression validation. */
function usesBinder(expression: JsonValue, depth = 0): boolean {
  const e = expression as JsonValue[];
  switch (e[0]) {
    case 'bvar': return naturalText(e[1], 2) === String(depth);
    case 'app': return usesBinder(e[1], depth) || usesBinder(e[2], depth);
    case 'lam': case 'forallE': return usesBinder(e[2], depth) || usesBinder(e[3], depth + 1);
    case 'letE': return usesBinder(e[2], depth) || usesBinder(e[3], depth) || usesBinder(e[4], depth + 1);
    case 'proj': return usesBinder(e[3], depth);
    default: return false;
  }
}

export function validateLogicalCandidate(value: JsonValue, input: PositionalStructuralInput,
  universeParams: JsonValue[], path: RawPath): LogicalCandidate {
  preflight({ value, input, universeParams }, 4 * 1024 * 1024, path, false, 120);
  const out = object(value, ['status', 'result', 'formation', 'domain', 'shape', 'checking'], path);
  requireThat(out.status === 'candidate', 'invalid logical candidate status', path);
  exact(out.result, input, [...path, 'result']);
  const formation = object(out.formation, ['inferredType'], [...path, 'formation']);
  validateHeadExpression(formation.inferredType, input.home.arity, [...path, 'formation', 'inferredType'], universeParams);
  validateHeadExpression(input.term, input.home.arity, [...path, 'input', 'term'], universeParams);
  const term = input.term as JsonValue[];
  const shape = out.shape as JsonObject;
  requireThat(shape !== null && typeof shape === 'object' && !Array.isArray(shape), 'invalid logical shape', [...path, 'shape']);
  if (term[0] === 'forallE') {
    object(shape, ['kind', 'binder', 'bodyUsesBinder', 'operands'], [...path, 'shape']);
    exact(shape, { kind: 'forall', binder: { name: term[1], info: term[4] }, bodyUsesBinder: usesBinder(term[3]),
      operands: [{ role: 'domain', path: ['piDomain'] }, { role: 'body', path: ['piBody'] }] }, [...path, 'shape']);
    const domain = object(out.domain, ['term', 'inferredType'], [...path, 'domain']);
    exact(domain.term, term[2], [...path, 'domain', 'term']);
    validateHeadExpression(domain.inferredType, input.home.arity, [...path, 'domain', 'inferredType'], universeParams);
  } else {
    exact(out.domain, null, [...path, 'domain']);
    if (shape.kind === 'unexpanded') exact(shape, { kind: 'unexpanded', operands: [] }, [...path, 'shape']);
    else {
      object(shape, ['kind', 'form', 'descriptor', 'operands'], [...path, 'shape']);
      requireThat(shape.kind === 'standard' && typeof shape.form === 'string' && Object.hasOwn(standard, shape.form),
        'unsupported logical interpretation', [...path, 'shape']);
      const rule = standard[shape.form as string], args: JsonValue[] = [];
      let head = term;
      while (head[0] === 'app') { args.unshift(head[2]); head = head[1] as JsonValue[]; }
      requireThat(head[0] === 'const' && Array.isArray(head[2]) && head[2].length === rule.universes && args.length === rule.roles.length,
        'logical application has the wrong shape or arity', [...path, 'shape']);
      exact(head[1], named(rule.name), [...path, 'shape', 'form']);
      const d = object(shape.descriptor, ['interpretationId', 'name', 'declaringModule', 'kind', 'levelParams', 'type', 'safety'], [...path, 'shape', 'descriptor']);
      exact(d.interpretationId, 'lean-standard-core-v1', [...path, 'shape', 'descriptor', 'interpretationId']);
      exact(d.name, head[1], [...path, 'shape', 'descriptor', 'name']);
      exact(d.declaringModule, strName(named('Init'), rule.module), [...path, 'shape', 'descriptor', 'declaringModule']);
      exact(d.kind, shape.form === 'not' ? 'defnDecl' : 'inductDecl', [...path, 'shape', 'descriptor', 'kind']);
      exact(d.safety, 'safe', [...path, 'shape', 'descriptor', 'safety']);
      const formal = array(d.levelParams, [...path, 'shape', 'descriptor', 'levelParams']);
      requireThat(formal.length === rule.universes, 'logical declaration universe arity differs', [...path, 'shape', 'descriptor']);
      const seen = new Set<string>();
      formal.forEach((name, i) => {
        validateHeadExpression(['const', name, []], 0, [...path, 'shape', 'descriptor', 'levelParams', i]);
        const identity = key(name);
        requireThat(identity !== '["anonymous"]' && !seen.has(identity), 'invalid formal universe identity', [...path, 'shape', 'descriptor']);
        seen.add(identity);
      });
      validateHeadExpression(d.type, 0, [...path, 'shape', 'descriptor', 'type'], formal);
      exact(shape.operands, rule.roles.map((role, i) => ({ role, path: [...Array(rule.roles.length - 1 - i).fill('appFun'), 'appArg'] })),
        [...path, 'shape', 'operands']);
    }
  }
  return out as unknown as LogicalCandidate;
}

/** Every closure is rebuilt in the actual pre-binder context. */
export function logicalDeclarations(candidate: LogicalCandidate, input: PositionalStructuralInput, items: ClosureItem[],
  prefix: JsonValue, universeParams: JsonValue[], count: number): JsonObject[] {
  return Array.from({ length: count }, (_, i): JsonObject => {
    const component = i % 2 === 1, domain = i >= 2;
    const name = strName(strName(strName(prefix, 'logical'), domain ? 'domain' : 'root'), component ? 'component' : 'context');
    const subject = domain ? candidate.domain!.term : input.term;
    const type = domain ? candidate.domain!.inferredType : candidate.formation.inferredType;
    return { kind: component ? 'defnDecl' : 'thmDecl', name, levelParams: universeParams,
      type: close(items, component ? type : constant('True'), 'forallE'),
      value: close(items, component ? subject : ['const', strName(named('True'), 'intro'), []], 'lam'), all: [name],
      ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
  });
}
