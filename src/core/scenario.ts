import type { Binder, Scenario, ScenarioValue, StatementNode } from './types';
import { MAX_NUMERICAL_DIMENSION } from './limits';

export function collectBinders(tree: StatementNode): Binder[] {
  const binders: Binder[] = [];
  const seen = new Set<string>();
  const visit = (node: StatementNode, depth: number): void => {
    if (depth > 128) return;
    if (node.binder && !seen.has(node.binder.id)) { seen.add(node.binder.id); binders.push(node.binder); }
    node.children.forEach(child => visit(child, depth + 1));
  };
  visit(tree, 0);
  return binders;
}

function defaultValue(binder: Binder): ScenarioValue | undefined {
  if (binder.role === 'assumption' || binder.domain === 'realFunction') return undefined;
  if (binder.domain === 'real') return /^(ε|ϵ|epsilon|eps|δ|delta|r|radius)$/i.test(binder.name) ? 1 : 0;
  if (binder.domain === 'sup2' || binder.domain === 'euclidean2' || binder.domain === 'supN' || binder.domain === 'euclideanN') {
    const dimension = binder.dimension ?? (binder.domain.endsWith('2') ? 2 : undefined);
    if (dimension && Number.isSafeInteger(dimension) && dimension >= 1 && dimension <= MAX_NUMERICAL_DIMENSION) return Array.from({ length: dimension }, () => 0);
  }
  return undefined;
}

export function initialScenario(tree: StatementNode): Scenario {
  return Object.fromEntries(collectBinders(tree).flatMap(binder => {
    const value = defaultValue(binder);
    return value === undefined ? [] : [[binder.id, value]];
  }));
}

/** A witness introduced before a changed universal remains fixed. Later dependent choices reset. */
export function updateScenario(tree: StatementNode, state: Scenario, binderId: string, value: ScenarioValue): Scenario {
  const binders = collectBinders(tree);
  const binder = binders.find(b => b.id === binderId);
  const expected = binder && defaultValue(binder);
  if (expected === undefined) return state;
  if (typeof expected === 'number' ? typeof value !== 'number' || !Number.isFinite(value) : !Array.isArray(value) || value.length !== expected.length || !value.every(Number.isFinite)) return state;
  const previous = state[binderId];
  if (typeof value === 'number' ? previous === value : Array.isArray(previous) && previous.length === value.length && previous.every((v, i) => v === value[i])) return state;
  const next: Scenario = { ...state, [binderId]: Array.isArray(value) ? [...value] : value };
  const invalidated = new Set([binderId]);
  for (const candidate of binders) {
    if (candidate.id === binderId || !candidate.dependsOn.some(id => invalidated.has(id))) continue;
    invalidated.add(candidate.id);
    const replacement = defaultValue(candidate);
    if (replacement === undefined || candidate.role === 'existential') delete next[candidate.id];
    else next[candidate.id] = replacement;
  }
  return next;
}

export function quantifierExplanation(binder: Binder, binders: Binder[]): string {
  const names = binder.dependsOn.map(id => binders.find(b => b.id === id)?.name).filter(Boolean);
  if (binder.role === 'assumption') return 'An assumption in this branch, not an independently chosen point.';
  if (binder.role === 'existential') return names.length
    ? `Choose a candidate ${binder.name} after ${names.join(', ')}. It may depend on these earlier choices, but not on later variables.`
    : `Choose a candidate ${binder.name} before the later variables. It stays fixed when those variables change.`;
  if (binder.role === 'lambda') return `Input ${binder.name} to the displayed function.`;
  if (binder.role === 'parameter') return `Parameter ${binder.name} of this definition; its signature is not a quantified proposition.`;
  return `Move one representative ${binder.name}. The quantifier concerns every value in its domain; samples are not a proof.`;
}
