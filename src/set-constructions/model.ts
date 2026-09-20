import type { Expr } from '../core/types';
import { headName } from '../core/expression';
import type { SemanticDocument, SemanticObject, SemanticRelation, SetOperation } from '../semantic/types';

export interface SetTerm {
  readonly objectId: string;
  readonly kind: 'atom' | 'operation' | 'image' | 'preimage';
  readonly object: SemanticObject;
  readonly operation?: SetOperation;
  readonly children: readonly SetTerm[];
  readonly functionObjectId?: string;
  readonly relationId?: string;
  /** An unexpanded expression remains an atom, never an approximated construction. */
  readonly collapsed?: boolean;
}
export interface SetMembershipRegion {
  readonly bits: readonly boolean[];
  readonly highlighted: boolean;
}
export interface SetConstructionModel {
  readonly relation: SemanticRelation;
  readonly mode: 'result' | 'allowed-membership' | 'required-empty' | 'required-witness';
  readonly left: SetTerm;
  readonly right?: SetTerm;
  readonly element?: SemanticObject;
  readonly atoms: readonly SemanticObject[];
  readonly steps: readonly SetTerm[];
  readonly regions?: readonly SetMembershipRegion[];
  readonly ambientType?: string;
  readonly ambientExpression?: Expr;
  readonly collapsed: boolean;
}
const port = (relation: SemanticRelation, role: string) => relation.ports.find(p => p.role === role)?.objectId;

/** Boolean membership only: map images are independent set atoms in their own
 * codomain. No element, inhabitedness, or numerical coordinates are supplied. */
export function evaluateSetMembership(term: SetTerm, memberships: ReadonlyMap<string, boolean>): boolean {
  const evaluated = new Map<string, boolean>();
  const visit = (current: SetTerm): boolean => {
    if (evaluated.has(current.objectId)) return evaluated.get(current.objectId)!;
    if (current.kind !== 'operation') {
      if (!memberships.has(current.objectId)) throw new Error(`Missing symbolic membership assignment for ${current.objectId}`);
      return memberships.get(current.objectId)!;
    }
    const first = visit(current.children[0]);
    const second = current.children[1] && visit(current.children[1]);
    const result = current.operation === 'complement' ? !first : current.operation === 'union' ? first || second! : current.operation === 'intersection' ? first && second! : first && !second;
    evaluated.set(current.objectId, result);
    return result;
  };
  return visit(term);
}

/** Compile only exact same-clause, same-scope producers. Passing another scope's
 * relations cannot capture local lambda/quantifier objects into the outer set. */
export function compileSetConstruction(document: SemanticDocument, relation: SemanticRelation, relations: readonly SemanticRelation[] = document.relations): SetConstructionModel | undefined {
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const producers = new Map<string, SemanticRelation>();
  for (const candidate of relations) {
    if (candidate.scopeId !== relation.scopeId || candidate.nodeId !== relation.nodeId || !['set-construction', 'image', 'preimage'].includes(candidate.kind)) continue;
    const result = port(candidate, 'result');
    if (result) producers.set(result, candidate);
  }
  const completed = new Map<string, SetTerm>();
  let visits = 0;
  const build = (id: string, depth = 0, seen: ReadonlySet<string> = new Set()): SetTerm | undefined => {
    if (completed.has(id)) return completed.get(id);
    const object = objects.get(id);
    if (!object) return;
    const producer = producers.get(id);
    const atom: SetTerm = { kind: 'atom', objectId: id, object, children: [] };
    if (!producer) return atom;
    if (depth >= 18 || ++visits > 80 || seen.has(id)) { const collapsed = { ...atom, collapsed: true }; completed.set(id, collapsed); return collapsed; }
    const nextSeen = new Set([...seen, id]);
    const operandIds = producer.kind === 'set-construction' ? producer.ports.filter(p => p.role.startsWith('operand ')).map(p => p.objectId) : [port(producer, 'set')].filter((value): value is string => !!value);
    const children = operandIds.flatMap(child => { const built = build(child, depth + 1, nextSeen); return built ? [built] : []; });
    const arity = producer.kind === 'set-construction' && producer.setOperation !== 'complement' ? 2 : 1;
    if (children.length !== arity || producer.kind === 'set-construction' && !producer.setOperation) return { ...atom, collapsed: true };
    const term: SetTerm = { kind: producer.kind === 'set-construction' ? 'operation' : producer.kind as 'image' | 'preimage', objectId: id, object, children, ...(producer.setOperation ? { operation: producer.setOperation } : {}), ...(port(producer, 'function') ? { functionObjectId: port(producer, 'function') } : {}), relationId: producer.id };
    completed.set(id, term);
    return term;
  };
  let mode: SetConstructionModel['mode'], leftId: string | undefined, rightId: string | undefined, element: SemanticObject | undefined;
  if (relation.kind === 'membership') { mode = 'allowed-membership'; leftId = port(relation, 'set'); element = objects.get(port(relation, 'element') ?? ''); }
  else if (relation.kind === 'subset') { mode = 'required-empty'; leftId = port(relation, 'subset'); rightId = port(relation, 'superset'); }
  else if (relation.kind === 'equality') { mode = relation.label === '≠' ? 'required-witness' : 'required-empty'; leftId = port(relation, 'left'); rightId = port(relation, 'right'); }
  else if (['set-construction', 'image', 'preimage'].includes(relation.kind)) { mode = 'result'; leftId = port(relation, 'result'); }
  else return;
  if (!leftId) return;
  const left = build(leftId), right = rightId ? build(rightId) : undefined;
  if (!left || rightId && !right || relation.kind === 'membership' && !element) return;
  const steps: SetTerm[] = [], stepIds = new Set<string>();
  let collapsed = false;
  const collectSteps = (term: SetTerm) => { if (stepIds.has(term.objectId)) return; stepIds.add(term.objectId); collapsed ||= !!term.collapsed; term.children.forEach(collectSteps); if (term.kind !== 'atom') steps.push(term); };
  collectSteps(left); if (right) collectSteps(right);
  if (!steps.length) return;
  const atoms: SemanticObject[] = [], atomIds = new Set<string>();
  const collectAtoms = (term: SetTerm) => { if (atomIds.has(term.objectId)) return; atomIds.add(term.objectId); if (term.kind === 'operation') term.children.forEach(collectAtoms); else atoms.push(term.object); };
  collectAtoms(left); if (right) collectAtoms(right);
  const regions = atoms.length <= 3 ? Array.from({ length: 2 ** atoms.length }, (_, index): SetMembershipRegion => {
    const bits = atoms.map((_, bit) => Boolean(index & 1 << bit));
    const memberships = new Map(atoms.map((atom, bit) => [atom.id, bits[bit]]));
    const a = evaluateSetMembership(left, memberships), b = right && evaluateSetMembership(right, memberships);
    return { bits, highlighted: right ? relation.kind === 'subset' ? a && !b : a !== b : a };
  }) : undefined;
  const descriptor = 'typeDescriptor' in left.object.expression ? left.object.expression.typeDescriptor : left.object.binder?.typeDescriptor;
  const expression = left.object.expression;
  const typeArg = expression.kind === 'app' ? expression.args.find((_, index) => expression.argumentKinds?.[index] === 'type') : undefined;
  const directHead = headName(expression);
  const ambientExpression = typeArg?.kind === 'app' && headName(typeArg) === 'Set' ? typeArg.args[0] : ['Set.union', 'Set.inter', 'Set.diff', 'Set.compl', 'Set.preimage'].includes(directHead ?? '') ? typeArg : directHead === 'Set.image' && expression.kind === 'app' ? expression.args.filter((_, index) => expression.argumentKinds?.[index] === 'type')[1] : undefined;
  return { relation, mode, left, ...(right ? { right } : {}), ...(element ? { element } : {}), atoms, steps, ...(regions ? { regions } : {}), ...(descriptor?.kind === 'set' ? { ambientType: descriptor.element?.lean } : {}), ...(ambientExpression ? { ambientExpression } : {}), collapsed };
}
