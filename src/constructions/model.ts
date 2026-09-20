import type { Binder, Expr, StatementNode, TypeDescriptor } from '../core/types';
import { headName } from '../core/expression';
import type { ReadingBinder } from '../reading/types';
import { applicationParts, binderTypeExpression, expressionKey, formatExpression } from '../semantic/expression';
import type { SemanticDocument, SemanticObject } from '../semantic/types';

export interface ConstructionType {
  readonly id: string;
  readonly label: string;
  readonly expression: Expr;
  readonly objectId?: string;
  readonly introduced: boolean;
}
export interface ConstructionObject {
  readonly objectId: string;
  readonly binderId: string;
  readonly name: string;
  readonly type: string;
  readonly role: Binder['role'];
  readonly scopeId: string;
}
export interface ConstructionMap extends ConstructionObject {
  readonly domainId: string;
  readonly codomainId: string;
}
export interface ConstructionMember extends ConstructionObject {
  readonly kind: 'element' | 'set';
  readonly typeId: string;
}
export interface ConstructionInput {
  readonly name: string;
  readonly type: string;
  readonly dependsOn: readonly number[];
}
export interface ConstructionSignature extends ConstructionObject {
  readonly kind: 'dependent-map' | 'multi-input-map' | 'relation' | 'family' | 'symbolic-map';
  readonly inputs: readonly ConstructionInput[];
  readonly result: string;
  readonly resultDependsOn: readonly number[];
  readonly explanation: string;
}
export interface ConstructionUnknown extends ConstructionObject { readonly reason: string }
export interface TypedConstruction {
  readonly status: 'ready' | 'empty' | 'invalid-scope';
  readonly role?: Binder['role'];
  readonly objects: readonly ConstructionObject[];
  readonly types: readonly ConstructionType[];
  readonly maps: readonly ConstructionMap[];
  readonly members: readonly ConstructionMember[];
  readonly signatures: readonly ConstructionSignature[];
  readonly unknowns: readonly ConstructionUnknown[];
  readonly diagnostics: readonly string[];
}

function empty(status: TypedConstruction['status'], reason?: string): TypedConstruction {
  return { status, objects: [], types: [], maps: [], members: [], signatures: [], unknowns: [], diagnostics: reason ? [reason] : [] };
}

function sourceNodes(root: StatementNode): Map<string, StatementNode> {
  const result = new Map<string, StatementNode>();
  const visit = (node: StatementNode) => { if (node.binder) result.set(node.binder.id, node); node.children.forEach(visit); };
  visit(root); return result;
}


function variableIds(expression: Expr, depth = 0): Set<string> {
  if (depth > 80) return new Set();
  if (expression.kind === 'var') return new Set([expression.id]);
  const parts = expression.kind === 'app' ? [expression.fn, ...expression.args] : expression.kind === 'forall' || expression.kind === 'lambda' ? [expression.binderType ?? expression.binder.typeExpression, expression.body].filter((e): e is Expr => !!e) : [];
  return new Set(parts.flatMap(part => [...variableIds(part, depth + 1)]));
}

/** Opaque display text is not a structural identity, even if two labels match. */
function completeIdentity(expression: Expr, depth = 0): boolean {
  if (depth > 80 || expression.kind === 'opaque') return false;
  if (expression.kind === 'app') return completeIdentity(expression.fn, depth + 1) && expression.args.every(arg => completeIdentity(arg, depth + 1));
  if (expression.kind === 'forall' || expression.kind === 'lambda') {
    const type = expression.binderType ?? expression.binder.typeExpression;
    return !!type && completeIdentity(type, depth + 1) && completeIdentity(expression.body, depth + 1);
  }
  return true;
}

const typeLabel = (expression: Expr, descriptor?: TypeDescriptor) => descriptor?.lean || formatExpression(expression);
const isProp = (expression: Expr) => expression.kind === 'sort' && (expression.name === '0' || expression.name === 'Prop');

/** Compile one contiguous introduction group, never combining sibling logical scopes.
 * Labels are for display only: all carrier sharing uses exported expression identities. */
export function compileTypedConstruction(document: SemanticDocument, binders: readonly ReadingBinder[]): TypedConstruction {
  if (!binders.length) return empty('empty');
  const nodes = sourceNodes(document.tree);
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const byBinder = new Map(document.objects.filter(object => object.binder).map(object => [object.binder!.id, object]));
  const scopes = new Map(document.scopes.map(scope => [scope.id, scope]));
  const selected: { reading: ReadingBinder; object: SemanticObject; node: StatementNode }[] = [];
  for (const reading of binders) {
    const object = reading.objectId ? objects.get(reading.objectId) : undefined;
    const node = nodes.get(reading.binderId);
    if (!object?.binder || object.binder.id !== reading.binderId || object.binder.role !== reading.role || !node || node.binder?.id !== reading.binderId || scopes.get(reading.scopeId)?.nodeId !== node.id || object.scopeId !== reading.scopeId) return empty('invalid-scope', 'An introduction has no matching typed source binder.');
    const previous = selected.at(-1);
    if (previous && (previous.reading.role !== reading.role || previous.node.kind !== node.kind || previous.node.children.length !== 1 || previous.node.children[0].id !== node.id)) return empty('invalid-scope', 'Construction groups must remain contiguous and within one quantifier role.');
    selected.push({ reading, object, node });
  }
  const availableIds = new Set(scopes.get(selected.at(-1)!.reading.scopeId)?.objectIds ?? []);
  const selectedIds = new Set(selected.map(entry => entry.object.id));
  const types: ConstructionType[] = [], maps: ConstructionMap[] = [], members: ConstructionMember[] = [], signatures: ConstructionSignature[] = [], unknowns: ConstructionUnknown[] = [];
  const typeKeys = new Map<string, ConstructionType>();
  const addType = (expression: Expr, descriptor?: TypeDescriptor): ConstructionType => {
    const key = completeIdentity(expression) ? expressionKey(expression) : `unresolved:${types.length}`;
    const existing = typeKeys.get(key);
    if (existing) return existing;
    const sourceObject = expression.kind === 'var' ? byBinder.get(expression.id) : undefined;
    const objectId = sourceObject && availableIds.has(sourceObject.id) ? sourceObject.id : undefined;
    const value: ConstructionType = { id: `type:${types.length}`, label: typeLabel(expression, descriptor), expression, objectId, introduced: !!objectId && selectedIds.has(objectId) };
    typeKeys.set(key, value); types.push(value); return value;
  };
  const introducedObjects: ConstructionObject[] = [];
  for (const { reading, object, node } of selected) {
    const binder = object.binder!;
    const base: ConstructionObject = { objectId: object.id, binderId: binder.id, name: binder.name, type: binder.type, role: reading.role, scopeId: reading.scopeId };
    introducedObjects.push(base);
    const type = binderTypeExpression(node, binder);
    const descriptor = binder.typeDescriptor;
    if (!type) { unknowns.push({ ...base, reason: 'The typed expression was not exported; its declared type is retained.' }); continue; }
    if (type.kind === 'sort' && !isProp(type)) {
      addType(object.expression, { kind: 'unknown', lean: binder.name }); continue;
    }
    if (type.kind === 'forall') {
      let current: Expr = type, currentDescriptor = descriptor;
      const inputs: ConstructionInput[] = [], inputExpressions: Expr[] = [], inputDescriptors: (TypeDescriptor | undefined)[] = [], boundIds: string[] = [];
      while (current.kind === 'forall' && inputs.length < 32) {
        const inputType = current.binderType ?? current.binder.typeExpression;
        if (!inputType) break;
        const references = variableIds(inputType);
        inputs.push({ name: current.binder.name, type: typeLabel(inputType, currentDescriptor?.domain), dependsOn: boundIds.flatMap((id, index) => references.has(id) ? [index] : []) });
        inputExpressions.push(inputType); inputDescriptors.push(currentDescriptor?.domain);
        boundIds.push(current.binder.id); current = current.body; currentDescriptor = currentDescriptor?.codomain;
      }
      if (current.kind === 'forall' || !inputs.length) { unknowns.push({ ...base, reason: 'The function type is only partially exported; no endpoint diagram is inferred.' }); continue; }
      const references = variableIds(current);
      const resultDependsOn = boundIds.flatMap((id, index) => references.has(id) ? [index] : []);
      const dependent = resultDependsOn.length > 0 || inputs.some(input => input.dependsOn.length > 0);
      const relation = isProp(current), family = current.kind === 'sort' && !relation;
      if (inputs.length === 1 && !dependent && !relation && !family && completeIdentity(inputExpressions[0]) && completeIdentity(current)) {
        maps.push({ ...base, domainId: addType(inputExpressions[0], inputDescriptors[0]).id, codomainId: addType(current, currentDescriptor).id });
      } else {
        const kind = relation ? 'relation' : family ? 'family' : dependent ? 'dependent-map' : inputs.length > 1 ? 'multi-input-map' : 'symbolic-map';
        signatures.push({ ...base, kind, inputs, result: typeLabel(current, currentDescriptor), resultDependsOn,
          explanation: relation ? 'These inputs determine a proposition; no truth value is asserted here.' : family ? 'Inputs index a type family; no single fixed target type is assumed.' : dependent ? 'Later input types or the result type depend on earlier inputs.' : inputs.length > 1 ? 'Inputs are ordered as in the curried function type; no independent maps between argument types are implied.' : 'The exported type is incomplete; its signature is retained without merging type identities.' });
      }
      continue;
    }
    const { fn, args } = applicationParts(type);
    if (descriptor?.kind === 'set' && headName(fn) === 'Set' && args.length === 1) {
      members.push({ ...base, kind: 'set', typeId: addType(args[0], descriptor.element).id }); continue;
    }
    if (type.kind === 'opaque' || !completeIdentity(type)) {
      unknowns.push({ ...base, reason: 'The type remains symbolic; no type identity or geometric interpretation is inferred.' }); continue;
    }
    members.push({ ...base, kind: 'element', typeId: addType(type, descriptor).id });
  }
  return { status: 'ready', role: binders[0].role, objects: introducedObjects, types, maps, members, signatures, unknowns, diagnostics: [] };
}

/** Numeric coordinates alone add no construction beyond the caller's binder strip. */
export function isUsefulConstruction(model: TypedConstruction): boolean {
  return model.status === 'ready' && (model.maps.length > 0 || model.signatures.length > 0 || model.types.some(type => type.introduced || !!type.objectId) || model.members.some(member => member.kind === 'set'));
}
