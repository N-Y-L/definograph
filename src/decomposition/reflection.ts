import type { Binder, Expr, ReflectedField, ReflectedStructure } from '../core/types';
import type { SemanticRuleMatch } from '../semantic/types';
import { applicationParts, checkedBinderTypeExpansion, expressionKey, formatExpression } from '../semantic/expression';

export interface FieldBinding { readonly owner: Binder; readonly field: ReflectedField }

const nonemptyString = (value: unknown): value is string => typeof value === 'string' && value.length > 0;
const stringArray = (value: unknown): value is string[] => Array.isArray(value) && value.every(nonemptyString);
const descriptorKinds = new Set(['real', 'natural', 'integer', 'rational', 'finite', 'type', 'set', 'map', 'relation', 'proposition', 'structure', 'unknown']);

/** Count the expression AST only. Binder display metadata, descriptors, and
 * optional views are covered by the envelope limit, not counted as AST copies. */
function boundedFieldExpression(value: unknown): value is Expr {
  let nodes = 0;
  const visit = (candidate: unknown, depth: number): boolean => {
    if (depth > 24 || ++nodes > 120 || !candidate || typeof candidate !== 'object') return false;
    const expression = candidate as Record<string, unknown>;
    switch (expression.kind) {
      case 'const': return nonemptyString(expression.name);
      case 'var': return nonemptyString(expression.id) && typeof expression.name === 'string' && typeof expression.type === 'string';
      case 'literal': return typeof expression.value === 'string' || typeof expression.value === 'number' && Number.isFinite(expression.value);
      case 'sort': return nonemptyString(expression.name);
      // In particular, exported instance arguments may be opaque. Retaining an
      // opaque node grants it no set, map, or geometric interpretation.
      case 'opaque': return typeof expression.text === 'string';
      case 'app': {
        if (!Array.isArray(expression.args) || expression.args.length > 120) return false;
        if (expression.argumentKinds !== undefined && (!Array.isArray(expression.argumentKinds) || expression.argumentKinds.length !== expression.args.length
          || !expression.argumentKinds.every(kind => ['instance', 'proof', 'type', 'value'].includes(kind)))) return false;
        return visit(expression.fn, depth + 1) && expression.args.every(argument => visit(argument, depth + 1));
      }
      case 'forall': case 'lambda': {
        if (!expression.binder || typeof expression.binder !== 'object') return false;
        const binder = expression.binder as Record<string, unknown>;
        if (!nonemptyString(binder.id) || typeof binder.name !== 'string' || typeof binder.type !== 'string') return false;
        const type = expression.binderType ?? binder.typeExpression;
        return visit(type, depth + 1) && visit(expression.body, depth + 1);
      }
      default: return false;
    }
  };
  // Lean's Expr.approxDepth gives leaves depth zero.
  return visit(value, 0);
}

function boundedLawTree(value: unknown): boolean {
  let nodes = 0;
  const visit = (candidate: unknown, depth: number): boolean => {
    if (depth > 24 || ++nodes > 120 || !candidate || typeof candidate !== 'object') return false;
    const node = candidate as Record<string, unknown>;
    return nonemptyString(node.id) && typeof node.label === 'string' && typeof node.lean === 'string'
      && ['forall', 'exists', 'implies', 'and', 'or', 'iff', 'not', 'predicate', 'parameter'].includes(node.kind as string)
      && boundedFieldExpression(node.expression) && Array.isArray(node.children) && node.children.length <= 120 && node.children.every(child => visit(child, depth + 1));
  };
  return visit(value, 0);
}

/** Metadata is an optional typed view. Reject malformed or unbounded envelopes
 * rather than interpreting field names or parsing pretty-printed types. */
export function checkedStructure(binder: Binder): ReflectedStructure | undefined {
  const value = binder.structure;
  if (!value || value.kernelChecked !== true || value.limits?.maxFields !== 16 || value.limits.maxFieldNodes !== 120 || value.limits.maxDepth !== 24
    || !nonemptyString(value.name) || !Array.isArray(value.fields) || value.fields.length > 16 || !Number.isSafeInteger(value.omittedFields) || value.omittedFields < 0
    || value.stopReason !== undefined && typeof value.stopReason !== 'string') return;
  try {
    const encoded = JSON.stringify(value);
    if (typeof encoded !== 'string' || new TextEncoder().encode(encoded).byteLength > 128 * 1024) return;
  } catch { return; }
  if (!boundedFieldExpression(value.typeExpression)) return;
  const names = new Set<string>();
  for (const field of value.fields) {
    if (!field || !nonemptyString(field.name) || !nonemptyString(field.projection) || !nonemptyString(field.type) || names.has(field.projection) || !['data', 'law'].includes(field.kind)
      || !field.typeDescriptor || !descriptorKinds.has(field.typeDescriptor.kind) || !nonemptyString(field.typeDescriptor.lean) || !stringArray(field.dependsOn)
      || field.parent !== undefined && !nonemptyString(field.parent)
      || !boundedFieldExpression(field.typeExpression) || !boundedFieldExpression(field.expression)
      || field.law !== undefined && !boundedLawTree(field.law)) return;
    const { fn, args } = applicationParts(field.expression);
    const owner = args.at(-1);
    if (fn.kind !== 'const' || fn.name !== field.projection || owner?.kind !== 'var' || owner.id !== binder.id) return;
    names.add(field.projection);
  }
  return value;
}

export function reflectedFields(binders: Iterable<Binder>): FieldBinding[] {
  return [...binders].flatMap(owner => (checkedStructure(owner)?.fields ?? []).map(field => ({ owner, field })));
}

export function exactField(expression: Expr, fields: readonly FieldBinding[]): FieldBinding | undefined {
  const key = expressionKey(expression);
  return fields.find(({ field }) => expressionKey(field.expression) === key);
}

/** A projection can be used as a function because its checked type says so.
 * The record and field spelling has no semantic significance. */
export function fieldApplication(expression: Expr, fields: readonly FieldBinding[]): { binding: FieldBinding; inputs: Expr[] } | undefined {
  if (expression.kind !== 'app') return;
  const actual = applicationParts(expression);
  for (const binding of fields) {
    const { field } = binding;
    const expanded = field.typeExpansion && checkedBinderTypeExpansion({ id: '', name: field.name, type: field.type, role: 'parameter', dependsOn: [], typeExpansion: field.typeExpansion });
    if (field.kind !== 'data' || !['map', 'relation'].includes(field.typeDescriptor.kind) && field.typeExpression.kind !== 'forall' && expanded?.kind !== 'forall') continue;
    const projected = applicationParts(field.expression);
    if (expressionKey(actual.fn) !== expressionKey(projected.fn) || actual.args.length <= projected.args.length) continue;
    if (!projected.args.every((arg, index) => expressionKey(arg) === expressionKey(actual.args[index]!))) continue;
    // Exported arguments include dependencies and implicit types. Only arguments
    // after the owning projection belong to this application of the field.
    const inputs = actual.args.slice(projected.args.length);
    return { binding, inputs };
  }
}

export function fieldApplicationRule(expression: Expr, fields: readonly FieldBinding[]): SemanticRuleMatch | undefined {
  const application = fieldApplication(expression, fields);
  if (!application) return;
  // A fully applied relation is a statement condition. A partial application
  // still denotes a function and belongs to the ordinary application grammar.
  // Read the actual exported result type, not a field name or a guessed arity.
  if ('typeDescriptor' in expression && expression.typeDescriptor?.kind === 'proposition') {
    return { kind: 'predicate', label: `${application.binding.owner.name}.${application.binding.field.name}`, fidelity: 'symbolic', arguments: [
      { role: 'relation', expression: application.binding.field.expression },
      ...application.inputs.map((input, index) => ({ role: `argument ${index + 1}`, expression: input })),
    ], conditions: ['An abstract relation supplied by this object. Its inputs and surrounding logical context are retained; no additional geometric meaning or truth value is inferred.'] };
  }
  return { kind: 'application', label: 'maps to', fidelity: 'symbolic', arguments: [
    { role: 'function', expression: application.binding.field.expression },
    ...application.inputs.map((input, index) => ({ role: `input ${index + 1}`, expression: input })),
    { role: 'output', expression },
  ], conditions: ['Application of a field with a Lean-checked function type. The owning object and its logical scope are retained.'] };
}

export function fieldLabel(expression: Expr, fields: readonly FieldBinding[], depth = 0): string {
  if (depth > 24) return formatExpression(expression);
  const direct = exactField(expression, fields);
  if (direct) return `${direct.owner.name}.${direct.field.name}`;
  const applied = fieldApplication(expression, fields);
  return applied ? `${applied.binding.owner.name}.${applied.binding.field.name}(${applied.inputs.map(input => fieldLabel(input, fields, depth + 1)).join(', ')})` : formatExpression(expression);
}
