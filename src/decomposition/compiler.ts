import type { Binder, Expr, ReflectedField, StatementNode } from '../core/types';
import { compileTypedConstruction, type TypedConstruction } from '../constructions/model';
import { compileReading } from '../reading/compiler';
import type { ReadingBinder } from '../reading/types';
import { compileSemanticDocument } from '../semantic/compiler';
import { binderTypeExpression, expressionKey } from '../semantic/expression';
import type { SemanticDocument, SemanticObject, SemanticPlugin, SemanticScope } from '../semantic/types';
import { checkedStructure, reflectedFields } from './reflection';
import type { StructuralField, StructuralObjectModel } from './types';

const terminal = (id: string): StatementNode => ({ id, kind: 'predicate', label: 'True', lean: 'True', expression: { kind: 'const', name: 'True', canonical: true }, children: [] });

/** Reuse the typed construction compiler for fields. These private layout
 * binders never enter the statement's quantifiers or witness obligations. */
function fieldConstruction(document: SemanticDocument, owner: SemanticObject, fields: readonly { metadata: ReflectedField; object: SemanticObject }[]): TypedConstruction {
  const data = fields.filter(field => field.metadata.kind === 'data');
  const available = document.scopes.find(scope => scope.id === owner.scopeId)?.objectIds ?? [];
  const scopes: SemanticScope[] = [...document.scopes];
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const nodes: StatementNode[] = [], readings: ReadingBinder[] = [];
  for (const [index, { metadata: field, object }] of data.entries()) {
    const id = `field-layout:${owner.id}:${index}`, scopeId = `scope:${id}`;
    const binder: Binder = { id, name: field.name, type: field.type, role: 'parameter', dependsOn: [], typeExpression: field.typeExpression, typeDescriptor: field.typeDescriptor, typeExpansion: field.typeExpansion };
    nodes.push({ id, kind: 'parameter', label: field.name, lean: field.type, expression: field.expression, binder, children: [] });
    objects.set(object.id, { ...object, binder, scopeId });
    const objectIds = [...available, ...data.slice(0, index + 1).map(entry => entry.object.id)];
    scopes.push({ id: scopeId, nodeId: id, parentId: index ? `scope:${nodes[index - 1]!.id}` : owner.scopeId, kind: 'parameter', label: 'Fields of this object', objectIds, assumptionNodeIds: [], context: [] });
    readings.push({ binderId: id, objectId: object.id, name: field.name, type: field.type, role: 'parameter', dependsOn: [], scopeId });
  }
  nodes.forEach((node, index) => { node.children = [nodes[index + 1] ?? terminal(`field-layout:${owner.id}:end`)]; });
  return compileTypedConstruction({ ...document, tree: nodes[0] ?? terminal(`field-layout:${owner.id}:empty`), objects: [...objects.values()], scopes }, readings);
}

/** Supplementary laws use the same identities as the enclosing statement.
 * Existing objects are context parameters here, not a second existence claim.
 * Their structure metadata is removed to prevent recursive reader expansion. */
function lawContext(document: SemanticDocument, owner: SemanticObject, law: StatementNode): StatementNode {
  const available = new Set(document.scopes.find(scope => scope.id === owner.scopeId)?.objectIds ?? []);
  available.add(owner.id);
  const parameters = document.objects.filter(object => available.has(object.id) && object.binder);
  const sourceBinders = new Map<string, StatementNode>();
  const index = (node: StatementNode) => { if (node.binder) sourceBinders.set(node.binder.id, node); node.children.forEach(index); };
  index(document.tree);
  let tree = law;
  for (const object of [...parameters].reverse()) {
    const original = object.binder!;
    const { structure: _structure, structureOmission: _omission, ...rest } = original;
    const source = sourceBinders.get(original.id);
    const binder: Binder = { ...rest, typeExpression: source ? binderTypeExpression(source, original) : original.typeExpression, role: original.role === 'assumption' ? 'assumption' : 'parameter' };
    const expression: Expr = { kind: 'forall', binder, binderType: binder.typeExpression, body: tree.expression };
    tree = { id: `law-context:${law.id}:${binder.id}`, kind: 'parameter', label: `Given ${binder.name}`, lean: binder.type, binder, expression, children: [tree] };
  }
  return tree;
}

/** Generic structural decomposition. No theorem, record, or field name selects
 * this path. A specialized lens is an optional refinement of this foundation. */
export function compileStructuralObject(document: SemanticDocument, object: SemanticObject, plugins?: readonly SemanticPlugin[]): StructuralObjectModel | undefined {
  const structure = object.binder && checkedStructure(object.binder);
  if (!structure || !document.objects.some(candidate => candidate === object || candidate.id === object.id && expressionKey(candidate.expression) === expressionKey(object.expression))) return;
  const byExpression = new Map(document.objects.map(value => [expressionKey(value.expression), value]));
  const entries = structure.fields.flatMap(metadata => {
    const fieldObject = byExpression.get(expressionKey(metadata.expression));
    return fieldObject ? [{ metadata, object: fieldObject }] : [];
  });
  const identities = new Map(document.objects.flatMap(value => value.binder ? [[value.binder.id, value.id] as const] : []));
  const bindings = reflectedFields(document.objects.flatMap(value => value.binder ? [value.binder] : []));
  const fields: StructuralField[] = entries.map(({ metadata: field, object: fieldObject }) => {
    const tree = field.kind === 'law' && field.law ? lawContext(document, object, field.law) : undefined;
    const lawDocument = tree ? compileSemanticDocument({ source: `${object.label}.${field.name} : ${field.type}`, tree, expression: tree.expression }, plugins, { identities, fields: bindings }) : undefined;
    return { name: field.name, projection: field.projection, object: fieldObject, type: field.type, typeExpression: field.typeExpression,
      typeDescriptor: field.typeDescriptor, kind: field.kind, dependsOn: field.dependsOn,
      ...(lawDocument ? { lawDocument, lawReading: compileReading(lawDocument, { selectedNodeId: field.law!.id }) } : {}) };
  });
  return { object, declarationName: structure.name, fields, construction: fieldConstruction(document, object, entries),
    omittedFields: structure.omittedFields + structure.fields.length - entries.length, stopReason: structure.stopReason };
}
