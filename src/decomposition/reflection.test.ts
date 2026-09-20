import { describe, expect, it } from 'vitest';
import type { Binder, Expr, ReflectedField, StatementNode, TypeDescriptor } from '../core/types';
import { checkedStructure, fieldApplication, fieldApplicationRule, reflectedFields, type FieldBinding } from './reflection';
import { compileSemanticDocument } from '../semantic/compiler';

const constant = (name: string): Expr => ({ kind: 'const', name });
const variable = (id: string, type = 'A'): Expr => ({ kind: 'var', id, name: id, type });
const binder = (id: string, type: string): Binder => ({ id, name: id, type, role: 'universal', dependsOn: [], typeExpression: constant(type) });
function fixture(descriptor: TypeDescriptor['kind'] = 'relation', ownerId = 'e'): FieldBinding {
  const owner = binder(ownerId, 'Unseen');
  const field: ReflectedField = {
    name: 'condition', projection: 'Unseen.condition', expression: { kind: 'app', fn: constant('Unseen.condition'), args: [variable('A', 'Type'), variable(ownerId, 'Unseen')], argumentKinds: ['type', 'value'] },
    type: 'A → A → Prop', typeExpression: constant('RelationType'), typeDescriptor: { kind: descriptor, lean: 'A → A → Prop' }, kind: 'data', dependsOn: [],
  };
  owner.structure = { name: 'Unseen', typeExpression: constant('Unseen'), fields: [field], omittedFields: 0, kernelChecked: true, limits: { maxFields: 16, maxFieldNodes: 120, maxDepth: 24 } };
  return { owner, field };
}
function apply(binding: FieldBinding, inputs: Expr[], result: TypeDescriptor['kind'] = 'proposition'): Expr {
  const projection = binding.field.expression as Extract<Expr, { kind: 'app' }>;
  return { kind: 'app', fn: projection.fn, args: [...projection.args, ...inputs], argumentKinds: [...projection.argumentKinds!, ...inputs.map(() => 'value' as const)], typeDescriptor: { kind: result, lean: result === 'proposition' ? 'Prop' : 'A → Prop' } };
}
const leaf = (id: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean: id, expression, children: [] });

describe('generic checked field applications', () => {
  it('reads a fully applied proposition-valued field as an abstract condition, with no output value arrow', () => {
    const binding = fixture(), expression = apply(binding, [variable('x'), variable('y')]);
    const rule = fieldApplicationRule(expression, [binding])!;
    expect(rule.kind).toBe('predicate');
    expect(rule.label).toBe('e.condition');
    expect(rule.arguments.map(argument => argument.role)).toEqual(['relation', 'argument 1', 'argument 2']);
    expect(rule.arguments[0]!.expression).toBe(binding.field.expression);
    expect(rule.conditions!.join(' ')).toContain('no additional geometric meaning or truth value');
  });

  it('retains a partially applied binary relation as an actual function value', () => {
    const binding = fixture(), expression = apply(binding, [variable('x')], 'relation');
    const rule = fieldApplicationRule(expression, [binding])!;
    expect(rule.kind).toBe('application');
    expect(rule.arguments.map(argument => argument.role)).toEqual(['function', 'input 1', 'output']);
    expect(rule.arguments.at(-1)!.expression).toBe(expression);
    expect(fieldApplicationRule(apply(binding, [variable('x'), variable('y')]), [binding])!.kind).toBe('predicate');
  });

  it('preserves implicit type arguments and dependent input order after the exact projection prefix', () => {
    const binding = fixture('map'), A = variable('A', 'Type'), x = variable('x', 'A'), proof = variable('h', 'P x');
    const expression = apply(binding, [A, x, proof], 'unknown') as Extract<Expr, { kind: 'app' }>;
    expression.argumentKinds = ['type', 'value', 'type', 'value', 'proof'];
    const rule = fieldApplicationRule(expression, [binding])!;
    expect(rule.kind).toBe('application');
    expect(rule.arguments.slice(1, -1).map(argument => argument.expression)).toEqual([A, x, proof]);
    expect(rule.arguments.slice(1, -1).map(argument => argument.role)).toEqual(['input 1', 'input 2', 'input 3']);
    expect(rule.arguments[0]!.expression).toBe(binding.field.expression);
  });

  it('requires the exact owning projection and its universe/parameter arguments', () => {
    const binding = fixture(), other = fixture('relation', 'other'), expression = apply(binding, [variable('x')]);
    expect(fieldApplication(expression, [other])).toBeUndefined();
    const differentParameter = { ...expression as Extract<Expr, { kind: 'app' }>, args: [variable('B', 'Type'), variable('e', 'Unseen'), variable('x')] };
    expect(fieldApplication(differentParameter, [binding])).toBeUndefined();
    expect(fieldApplication(binding.field.expression, [binding])).toBeUndefined();
  });

  it('uses a checked function alias while leaving its declared name and projection identity intact', () => {
    const binding = fixture('structure');
    const x = binder('input', 'A');
    const expanded: Expr = { kind: 'forall', binder: x, binderType: constant('A'), body: { kind: 'sort', name: 'Prop' } };
    binding.field.type = 'PredicateAlias A';
    binding.field.typeExpansion = { before: binding.field.type, after: 'A → Prop', expression: expanded, constants: ['PredicateAlias'], maxDepth: 2, definitionalEquality: true };
    const rule = fieldApplicationRule(apply(binding, [variable('x')]), [binding])!;
    expect(rule.kind).toBe('predicate');
    expect(rule.arguments[0]!.expression).toBe(binding.field.expression);
    expect(binding.field.type).toBe('PredicateAlias A');
    expect(fieldApplicationRule(apply(binding, [variable('x')]), [{ ...binding, field: { ...binding.field, typeExpansion: { ...binding.field.typeExpansion, before: 'WrongAlias' } } }])).toBeUndefined();
  });

  it('does not turn a proof field into a new callable data field', () => {
    const binding = fixture();
    expect(fieldApplicationRule(apply(binding, [variable('x')]), [{ ...binding, field: { ...binding.field, kind: 'law' } }])).toBeUndefined();
  });

  it('only interprets field applications where the owner is available in the current logical scope', () => {
    const binding = fixture(), expression = apply(binding, [variable('x')]);
    const inside: StatementNode = { id: 'inside', kind: 'forall', label: 'inside', lean: 'inside', expression: constant('True'), binder: binding.owner, children: [leaf('valid', expression)] };
    const tree: StatementNode = { id: 'root', kind: 'and', label: 'root', lean: 'root', expression: constant('True'), children: [inside, leaf('outside', expression)] };
    const document = compileSemanticDocument({ source: 'scope fixture', tree, expression: tree.expression }, []);
    const interpreted = document.relations.filter(relation => relation.pluginId === 'structure-fields');
    expect(interpreted).toHaveLength(1);
    expect(interpreted[0]).toMatchObject({ kind: 'predicate', nodeId: 'valid', scopeId: 'scope:valid' });
    expect(document.opaqueRegions.some(region => region.nodeId === 'outside')).toBe(true);
    const ownerObject = document.objects.find(object => object.binder?.id === binding.owner.id)!;
    expect(document.scopes.find(scope => scope.id === 'scope:outside')!.objectIds).not.toContain(ownerObject.id);
  });

  it('uses the same predicate grammar for a direct unary field and a nested application representation', () => {
    const binding = fixture(), x = variable('x');
    const expression: Expr = { kind: 'app', fn: binding.field.expression, args: [x], argumentKinds: ['value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } };
    expect(fieldApplicationRule(expression, reflectedFields([binding.owner]))).toMatchObject({ kind: 'predicate', label: 'e.condition' });
  });
});

describe('bounded reflected structure envelopes', () => {
  it('validates actual expression depth before flattening a projection spine', () => {
    const binding = fixture();
    let expression = binding.field.expression;
    for (let index = 0; index < 26; index++) expression = { kind: 'app', fn: expression, args: [] };
    binding.field.expression = expression;
    expect(() => checkedStructure(binding.owner)).not.toThrow();
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it('enforces the depth boundary independently for a field type', () => {
    const binding = fixture();
    let expression: Expr = constant('Base');
    for (let index = 0; index < 24; index++) expression = { kind: 'app', fn: constant('Layer'), args: [expression] };
    binding.field.typeExpression = expression;
    expect(checkedStructure(binding.owner)).toBeDefined();
    binding.field.typeExpression = { kind: 'app', fn: constant('Layer'), args: [expression] };
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it('enforces the field AST node limit independently of depth', () => {
    const binding = fixture();
    binding.field.typeExpression = { kind: 'app', fn: constant('Wide'), args: Array.from({ length: 118 }, () => constant('A')) };
    expect(checkedStructure(binding.owner)).toBeDefined();
    binding.field.typeExpression.args.push(constant('A'));
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it('counts binder types once rather than traversing duplicate inline display metadata', () => {
    const binding = fixture(), type: Expr = { kind: 'app', fn: constant('Wide'), args: Array.from({ length: 78 }, () => constant('A')) };
    const x = { ...binder('x', 'Wide'), typeExpression: type };
    binding.field.typeExpression = { kind: 'forall', binder: x, binderType: type, body: constant('Result') };
    expect(checkedStructure(binding.owner)).toBeDefined();
  });

  it('limits the whole envelope in UTF-8 bytes rather than JavaScript character count', () => {
    const binding = fixture();
    binding.owner.structure!.stopReason = '漢'.repeat(50_000);
    expect(JSON.stringify(binding.owner.structure).length).toBeLessThan(128 * 1024);
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it('rejects unserializable envelopes without traversing cyclic expressions', () => {
    const binding = fixture(), cyclic: Expr = { kind: 'app', fn: constant('Cycle'), args: [] };
    cyclic.args.push(cyclic);
    binding.field.typeExpression = cyclic;
    expect(() => checkedStructure(binding.owner)).not.toThrow();
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it.each([
    { typeDescriptor: undefined },
    { typeDescriptor: { kind: 'not-a-type-kind', lean: 'A' } },
    { typeDescriptor: { kind: 'map' } },
    { dependsOn: 'previous' },
    { dependsOn: [null] },
    { type: 3 },
    { name: '' },
    { expression: { kind: 'app', fn: constant('Unseen.condition'), args: null } },
    { typeExpression: { kind: 'unrecognized-node' } },
  ])('rejects malformed required field shapes %#', malformed => {
    const binding = fixture();
    Object.assign(binding.field, malformed);
    expect(() => checkedStructure(binding.owner)).not.toThrow();
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });

  it('retains an opaque instance argument without granting it any primitive meaning', () => {
    const binding = fixture(), instance: Expr = { kind: 'opaque', text: 'instance retained symbolically' };
    const projection = binding.field.expression as Extract<Expr, { kind: 'app' }>;
    projection.args.splice(1, 0, instance);
    projection.argumentKinds = ['type', 'instance', 'value'];
    expect(checkedStructure(binding.owner)).toBeDefined();
    const rule = fieldApplicationRule(apply(binding, [variable('x')]), reflectedFields([binding.owner]))!;
    expect(rule.kind).toBe('predicate');
    expect(rule.arguments.map(argument => argument.role)).toEqual(['relation', 'argument 1']);
    expect(rule.arguments[0]!.expression).toBe(projection);
  });

  it('rejects a malformed supplementary law tree before the logical reader uses it', () => {
    const binding = fixture();
    binding.field.kind = 'law';
    binding.field.law = { ...leaf('law', constant('True')), children: null } as unknown as StatementNode;
    expect(checkedStructure(binding.owner)).toBeUndefined();
  });
});
