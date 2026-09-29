import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileReading } from '../reading/compiler';
import type { SemanticDocument, SemanticRelation } from '../semantic/types';
import { validateSourceSnapshot } from '../editor/source-snapshot';
import { validateSourceOccurrence } from '../editor/source-occurrence';
import { createExactJsonTools, type JsonValue } from './packet';
import { compilePositionalComponent, type PositionalComponentReading, type RecordedContextDeclaration } from './semantic';
import { recordedContextHeadings } from './StructuralReading';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { PositionalReadingPane } from '../editor/SourceOccurrenceGuidedReading';
import { UNMATCHED_RECORDED_KINDS } from '../core/context-entry';
import { sourceOccurrenceReading } from '../editor/source-occurrence-reading';
import type { SourceOccurrence } from '../editor/source-occurrence';
import { headExposureReading } from '../editor/source-head-exposure-reading';
import type { SourceHeadExposure } from '../editor/source-head-exposure';
import { decompositionReading } from '../editor/source-decomposition-reading';
import { validateDecompositionHistory, validateSourceDecomposition, type SourceDecomposition } from '../editor/source-decomposition';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing, type PositionalStructuralInput } from './structure';

type Path = (string | number)[];
const name = (text: string): JsonValue => ['str', ['anonymous'], text];
const n = (value: number | string): JsonValue => ['nat', String(value)];
const b = (index: number): JsonValue => ['bvar', n(index)];
const c = (text: string): JsonValue => ['const', name(text), []];
const app = (fn: JsonValue, ...args: JsonValue[]): JsonValue => args.reduce<JsonValue>((head, arg) => ['app', head, arg], fn);
const pi = (type: JsonValue, body: JsonValue, label = 'input'): JsonValue => ['forallE', name(label), type, body, 'default'];
const lam = (type: JsonValue, body: JsonValue, label = 'input'): JsonValue => ['lam', name(label), type, body, 'default'];
const letExpr = (type: JsonValue, value: JsonValue, body: JsonValue, nondep = false): JsonValue => ['letE', name('same'), type, value, body, nondep];
const literal = (value: number | string): JsonValue => ['lit', ['natVal', n(value)]];
const sort: JsonValue = ['sort', ['succ', ['zero']]];
const port = (previous: JsonValue, label: string, type: JsonValue, info = 'default'): JsonValue => ['port', previous, { name: name(label), info }, type];
const define = (previous: JsonValue, type: JsonValue, value: JsonValue, nondep = false): JsonValue => ['letE', previous, name('same'), nondep, type, value];
const base: Path = ['checking', 'selected'];
const { canonical } = createExactJsonTools();
const key = (value: unknown) => canonical(value as JsonValue);
const nodes = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(nodes)];
const expressions = (value: Expr): Expr[] => value.kind === 'app' ? [value, ...expressions(value.fn), ...value.args.flatMap(expressions)]
  : value.kind === 'lambda' || value.kind === 'forall' ? [value, ...(value.binderType ? expressions(value.binderType) : []), ...expressions(value.body)] : [value];
function compile(input: PositionalStructuralInput, target: 'term' | 'type' = 'term', identity = 'component-control', sourcePath = base) {
  return compilePositionalComponent(input, { target, sourceIdentity: identity, sourcePath });
}
function document(result: PositionalComponentReading): SemanticDocument {
  expect(result.reason).toBeUndefined(); expect(result.document).toBeDefined(); return result.document!;
}
function composition(labels = ['CarrierAlpha', 'SpaceBeta', 'TargetGamma', 'weave', 'unfold', 'seed']): PositionalStructuralInput {
  let telescope = port(['nil'], labels[0], sort);
  telescope = port(telescope, labels[1], sort); telescope = port(telescope, labels[2], sort);
  telescope = port(telescope, labels[3], pi(b(2), b(2))); // A -> B in prefix A,B,C.
  telescope = port(telescope, labels[4], pi(b(2), b(2))); // B -> C in prefix A,B,C,f.
  telescope = port(telescope, labels[5], b(4));
  return { home: { arity: 6, telescope }, term: app(b(1), app(b(2), b(0))), type: b(3) };
}

/** Walk CTel and Core directly to recover the exact preceding scope for each
 * source constructor. The guide is not used as a source or readback oracle. */
function sourceOracle(input: PositionalStructuralInput, root: Path) {
  const located = new Map<string, { syntax: JsonValue; scope: Path[] }>();
  const add = (syntax: JsonValue, path: Path, scope: Path[]) => located.set(key(path), { syntax, scope: scope.map(path => [...path]) });
  const expr = (raw: JsonValue, path: Path, scope: Path[]): void => {
    const value = raw as JsonValue[]; add(raw, path, scope);
    if (value[0] === 'app') { expr(value[1], [...path, 1], scope); expr(value[2], [...path, 2], scope); }
    else if (value[0] === 'lam' || value[0] === 'forallE') { expr(value[2], [...path, 2], scope); expr(value[3], [...path, 3], [...scope, path]); }
    else if (value[0] === 'letE') { expr(value[2], [...path, 2], scope); expr(value[3], [...path, 3], scope); expr(value[4], [...path, 4], [...scope, path]); }
    else if (value[0] === 'proj') expr(value[3], [...path, 3], scope);
  };
  const context = (raw: JsonValue, path: Path): Path[] => {
    const value = raw as JsonValue[];
    if (value[0] === 'nil') return [];
    const scope = context(value[1], [...path, 1]); add(raw, path, scope);
    expr(value[value[0] === 'port' ? 3 : 4], [...path, value[0] === 'port' ? 3 : 4], scope);
    if (value[0] === 'letE') expr(value[5], [...path, 5], scope);
    return [...scope, path];
  };
  const scope = context(input.home.telescope, [...root, 'home', 'telescope']);
  expr(input.term, [...root, 'term'], scope); expr(input.type, [...root, 'type'], scope);
  return { located, context: scope };
}
function outerReferences(raw: JsonValue, depth = 0, found = new Set<number>()): Set<number> {
  const value = raw as JsonValue[];
  if (value[0] === 'bvar') { const index = Number((value[1] as JsonValue[])[1]); if (index >= depth) found.add(index - depth); }
  else if (value[0] === 'app') { outerReferences(value[1], depth, found); outerReferences(value[2], depth, found); }
  else if (value[0] === 'lam' || value[0] === 'forallE') { outerReferences(value[2], depth, found); outerReferences(value[3], depth + 1, found); }
  else if (value[0] === 'letE') { outerReferences(value[2], depth, found); outerReferences(value[3], depth, found); outerReferences(value[4], depth + 1, found); }
  else if (value[0] === 'proj') outerReferences(value[3], depth, found);
  return found;
}
function verify(input: PositionalStructuralInput, result: PositionalComponentReading, root = base): SemanticDocument {
  const doc = document(result), oracle = sourceOracle(input, root), allNodes = nodes(doc.tree);
  expect(doc.presentation).toEqual({ kind: 'component', target: result.target, contextNodeIds: result.contextNodeIds, targetNodeId: result.targetNodeId });
  expect(result.contextNodeIds).toHaveLength(input.home.arity);
  result.contextNodeIds.forEach((id, i) => {
    const node = allNodes.find(node => node.id === id)!;
    expect(node).toBeDefined(); expect(['parameter', 'definition']).toContain(node.kind);
    expect(result.sourceById[id].path).toEqual(oracle.context[i]);
    expect(result.sourceById[node.binder!.id].path).toEqual(oracle.context[i]);
  });
  expect(result.targetNodeId).toBeDefined();
  expect(result.sourceById[result.targetNodeId!].path).toEqual([...root, result.target]);
  const ids = new Set([...allNodes.map(node => node.id), ...allNodes.flatMap(node => node.binder ? [node.binder.id] : []),
    ...doc.objects.map(value => value.id), ...doc.relations.map(value => value.id), ...doc.choices.map(value => value.id),
    ...doc.scopes.map(value => value.id), ...doc.opaqueRegions.map(value => value.id)]);
  for (const id of ids) expect(result.sourceById[id], id).toBeDefined();
  for (const [id, source] of Object.entries(result.sourceById)) {
    const expected = oracle.located.get(key(source.path)); expect(expected, id).toBeDefined();
    expect(key(source.syntax), id).toBe(key(expected!.syntax));
    expect(source.scopeBinderIds.map(binderId => result.sourceById[binderId]?.path), id).toEqual(expected!.scope);
  }
  for (const node of allNodes) if (node.binder) {
    const binder = node.binder, source = result.sourceById[binder.id], raw = source.syntax as JsonValue[];
    const ambient = key(source.path).includes('"home","telescope"');
    const type = raw[ambient ? raw[0] === 'port' ? 3 : 4 : 2];
    const references = outerReferences(type);
    if (raw[0] === 'letE') outerReferences(raw[ambient ? 5 : 3], 0, references);
    const expected = source.scopeBinderIds.filter((_, i, scope) => references.has(scope.length - i - 1));
    expect(binder.dependsOn).toEqual(expected);
    expect(binder.typeDescriptor).toBeUndefined(); expect(binder.typeExpansion).toBeUndefined(); expect(binder.structure).toBeUndefined();
  }
  for (const object of doc.objects) {
    expect(object.provenance.every(value => value.origin === 'selected-occurrence')).toBe(true);
    if (object.expression.kind === 'var') {
      const source = result.sourceById[object.id], raw = source.syntax as JsonValue[];
      if (raw[0] === 'bvar') expect(object.expression.id).toBe(source.scopeBinderIds[source.scopeBinderIds.length - Number((raw[1] as JsonValue[])[1]) - 1]);
      else if (object.binder) expect(object.expression.id).toBe(object.binder.id);
    }
  }
  expect(doc.relations.every(value => value.provenance.origin === 'selected-occurrence' && value.kind === 'application')).toBe(true);
  expect(doc.scopes.every(scope => scope.assumptionNodeIds.length === 0)).toBe(true);
  expect(doc.choices.every(choice => ['parameter', 'lambda', 'definition'].includes(choice.role))).toBe(true);
  expect(allNodes.every(node => !['forall', 'exists', 'implies', 'and', 'or', 'iff', 'not'].includes(node.kind))).toBe(true);
  expect(doc.scenes).toEqual([]);
  for (const expression of [...allNodes.flatMap(node => expressions(node.expression)), ...doc.objects.flatMap(object => expressions(object.expression))]) {
    expect(expression.exactIdentity).toBeTruthy();
    for (const property of ['typeDescriptor', 'operator', 'metric', 'dimension', 'typeExpansion', 'structure']) expect(Object.hasOwn(expression, property), property).toBe(false);
    expect((expression as { canonical?: boolean }).canonical).not.toBe(true);
  }
  const structure = buildPositionalStructuralDrawing(input, { sourceIdentity: 'independent-complete-source', sourcePath: root });
  expect(structure.ok).toBe(true);
  if (structure.ok) {
    const readback = readPositionalStructuralDrawing(structure.value); expect(readback.ok).toBe(true);
    if (readback.ok) expect(key(readback.value)).toBe(key(input));
  }
  return doc;
}
function portId(relation: SemanticRelation, role: string) {
  const port = relation.ports.find(port => port.role === role); expect(port).toBeDefined(); return port!.objectId;
}
function topology(result: PositionalComponentReading) {
  const doc = document(result), indices = new Map(doc.objects.map((object, i) => [object.id, i]));
  return { nodes: nodes(doc.tree).map(node => [node.kind, node.binder?.role, node.children.length]),
    objects: doc.objects.map(object => [object.kind, object.binder?.role]),
    relations: doc.relations.map(relation => [relation.kind, relation.ports.map(port => [port.role, indices.get(port.objectId)])]),
    choices: doc.choices.map(choice => [choice.role, choice.dependsOn.length, choice.availableObjectIds.length]) };
}

describe('neutral positional component guided readings', () => {
  it('composes unfamiliar f/g/x applications through the exact shared intermediate object in source order', () => {
    const input = composition(), result = compile(input), doc = verify(input, result), context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!);
    const object = (binder: Binder) => doc.objects.find(object => object.binder?.id === binder.id)!;
    const f = object(context[3].binder!), g = object(context[4].binder!), x = object(context[5].binder!);
    const fRelation = doc.relations.find(relation => portId(relation, 'function') === f.id)!;
    const gRelation = doc.relations.find(relation => portId(relation, 'function') === g.id)!;
    expect(doc.relations).toHaveLength(2);
    expect(fRelation.ports.map(port => port.role)).toEqual(['function', 'input 1', 'output']);
    expect(portId(fRelation, 'input 1')).toBe(x.id);
    expect(portId(gRelation, 'input 1')).toBe(portId(fRelation, 'output'));
    expect(portId(gRelation, 'output')).not.toBe(portId(fRelation, 'output'));
    const reading = compileReading(doc);
    expect(reading.panels.flatMap(panel => panel.groups).flatMap(group => group.connections)).toContainEqual({
      kind: 'feeds', objectId: portId(fRelation, 'output'), fromRelationId: fRelation.id, toRelationId: gRelation.id,
    });
    expect(topology(compile(composition(['Σ', '别', 'Zed', 'unknownBeta', 'unknownAlpha', 'q'])))).toEqual(topology(result));
  });

  it('retains every repeated, unused and dependent CTel entry in its real preceding scope', () => {
    let telescope = port(['nil'], 'same', sort, 'implicit');
    telescope = port(telescope, 'same', pi(b(0), sort));
    telescope = port(telescope, 'same', b(1));
    telescope = port(telescope, 'same', app(b(1), b(0)));
    const input = { home: { arity: 4, telescope }, term: c('UnknownUnrelatedConstant'), type: c('Nat') };
    const result = compile(input), doc = verify(input, result), binders = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
    expect(new Set(binders.map(binder => binder.id)).size).toBe(4);
    expect(binders.map(binder => binder.dependsOn)).toEqual([[], [binders[0].id], [binders[0].id], [binders[1].id, binders[2].id]]);
    expect(doc.choices.filter(choice => result.contextNodeIds.includes(choice.nodeId))).toHaveLength(4);
  });

  it.each([false, true])('retains CTel and owned let values without substitution, nondep=%s', nondep => {
    let telescope = port(['nil'], 'same', c('Nat'));
    telescope = port(telescope, 'same', c('Nat'));
    telescope = define(telescope, c('Nat'), b(1), nondep);
    const input = { home: { arity: 3, telescope }, term: letExpr(c('Nat'), b(0), b(0), nondep), type: c('Nat') };
    const result = compile(input), doc = verify(input, result);
    const contextDefinition = nodes(doc.tree).find(node => node.id === result.contextNodeIds[2])!.binder!;
    const owned = nodes(doc.tree).find(node => node.id === result.targetNodeId)!.binder!;
    expect(contextDefinition.definition?.nondep).toBe(nondep); expect(owned.definition?.nondep).toBe(nondep);
    expect(owned.definition?.value.kind).toBe('var');
    expect(owned.dependsOn).toEqual([contextDefinition.id]);
    const changed = structuredClone(input); (changed.home.telescope as JsonValue[])[5] = b(0);
    const changedResult = compile(changed), changedDoc = verify(changed, changedResult);
    const changedDefinition = nodes(changedDoc.tree).find(node => node.id === changedResult.contextNodeIds[2])!.binder!;
    expect(changedDefinition.dependsOn).not.toEqual(contextDefinition.dependsOn);
    expect(changedDefinition.definition!.value.exactIdentity).not.toBe(contextDefinition.definition!.value.exactIdentity);
  });

  it('changes literal defining-value identity without inventing a changed variable dependency', () => {
    const make = (value: number) => ({ home: { arity: 1, telescope: define(['nil'], c('Nat'), literal(value)) }, term: b(0), type: c('Nat') });
    const before = compile(make(0)), after = compile(make(1));
    const first = verify(make(0), before).tree.binder!, second = verify(make(1), after).tree.binder!;
    expect(first.dependsOn).toEqual([]); expect(second.dependsOn).toEqual([]);
    expect(first.definition!.value.exactIdentity).not.toBe(second.definition!.value.exactIdentity);
    expect(first.definition!.value).toMatchObject({ kind: 'literal', value: '0' });
    expect(second.definition!.value).toMatchObject({ kind: 'literal', value: '1' });
  });

  it('shares ambient identity across explicit term/type targets but separates their owned binders', () => {
    const input = { home: { arity: 1, telescope: port(['nil'], 'same', sort) }, term: lam(b(0), b(0), 'same'), type: pi(b(0), b(1), 'same') };
    const term = compile(input, 'term'), type = compile(input, 'type');
    const termDoc = verify(input, term), typeDoc = verify(input, type);
    expect(term.target).toBe('term'); expect(type.target).toBe('type');
    expect(termDoc.tree.binder!.id).toBe(typeDoc.tree.binder!.id);
    const termOwned = nodes(termDoc.tree).find(node => node.id === term.targetNodeId)!.binder!;
    const typeOwned = nodes(typeDoc.tree).find(node => node.id === type.targetNodeId)!.binder!;
    expect(termOwned.role).toBe('lambda'); expect(typeOwned.role).toBe('parameter');
    expect(termOwned.id).not.toBe(typeOwned.id);
    expect(term.targetNodeId).not.toBe(type.targetNodeId);
    for (const result of [term, type]) {
      const groups = compileReading(result.document!).quantifierGroups;
      const ambient = groups.find(group => group.nodeIds.includes(result.contextNodeIds[0]))!;
      const owned = groups.find(group => group.nodeIds.includes(result.targetNodeId!))!;
      expect(ambient).toBeDefined(); expect(owned).toBeDefined();
      expect(ambient.id).not.toBe(owned.id);
      expect(ambient.nodeIds).toEqual(result.contextNodeIds);
      expect(ambient.bodyNodeId).toBe(result.targetNodeId);
      expect(owned.nodeIds.some(id => result.contextNodeIds.includes(id))).toBe(false);
    }
  });

  it('uses the supplied capture and exact source prefix without retaining mutable input aliases', () => {
    const input = composition(), prefix: Path = ['extracts', 3, 'selected'];
    const result = compile(input, 'term', 'capture-one', prefix), expected = structuredClone(input);
    const doc = verify(expected, result, prefix), previous = key(result.sourceById);
    const other = compile(expected, 'term', 'capture-two', prefix);
    const otherIds = new Set(nodes(document(other).tree).map(node => node.id));
    expect(nodes(doc.tree).some(node => otherIds.has(node.id))).toBe(false);
    input.term = c('Changed'); (input.home.telescope as JsonValue[])[3] = c('ChangedType'); prefix.push('changed');
    expect(key(result.sourceById)).toBe(previous);
    verify(expected, result, ['extracts', 3, 'selected']);
    const defaultPath = compilePositionalComponent(expected, { target: 'term', sourceIdentity: 'default-path' });
    verify(expected, defaultPath);
  });

  it.each([pi(c('Nat'), c('Nat')), pi(c('Nat'), ['sort', ['zero']], 'n')].map(type => ({ type })))('does not turn an owned Pi type into a universal logical claim', ({ type }) => {
    const input = { home: { arity: 0, telescope: ['nil'] as JsonValue }, term: c('unfamiliarValue'), type };
    const result = compile(input, 'type'), doc = verify(input, result), reading = compileReading(doc);
    expect(doc.tree.kind).toBe('parameter'); expect(doc.tree.binder!.role).toBe('parameter');
    expect(reading.quantifierGroups.every(group => group.kind === 'parameter')).toBe(true);
    expect(reading.nodes.map(node => node.phrase).join(' ')).not.toMatch(/for every|universal|assume|conclusion|conditions hold|logical statement|packet/i);
  });

  it('keeps a selected proof term as that term and treats And/Eq as ordered generic applications', () => {
    const proof = { home: { arity: 2, telescope: port(port(['nil'], 'P', ['sort', ['zero']]), 'h', b(0)) }, term: b(0), type: b(1) };
    const term = compile(proof), type = compile(proof, 'type'); verify(proof, term); verify(proof, type);
    expect(term.sourceById[term.targetNodeId!].syntax).toEqual(b(0)); expect(type.sourceById[type.targetNodeId!].syntax).toEqual(b(1));
    expect(nodes(term.document!.tree).find(node => node.id === term.targetNodeId)!.expression).toMatchObject({ kind: 'var', id: nodes(term.document!.tree).find(node => node.id === term.contextNodeIds[1])!.binder!.id });
    const eq: JsonValue = ['const', name('Eq'), [['succ', ['zero']]]];
    const input = { home: { arity: 0, telescope: ['nil'] as JsonValue }, term: app(c('And'), app(eq, c('Nat'), literal(1), literal(1)), c('False')), type: ['sort', ['zero']] as JsonValue };
    const doc = verify(input, compile(input));
    expect(doc.tree.kind).toBe('predicate'); expect(doc.relations.map(relation => relation.kind)).toEqual(['application', 'application']);
    expect(doc.relations[1].ports.map(port => port.role)).toEqual(['function', 'input 1', 'input 2', 'input 3', 'output']);
  });

  it('keeps nested binding/projection boundaries exact and does not introduce their bodies as outer choices', () => {
    const nested: JsonValue[] = [letExpr(c('Nat'), b(0), b(0)), lam(c('Nat'), b(0)), pi(c('Nat'), c('Nat')), ['proj', name('ForeignRecord'), n(2), b(0)]];
    const input = { home: { arity: 1, telescope: port(['nil'], 'owner', c('Nat')) }, term: app(c('Unknown'), ...nested), type: c('Nat') };
    const result = compile(input), doc = verify(input, result);
    expect(doc.choices).toHaveLength(1);
    for (const raw of nested) {
      const region = doc.opaqueRegions.find(region => key(result.sourceById[region.id].syntax) === key(raw));
      expect(region).toBeDefined(); expect(region!.reason).toMatch(/exact|retained/);
      expect(result.sourceById[region!.id].scopeBinderIds).toEqual([doc.tree.binder!.id]);
    }
    expect(doc.coverage.some(fragment => fragment.status === 'partial')).toBe(true);
    const defined = { ...input, home: { arity: 2, telescope: define(input.home.telescope, c('Nat'), nested[3], true) }, term: b(0) };
    const definition = compile(defined), definitionDoc = verify(defined, definition);
    expect(definitionDoc.opaqueRegions.some(region => key(definition.sourceById[region.id].path) === key([...base, 'home', 'telescope', 5]))).toBe(true);
  });

  it.each(['outside scope', 'mdata', 'arity', 'extra field', 'unsafe natural', 'sparse', 'cycle', 'depth'])('refuses %s with an explicit bounded reason and no partial reading', mutation => {
    const input = composition();
    switch (mutation) {
      case 'outside scope': input.term = b(6); break;
      case 'mdata': input.term = ['mdata', ['mdataEntries', []], c('True')]; break;
      case 'arity': input.home.arity++; break;
      case 'extra field': Object.assign(input.home, { registry: [] }); break;
      case 'unsafe natural': input.term = ['lit', ['natVal', 9007199254740992]]; break;
      case 'sparse': input.term = ['const', name('C'), Array(1)]; break;
      case 'cycle': (input.home.telescope as JsonValue[])[1] = input.home.telescope; break;
      case 'depth': for (let i = 0; i < 150; i++) input.term = app(c('Foreign'), input.term); break;
    }
    const result = compile(input);
    expect(result.document).toBeUndefined(); expect(result.targetNodeId).toBeUndefined(); expect(result.contextNodeIds).toEqual([]);
    expect(typeof result.reason).toBe('string'); expect(result.reason!.length).toBeGreaterThan(0);
    expect(Object.keys(result.sourceById)).toEqual([]);
  });

  it.each(['accessor', 'hidden', 'symbol', 'prototype', 'unselected invalid type'])('refuses hostile %s input before presenting a candidate', mutation => {
    const input = composition(); let evaluated = false;
    switch (mutation) {
      case 'accessor': Object.defineProperty(input, 'term', { enumerable: true, get() { evaluated = true; throw new Error('getter must not run'); } }); break;
      case 'hidden': Object.defineProperty(input.home, 'hidden', { value: true }); break;
      case 'symbol': Object.assign(input.home, { [Symbol('extra')]: true }); break;
      case 'prototype': Object.setPrototypeOf(input.home, { inherited: true }); break;
      case 'unselected invalid type': input.type = b(6); break;
    }
    const result = compile(input);
    expect(evaluated).toBe(false); expect(result.reason).toBeTruthy(); expect(result.document).toBeUndefined();
    expect(result.contextNodeIds).toEqual([]); expect(result.targetNodeId).toBeUndefined(); expect(Object.keys(result.sourceById)).toEqual([]);
  });

  it.each(['target', 'accessor', 'path', 'identity'])('refuses invalid %s options without evaluating accessors or retaining partial data', mutation => {
    const options: Record<string, unknown> = { target: 'term', sourceIdentity: 'control' }; let evaluated = false;
    switch (mutation) {
      case 'target': options.target = 'whichever-is-a-proposition'; break;
      case 'accessor': Object.defineProperty(options, 'target', { enumerable: true, get() { evaluated = true; return 'term'; } }); break;
      case 'path': options.sourcePath = ['checking', -1]; break;
      case 'identity': options.sourceIdentity = ''; break;
    }
    const result = compilePositionalComponent(composition(), options as never);
    expect(evaluated).toBe(false); expect(result.reason).toBeTruthy(); expect(result.document).toBeUndefined();
    expect(result.contextNodeIds).toEqual([]); expect(result.targetNodeId).toBeUndefined(); expect(Object.keys(result.sourceById)).toEqual([]);
  });
});

for (const [label, variable, includesRejectedSource] of [
  ['retained native', 'DEFINOGRAPH_SOURCE_OCCURRENCE_FIXTURES', true],
  ['independent retained challenge', 'DEFINOGRAPH_POSITIONAL_THEORY_FIXTURES', true],
  ['fresh unfamiliar source', 'DEFINOGRAPH_POSITIONAL_GUIDED_CAPTURES', false],
] as const) describe.runIf(!!process.env[variable])(`${label} positional component readings`, () => {
  it('compiles both explicit targets for every available selected candidate without changing outcomes', () => {
    const captures = JSON.parse(readFileSync(process.env[variable]!, 'utf8')); let compiled = 0, rejectedSource = 0;
    expect(captures.length).toBeGreaterThan(0);
    for (const item of captures) {
      const response = item.response ?? item, before = key(response);
      const snapshot = validateSourceSnapshot(response.sourceSnapshot ?? response.snapshot);
      const occurrence = validateSourceOccurrence(response.sourceOccurrence ?? response.occurrence, snapshot);
      if (occurrence.checking.status === 'captured' && occurrence.checking.selected) {
        const selected = occurrence.checking.selected;
        for (const target of ['term', 'type'] as const) {
          const result = compile(selected, target, `${occurrence.captureId}:${JSON.stringify(occurrence.path)}`);
          verify(selected, result); compiled++;
        }
        if (occurrence.checking.checks.some(check => check.outcome.tag !== 'accepted')) rejectedSource++;
      }
      expect(key(response)).toBe(before);
    }
    expect(compiled).toBeGreaterThan(0);
    if (includesRejectedSource) expect(rejectedSource).toBeGreaterThan(0);
  });
});

describe.runIf(!!process.env.DEFINOGRAPH_POSITIONAL_GUIDED_CAPTURES)('fresh native positional meaning controls', () => {
  it('preserves unfamiliar composition, renamed topology, neutral dependent Pis and the selected proof term', () => {
    const captures = JSON.parse(readFileSync(process.env.DEFINOGRAPH_POSITIONAL_GUIDED_CAPTURES!, 'utf8'));
    const read = (label: string) => {
      const item = captures.find((item: { label: string }) => item.label === label); expect(item).toBeDefined();
      const snapshot = validateSourceSnapshot(item.response.sourceSnapshot);
      const occurrence = validateSourceOccurrence(item.response.sourceOccurrence, snapshot);
      expect(occurrence.checking.status).toBe('captured');
      if (occurrence.checking.status !== 'captured' || !occurrence.checking.selected) throw new Error('Missing actual selected component');
      const selected = occurrence.checking.selected, result = compile(selected, 'term', occurrence.captureId);
      return { selected, result, doc: verify(selected, result) };
    };
    const original = read('unfamiliar ordered composition'), renamed = read('renamed ordered composition');
    expect(original.selected.term).toEqual(app(b(2), app(b(3), b(1))));
    for (const { result, doc } of [original, renamed]) {
      const context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
      const resolve = (index: number) => doc.objects.find(object => object.binder?.id === context[context.length - index - 1].id)!.id;
      expect(doc.relations).toHaveLength(2);
      const inner = doc.relations.find(relation => portId(relation, 'function') === resolve(3))!;
      const outer = doc.relations.find(relation => portId(relation, 'function') === resolve(2))!;
      expect(portId(inner, 'input 1')).toBe(resolve(1));
      expect(portId(outer, 'input 1')).toBe(portId(inner, 'output'));
      expect(inner.ports.map(port => port.role)).toEqual(['function', 'input 1', 'output']);
      expect(outer.ports.map(port => port.role)).toEqual(['function', 'input 1', 'output']);
    }
    expect(topology(original.result)).toEqual(topology(renamed.result));
    const dependent = read('dependent function type root'), proposition = read('proposition valued function type root');
    for (const { result, doc } of [dependent, proposition]) {
      const target = nodes(doc.tree).find(node => node.id === result.targetNodeId)!;
      expect(target.kind).toBe('parameter'); expect(target.binder!.role).toBe('parameter');
      expect(compileReading(doc).nodes.map(node => node.phrase).join(' ')).not.toMatch(/for every|universal|assume|conclusion|conditions hold/i);
    }
    const dependentTarget = nodes(dependent.doc.tree).find(node => node.id === dependent.result.targetNodeId)!;
    expect(dependentTarget.children[0].binder!.dependsOn).toEqual([dependentTarget.binder!.id]);
    const proof = read('proof term remains selected term');
    expect(proof.selected.term).toEqual(b(0)); expect(proof.selected.type).toEqual(b(1));
    const target = nodes(proof.doc.tree).find(node => node.id === proof.result.targetNodeId)!;
    expect(target.expression).toMatchObject({ kind: 'var', id: nodes(proof.doc.tree).find(node => node.id === proof.result.contextNodeIds.at(-1))!.binder!.id });
    expect(proof.result.sourceById[target.id].syntax).toEqual(proof.selected.term);
  });
});


it('associates a derived positional pair with exposure provenance and its actual fields', () => {
  const input = composition(), sourcePath = ['checking', 'exposure', 'result'];
  const result = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'fresh-derived-control', sourcePath, sourceOrigin: 'definition-head-exposure' });
  const doc = document(result);
  expect(result.sourceById[result.targetNodeId!].path).toEqual([...sourcePath, 'term']);
  expect(result.sourceById[result.targetNodeId!].syntax).toEqual(input.term);
  expect(doc.objects.flatMap(object => object.provenance).every(p => p.origin === 'definition-head-exposure')).toBe(true);
  expect(doc.relations.every(relation => relation.provenance.origin === 'definition-head-exposure')).toBe(true);
  expect(doc.scenes).toEqual([]);
  for (const sourceOrigin of [null, 'kernel-certified', 'imported-packet']) {
    const invalid = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'invalid-origin', sourceOrigin } as never);
    expect(invalid.document).toBeUndefined(); expect(Object.keys(invalid.sourceById)).toEqual([]);
  }
});


/** Recorded kinds change presentation only. The oracle below still walks the
 * original CTel/Core constructors, independently of roles and choices. */
function verifyRecordedContext(input: PositionalStructuralInput, result: PositionalComponentReading, root = base) {
  const doc = document(result), oracle = sourceOracle(input, root), all = nodes(doc.tree);
  expect(result.contextNodeIds).toHaveLength(input.home.arity);
  for (const [id, source] of Object.entries(result.sourceById)) {
    const expected = oracle.located.get(key(source.path));
    expect(expected, id).toBeDefined();
    expect(key(source.syntax), id).toBe(key(expected!.syntax));
    expect(source.scopeBinderIds.map(binderId => result.sourceById[binderId]?.path), id).toEqual(expected!.scope);
  }
  result.contextNodeIds.forEach((id, index) => {
    const node = all.find(node => node.id === id)!;
    expect(result.sourceById[id].path).toEqual(oracle.context[index]);
    expect(result.sourceById[node.binder!.id].path).toEqual(oracle.context[index]);
  });
  for (const node of all) if (node.binder) {
    const source = result.sourceById[node.binder.id], raw = source.syntax as JsonValue[];
    const ambient = result.contextNodeIds.includes(node.id);
    const references = outerReferences(raw[ambient ? raw[0] === 'port' ? 3 : 4 : 2]);
    if (raw[0] === 'letE') outerReferences(raw[ambient ? 5 : 3], 0, references);
    // Exact binder dependencies retain neutral entries too; only the ordinary
    // choice list is filtered. Do not weaken this to the displayed list.
    expect(node.binder.dependsOn).toEqual(source.scopeBinderIds.filter((_, i, scope) => references.has(scope.length - i - 1)));
  }
  for (const object of doc.objects) if (object.expression.kind === 'var') {
    const source = result.sourceById[object.id], raw = source.syntax as JsonValue[];
    if (raw[0] === 'bvar') expect(object.expression.id).toBe(source.scopeBinderIds[source.scopeBinderIds.length - Number((raw[1] as JsonValue[])[1]) - 1]);
  }
  const structure = buildPositionalStructuralDrawing(input, { sourceIdentity: 'recorded-kind-oracle', sourcePath: root });
  expect(structure.ok).toBe(true);
  if (structure.ok) expect(readPositionalStructuralDrawing(structure.value)).toEqual({ ok: true, value: input });
  return doc;
}

describe('positional recorded declaration kinds', () => {
  it.each(['null', 'object', 'string', 'bare kind', 'unknown kind', 'null item', 'sparse', 'extra', 'hidden', 'symbol', 'accessor item', 'prototype', 'accessor option',
    'item without name', 'item extra key', 'item accessor', 'item prototype', 'item hidden', 'oversized', 'huge sparse',
    'name accessor', 'name function', 'name symbol', 'name non-finite number', 'name prototype'])(
    'refuses %s metadata without evaluating accessors or retaining partial presentation', mutation => {
      const input = { home: { arity: 1, telescope: port(['nil'], 'x', c('Nat')) }, term: b(0), type: c('Nat') };
      const entry = (): Record<string, unknown> => ({ name: name('x'), kind: 'auxDecl' });
      let metadata: unknown = [entry()], evaluated = false;
      const item = (metadata as Record<string, unknown>[])[0]!;
      const options: Record<string, unknown> = { target: 'term', sourceIdentity: 'kind-validation' };
      switch (mutation) {
        case 'null': metadata = null; break;
        case 'object': metadata = { 0: entry(), length: 1 }; break;
        case 'string': metadata = 'auxDecl'; break;
        case 'bare kind': metadata = ['auxDecl']; break;
        case 'unknown kind': item.kind = 'hypothesis'; break;
        case 'null item': metadata = [null]; break;
        case 'sparse': metadata = Array(1); break;
        case 'extra': Object.assign(metadata as object, { extra: entry() }); break;
        case 'hidden': Object.defineProperty(metadata, '0', { value: entry(), enumerable: false }); break;
        case 'symbol': Object.assign(metadata as object, { [Symbol('extra')]: entry() }); break;
        case 'accessor item': Object.defineProperty(metadata, '0', { enumerable: true, get() { evaluated = true; return entry(); } }); break;
        case 'prototype': Object.setPrototypeOf(metadata, null); break;
        case 'item without name': delete item.name; break;
        case 'item extra key': item.role = 'parameter'; break;
        case 'item accessor': Object.defineProperty(item, 'kind', { enumerable: true, get() { evaluated = true; return 'auxDecl'; } }); break;
        case 'item prototype': Object.setPrototypeOf(item, { inherited: true }); break;
        case 'item hidden': Object.defineProperty(item, 'kind', { value: 'auxDecl', enumerable: false }); break;
        case 'oversized': metadata = Array.from({ length: 129 }, entry); break;
        case 'huge sparse': metadata = Array(2 ** 31); break;
        case 'name accessor': { const part: Record<string, unknown> = {}; Object.defineProperty(part, 'text', { enumerable: true, get() { evaluated = true; return 'x'; } }); item.name = ['str', ['anonymous'], part]; break; }
        case 'name function': item.name = ['str', ['anonymous'], () => 'x']; break;
        case 'name symbol': item.name = Object.assign(['str', ['anonymous'], 'x'], { [Symbol('extra')]: 1 }); break;
        case 'name non-finite number': item.name = ['num', ['anonymous'], Number.POSITIVE_INFINITY]; break;
        case 'name prototype': item.name = Object.setPrototypeOf(['str', ['anonymous'], 'x'], null); break;
      }
      if (mutation === 'accessor option') Object.defineProperty(options, 'recordedContext', { enumerable: true, get() { evaluated = true; return metadata; } });
      else options.recordedContext = metadata;
      const result = compilePositionalComponent(input, options as never);
      expect(evaluated).toBe(false); expect(result.document).toBeUndefined(); expect(result.reason).toBeTruthy();
      expect(result.contextNodeIds).toEqual([]); expect(result.targetNodeId).toBeUndefined(); expect(Object.keys(result.sourceById)).toEqual([]);
    });

  it('accepts a frozen dense prefix, leaves later entered entries unclassified, and does not retain mutable metadata', () => {
    const input = { home: { arity: 2, telescope: port(port(['nil'], '__h', c('Nat')), '__h', c('Nat')) }, term: b(0), type: c('Nat') };
    const metadata: RecordedContextDeclaration[] = [{ name: name('__h'), kind: 'auxDecl' }];
    const result = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'prefix-kinds', recordedContext: metadata });
    const before = JSON.stringify(result), doc = verifyRecordedContext(input, result);
    const context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
    expect(context.map(binder => [binder.role, binder.declarationKind])).toEqual([['auxiliary', 'auxDecl'], ['parameter', undefined]]);
    metadata[0] = { name: name('__h'), kind: 'default' }; metadata.push({ name: name('__h'), kind: 'auxDecl' });
    expect(JSON.stringify(result)).toBe(before);
    const frozen = compilePositionalComponent(input, { target: 'type', sourceIdentity: 'frozen-kinds', recordedContext: Object.freeze([Object.freeze({ name: name('__h'), kind: 'auxDecl' as const })]) });
    verifyRecordedContext(input, frozen);
    for (const kinds of [undefined, [], ['default', 'default']] as const) {
      const ordinary = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'ordinary-kinds', ...(kinds === undefined ? {} : { recordedContext: kinds.map(kind => ({ name: name('__h'), kind })) }) });
      const ordinaryDoc = document(ordinary);
      expect(ordinary.contextNodeIds.map(id => nodes(ordinaryDoc.tree).find(node => node.id === id)!.binder!.role)).toEqual(['parameter', 'parameter']);
      expect(ordinaryDoc.choices).toHaveLength(2);
    }
  });

  it.each((['auxDecl', 'implDetail'] as const).flatMap(kind => [
    { kind, shape: 'port' as const, nondep: false },
    { kind, shape: 'let' as const, nondep: false },
    { kind, shape: 'let' as const, nondep: true },
  ]))('keeps exact $kind $shape entries and nondep=$nondep while filtering ordinary choices', ({ kind, shape, nondep }) => {
    const first = port(['nil'], 'Owner', sort);
    const neutral: JsonValue = shape === 'port' ? port(first, '__h', b(0)) : ['letE', first, name('__h'), nondep, b(0), b(0)];
    const input = { home: { arity: 3, telescope: port(neutral, 'dependent', b(0)) }, term: app(c('consume'), b(1), b(0)), type: b(2) };
    const before = key(input);
    for (const target of ['term', 'type'] as const) {
      const result = compilePositionalComponent(input, { target, sourceIdentity: 'neutral-record', recordedContext: [{ name: name('Owner'), kind: 'default' }, { name: name('__h'), kind }] });
      const doc = verifyRecordedContext(input, result), all = nodes(doc.tree);
      const context = result.contextNodeIds.map(id => all.find(node => node.id === id)!);
      const [owner, recorded, dependent] = context.map(node => node.binder!);
      expect(context.map(node => node.kind)).toEqual(['parameter', 'auxiliary', 'parameter']);
      expect(recorded).toMatchObject({ role: 'auxiliary', declarationKind: kind, name: '__h', dependsOn: [owner.id] });
      expect(context[1].label).toBe(`${kind === 'auxDecl' ? 'Auxiliary' : 'Context'} entry __h, recorded kind ${kind}`);
      expect(recorded.definition?.nondep).toBe(shape === 'let' ? nondep : undefined);
      if (shape === 'let') expect(recorded.definition!.value).toMatchObject({ kind: 'var', id: owner.id });
      expect(dependent.dependsOn).toEqual([recorded.id]);
      const objectId = (id: string) => doc.objects.find(object => object.binder?.id === id)!.id;
      expect(doc.choices.map(choice => choice.binderId)).toEqual([owner.id, dependent.id]);
      expect(doc.choices.map(choice => choice.availableObjectIds)).toEqual([[], [objectId(owner.id)]]);
      expect(doc.choices.map(choice => choice.dependsOn)).toEqual([[], []]);
      expect(result.sourceById[result.targetNodeId!].scopeBinderIds).toEqual([owner.id, recorded.id, dependent.id]);
      expect(doc.scopes.find(scope => scope.nodeId === result.targetNodeId)!.objectIds).toEqual(context.map(node => objectId(node.binder!.id)));
      expect(result.sourceById[result.targetNodeId!].syntax).toEqual(input[target]);
      const ordinary = compilePositionalComponent(input, { target, sourceIdentity: 'neutral-record' });
      expect(result.sourceById).toEqual(ordinary.sourceById);
      expect(result.contextNodeIds).toEqual(ordinary.contextNodeIds);
      expect(doc.objects.map(object => [object.id, object.expression.exactIdentity])).toEqual(document(ordinary).objects.map(object => [object.id, object.expression.exactIdentity]));
    }
    expect(key(input)).toBe(before);
  });

  it('excludes neutral entries from an existential candidate list without removing its positional scope', () => {
    const exists: JsonValue = ['const', name('Exists'), [['succ', ['zero']]]];
    const input = { home: { arity: 2, telescope: port(port(['nil'], 'recorded', c('Nat')), 'ordinary', c('Nat')) },
      term: app(exists, c('Nat'), lam(c('Nat'), c('True'), 'candidate')), type: ['sort', ['zero']] as JsonValue };
    const result = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'candidate-context', recordedContext: [{ name: name('recorded'), kind: 'implDetail' }, { name: name('ordinary'), kind: 'default' }], logicalRoot: { form: 'exists' } });
    const doc = verifyRecordedContext(input, result), all = nodes(doc.tree);
    const [neutral, ordinary] = result.contextNodeIds.map(id => all.find(node => node.id === id)!.binder!);
    const candidate = doc.choices.find(choice => choice.role === 'existential')!;
    const ordinaryId = doc.objects.find(object => object.binder?.id === ordinary.id)!.id;
    expect(candidate).toBeDefined(); expect(candidate.availableObjectIds).toEqual([ordinaryId]); expect(candidate.dependsOn).toEqual([ordinaryId]);
    expect(result.sourceById[candidate.binderId].scopeBinderIds).toEqual([neutral.id, ordinary.id]);
  });

  it('allocates ordinary duplicate names before neutral names while references retain their exact positions', () => {
    let telescope = port(['nil'], '_example', c('Nat'));
    for (let i = 0; i < 3; i++) telescope = port(telescope, '_example', c('Nat'));
    const input = { home: { arity: 4, telescope }, term: app(c('use'), b(3), b(2), b(1), b(0)), type: c('Nat') };
    const result = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'same-names', recordedContext: (['auxDecl', 'default', 'default', 'implDetail'] as const).map(kind => ({ name: name('_example'), kind })) });
    const doc = verifyRecordedContext(input, result), context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
    expect(context.map(binder => binder.name)).toEqual(['_example@3', '_example', '_example@2', '_example@4']);
    expect(new Set(context.map(binder => binder.id)).size).toBe(4);
    expect(doc.choices.map(choice => choice.binderId)).toEqual([context[1].id, context[2].id]);
    const selected = nodes(doc.tree).find(node => node.id === result.targetNodeId)!.expression;
    expect(selected.kind).toBe('app');
    if (selected.kind === 'app') expect(selected.args.map(arg => arg.kind === 'var' ? [arg.id, arg.name] : null)).toEqual(context.map(binder => [binder.id, binder.name]));
    for (const id of result.contextNodeIds) expect((result.sourceById[id].syntax as JsonValue[])[2]).toEqual({ name: name('_example'), info: 'default' });
  });

  it('threads recorded kinds through all three adapters without treating later home entries as captured declarations', () => {
    const input = { home: { arity: 2, telescope: port(port(['nil'], '__h', c('Nat')), 'entered', c('Nat')) }, term: b(0), type: c('Nat') };
    const binding = { context: { originalDeclarations: [{ userName: name('__h'), kind: 'implDetail' }] } };
    // Adapter-shaped constructions isolate transport; these are not native
    // captures and no validator acceptance is claimed for the partial records.
    const occurrence = { captureId: 'adapter-occurrence', path: [], checking: { status: 'captured', selected: input, binding } } as unknown as SourceOccurrence;
    const exposure = { captureId: 'adapter-exposure', target: 'term', checking: { status: 'captured', exposure: { status: 'candidate', result: input }, binding } } as unknown as SourceHeadExposure;
    const decomposition = { captureId: 'adapter-decomposition', checking: { status: 'captured', steps: [{ output: { status: 'candidate', result: input } }], binding } } as unknown as SourceDecomposition;
    const results = [sourceOccurrenceReading(occurrence, 'term')!, sourceOccurrenceReading(occurrence, 'type')!, headExposureReading(exposure)!,
      decompositionReading(decomposition, 0, 'term', null)!, decompositionReading(decomposition, 0, 'type', null)!];
    for (const result of results) {
      const doc = document(result), context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
      expect(context.map(binder => [binder.role, binder.declarationKind])).toEqual([['auxiliary', 'implDetail'], ['parameter', undefined]]);
      expect(doc.choices.map(choice => choice.binderId)).toEqual([context[1].id]);
      expect(result.sourceById[result.targetNodeId!].scopeBinderIds).toEqual(context.map(binder => binder.id));
      expect(result.sourceById[result.targetNodeId!].syntax).toEqual(input[result.target]);
    }
  });
});

describe('alignment of recorded context declarations', () => {
  // Owner (port), __h (port), dependent (port); the dependent entry is entered later and has no record.
  const input = { home: { arity: 3, telescope: port(port(port(['nil'], 'Owner', sort), '__h', b(0)), 'dependent', b(0)) }, term: app(c('consume'), b(1), b(0)), type: b(2) };
  const record = (text: string, kind: RecordedContextDeclaration['kind']): RecordedContextDeclaration => ({ name: name(text), kind });
  const context = (result: PositionalComponentReading) => { const doc = document(result); return result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!); };

  it.each([
    ['a renamed record', [record('Other', 'default'), record('__h', 'auxDecl')]],
    ['swapped records', [record('__h', 'auxDecl'), record('Owner', 'default')]],
    ['one record too many', [record('Owner', 'default'), record('__h', 'auxDecl'), record('dependent', 'default'), record('later', 'default')]],
  ] as const)('reads every context entry neutrally for %s, never by constructor or kind', (_, recorded) => {
    for (const target of ['term', 'type'] as const) {
      const result = compilePositionalComponent(input, { target, sourceIdentity: 'unaligned-record', recordedContext: recorded });
      const doc = verifyRecordedContext(input, result), entries = context(result);
      expect(entries.map(node => [node.kind, node.binder!.role, node.binder!.declarationKind])).toEqual(Array(3).fill(['auxiliary', 'auxiliary', undefined]));
      expect(entries.map(node => node.label)).toEqual(['Owner', '__h', 'dependent'].map(text => `Context entry ${text}, recorded kind unavailable`));
      expect(doc.choices).toEqual([]);
      expect(result.sourceById[result.targetNodeId!].syntax).toEqual(input[target]);
      expect(result.recordedKindsUnmatched).toBe(true);
    }
  });

  it('marks and shows only a reading whose recorded kinds could not be matched', () => {
    const pane = (result: PositionalComponentReading) => renderToStaticMarkup(createElement(PositionalReadingPane, { model: result, title: 'Selected term' }));
    for (const recorded of [undefined, [], [record('Owner', 'default'), record('__h', 'auxDecl')], [record('Owner', 'implDetail')]] as const) {
      const result = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'matched-record', ...(recorded ? { recordedContext: recorded } : {}) });
      expect(result.recordedKindsUnmatched).toBeUndefined();
      expect(pane(result)).not.toContain(UNMATCHED_RECORDED_KINDS);
    }
    const unmatched = compilePositionalComponent(input, { target: 'term', sourceIdentity: 'unmatched-record', recordedContext: [record('__h', 'auxDecl')] });
    const html = pane(unmatched);
    expect(html.split(UNMATCHED_RECORDED_KINDS)).toHaveLength(2);
    expect(html).toContain(`<p class="snapshot-unavailable" data-recorded-kinds-unmatched="">${UNMATCHED_RECORDED_KINDS}</p>`);
  });

  it('follows the same rule as the structural presentation: kinds on aligned names only, otherwise neutral', () => {
    const drawn = buildPositionalStructuralDrawing(input, { sourceIdentity: 'one-rule', sourcePath: base });
    if (!drawn.ok) throw new Error(drawn.error.message);
    for (const recorded of [[record('Owner', 'default'), record('__h', 'auxDecl')], [record('Owner', 'implDetail')], [record('__h', 'auxDecl')], [record('Owner', 'default'), record('__h', 'auxDecl'), record('dependent', 'default'), record('later', 'default')]]) {
      const guided = context(compilePositionalComponent(input, { target: 'term', sourceIdentity: 'one-rule', recordedContext: recorded }));
      const headings = recordedContextHeadings(drawn.value, recorded)!;
      guided.forEach((node, index) => {
        const heading = headings[index];
        if (heading === 'Context entry') expect(node.label).toMatch(/^Context entry .+, recorded kind unavailable$/);
        else if (heading === undefined) expect(node.binder!.role).toBe('parameter');
        else expect(node.label.replace(` ${node.binder!.name},`, ',')).toBe(heading);
      });
    }
  });
});

it.runIf(!!process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES)('preserves the real default variable when its name matches the auxiliary entry in both adapters', () => {
  const rows = JSON.parse(readFileSync(process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES!, 'utf8'));
  const row = rows.filter((candidate: { label: string }) => candidate.label === 'variable named like the auxiliary entry').at(-1);
  expect(row).toBeDefined();
  const snapshot = validateSourceSnapshot(row.parent.snapshot), occurrence = validateSourceOccurrence(row.parent.occurrence, snapshot);
  const history = validateDecompositionHistory({ snapshot, occurrence, seed: row.seed,
    attempts: row.priorAttempts.map((attempt: { snapshot: unknown; record: unknown }) => ({ snapshot: attempt.snapshot, record: attempt.record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, validateSourceSnapshot(row.response.sourceSnapshot), history);
  const original = sourceOccurrenceReading(occurrence, 'term')!, derived = decompositionReading(record, record.operations.length - 1, 'term', null)!;
  for (const result of [original, derived]) {
    const doc = document(result), context = result.contextNodeIds.map(id => nodes(doc.tree).find(node => node.id === id)!.binder!);
    expect(context.map(binder => [binder.name, binder.role, binder.declarationKind])).toEqual([
      ['_example@2', 'auxiliary', 'auxDecl'], ['_example', 'parameter', undefined],
    ]);
    expect(doc.choices.map(choice => choice.binderId)).toEqual([context[1].id]);
    expect(result.sourceById[result.targetNodeId!].scopeBinderIds).toEqual(context.map(binder => binder.id));
  }
  expect(original.sourceById[original.targetNodeId!].syntax).toEqual(['bvar', ['nat', '0']]);
  expect(nodes(original.document!.tree).find(node => node.id === original.targetNodeId)!.expression).toMatchObject({ kind: 'var', name: '_example' });
});
