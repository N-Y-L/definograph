import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Expr } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { compileGraphConstraint } from './model';
import { GraphConstraintFigure } from './GraphConstraintFigure';

const constant = (name: string, canonical = true): Expr => ({ kind: 'const', name, canonical });
const literal = (value: number | string): Expr => ({ kind: 'literal', value });
const fin = (value: Expr, canonical = true): Expr => ({ kind: 'app', fn: constant('Fin', canonical), args: [value], argumentKinds: ['value'] });
const variable = (id: string): Expr => ({ kind: 'var', id, name: id, type: 'abstract type' });
const object = (id: string, expression = variable(id), label = id): SemanticObject => ({ id, kind: 'variable', expression, label, type: 'abstract type', scopeId: 'scope:clause', provenance: [{ nodeId: 'clause', expressionPath: id, origin: 'elaborated-expression' }] });
function fixture(kind: SemanticRelation['kind'], ports: readonly (readonly [string, SemanticObject])[], extra: Partial<SemanticRelation> = {}) {
  const relation: SemanticRelation = { id: 'relation:clause:graph', kind, label: kind, expression: { kind: 'app', fn: constant('known.constructor'), args: ports.map(([, object]) => object.expression) }, scopeId: 'scope:clause', nodeId: 'clause', pluginId: 'simple-graphs', fidelity: 'symbolic', provenance: { nodeId: 'clause', expressionPath: 'expression', origin: 'elaborated-expression' }, conditions: [], ports: ports.map(([role, object]) => ({ role, objectId: object.id })), ...extra };
  const document: SemanticDocument = { schemaVersion: '1.0.0', prover: 'lean', source: 'fixture', tree: { id: 'clause', kind: 'predicate', lean: 'fixture', label: 'fixture', expression: relation.expression, children: [] }, objects: [...new Map(ports.map(([, object]) => [object.id, object])).values()], relations: [relation], scopes: [{ id: 'scope:clause', nodeId: 'clause', kind: 'predicate', label: 'fixture', objectIds: ports.map(([, object]) => object.id), assumptionNodeIds: ['premise'], context: ['Inside a negation'] }], choices: [], opaqueRegions: [], coverage: [], scenes: [], diagnostics: [] };
  return { document, relation };
}
const coloring = (count: Expr = literal(4), finite = true) => fixture('graph-coloring', [['graph', object('G')], ['coloring', object('c')], ['colors', object('C', finite ? fin(count) : count)]]);
const colorable = (count: Expr) => fixture('graph-colorable', [['graph', object('G')], ['color bound', object('n', count)]]);
const html = (result: ReturnType<typeof fixture>) => renderToStaticMarkup(createElement(GraphConstraintFigure, result));

describe('graph constraint model', () => {
  it('retains adjacency endpoints by exact identity, independently of their display names', () => {
    const result = fixture('graph-adjacency', [['graph', object('G')], ['left vertex', object('a', variable('a'), 'v')], ['right vertex', object('b', variable('b'), 'v')]]);
    const model = compileGraphConstraint(result.document, result.relation)!;
    expect(model.kind).toBe('adjacency');
    expect(model.endpoints.map(endpoint => endpoint.id)).toEqual(['a', 'b']);
    expect(model.sameEndpoint).toBe(false);
    expect(model.scopeId).toBe('scope:clause');
    expect(model.relation).toBe(result.relation);
    expect(model.endpoints.every(endpoint => endpoint.role === 'source-object')).toBe(true);
    const rendered = html(result);
    expect(rendered).toContain('data-reading-object="a"');
    expect(rendered).toContain('data-reading-object="b"');
    expect(rendered).toContain('does not specify the full graph');
  });

  it('does not split the same named vertex into two distinct drawn objects', () => {
    const vertex = object('v');
    const result = fixture('graph-adjacency', [['graph', object('G')], ['left vertex', vertex], ['right vertex', vertex]]);
    expect(compileGraphConstraint(result.document, result.relation)!.sameEndpoint).toBe(true);
    expect((html(result).match(/data-graph-endpoint=/g) ?? []).length).toBe(1);
    expect(html(result)).toContain('same vertex occurs at both endpoints');
  });

  it('represents colorability with formal endpoint slots and no fabricated coloring', () => {
    const result = colorable(literal(4)), model = compileGraphConstraint(result.document, result.relation)!;
    expect(model.coloring).toBeUndefined();
    expect(model.application).toBeUndefined();
    expect(model.endpoints.every(endpoint => endpoint.role === 'arbitrary-slot' && !endpoint.object)).toBe(true);
    expect(model.palette).toMatchObject({ kind: 'finite', count: '4', labels: ['0', '1', '2', '3'] });
    const rendered = html(result);
    expect(rendered).toContain('no witness is selected');
    expect(rendered).toContain('A coloring may use fewer labels');
    expect(rendered).not.toMatch(/data-reading-object="slot:/);
  });

  it('handles zero colors through emptiness and vacuity rather than fabricated vertex assignments', () => {
    const result = colorable(literal(0)), model = compileGraphConstraint(result.document, result.relation)!;
    expect(model.palette).toMatchObject({ count: '0', labels: [] });
    expect(model.explanation).toContain('only if the vertex type is empty');
    const rendered = html(result);
    expect(rendered).toContain('edge rule is vacuous');
    expect(rendered).toContain('Empty vertex type required');
    expect(rendered).not.toContain('data-graph-endpoint=');
    expect(rendered).not.toContain('data-palette-label=');
    expect(html(coloring(literal(0)))).toContain('has an empty vertex type');
  });

  it('does not confuse a one-color bound with one vertex or a chosen graph', () => {
    const rendered = html(colorable(literal(1)));
    expect(rendered).toContain('requires no edges');
    expect(rendered).toContain('does not require a single vertex');
    expect((rendered.match(/data-palette-label=/g) ?? []).length).toBe(1);
  });

  it('bounds palette display while retaining a huge exact symbolic count', () => {
    const result = colorable(literal('1000000000000000000000000000000'));
    const model = compileGraphConstraint(result.document, result.relation)!;
    expect(model.palette!.count).toBe('1000000000000000000000000000000');
    expect(model.palette!.labels).toHaveLength(8);
    expect(model.palette!.omittedCount).toBe('999999999999999999999999999992');
    const rendered = html(result);
    expect((rendered.match(/data-palette-label=/g) ?? []).length).toBe(8);
    expect(rendered).toContain('further labels');
  });

  it.each([variable('n'), literal(-1), literal(1.5), literal(Number.MAX_SAFE_INTEGER + 1), literal('1e3'), literal('9'.repeat(129))])('does not invent a finite palette from an unevaluated or unsuitable bound %#', bound => {
    const result = colorable(bound);
    expect(compileGraphConstraint(result.document, result.relation)!.palette!.kind).toBe('symbolic');
    expect(html(result)).not.toContain('data-palette-label=');
  });

  it('requires trusted Fin structure and ignores cardinality-looking display names', () => {
    const plain = coloring(variable('C'), false);
    const objects = plain.document.objects.map(object => object.id === 'C' ? { ...object, label: 'Fin 4', type: 'Fin 4' } : object);
    expect(compileGraphConstraint({ ...plain.document, objects }, plain.relation)!.palette!.kind).toBe('symbolic');
    const foreign = fixture('graph-coloring', [['graph', object('G')], ['coloring', object('c')], ['colors', object('C', fin(literal(4), false))]]);
    expect(compileGraphConstraint(foreign.document, foreign.relation)!.palette!.kind).toBe('symbolic');
    const incomplete = coloring({ kind: 'app', fn: constant('Fin'), args: [] }, false);
    expect(compileGraphConstraint(incomplete.document, incomplete.relation)!.palette!.kind).toBe('symbolic');
    const unaudited = coloring({ kind: 'app', fn: { kind: 'const', name: 'Fin' }, args: [literal(4)] }, false);
    expect(compileGraphConstraint(unaudited.document, unaudited.relation)!.palette!.kind).toBe('symbolic');
  });

  it('retains the actual coloring application without choosing an output color', () => {
    const base = coloring();
    const result = fixture('graph-coloring', [...base.relation.ports.map(port => [port.role, base.document.objects.find(object => object.id === port.objectId)!] as const), ['vertex', object('u')], ['color', object('c(u)', { kind: 'opaque', text: 'source application' })]]);
    const model = compileGraphConstraint(result.document, result.relation)!;
    expect(model.coloring!.id).toBe('c');
    expect(model.application).toMatchObject({ vertex: { id: 'u' }, value: { id: 'c(u)' } });
    expect(html(result)).toContain('data-reading-object="c(u)"');
    expect(html(result)).toContain('not colors assigned to the displayed endpoint slots');
  });

  it('distinguishes graph homomorphisms from embeddings and preserves actual application ports', () => {
    const ports: [string, SemanticObject][] = [['source graph', object('G')], ['target graph', object('H')], ['map', object('f')], ['source vertex', object('u')], ['target vertex', object('fu')]];
    const hom = fixture('graph-map', ports, { graphMapKind: 'homomorphism' });
    const embedding = fixture('graph-map', ports, { graphMapKind: 'embedding' });
    expect(compileGraphConstraint(hom.document, hom.relation)!.application?.value.id).toBe('fu');
    expect(html(hom)).toContain('injectivity is not required');
    expect(html(hom)).not.toContain('if and only if');
    expect(html(embedding)).toContain('if and only if');
    expect(html(embedding)).toContain('distinct vertices have distinct images');
    expect(html(embedding)).not.toContain('surjective');
    const unspecified = fixture('graph-map', ports);
    expect(compileGraphConstraint(unspecified.document, unspecified.relation)!.mapKind).toBeUndefined();
    expect(html(unspecified)).not.toContain('injectivity is not required');
  });

  it('never associates a relation from a sibling source or local expression scope', () => {
    const result = coloring();
    const local = { ...result.relation, id: 'local', scopeId: 'scope:lambda' };
    const sibling = { ...result.relation, id: 'sibling', nodeId: 'other' };
    const related = { ...result.relation, id: 'related' };
    expect(compileGraphConstraint(result.document, result.relation, [local, sibling, related])!.relatedRelationIds).toEqual(['related']);
    expect(compileGraphConstraint(result.document, local)).toBeUndefined();
  });

  it('refuses a bound coloring object that is unavailable in the relation scope', () => {
    const result = coloring();
    const objects = result.document.objects.map(object => object.id === 'c' ? { ...object, binder: { id: 'c', name: 'c', type: 'G.Coloring C', role: 'universal' as const, dependsOn: [] } } : object);
    const scopes = result.document.scopes.map(scope => ({ ...scope, objectIds: scope.objectIds.filter(id => id !== 'c') }));
    expect(compileGraphConstraint({ ...result.document, objects, scopes }, result.relation)).toBeUndefined();
  });

  it('reports capped related stages without changing the source condition', () => {
    const result = coloring();
    const relations = Array.from({ length: 60 }, (_, index) => ({ ...result.relation, id: `related:${index}` }));
    const model = compileGraphConstraint(result.document, result.relation, relations)!;
    expect(model.relatedRelationIds).toHaveLength(48);
    expect(model.omittedRelatedRelationCount).toBe(12);
    expect(model.relation).toBe(result.relation);
  });

  it('refuses missing, duplicate, or incomplete graph ports and unsupported meaning', () => {
    const result = coloring();
    expect(compileGraphConstraint(result.document, { ...result.relation, ports: result.relation.ports.filter(port => port.role !== 'colors') })).toBeUndefined();
    expect(compileGraphConstraint(result.document, { ...result.relation, ports: [...result.relation.ports, result.relation.ports[0]] })).toBeUndefined();
    expect(compileGraphConstraint(result.document, { ...result.relation, ports: [...result.relation.ports, { role: 'vertex', objectId: 'c' }] })).toBeUndefined();
    expect(compileGraphConstraint(result.document, { ...result.relation, ports: [...result.relation.ports, { role: 'vertex', objectId: 'missing-v' }, { role: 'color', objectId: 'missing-c' }] })).toBeUndefined();
    expect(compileGraphConstraint(result.document, { ...result.relation, fidelity: 'structural' })).toBeUndefined();
    expect(compileGraphConstraint(result.document, { ...result.relation, expression: { kind: 'app', fn: constant('SimpleGraph.Coloring', false), args: [] } })).toBeUndefined();
    expect(compileGraphConstraint({ ...result.document, scopes: [] }, result.relation)).toBeUndefined();
  });

  it('is deterministic and does not mutate source identities, scopes, or relation metadata', () => {
    const result = coloring();
    const before = JSON.stringify(result);
    const first = compileGraphConstraint(result.document, result.relation);
    expect(compileGraphConstraint(result.document, result.relation)).toEqual(first);
    expect(JSON.stringify(result)).toBe(before);
    const renamed = { ...result.document, objects: result.document.objects.map(object => ({ ...object, label: `renamed ${object.label}` })) };
    const second = compileGraphConstraint(renamed, result.relation)!;
    expect(second.endpoints.map(endpoint => endpoint.id)).toEqual(first!.endpoints.map(endpoint => endpoint.id));
    expect(second.graph.id).toBe(first!.graph.id);
    expect(second.coloring!.id).toBe(first!.coloring!.id);
  });

  it('renders object controls with identity, keyboard affordances, and preserved scope', () => {
    const result = fixture('graph-adjacency', [['graph', object('G')], ['left vertex', object('u')], ['right vertex', object('v')]]);
    const rendered = renderToStaticMarkup(createElement(GraphConstraintFigure, { ...result, selectedObjectId: 'u', onObjectSelect: () => undefined }));
    expect(rendered).toContain('data-graph-scope="scope:clause"');
    expect(rendered).toContain('role="button"');
    expect(rendered).toContain('tabindex="0"');
    expect(rendered).toContain('aria-pressed="true"');
    expect(rendered).not.toContain('type="range"');
    expect(rendered).not.toContain('type="number"');
  });
});
