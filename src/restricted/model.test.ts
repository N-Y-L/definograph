import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Expr } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';
import { compileRestrictedMap, type RestrictedMapStructure } from './model';
import { RestrictedMapFigure, RestrictedRegionDiagram, RestrictedRoundTrips } from './RestrictedMapFigure';

const constant = (name: string, canonical = true): Expr => ({ kind: 'const', name, canonical });
const variable = (id: string): Expr => ({ kind: 'var', id, name: id, type: 'abstract type' });
const object = (id: string, expression = variable(id), label = id): SemanticObject => ({ id, kind: 'variable', label, expression, type: 'abstract type', scopeId: 'scope:clause', provenance: [{ nodeId: 'clause', expressionPath: id, origin: 'elaborated-expression' }] });
const base = (): [string, SemanticObject][] => [['map', object('e')], ['source carrier', object('M')], ['target carrier', object('N')]];
function fixture(kind: SemanticRelation['kind'] = 'restricted-equivalence', ports: readonly (readonly [string, SemanticObject])[] = base(), extra: Partial<SemanticRelation> = {}) {
  const relation: SemanticRelation = { id: 'relation:clause:restricted', kind, expression: { kind: 'app', fn: constant('PartialEquiv'), args: [variable('M'), variable('N')] }, label: 'fixture', scopeId: 'scope:clause', nodeId: 'clause', pluginId: 'restricted-maps', fidelity: 'symbolic', provenance: { nodeId: 'clause', expressionPath: 'expression', origin: 'elaborated-expression' }, conditions: [], ports: ports.map(([role, object]) => ({ role, objectId: object.id })), restrictedMapKind: 'partial-equivalence', restrictedDirection: 'forward', ...extra };
  const document: SemanticDocument = { schemaVersion: '1.0.0', prover: 'lean', source: 'fixture', tree: { id: 'clause', kind: 'predicate', lean: 'fixture', label: 'fixture', expression: relation.expression, children: [] }, objects: [...new Map(ports.map(([, object]) => [object.id, object])).values()], relations: [relation], scopes: [{ id: 'scope:clause', nodeId: 'clause', kind: 'predicate', label: 'fixture', objectIds: ports.map(([, object]) => object.id), assumptionNodeIds: [], context: [] }], choices: [], opaqueRegions: [], coverage: [], scenes: [], diagnostics: [] };
  return { document, relation };
}
const application = (inverse = false) => fixture('restricted-application', [...base(), ['input', object('input')], ['output', object('output')]], { restrictedDirection: inverse ? 'inverse' : 'forward' });
const html = (result: ReturnType<typeof fixture>) => renderToStaticMarkup(createElement(RestrictedMapFigure, result));

describe('restricted map representation', () => {
  it('composes the same diagram vocabulary without a Lean bundle, relation, or named theorem', () => {
    const structure: RestrictedMapStructure = {
      map: object('map'), sourceCarrier: object('carrier-a'), targetCarrier: object('carrier-b'),
      source: { role: 'source', label: 'U', empty: false }, target: { role: 'target', label: 'V', empty: false },
      direction: 'forward', sameCarrier: false,
      properties: { sourceOpen: true, targetOpen: false, forwardContinuousOnSource: true, inverseContinuousOnTarget: false },
    };
    const diagram = renderToStaticMarkup(createElement(RestrictedRegionDiagram, { structure }));
    const laws = renderToStaticMarkup(createElement(RestrictedRoundTrips, { structure }));
    expect(diagram).toContain('open source region');
    expect(diagram).not.toContain('open target region');
    expect(diagram).toContain('forward continuous on source');
    expect(laws).toContain('For every element in the source region');
    expect(laws).toContain('For every element in the target region');
    expect(diagram).not.toContain('PartialEquiv');
  });

  it('shows inverse laws only between named valid regions, without chosen points', () => {
    const result = fixture(), model = compileRestrictedMap(result.document, result.relation)!;
    expect(model).toMatchObject({ kind: 'equivalence', map: { id: 'e' }, sourceCarrier: { id: 'M' }, targetCarrier: { id: 'N' }, source: { label: 'e.source', role: 'source' }, target: { label: 'e.target', role: 'target' } });
    expect(model.source.object).toBeUndefined();
    expect(model.target.object).toBeUndefined();
    const rendered = html(result);
    expect(rendered).toContain('For every element in the source region');
    expect(rendered).toContain('For every element in the target region');
    expect(rendered).toContain('no inverse law is asserted on the whole carriers');
    expect(rendered).toContain('possibly empty');
    expect(rendered).not.toContain('<circle');
    expect(rendered).not.toMatch(/data-reading-object="e\.(source|target)"/);
  });

  it('shares the same region and round-trip grammar with optional open/continuous properties', () => {
    const partial = html(fixture());
    const open = html(fixture('restricted-equivalence', base(), { restrictedMapKind: 'open-partial-homeomorphism' }));
    expect(partial).not.toContain('continuous');
    expect(partial).not.toContain('open source region');
    expect(open).toContain('open source region');
    expect(open).toContain('open target region');
    expect(open).toContain('continuous on these regions');
    expect(open).toContain('For every element in the source region');
    expect(open).not.toContain('differentiable');
    expect(open).not.toContain('Euclidean');
  });

  it('uses an actual observed region identity while keeping the opposite side schematic', () => {
    const result = fixture('restricted-region', [...base(), ['region', object('source-expr', variable('source-expr'), 'e.source')]], { restrictedRegion: 'source' });
    const model = compileRestrictedMap(result.document, result.relation)!;
    expect(model.source.object?.id).toBe('source-expr');
    expect(model.target.object).toBeUndefined();
    expect(model.selectedRegion).toBe('source');
    const rendered = html(result);
    expect(rendered).toContain('data-reading-object="source-expr"');
    expect(rendered).toContain('data-region-evidence="source-expression"');
    expect(rendered).toContain('data-region-evidence="schematic"');
  });

  it('keeps normalized source/target roles when a projection comes from symm', () => {
    const result = fixture('restricted-region', [...base(), ['region', object('inverse-source', variable('inverse-source'), 'e.symm.source')]], { restrictedDirection: 'inverse', restrictedRegion: 'target' });
    const model = compileRestrictedMap(result.document, result.relation)!;
    expect(model.target.object?.id).toBe('inverse-source');
    expect(model.source.object).toBeUndefined();
    expect(model.sourceCarrier.id).toBe('M');
    expect(model.targetCarrier.id).toBe('N');
    expect(html(result)).toContain('The target region');
  });

  it.each([false, true])('retains source application input/output without placing either in a valid region (inverse=%s)', inverse => {
    const result = application(inverse), model = compileRestrictedMap(result.document, result.relation)!;
    expect(model.application).toMatchObject({ input: { id: 'input' }, output: { id: 'output' } });
    expect(model.direction).toBe(inverse ? 'inverse' : 'forward');
    const rendered = html(result);
    expect(rendered).toContain('data-reading-object="input"');
    expect(rendered).toContain('data-reading-object="output"');
    expect(rendered).toContain('Region membership must come from the surrounding statement.');
    expect(rendered).toContain('Its type alone does not establish membership');
    const svg = rendered.slice(rendered.indexOf('<svg'), rendered.indexOf('</svg>'));
    expect(svg).not.toContain('data-reading-object="input"');
    expect(svg).not.toContain('data-reading-object="output"');
    expect(rendered.indexOf('data-reading-object="input"')).toBeLessThan(rendered.indexOf('<svg'));
  });

  it('does not split an identical input/output object into invented intermediate identities', () => {
    const x = object('x'), result = fixture('restricted-application', [...base(), ['input', x], ['output', x]]);
    const model = compileRestrictedMap(result.document, result.relation)!;
    expect(model.application!.input).toBe(model.application!.output);
    expect(html(result)).not.toContain('data-reading-object="x-copy');
  });

  it('keeps equal display labels distinct but repeats a genuinely shared carrier identity', () => {
    const distinct = fixture('restricted-equivalence', [['map', object('e')], ['source carrier', object('M', variable('M'), 'X')], ['target carrier', object('N', variable('N'), 'X')]]);
    expect(compileRestrictedMap(distinct.document, distinct.relation)!.sameCarrier).toBe(false);
    const M = object('M'), same = fixture('restricted-equivalence', [['map', object('e')], ['source carrier', M], ['target carrier', M]]);
    expect(compileRestrictedMap(same.document, same.relation)!.sameCarrier).toBe(true);
    expect(html(same)).toContain('Two roles of the same carrier; the regions may overlap.');
    expect(html(distinct)).not.toContain('Two roles of the same carrier');
  });

  it('can express an empty region without supplying witnesses or treating a display name as evidence', () => {
    const empty: Expr = { kind: 'app', fn: constant('Set.empty'), args: [variable('M')], argumentKinds: ['type'] };
    const result = fixture('restricted-region', [...base(), ['region', object('empty', empty, '∅')]], { restrictedRegion: 'source' });
    expect(compileRestrictedMap(result.document, result.relation)!.source.empty).toBe(true);
    expect(html(result)).toContain('Vacuous when this region is empty');
    expect(html(result)).not.toContain('<circle');
    const justNamed = fixture('restricted-region', [...base(), ['region', object('empty', variable('empty'), '∅')]], { restrictedRegion: 'source' });
    expect(compileRestrictedMap(justNamed.document, justNamed.relation)!.source.empty).toBe(false);
    expect(html(justNamed)).not.toContain('Vacuous when this region is empty');
    const untrusted = fixture('restricted-region', [...base(), ['region', object('empty', { ...empty, fn: constant('Set.empty', false) }, '∅')]], { restrictedRegion: 'source' });
    expect(compileRestrictedMap(untrusted.document, untrusted.relation)!.source.empty).toBe(false);
  });

  it('reuses projection identities only in the exact clause/scope and original map orientation', () => {
    const result = fixture(), projection = fixture('restricted-region', [...base(), ['region', object('s')]], { id: 'projection', restrictedRegion: 'source' });
    const document = { ...result.document, objects: [...result.document.objects, projection.document.objects.at(-1)!] };
    expect(compileRestrictedMap(document, result.relation, [projection.relation])!.source.object?.id).toBe('s');
    for (const other of [{ nodeId: 'sibling' }, { scopeId: 'scope:lambda' }, { restrictedMapKind: 'open-partial-homeomorphism' as const }, { fidelity: 'structural' as const }]) {
      expect(compileRestrictedMap(document, result.relation, [{ ...projection.relation, ...other }])!.source.object).toBeUndefined();
    }
    const differentMap = { ...projection.relation, ports: projection.relation.ports.map(port => port.role === 'map' ? { ...port, objectId: 'N' } : port) };
    expect(compileRestrictedMap(document, result.relation, [differentMap])!.source.object).toBeUndefined();
  });

  it('does not silently replace two definitionally related source-expression identities', () => {
    const result = fixture(), first = fixture('restricted-region', [...base(), ['region', object('s')]], { id: 'projection-1', restrictedRegion: 'source' });
    const second = fixture('restricted-region', [...base(), ['region', object('inverse-target')]], { id: 'projection-2', restrictedRegion: 'source', restrictedDirection: 'inverse' });
    const document = { ...result.document, objects: [...result.document.objects, first.document.objects.at(-1)!, second.document.objects.at(-1)!] };
    expect(compileRestrictedMap(document, result.relation, [first.relation, second.relation])!.source.object).toBeUndefined();
    expect(compileRestrictedMap(document, first.relation, [first.relation, second.relation])!.source.object?.id).toBe('s');
  });

  it('rejects a bound map outside the current scope, including hidden references inside composite objects', () => {
    const result = fixture(), bound = { ...object('hidden'), binder: { id: 'hidden', name: 'e', type: 'PartialEquiv M N', role: 'universal' as const, dependsOn: [] } };
    const direct = { ...result.document, objects: result.document.objects.map(object => object.id === 'e' ? { ...object, binder: { ...bound.binder, id: 'e' } } : object), scopes: result.document.scopes.map(scope => ({ ...scope, objectIds: scope.objectIds.filter(id => id !== 'e') })) };
    expect(compileRestrictedMap(direct, result.relation)).toBeUndefined();
    const composite = { ...result.document, objects: [...result.document.objects.map(object => object.id === 'e' ? { ...object, expression: { kind: 'app' as const, fn: constant('mapWrapper'), args: [variable('hidden')] } } : object), bound] };
    expect(compileRestrictedMap(composite, result.relation)).toBeUndefined();
  });

  it('does not capture a locally bound variable in an application expression', () => {
    const result = application(), binder = { id: 'local', name: 'x', type: 'M', role: 'lambda' as const, dependsOn: [] };
    const local = { ...object('local'), binder };
    const document = { ...result.document, objects: [...result.document.objects.map(object => object.id === 'input' ? { ...object, expression: { kind: 'lambda' as const, binder, body: variable('local') } } : object), local] };
    expect(compileRestrictedMap(document, result.relation)?.application).toBeDefined();
  });

  it('rejects absent, duplicated, incomplete, or incompatible ports and metadata', () => {
    const result = fixture();
    const compile = (extra: Partial<SemanticRelation>) => compileRestrictedMap(result.document, { ...result.relation, ...extra });
    expect(compile({ ports: result.relation.ports.slice(1) })).toBeUndefined();
    expect(compile({ ports: [...result.relation.ports, result.relation.ports[0]] })).toBeUndefined();
    expect(compile({ ports: [...result.relation.ports, { role: 'input', objectId: 'M' }] })).toBeUndefined();
    expect(compile({ kind: 'restricted-application' })).toBeUndefined();
    expect(compile({ kind: 'restricted-region' })).toBeUndefined();
    expect(compile({ restrictedMapKind: undefined })).toBeUndefined();
    expect(compile({ restrictedDirection: undefined })).toBeUndefined();
    expect(compile({ fidelity: 'structural' })).toBeUndefined();
    expect(compile({ expression: { kind: 'app', fn: constant('PartialEquiv', false), args: [] } })).toBeUndefined();
    expect(compile({ scopeId: 'scope:other' })).toBeUndefined();
    expect(compile({ nodeId: 'other' })).toBeUndefined();
  });

  it('preserves long full labels accessibly while bounding SVG text and keeping identifiers stable', () => {
    const label = `aVeryLongMapName${'withMoreMeaning'.repeat(60)}`, result = fixture('restricted-equivalence', [['map', object('e', variable('e'), label)], ['source carrier', object('M')], ['target carrier', object('N')]]);
    const rendered = html(result);
    expect(rendered).toContain(`aria-label="${label} : abstract type"`);
    expect(rendered).toContain(`title="${label} : abstract type"`);
    expect(rendered).toContain('…');
    expect(rendered).toContain('data-reading-object="e"');
    expect(rendered).not.toContain(`data-reading-object="${label}"`);
  });

  it('preserves exact relation and scope identities with keyboard object controls', () => {
    const result = fixture();
    const rendered = renderToStaticMarkup(createElement(RestrictedMapFigure, { ...result, selectedObjectId: 'e', onObjectSelect: () => undefined }));
    expect(rendered).toContain('data-restricted-relation="relation:clause:restricted"');
    expect(rendered).toContain('data-restricted-scope="scope:clause"');
    expect(rendered).toContain('tabindex="0"');
    expect(rendered).toContain('role="button"');
    expect(rendered).toContain('aria-pressed="true"');
    expect(rendered).not.toContain('type="range"');
  });

  it('is deterministic, immutable, and independent of rendered display names for identity', () => {
    const result = fixture(), before = JSON.stringify(result), model = compileRestrictedMap(result.document, result.relation)!;
    expect(compileRestrictedMap(result.document, result.relation)).toEqual(model);
    expect(JSON.stringify(result)).toBe(before);
    const renamed = { ...result.document, objects: result.document.objects.map(object => ({ ...object, label: `renamed ${object.label}` })) };
    const renamedModel = compileRestrictedMap(renamed, result.relation)!;
    expect(renamedModel.map.id).toBe(model.map.id);
    expect(renamedModel.sourceCarrier.id).toBe(model.sourceCarrier.id);
    expect(renamedModel.targetCarrier.id).toBe(model.targetCarrier.id);
  });
});
