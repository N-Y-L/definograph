import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { JsonValue } from '../packets/packet';
import { compilePositionalComponent } from '../packets/semantic';
import type { PositionalStructuralInput } from '../packets/structure';
import type { PlannedView } from '../semantic/types';
import { GuidedReading } from '../visual/GuidedReading';
import { SemanticView } from '../visual/SemanticView';
import { StatementReadingView } from '../visual/StatementReadingView';
import { TypedConstructionFigure } from '../constructions/TypedConstructionFigure';
import { compileTypedConstruction } from '../constructions/model';
import { compileReading } from './compiler';
import { compileReadingCues } from './cues';
import { planReadingPresentation } from './presentation';

const name = (text: string): JsonValue => ['str', ['anonymous'], text];
const constant = (text: string): JsonValue => ['const', text.split('.').reduce<JsonValue>((prefix, part) => ['str', prefix, part], ['anonymous']), []];
const bound = (index: number): JsonValue => ['bvar', ['nat', String(index)]];
const apply = (fn: JsonValue, arg: JsonValue): JsonValue => ['app', fn, arg];
const sort: JsonValue = ['sort', ['succ', ['zero']]];
const pi = (type: JsonValue, body: JsonValue, text = 'input'): JsonValue => ['forallE', name(text), type, body, 'default'];
const port = (prefix: JsonValue, text: string, type: JsonValue): JsonValue => ['port', prefix, { name: name(text), info: 'default' }, type];
const empty: PositionalStructuralInput['home'] = { arity: 0, telescope: ['nil'] };
const applications: PositionalStructuralInput = {
  home: { arity: 3, telescope: port(port(port(['nil'], 'f', pi(constant('Alpha'), constant('Beta'))),
    'g', pi(constant('Beta'), constant('Gamma'))), 'x', constant('Alpha')) },
  term: apply(bound(1), apply(bound(2), bound(0))), type: constant('Gamma'),
};

function prepare(input: PositionalStructuralInput, target: 'term' | 'type' = 'term') {
  const compiled = compilePositionalComponent(input, { sourceIdentity: 'neutral-reading-test', target });
  if (!compiled.document) throw new Error(compiled.reason);
  const document = compiled.document, reading = compileReading(document), plan = compileReadingCues(reading, document);
  const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading }));
  return { compiled, document, reading, plan, html };
}

// Inspect actual rendered text, including the closed complete-reading contents.
// Class names and source identities deliberately retain their existing API names.
const visible = (html: string) => html.replace(/<[^>]*>/g, ' ').replace(/\s+/g, ' ');
function expectNeutral(text: string) {
  expect(text).not.toMatch(/Full visual statement|Whole statement|Definition parameter|For every|universal choice|Candidate witness|Given assumptions|conditional conclusion|conditions hold|Logical structure|logical statement|packet/i);
}

describe('neutral positional component reading', () => {
  it('keeps ordered unfamiliar applications and their exact intermediate identity', () => {
    const { compiled, document, reading, plan, html } = prepare(applications);
    const stages = plan.cues.filter(cue => cue.intent === 'apply');
    expect(stages.map(cue => cue.title)).toEqual(['Follow f', 'Follow g']);
    const first = document.relations.find(relation => relation.id === stages[0].stage.relationId)!;
    const intermediate = first.ports.find(p => p.role === 'output')!.objectId;
    expect(stages[1].retainedObjectIds).toContain(intermediate);
    expect(stages[0].nodeId).toBe(stages[1].nodeId);
    expect(compiled.sourceById[stages[0].stage.relationId!].path).toEqual(['checking', 'selected', 'term', 2]);
    expect(compiled.sourceById[stages[1].stage.relationId!].path).toEqual(['checking', 'selected', 'term']);
    expect(document.relations.every(relation => relation.kind === 'application')).toBe(true);
    expect(reading.nodes.flatMap(node => node.edgeFromParent ? [node.edgeFromParent.role] : [])).toEqual(['body', 'body', 'body']);
    expect(plan.cues.every(cue => !['condition', 'logic', 'compare'].includes(cue.intent))).toBe(true);
    expect(html).toContain('Full visual reading');
    expect(html).toContain('Expression and context');
    expectNeutral(visible(html));
    for (const cue of plan.cues) {
      const stage = renderToStaticMarkup(createElement(GuidedReading, { plan, cue, reading, document,
        onChoose: () => undefined, children: createElement('div', {}, 'Current expression') }));
      expectNeutral(visible(stage));
    }
  });

  it.each(['term', 'type'] as const)('separates ambient parameters from owned %s inputs despite identical names', target => {
    const input: PositionalStructuralInput = { home: { arity: 1, telescope: port(['nil'], 'same', sort) },
      term: ['lam', name('same'), bound(0), bound(0), 'default'], type: pi(bound(0), bound(1), 'same') };
    const { compiled, document, reading, plan, html } = prepare(input, target);
    const ambient = compiled.contextNodeIds[0], owned = compiled.targetNodeId!;
    expect(ambient).not.toBe(owned);
    expect(reading.quantifierGroups.some(group => group.nodeIds.includes(ambient) && group.nodeIds.includes(owned))).toBe(false);
    const presentation = planReadingPresentation(reading, { boundaryNodeIds: [owned] });
    expect(presentation.nodeToRegionId[ambient]).not.toBe(presentation.nodeToRegionId[owned]);
    expect(plan.cues.filter(cue => cue.intent === 'introduce').map(cue => cue.title)).toEqual(['Names in scope: same', 'Function inputs: same@2']);
    expect(document.choices.map(choice => choice.role)).toEqual(['parameter', target === 'term' ? 'lambda' : 'parameter']);
    expect(html).toContain('data-component-region="context"');
    expect(html).toContain('data-component-region="expression"');
    expect(html).toContain(`data-component-target="${target}"`);
    expect(html).toContain(`${target === 'term' ? 'Selected term' : 'Inferred type'} begins here.`);
    expectNeutral(visible(html));
    expectNeutral(plan.cues.map(cue => `${cue.title} ${cue.detail}`).join(' '));
  });

  it('separates context and owned definitions while retaining unused context and repeated names', () => {
    const input: PositionalStructuralInput = { home: { arity: 2, telescope:
      ['letE', ['letE', ['nil'], name('same'), false, constant('Alpha'), constant('seed')],
        name('same'), true, constant('Alpha'), bound(0)] },
    term: ['letE', name('same'), constant('Alpha'), bound(0), bound(0), true], type: constant('Alpha') };
    const { compiled, document, reading, plan, html } = prepare(input);
    const introductions = plan.cues.filter(cue => cue.intent === 'introduce');
    expect(introductions.map(cue => cue.title)).toEqual(['Context definitions: same, same@2', 'Local definitions: same@3']);
    expect(introductions[0].sourceNodeIds).toEqual(compiled.contextNodeIds);
    expect(introductions[1].sourceNodeIds).toEqual([compiled.targetNodeId]);
    expect(new Set(document.choices.map(choice => choice.objectId)).size).toBe(3);
    expect(reading.quantifierGroups.map(group => group.nodeIds.length)).toEqual([2, 1]);
    expect(html).toContain('Context definitions'); expect(html).toContain('Local definitions');
    expect(html).toContain('seed');
    expectNeutral(visible(html));
  });

  it('keeps a proof term and its type as separately selected expressions', () => {
    const input: PositionalStructuralInput = { home: empty, term: constant('True.intro'), type: constant('True') };
    const term = prepare(input), type = prepare(input, 'type');
    expect(term.document.tree.lean).toBe('True.intro');
    expect(type.document.tree.lean).toBe('True');
    expect(term.compiled.targetNodeId).not.toBe(type.compiled.targetNodeId);
    expect(term.plan.cues[0].title).toBe('Read the expression');
    expect(term.plan.cues[0].role).toBe('expression');
    expect(term.html).toContain('Selected term begins here.');
    expect(type.html).toContain('Inferred type begins here.');
    expectNeutral(visible(term.html)); expectNeutral(visible(type.html));
  });

  it('does not promote equality or conjunction syntax to an asserted condition', () => {
    const expression = apply(apply(constant('And'), apply(apply(constant('Eq'), constant('left')), constant('right'))), constant('extra'));
    const { document, plan, html } = prepare({ home: empty, term: expression, type: constant('Prop') });
    expect(document.tree.kind).toBe('predicate');
    expect(document.relations.every(relation => relation.kind === 'application')).toBe(true);
    expect(plan.cues.map(cue => cue.intent)).toEqual(['apply', 'apply']);
    expect(visible(html)).not.toMatch(/required together|Both conditions|membership condition|Compare the expressions/);
    expectNeutral(visible(html));
  });

  it('retains neutral instructions when the guided sequence reaches its display bound', () => {
    const { document, reading } = prepare(applications);
    const plan = compileReadingCues(reading, document, { maxCues: 1 });
    expect(plan.truncated).toBe(true);
    const html = renderToStaticMarkup(createElement(GuidedReading, { plan, cue: plan.cues[0], document, reading,
      onChoose: () => undefined, children: createElement('div') }));
    expect(html).toContain('full visual reading below');
    expectNeutral(visible(html)); expectNeutral(plan.diagnostics.join(' '));
  });

  it('uses neutral labels in the shared dependency and object views', () => {
    const { document } = prepare(applications);
    const view: PlannedView = { id: 'component-view', kind: 'quantifier-flow', title: 'Context', score: 1,
      reason: '', fidelity: 'structural', nodeIds: document.choices.map(choice => choice.nodeId),
      objectIds: document.objects.map(object => object.id), relationIds: document.relations.map(relation => relation.id), sceneIds: [], conditions: [] };
    for (const kind of ['quantifier-flow', 'semantic-map', 'relation-map'] as const) {
      const html = renderToStaticMarkup(createElement(SemanticView, { document, view: { ...view, kind } }));
      expectNeutral(visible(html));
      if (kind === 'quantifier-flow') {
        expect(html).toContain('Context parameter');
        const legend = html.match(/<div class="sv-choice-legend">(.*?)<\/div>/)![1];
        expect(visible(legend)).not.toContain('∀'); expect(visible(legend)).not.toContain('∃');
      }
    }
  });
});

describe('component signatures describe declared syntax', () => {
  const zero: JsonValue = ['lit', ['natVal', ['nat', '0']]];
  const annotated = (annotation: JsonValue): PositionalStructuralInput => ({
    home: { arity: 1, telescope: port(['nil'], 'f', annotation) }, term: bound(0), type: annotation,
  });
  function construction(input: PositionalStructuralInput) {
    const result = prepare(input), binders = result.reading.quantifierGroups[0].binders;
    const model = compileTypedConstruction(result.document, binders);
    const html = renderToStaticMarkup(createElement(TypedConstructionFigure, { document: result.document, binders }));
    return { ...result, binders, model, figure: html };
  }

  it('retains an ill-typed domain ending in Prop without claiming that inputs determine a proposition', () => {
    const { model, figure, html, document, binders } = construction(annotated(pi(zero, ['sort', ['zero']], 'x')));
    expect(model.signatures[0]).toMatchObject({ kind: 'relation', inputs: [{ type: '0' }], resultDependsOn: [] });
    expect(figure).toContain('aria-label="Declared types and signatures"');
    expect(figure).toContain('Declared signature');
    expect(figure).toContain('Result annotation');
    expect(figure).toContain('The displayed signature ends in Prop.');
    expect(figure).toContain(model.signatures[0].result);
    expect(visible(html)).not.toContain('inputs determine a proposition');
    expect(visible(figure)).not.toMatch(/\brelation\b|\bproposition\b|typed objects and maps/);
    expect(figure).toContain('Type, element, and signature labels show declared annotations.');
    // Presentation mode does not change signature identity, roles or dependencies.
    const legacy = { ...document, presentation: undefined };
    expect(compileTypedConstruction(legacy, binders)).toEqual(model);
    const oldFigure = renderToStaticMarkup(createElement(TypedConstructionFigure, { document: legacy, binders }));
    expect(oldFigure).toContain('These inputs determine a proposition; no truth value is asserted here.');
    expect(oldFigure).not.toContain('Result annotation');
  });

  it('retains the exact displayed Sort result as an annotation without asserting a type family', () => {
    const { model, figure } = construction(annotated(pi(zero, ['sort', ['max', ['param', name('u')], ['succ', ['zero']]]])));
    expect(model.signatures[0].kind).toBe('family');
    expect(visible(figure)).toContain(`The displayed signature ends in ${model.signatures[0].result}.`);
    expect(figure).toContain('Result annotation');
    expect(visible(figure)).not.toMatch(/type family|Inputs index|fixed target type/);
  });

  it.each([
    { label: 'result', annotation: pi(zero, bound(0)), inputs: [[]], result: [0] },
    { label: 'later input', annotation: pi(zero, pi(bound(0), constant('Result'), 'later')), inputs: [[], [0]], result: [] },
  ])('reports $label references as syntax while preserving their positions', ({ annotation, inputs, result }) => {
    const { model, figure } = construction(annotated(annotation));
    expect(model.signatures[0].kind).toBe('dependent-map');
    expect(model.signatures[0].inputs.map(input => input.dependsOn)).toEqual(inputs);
    expect(model.signatures[0].resultDependsOn).toEqual(result);
    expect(visible(figure)).toContain('references input 1');
    expect(visible(figure)).toContain('Later input annotations or the result annotation reference earlier inputs.');
    expect(visible(figure)).not.toMatch(/dependent map|depends on input|result type depend/);
  });

  it('describes curried inputs by annotation order without certifying a function', () => {
    const { model, figure } = construction(annotated(pi(zero, pi(zero, constant('Result'), 'later'))));
    expect(model.signatures[0].kind).toBe('multi-input-map');
    expect(visible(figure)).toContain('Input annotations follow the order of the displayed signature.');
    expect(figure).toContain('Input annotation 1'); expect(figure).toContain('Input annotation 2');
    expect(visible(figure)).not.toContain('curried function type');
  });

  it('qualifies compact graph and expanded row labels as declared annotations', () => {
    const compact = construction(applications);
    expect(compact.figure).toContain('aria-label="Arrows between declared annotations"');
    expect(compact.figure).toContain('Declared type annotation Alpha');
    expect(compact.figure).toContain('annotation: Alpha');
    expect(compact.figure).not.toContain('Maps between the declared types');
    let telescope: JsonValue = ['nil'];
    for (let i = 0; i < 5; i++) telescope = port(telescope, `map${i}`, pi(zero, constant('Result')));
    const expanded = construction({ home: { arity: 5, telescope }, term: bound(0), type: constant('Result') });
    expect(expanded.model.maps).toHaveLength(5);
    expect(expanded.figure.match(/class="tc-map-row"/g)).toHaveLength(5);
    expect(expanded.figure).toContain('Declared type annotation 0');
    expect(expanded.figure).toContain('declared annotation');
    expect(visible(expanded.figure)).not.toContain('Named elements retain their types');
  });
});
