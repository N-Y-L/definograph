import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { PlannedView, SemanticDocument, SemanticObject } from '../semantic/types';
import { SemanticView } from './SemanticView';

const objects: SemanticObject[] = ['x', 'y', 'z'].map(id => ({ id, label: id, kind: 'variable', type: 'ℝ', expression: { kind: 'const', name: id }, scopeId: 'scope', provenance: [] }));
const document: SemanticDocument = {
  schemaVersion: '1.0.0', prover: 'lean', source: '', tree: { id: 'root', kind: 'predicate', label: '', lean: '', children: [], expression: { kind: 'const', name: 'True' } }, objects,
  relations: [], scopes: [{ id: 'scope', nodeId: 'root', kind: 'or', label: '', objectIds: ['x', 'y'], assumptionNodeIds: [], context: ['Alternative 2 of a disjunction'] }],
  choices: [{ id: 'parameter', objectId: 'x', binderId: 'bx', nodeId: 'root', role: 'parameter', dependsOn: [], availableObjectIds: [], scopeId: 'scope', explanation: 'A parameter of this definition.' }, { id: 'witness', objectId: 'y', binderId: 'by', nodeId: 'witness', role: 'existential', dependsOn: ['x'], availableObjectIds: ['x'], scopeId: 'scope', explanation: 'May use the earlier parameter.' }], opaqueRegions: [], coverage: [], scenes: [], diagnostics: [],
};
const view: PlannedView = { id: 'choice-view', kind: 'quantifier-flow', title: 'Choice scope', score: 1, reason: '', fidelity: 'structural', nodeIds: ['root', 'witness'], objectIds: ['x', 'y'], relationIds: [], sceneIds: [], conditions: [] };

describe('semantic view interpretation labels', () => {
  it('distinguishes definition parameters from quantified arbitrary choices', () => {
    const html = renderToStaticMarkup(createElement(SemanticView, { document, view }));
    expect(html).toContain('Definition parameter');
    expect(html).toContain('Candidate witness');
    expect(html).not.toContain('Arbitrary choice');
    expect(html).toContain('Alternative 2 of a disjunction');
  });

  it('uses object identity for dependency links without importing unrelated branches', () => {
    const html = renderToStaticMarkup(createElement(SemanticView, { document, view, selectedObjectId: 'x', onObjectSelect: () => undefined }));
    expect(html).toContain('May depend on');
    expect(html).toContain('aria-label="x, ℝ"');
    expect(html).not.toContain('aria-label="z, ℝ"');
  });

  it('keeps relation context and explicit mathematical roles in a symbolic diagram', () => {
    const membership = { id: 'membership', kind: 'membership' as const, label: 'belongs to', ports: [{ role: 'element', objectId: 'x' }, { role: 'set', objectId: 'y' }], expression: { kind: 'const' as const, name: 'Set.Mem' }, scopeId: 'scope', nodeId: 'root', pluginId: 'sets', fidelity: 'symbolic' as const, provenance: { nodeId: 'root', expressionPath: '', origin: 'elaborated-expression' as const }, conditions: [] };
    const html = renderToStaticMarkup(createElement(SemanticView, { document: { ...document, relations: [membership] }, view: { ...view, kind: 'relation-map', relationIds: ['membership'] } }));
    expect(html).toContain('Alternative 2 of a disjunction');
    expect(html).toContain('element: x');
    expect(html).toContain('set: y');
    expect(html).toContain('∈');
    expect(html).toContain('Relative position and distance carry no geometric meaning');
  });
});
