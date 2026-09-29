import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Analysis, Binder, StatementNode } from '../core/types';
import { initialScenario, updateScenario } from '../core/scenario';
import { contextEntryTitle } from '../core/context-entry';
import { compileSemanticDocument } from '../semantic/compiler';
import { compileReading } from '../reading/compiler';
import { compileReadingCues } from '../reading/cues';
import { compileTypedConstruction, isUsefulConstruction } from '../constructions/model';
import { checkedStructure } from '../decomposition/reflection';
import { StatementReadingView } from '../visual/StatementReadingView';
import { VariableControl } from '../VariableControl';

const nodes = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(nodes)];
const fixture = (binding: Binder): StatementNode => ({ id: 'entry', kind: 'auxiliary', label: contextEntryTitle(binding), lean: binding.type,
  binder: binding, expression: { kind: 'lambda', binder: binding, body: { kind: 'const', name: 'True' } },
  children: [{ id: 'selected', kind: 'predicate', label: 'True', lean: 'True', expression: { kind: 'const', name: 'True' }, children: [] }] });

describe('recorded nondefault context entries', () => {
  it('does not turn retained type metadata into choices, numeric inputs or constructions', () => {
    for (const declarationKind of ['auxDecl', 'implDetail'] as const) {
      const binder: Binder = { id: 'entry.binder', name: 'renamed_entry', type: 'Real', domain: 'real', role: 'auxiliary', declarationKind, dependsOn: [],
        structure: { name: 'Unfamiliar', typeExpression: { kind: 'const', name: 'Unfamiliar' }, fields: [], omittedFields: 0, kernelChecked: true,
          limits: { maxFields: 16, maxFieldNodes: 120, maxDepth: 24 } } };
      expect(checkedStructure({ ...binder, role: 'parameter' })).toBeDefined();
      expect(checkedStructure(binder)).toBeUndefined();
      const tree = fixture(binder), document = compileSemanticDocument({ source: 'constructed control', tree, expression: tree.expression });
      const reading = compileReading(document);
      expect(document.choices).toHaveLength(0);
      expect(document.scopes.at(-1)?.objectIds).toContain(reading.root.binder?.objectId);
      expect(initialScenario(tree)).toEqual({});
      expect(updateScenario(tree, {}, binder.id, 1)).toEqual({});
      expect(renderToStaticMarkup(createElement(VariableControl, { binder, value: undefined, onChange() {}, names: {} }))).toBe('');
      expect(isUsefulConstruction(compileTypedConstruction(document, [reading.root.binder!]))).toBe(false);
      expect(compileReadingCues(reading, document).cues[0]?.title).toBe(contextEntryTitle(binder));
      const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading }));
      expect(html).toContain(contextEntryTitle(binder));
      expect(html).not.toContain('Given assumptions');
      expect(html).not.toContain('typed-construction');
    }
  });

  const captureFile = process.env.DEFINOGRAPH_AUXILIARY_CAPTURES;
  it.runIf(Boolean(captureFile))('preserves real native entry identities and separate genuine hypotheses through rendering', () => {
    const captures = JSON.parse(readFileSync(captureFile!, 'utf8')) as { name: string; analysis: Analysis }[];
    expect(captures.map(c => c.name)).toEqual(['proposition-valued example', 'named theorem', 'genuine hypothesis', 'tactic hypothesis', 'explicit __h parameter', 'lambda implementation detail', 'tactic have implementation detail', 'term let implementation detail', 'recursive reference', 'duplicate names']);
    for (const { name, analysis } of captures) {
      const entries = nodes(analysis.tree).filter(node => node.binder?.role === 'auxiliary');
      if (name === 'tactic have implementation detail' || name === 'term let implementation detail') {
        const raw = (analysis as Analysis & { sourceSnapshot: { original: { frame: { originalDeclarations: { constructor: string; kind: string; nondep?: boolean; value?: unknown }[] } } } }).sourceSnapshot.original.frame.originalDeclarations;
        const localLet = raw.at(-1)!;
        expect(localLet.constructor).toBe('ldecl');
        expect(localLet.kind).toBe('implDetail');
        expect(localLet.nondep).toBe(name === 'tactic have implementation detail');
        expect(localLet.value).toBeDefined();
      }
      const document = compileSemanticDocument(analysis), reading = compileReading(document), cues = compileReadingCues(reading, document);
      const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading }));
      for (const entry of entries) {
        const binder = reading.nodes.find(node => node.id === entry.id)!.binder!;
        expect(binder.declarationKind).toBe(entry.binder!.declarationKind);
        expect(html).toContain(contextEntryTitle(entry.binder!));
        expect(document.choices.some(choice => choice.binderId === binder.binderId)).toBe(false);
        expect(document.choices.some(choice => choice.dependsOn.includes(binder.objectId!) || choice.availableObjectIds.includes(binder.objectId!))).toBe(false);
        expect(document.scopes.some(scope => scope.assumptionNodeIds.includes(entry.id + '.premise'))).toBe(false);
        const cue = cues.cues.find(cue => cue.binders.some(b => b.binderId === binder.binderId))!;
        expect(cue.role).toBe('auxiliary');
        expect(cue.title + ' ' + cue.detail).not.toMatch(/\b(assume|assumption|hypothesis|given|premise)\b/i);
      }
      if (name === 'genuine hypothesis' || name === 'tactic hypothesis') {
        expect(document.choices.some(choice => choice.role === 'assumption')).toBe(true);
        expect(html).toContain('Given assumptions');
      }
    }
  });
});
