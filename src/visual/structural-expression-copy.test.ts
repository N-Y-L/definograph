import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode, TypeDescriptor } from '../core';
import { compileSemanticDocument } from '../semantic';
import { compileReading, compileReadingCues } from '../reading';
import { StatementReadingView } from './StatementReadingView';

const variable = (name: string, type: string): Expr => ({ kind: 'var', id: name, name, type });
function contained(expression: Expr) {
  const wrapper: Expr = { kind: 'app', fn: variable('surroundingCondition', 'Unknown → Prop'),
    args: [expression], argumentKinds: ['value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } };
  const tree: StatementNode = { id: 'clause', kind: 'predicate', label: 'clause', lean: 'surroundingCondition (compose a b)', expression: wrapper, children: [] };
  const document = compileSemanticDocument({ source: tree.lean, tree, expression: wrapper });
  const reading = compileReading(document);
  return { document, reading, plan: compileReadingCues(reading, document) };
}

describe('uninterpreted expression wording', () => {
  it.each([
    ['a constructed value', { kind: 'structure', lean: 'CoordinateTransfer X Z', head: 'CoordinateTransfer' }],
    ['an uninterpreted proposition', { kind: 'proposition', lean: 'Prop' }],
    ['a type', { kind: 'type', lean: 'Type' }],
  ] as [string, TypeDescriptor][])('does not infer predicate status for %s from a structural relation record', (_name, typeDescriptor) => {
    const expression: Expr = { kind: 'app', fn: { kind: 'const', name: 'Unregistered.compose' },
      args: [variable('a', 'CoordinateTransfer X Y'), variable('b', 'CoordinateTransfer Y Z')], argumentKinds: ['value', 'value'], type: typeDescriptor.lean, typeDescriptor };
    const { document, reading, plan } = contained(expression);
    const relation = document.relations.find(item => item.fidelity === 'structural' && item.expression === expression)!;
    expect(relation).toBeDefined();
    const cue = plan.cues.find(item => item.stage.relationId === relation.id)!;
    expect(cue.stage.kind).toBe('contained');
    expect(cue.intent).toBe('inspect');
    expect(cue.detail).toContain('ordered arguments');
    expect(cue.detail).not.toContain('its truth');
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedRelationId: relation.id }));
    expect(html).toContain('this expression has no interpreted geometric meaning');
    expect(html).toContain('This part retains its expression scope.');
    expect(html).not.toContain('this predicate');
    expect(html).not.toContain('This inner relation is not asserted separately.');
    for (const port of relation.ports) expect(html).toContain(`data-reading-object="${port.objectId}"`);
  });

  it('keeps a recognized proposition tied to its enclosing clause', () => {
    const equality: Expr = { kind: 'app', fn: { kind: 'const', name: 'Eq' }, args: [variable('x', 'X'), variable('y', 'X')], argumentKinds: ['value', 'value'], typeDescriptor: { kind: 'proposition', lean: 'Prop' } };
    const { document, reading, plan } = contained(equality);
    const relation = document.relations.find(item => item.kind === 'equality')!;
    expect(plan.cues.find(item => item.stage.relationId === relation.id)!.intent).toBe('compare');
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedRelationId: relation.id }));
    expect(html).toContain('This inner relation is not asserted separately.');
  });
});
