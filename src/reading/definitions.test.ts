import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic/compiler';
import { expressionKey, formatExpression } from '../semantic/expression';
import { StatementReadingView } from '../visual/StatementReadingView';
import { compileReading } from './compiler';
import { compileReadingCues } from './cues';

describe('exact expression identity and local definitions', () => {
  it('honors supplied identities before alpha renaming or legacy normalization', () => {
    const left: Expr = { kind: 'var', id: 'same', name: 'x', type: 'A', exactIdentity: 'record-a/binder-1' };
    const right: Expr = { ...left, exactIdentity: 'record-b/binder-1' };
    const aliases = new Map([['same', 'display-name']]);
    expect(expressionKey(left, aliases)).not.toBe(expressionKey(right, aliases));
    const wrap = (value: Expr): Expr => ({ kind: 'app', fn: { kind: 'const', name: 'f' }, args: [value] });
    expect(expressionKey(wrap(left))).not.toBe(expressionKey(wrap(right)));
    expect(expressionKey({ ...left, name: 'renamed' })).toBe(expressionKey(left));
  });

  it('uses exact display text without dropping inputs through legacy name heuristics', () => {
    const expression: Expr = { kind: 'app', fn: { kind: 'const', name: 'Metric.custom' },
      args: [{ kind: 'literal', value: 1 }, { kind: 'literal', value: 2 }, { kind: 'literal', value: 3 }],
      exactIdentity: 'all-three-arguments', displayText: '(Metric.custom 1 2 3)' };
    expect(formatExpression(expression)).toBe('(Metric.custom 1 2 3)');
  });

  it('keeps a definition and its value distinct from subsequent universal choices', () => {
    const seed: Binder = { id: 'seed', name: 'seed', type: 'Nat', role: 'definition', dependsOn: [],
      typeExpression: { kind: 'const', name: 'Nat' }, definition: { value: { kind: 'literal', value: 0 }, nondep: false } };
    const x: Binder = { id: 'x', name: 'x', type: 'Nat', role: 'universal', dependsOn: ['seed'] };
    const leaf: StatementNode = { id: 'body', kind: 'predicate', label: 'P', lean: 'P seed x',
      expression: { kind: 'opaque', text: 'P seed x' }, children: [] };
    const quantified: StatementNode = { id: 'all', kind: 'forall', label: 'x', lean: '∀ x : Nat, P seed x',
      binder: x, expression: { kind: 'forall', binder: x, body: leaf.expression }, children: [leaf] };
    const tree: StatementNode = { id: 'definition', kind: 'definition', label: 'seed',
      lean: 'let seed : Nat := 0; ∀ x : Nat, P seed x', binder: seed,
      expression: { kind: 'opaque', text: 'exact let expression' }, children: [quantified] };
    const document = compileSemanticDocument({ source: tree.lean, tree, expression: tree.expression });
    const reading = compileReading(document), cues = compileReadingCues(reading, document);
    expect(reading.quantifierGroups.map(group => group.kind)).toEqual(['definition', 'forall']);
    expect(reading.root.phrase).toBe('Define seed : Nat := 0');
    expect(reading.root.binder?.definition).toEqual(seed.definition);
    expect(cues.cues[0]).toMatchObject({ role: 'definition', title: 'Define seed' });
    expect(cues.cues[1]).toMatchObject({ role: 'arbitrary', title: 'For every x' });
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading }));
    expect(html).toContain('sr-binder-definition');
    expect(html).toContain('sr-definition-value');
    expect(html).toContain(':= <code>0</code>');
    expect(html).not.toContain('For every seed');
  });
});
