import { describe, expect, it } from 'vitest';
import type { Analysis, DefinitionPreview, Expr, StatementNode } from '../core/types';
import { inspectSmallDefinitions } from './inspection';

const constant = (name: string): Expr => ({ kind: 'const', name });
const equal: Expr = { kind: 'app', fn: constant('Eq'), args: [constant('Nat'), { kind: 'literal', value: 1 }, { kind: 'literal', value: 1 }] };
const wrapped: Expr = { kind: 'app', fn: constant('Example.condition'), args: [equal] };
const node = (expression: Expr): StatementNode => ({ id: 'root', kind: 'predicate', label: '', lean: 'Example.condition (1 = 1)', expression, children: [] });
function fixture(): Analysis {
  const tree = node(equal);
  tree.expansion = { constant: 'Example.condition', before: 'Example.condition (1 = 1)', after: '1 = 1', definitionalEquality: true };
  const preview: DefinitionPreview = { constant: 'Example.condition', pretty: '1 = 1', tree, expression: equal, expansionPolicy: { constants: ['Example.condition'], maxDepth: 1 } };
  return { ok: true, source: 'original', pretty: 'Example.condition (1 = 1)', type: 'Prop', tree: node(wrapped), expression: wrapped,
    diagnostics: [], metrics: [], definitions: [{ name: 'Example.condition', kind: 'definition', type: 'Prop → Prop', canExpand: true }], definitionPreviews: [preview] };
}

describe('automatic small definition inspection', () => {
  it('selects a checked improvement while retaining original identity and source', () => {
    const initial = fixture(), before = JSON.stringify(initial);
    const result = inspectSmallDefinitions(initial);
    expect(result.automaticInspection).toMatchObject({ constant: 'Example.condition', originalPretty: initial.pretty });
    expect(result.tree).toBe(initial.definitionPreviews![0]!.tree);
    expect(result.originalExpression).toBe(initial.expression);
    expect(result.source).toBe(initial.source);
    expect(JSON.stringify(initial)).toBe(before);
  });
  it('rejects an unchecked expansion and a preview of a different definition', () => {
    const initial = fixture();
    initial.definitionPreviews![0]!.tree.expansion!.definitionalEquality = false as true;
    expect(inspectSmallDefinitions(initial)).toBe(initial);
    initial.definitionPreviews![0]!.tree.expansion!.definitionalEquality = true;
    initial.definitionPreviews![0]!.constant = 'Unrequested.definition';
    expect(inspectSmallDefinitions(initial)).toBe(initial);
  });
  it('does not expand a theorem or a definition without reduced unknown meaning', () => {
    const initial = fixture();
    initial.definitions![0]!.canExpand = false;
    expect(inspectSmallDefinitions(initial)).toBe(initial);
    initial.definitions![0]!.canExpand = true;
    const unknown = { ...node(constant('Other.unknown')), expansion: initial.definitionPreviews![0]!.tree.expansion };
    initial.definitionPreviews![0]!.tree = unknown;
    initial.definitionPreviews![0]!.expression = unknown.expression;
    expect(inspectSmallDefinitions(initial)).toBe(initial);
  });
  it('keeps a preview with truncated exports or an excessive tree folded', () => {
    const initial = fixture();
    initial.definitionPreviews![0]!.tree.children = Array.from({ length: 80 }, (_, i) => ({ ...node(equal), id: `child${i}` }));
    expect(inspectSmallDefinitions(initial)).toBe(initial);
    const opaque = fixture();
    opaque.definitionPreviews![0]!.tree.expression = { kind: 'opaque', text: 'truncated' };
    expect(inspectSmallDefinitions(opaque)).toBe(opaque);
  });
  it('preserves an explicitly inspected definition body and absent previews', () => {
    const initial = fixture(); initial.definitionTree = node(equal);
    expect(inspectSmallDefinitions(initial)).toBe(initial);
    delete initial.definitionTree; delete initial.definitionPreviews;
    expect(inspectSmallDefinitions(initial)).toBe(initial);
  });
});
