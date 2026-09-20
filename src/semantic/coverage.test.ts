import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from './compiler';
import { compileInterpretationReport } from './coverage';

const c = (name: string): Expr => ({ kind: 'const', name });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: c(name), args });
const leaf = (id: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean: id, expression, children: [] });
const compile = (tree: StatementNode) => compileSemanticDocument({ source: 'test', tree, expression: tree.expression });

describe('interpretation reports', () => {
  it('distinguishes unknown outer meaning from interpreted constructions inside it', () => {
    const doc = compile(leaf('root', app('Custom.Condition', [app('Eq', [c('Nat'), { kind: 'literal', value: 2 }, { kind: 'literal', value: 2 }])])));
    const report = compileInterpretationReport(doc, [{ name: 'Custom.Condition', kind: 'definition', type: 'Prop → Prop', canExpand: true }]);
    expect(report.clauses).toEqual({ total: 1, interpreted: 0, partial: 1, structural: 0 });
    expect(report.gaps[0]).toMatchObject({ constant: 'Custom.Condition', canExpand: true, nodeIds: ['root'] });
    expect(report.gaps[0]!.retainedRelationIds).toHaveLength(1);
    expect(report.vocabulary).toEqual([{ id: 'relations', label: 'Equality and order', relationCount: 1 }]);
  });
  it('groups repeated constants while preserving all scopes and filters the selected branch', () => {
    const left = leaf('left', app('Unknown.P', [c('A')])), right = leaf('right', app('Unknown.P', [c('B')]));
    const root: StatementNode = { id: 'root', kind: 'or', label: 'or', lean: 'P A ∨ P B', expression: c('Or'), children: [left, right] };
    const doc = compile(root);
    expect(compileInterpretationReport(doc).gaps[0]).toMatchObject({ occurrences: 2, nodeIds: ['left', 'right'], scopeIds: ['scope:left', 'scope:right'] });
    expect(compileInterpretationReport(doc, [], 'right').gaps[0]).toMatchObject({ occurrences: 1, nodeIds: ['right'], scopeIds: ['scope:right'] });
    expect(() => compileInterpretationReport(doc, [], 'missing')).toThrow('Unknown statement node');
  });
  it('does not infer expansion eligibility from a familiar name or a theorem declaration', () => {
    const expr: Expr = { kind: 'app', fn: { kind: 'const', name: 'Metric.ball', canonical: false }, args: [c('x'), c('r')] };
    const doc = compile(leaf('root', expr));
    expect(compileInterpretationReport(doc, [{ name: 'Metric.ball', kind: 'theorem', type: 'Prop', canExpand: false }]).gaps[0]).toMatchObject({ constant: 'Metric.ball', canExpand: false });
    expect(compileInterpretationReport(doc).vocabulary).toHaveLength(0);
  });
  it('reports opaque export boundaries independently without merging printed labels', () => {
    const left = leaf('left', { kind: 'opaque', text: 'large expression' }), right = leaf('right', { kind: 'opaque', text: 'large expression' });
    const doc = compile({ id: 'root', kind: 'and', label: 'and', lean: '', expression: c('And'), children: [left, right] });
    const report = compileInterpretationReport(doc);
    expect(report.gaps).toHaveLength(2);
    expect(report.gaps.every(gap => gap.kind === 'opaque' && !gap.canExpand)).toBe(true);
  });
});
