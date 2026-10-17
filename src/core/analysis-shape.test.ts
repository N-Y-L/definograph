import { readdirSync, readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { analysisShapeIssue } from './analysis-shape';
import type { Expr, StatementNode } from './types';

const constant = (name: string): Expr => ({ kind: 'const', name });
const x: Expr = { kind: 'var', id: 'x', name: 'x', type: 'ℝ' };
const leaf: StatementNode = { id: 'n.0', kind: 'predicate', label: 'x < 2', lean: 'x < 2', children: [], expression: { kind: 'app', fn: constant('LT.lt'), args: [x, { kind: 'literal', value: 2 }] } };
const tree: StatementNode = { id: 'n', kind: 'forall', label: '∀ x', lean: '∀ x, x < 2', children: [leaf], binder: { id: 'x', name: 'x', type: 'ℝ', role: 'universal', dependsOn: [] },
  expression: { kind: 'forall', binder: { id: 'x', name: 'x', type: 'ℝ', role: 'universal', dependsOn: [] }, binderType: constant('Real'), body: leaf.expression } };
const reply = (extra: Record<string, unknown> = {}) => ({ ok: true, source: '∀ x : ℝ, x < 2', pretty: '∀ (x : ℝ), x < 2', type: 'Prop', tree, expression: tree.expression, metrics: [], diagnostics: [], ...extra });

describe('analysis reply shape', () => {
  it('accepts every recorded tree of the real Lean exporter', () => {
    const directory = new URL('./fixtures/', import.meta.url);
    const names = readdirSync(directory).filter(name => name.endsWith('.json'));
    expect(names.length).toBeGreaterThan(0);
    for (const name of names) {
      const recorded = JSON.parse(readFileSync(new URL(name, directory), 'utf8')) as { source: string; tree: StatementNode };
      expect(analysisShapeIssue({ ok: true, source: recorded.source, pretty: recorded.source, tree: recorded.tree, expression: recorded.tree.expression, diagnostics: [] }), name).toBeUndefined();
    }
  });

  it('accepts a complete reply, with optional fields absent, null or present', () => {
    expect(analysisShapeIssue(reply())).toBeUndefined();
    expect(analysisShapeIssue(reply({ definitionTree: null, definitionExpression: null, validation: 'kernel-type-checked-statement' }))).toBeUndefined();
    expect(analysisShapeIssue(reply({
      definitionTree: tree, sourceTerms: [{ startByte: 0, endByte: 3, lean: 'x', type: 'ℝ', isBinder: true, origin: 'lean-infotree' }],
      definitions: [{ name: 'LT.lt', kind: 'definition', type: 'α → α → Prop', canExpand: false }],
      definitionPreviews: [{ constant: 'LT.lt', pretty: 'x < 2', tree: leaf, expression: leaf.expression, expansionPolicy: { constants: ['LT.lt'], maxDepth: 1 } }],
      readableMath: { provider: 'leantex', status: 'unavailable', reason: 'test' }, provenance: { assistant: 'lean', inputMode: 'term' },
    }))).toBeUndefined();
  });

  it('accepts a very deep statement without exhausting the call stack', () => {
    let deep: StatementNode = leaf;
    for (let depth = 0; depth < 20_000; depth++) deep = { ...leaf, id: `d${depth}`, children: [deep] };
    expect(analysisShapeIssue(reply({ tree: deep }))).toBeUndefined();
  });

  it('names the first field the reader would fail on', () => {
    const child = (change: Record<string, unknown>) => reply({ tree: { ...tree, children: [{ ...leaf, ...change }] } });
    const cases: [unknown, string][] = [
      [null, 'the reply is not an object'],
      [[], 'the reply is not an object'],
      [reply({ ok: false }), 'ok is not true'],
      [reply({ pretty: undefined }), 'pretty is not text'],
      [reply({ diagnostics: 'none' }), 'diagnostics is not a list'],
      [reply({ validation: 3 }), 'validation is not text'],
      [reply({ tree: undefined }), 'tree is not a statement node'],
      [reply({ tree: { ...tree, children: 'none' } }), 'tree.children is not a list'],
      [child({ lean: undefined }), 'tree.children[0].lean is not text'],
      [child({ expression: { kind: 'app', fn: constant('f'), args: [{ kind: 'mystery' }] } }), 'tree.children[0].expression.args[0].kind is not a known expression kind'],
      [child({ expression: { kind: 'var', id: 'x', name: 'x' } }), 'tree.children[0].expression.type is missing'],
      [reply({ tree: { ...tree, binder: { ...tree.binder, dependsOn: 'x' } } }), 'tree.binder.dependsOn is not a list of names'],
      [reply({ expression: { kind: 'forall', binder: { id: 'x' }, body: x } }), 'expression.binder has no id, name or type'],
      [reply({ definitionTree: 'body' }), 'definitionTree is not a statement node'],
      [reply({ sourceTerms: {} }), 'sourceTerms is not a list'],
      [reply({ sourceTerms: [{ startByte: 0, lean: 'x', type: 'ℝ' }] }), 'sourceTerms[0] has no byte range'],
      [reply({ definitions: [{ name: 'f' }] }), 'definitions[0] has no name or expansion flag'],
      [reply({ definitionPreviews: [{ constant: 'f', pretty: 'f', tree: {}, expression: x }] }), 'definitionPreviews[0].tree.id is not text'],
      [reply({ provenance: 'lean' }), 'provenance is not an object'],
    ];
    for (const [value, issue] of cases) expect(analysisShapeIssue(value), issue).toBe(issue);
  });
});
