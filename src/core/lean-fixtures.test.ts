import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { ballGeometry, discoverScenes, evaluateExpression, initialScenario, sampleGraph, sliceGeometry } from './index';
import type { StatementNode } from './types';

function fixture(name: string): StatementNode {
  return JSON.parse(readFileSync(new URL(`./fixtures/${name}.json`, import.meta.url), 'utf8')).tree as StatementNode;
}

describe('real Lean exporter snapshots', () => {
  it('recognizes product balls with actual Membership.mem ordering and the max metric', () => {
    const tree = fixture('product-ball');
    const scene = discoverScenes(tree).find(s => s.kind === 'ball');
    expect(scene?.kind).toBe('ball');
    if (scene?.kind !== 'ball') throw new Error('Missing ball scene');
    expect(scene.metric).toBe('sup2');
    expect(ballGeometry(scene, initialScenario(tree))).toMatchObject({ center: [0, 0], radius: 1, point: [0, 0], membership: { status: 'true' } });
  });
  it('interprets a standard Euclidean zero vector and radius numeral', () => {
    const tree = fixture('euclidean-ball');
    const scene = discoverScenes(tree).find(s => s.kind === 'ball');
    if (scene?.kind !== 'ball') throw new Error('Missing ball scene');
    expect(ballGeometry(scene, initialScenario(tree))).toMatchObject({ metric: 'euclidean2', center: [0, 0], radius: 1, boundary: 'closed' });
  });
  it('extracts an explicit function body with working binder references', () => {
    const tree = fixture('lambda-graph');
    const scene = discoverScenes(tree).find(s => s.kind === 'graph');
    if (scene?.kind !== 'graph') throw new Error('Missing function graph');
    expect(sampleGraph(scene, initialScenario(tree), { min: -2, max: 2, count: 3 })).toEqual([{ x: -2, y: 4 }, { x: 0, y: 0 }, { x: 2, y: 4 }]);
  });
  it('retains ambient and intrinsic dimensions for a four-dimensional sphere', () => {
    const tree = fixture('four-dimensional-sphere');
    const scene = discoverScenes(tree).find(s => s.kind === 'ball');
    if (scene?.kind !== 'ball') throw new Error('Missing sphere scene');
    expect(sliceGeometry(scene, initialScenario(tree))).toMatchObject({ ambientDimension: 4, intrinsicDimension: 3, radius: 1, boundary: 'sphere', pointInSlice: true });
  });
  it('refuses to draw a disk for an overridden metric instance', () => {
    expect(discoverScenes(fixture('custom-metric')).filter(s => s.kind === 'ball')).toEqual([]);
  });
  it('refuses numerical interpretation of an overridden real addition instance', () => {
    const tree = fixture('custom-addition');
    const all: StatementNode[] = [];
    const walk = (n: StatementNode): void => { all.push(n); n.children.forEach(walk); };
    walk(tree);
    const leaf = all.find(n => n.kind === 'predicate');
    if (!leaf || leaf.expression.kind !== 'app') throw new Error('Missing custom-operation predicate');
    const custom = leaf.expression.args.find(a => a.kind === 'app' && a.standard === false);
    expect(custom).toBeDefined();
    if (custom) expect(evaluateExpression(custom, initialScenario(tree)).status).toBe('unknown');
  });
});
