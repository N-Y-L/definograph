import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { VariableControl } from '../VariableControl';
import { SceneView } from '../SceneView';
import type { BallScene, Binder } from '../core';

const binder = (dimension: number): Binder => ({ id: 'p', name: 'p', type: `EuclideanSpace ℝ (Fin ${dimension})`, domain: 'euclideanN', dimension, role: 'universal', dependsOn: [] });

describe('high-dimensional view controls', () => {
  it('offers one coordinate editor while retaining access to all 256 coordinates', () => {
    const html = renderToStaticMarkup(createElement(VariableControl, { binder: binder(256), value: Array(256).fill(0), onChange: () => undefined, names: {} }));
    expect((html.match(/type="range"/g) ?? [])).toHaveLength(1);
    expect((html.match(/<option/g) ?? [])).toHaveLength(256);
    expect(html).toContain('x256');
  });

  it('retains a large typed dimension symbolically without creating numerical inputs', () => {
    const html = renderToStaticMarkup(createElement(VariableControl, { binder: binder(1_000_000), value: undefined, onChange: () => undefined, names: {} }));
    expect(html).toContain('symbolic');
    expect(html).toContain('up to 256 coordinates');
    expect(html).not.toContain('<input');
    expect(html).not.toContain('<option');
  });

  it('initially shows an all-coordinate profile for a high-dimensional representative', () => {
    const scene: BallScene = { id: 'ball', nodeId: 'n', title: '', expression: { kind: 'const', name: 'Metric.ball' }, scope: [], guards: [], context: [], kind: 'ball', metric: 'euclideanN', dimension: 21, center: { kind: 'var', id: 'c', name: 'c', type: '' }, radius: { kind: 'literal', value: 1 }, point: { kind: 'var', id: 'p', name: 'p', type: '' }, boundary: 'open' };
    const html = renderToStaticMarkup(createElement(SceneView, { scene, scenario: { c: Array(21).fill(0), p: Array(21).fill(0) }, onVariableChange: () => undefined }));
    expect(html).toContain('all 21 coordinates shown');
    expect(html).toContain('Full 21-coordinate distance');
    expect(html).toContain('Coordinate slice');
    expect(html).not.toContain('Slice fixed coordinate');
  });
});
