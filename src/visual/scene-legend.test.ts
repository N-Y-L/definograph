import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { SceneView } from '../SceneView';
import type { BallScene } from '../core';

const scene: BallScene = { id: 'ball', nodeId: 'n', title: '', expression: { kind: 'const', name: 'Metric.ball' }, scope: [], guards: [], context: [], kind: 'ball', metric: 'euclideanN', dimension: 2, center: { kind: 'var', id: 'c', name: 'c', type: '' }, radius: { kind: 'literal', value: 1 }, point: { kind: 'var', id: 'p', name: 'p', type: '' }, boundary: 'open' };
const scenario = { c: [0, 0], p: [0.5, 0] };

describe('scene legends', () => {
  it('offer to move the representative point only when the scene can change it', () => {
    const passive = renderToStaticMarkup(createElement(SceneView, { scene, scenario }));
    const interactive = renderToStaticMarkup(createElement(SceneView, { scene, scenario, onVariableChange: () => undefined }));
    expect(passive).toContain('Representative point');
    expect(passive).not.toContain('click or drag');
    expect(interactive).toContain('Representative point · click or drag');
  });
});
