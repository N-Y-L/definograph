import { describe, expect, it } from 'vitest';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import type { BallScene, Expr } from '../core';
import type { DiagramTextSize } from '../components/map-diagram-layout';
import { layoutMetricShape, layoutMetricDistance } from './metric-region-layout';
import { MetricStatementFigure } from './MetricStatementFigure';
const size = (width: number, height: number, ascent = height * .7): DiagramTextSize => ({ width, height, ascent, descent: height - ascent });
const at = (label: DiagramTextSize, x: number, y: number, start = false) => ({ x: x - (start ? 0 : label.width / 2), y: y - label.ascent, width: label.width, height: label.height });
const overlaps = (a: ReturnType<typeof at>, b: ReturnType<typeof at>) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;
function check(labels: ReturnType<typeof at>[], width: number, height: number) {
  for (const [i, label] of labels.entries()) {
    expect(label.x).toBeGreaterThanOrEqual(0); expect(label.y).toBeGreaterThanOrEqual(0);
    expect(label.x + label.width).toBeLessThanOrEqual(width); expect(label.y + label.height).toBeLessThanOrEqual(height);
    for (const other of labels.slice(i + 1)) expect(overlaps(label, other)).toBe(false);
  }
}
describe('measured metric region labels', () => {
  it('keeps stacked and long labels outside a circle or square without changing point roles', () => {
    for (const sphere of [false, true]) for (const radius of [size(25, 18), size(300, 140), size(700, 450)]) {
      const center = size(580, 100), point = size(900, 85), layout = layoutMetricShape({ center, radius, point }, sphere);
      const labels = [at(center, layout.centerX, layout.centerLabelY), at(radius, layout.radiusX, layout.radiusY, true), at(point, layout.pointX, layout.pointLabelY)];
      check([...labels, { x: layout.centerX - 72, y: layout.centerY - 72, width: 144, height: 144 }], layout.width, layout.height);
      expect(layout.pointX - layout.centerX).toBe(sphere ? 0 : -30);
      expect(layout.pointY - layout.centerY).toBe(sphere ? -72 : -31);
      expect(layout.pointLeaderTop).toBeLessThan(layout.pointY);
    }
  });
  it('separates tall endpoint labels from the distance title and explanatory row', () => {
    const labels = { title: size(1200, 150), zero: size(20, 20), radius: size(900, 220), description: size(420, 24) };
    const layout = layoutMetricDistance(labels);
    check([at(labels.title, layout.width / 2, layout.titleY), at(labels.zero, layout.leftX, layout.endpointY),
      at(labels.radius, layout.rightX, layout.endpointY), at(labels.description, layout.width / 2, layout.descriptionY)], layout.width, layout.height);
    expect(layout.rightX).toBeGreaterThan(layout.leftX);
    expect(layout.axisY).toBeGreaterThan(layout.titleY + labels.title.descent);
  });
  it('typesets recorded arithmetic without changing source data or the region boundary', () => {
    const variable = (id: string): Expr => ({ kind: 'var', id, name: `${id}₁`, type: 'ℝ' });
    const quotient: Expr = { kind: 'app', fn: { kind: 'const', name: 'HDiv.hDiv', canonical: true },
      args: [variable('r'), variable('δ')], argumentKinds: ['value', 'value'], operator: 'div', standard: true, domain: 'real', type: 'ℝ' };
    const scene: BallScene = { kind: 'ball', id: 'metric', nodeId: 'clause', title: 'Metric condition', expression: quotient,
      metric: 'euclidean2', dimension: 2, center: variable('c'), point: variable('p'), radius: quotient,
      boundary: 'sphere', scope: [], guards: [], context: ['Inside a negation'] };
    const before = JSON.stringify(scene), html = renderToStaticMarkup(createElement(MetricStatementFigure, { scene }));
    expect(html).toContain('class="katex"'); expect(html).toContain('\\frac'); expect(html).toContain('<mfrac>');
    expect(html).toContain('class="metric-region sphere"'); expect(html).toContain('Boundary only.');
    expect(html).toContain('data-diagram-label="radius"'); expect(JSON.stringify(scene)).toBe(before);
    const fallback = renderToStaticMarkup(createElement(MetricStatementFigure, { scene: { ...scene, radius: { kind: 'opaque', text: 'unknown exact radius' } } }));
    expect(fallback).toContain('data-math-fallback="source"'); expect(fallback).toContain('unknown exact radius');
  });
});
