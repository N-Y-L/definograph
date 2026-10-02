import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { BallScene, Expr } from '../core';
import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';
import { MetricStatementFigure } from './MetricStatementFigure';
import { layoutMetricInterval } from './metric-interval-layout';

const label = (width: number, height = 18, ascent = height * .8): DiagramTextSize => ({ width, height, ascent, descent: height - ascent });
const boxAt = (size: DiagramTextSize, x: number, y: number): DiagramRect => ({ x: x - size.width / 2, y: y - size.ascent, width: size.width, height: size.height });
const overlaps = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;

describe('metric interval label layout', () => {
  it('keeps full endpoint formulas apart and all labels within the figure, including wide and tall glyphs', () => {
    for (const left of [label(28), label(267), label(930, 65)]) for (const right of [label(30), label(267), label(740, 82, 33)]) {
      for (const point of [undefined, label(180), label(1300, 125)]) for (const atEndpoint of [false, true]) {
        const center = label(730, 48), layout = layoutMetricInterval({ left, right, center, point }, atEndpoint);
        const boxes = [boxAt(left, layout.leftX, layout.endpointY), boxAt(right, layout.rightX, layout.endpointY), boxAt(center, layout.centerX, layout.centerY)];
        if (point) boxes.push(boxAt(point, layout.pointX, layout.pointY));
        for (const [i, box] of boxes.entries()) {
          expect(box.x).toBeGreaterThanOrEqual(24);
          expect(box.x + box.width).toBeLessThanOrEqual(layout.width - 24);
          expect(box.y).toBeGreaterThanOrEqual(24);
          expect(box.y + box.height).toBeLessThanOrEqual(layout.height - 24);
          for (const other of boxes.slice(i + 1)) expect(overlaps(box, other)).toBe(false);
        }
        expect(boxes[1].x - boxes[0].x - boxes[0].width).toBeGreaterThanOrEqual(24);
        expect(boxes[0].y).toBeGreaterThan(layout.axisY + 5);
        expect(boxes[1].y).toBeGreaterThan(layout.axisY + 5);
        if (point) expect(boxes[3].y + boxes[3].height).toBeLessThan(layout.axisY - 5);
      }
    }
  });

  it('keeps the canvas scale stable across the observed subpixel glyph variations', () => {
    // Chrome's scaled fallback font measured these two widths for the same
    // mixed CJK/Latin labels; using each fractional extent caused a render loop.
    const first = layoutMetricInterval({ left: label(693.46234), right: label(693.46234), center: label(713.78595), point: label(1201.57971) }, true);
    const second = layoutMetricInterval({ left: label(693.77429), right: label(693.77429), center: label(714.10773), point: label(1202.11536) }, true);
    expect(first.width).toBe(second.width);
    expect(Number.isInteger(first.width)).toBe(true);
  });

  it('preserves endpoint order, the center midpoint, and the existing schematic point placement', () => {
    const labels = { left: label(400), right: label(560), center: label(160), point: label(390) };
    const interval = layoutMetricInterval(labels, false), sphere = layoutMetricInterval(labels, true);
    for (const layout of [interval, sphere]) {
      expect(layout.leftX).toBeLessThan(layout.rightX);
      expect(layout.centerX).toBe((layout.leftX + layout.rightX) / 2);
      expect(layout.leftX - 50).toBeGreaterThan(0);
      expect(layout.rightX + 50).toBeLessThan(layout.width);
    }
    expect((interval.pointX - interval.leftX) / (interval.rightX - interval.leftX)).toBeCloseTo(75 / 220);
    expect(sphere.pointX).toBe(sphere.leftX);
  });

  it('measures complete formulas in the actual component without changing open, closed, or sphere semantics', () => {
    const variable = (id: string, name: string): Expr => ({ kind: 'var', id, name, type: 'ℝ' });
    const center = variable('c', 'referenceConfiguration'), radius = variable('r', 'admissibleRadius'), point = variable('p', 'perturbedConfiguration');
    const scene: BallScene = { id: 'interval', nodeId: 'clause', title: 'Metric condition', kind: 'ball', expression: radius,
      metric: 'real', dimension: 1, center, point, radius, boundary: 'open', scope: [], guards: [], context: [] };
    for (const [boundary, relation] of [['open', '&lt;'], ['closed', '≤'], ['sphere', '=']] as const) {
      const html = renderToStaticMarkup(createElement(MetricStatementFigure, { scene: { ...scene, boundary } }));
      for (const [key, text] of [['left', 'referenceConfiguration − admissibleRadius'], ['right', 'referenceConfiguration + admissibleRadius'], ['center', 'center referenceConfiguration'], ['point', `perturbedConfiguration${boundary === 'sphere' ? ' (either endpoint)' : ''}`]]) {
        expect(html).toContain(`data-diagram-label="${key}" data-diagram-source="${text}"`);
      }
      expect(html).toContain(`dist(perturbedConfiguration, referenceConfiguration) ${relation} admissibleRadius`);
      expect(html).toContain(`class="metric-endpoint ${boundary}"`);
      expect(html.includes('class="metric-interval"')).toBe(boundary !== 'sphere');
      expect(html).toContain('Schematic positions; no coordinates chosen. Named points may coincide.');
      expect(html).not.toContain('…');
      expect(html).toContain('class="katex"');
      expect(html).toContain('<foreignObject');
    }
  });
});
