import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { BallScene, Expr } from '../core';
import { MetricStatementFigure } from './MetricStatementFigure';
import { literalSign, metricReading } from './model';

const center: Expr = { kind: 'var', id: 'center', name: 'c', type: 'ℝ × ℝ' };
const point: Expr = { kind: 'var', id: 'point', name: 'p', type: 'ℝ × ℝ' };
const radius: Expr = { kind: 'var', id: 'radius', name: 'r', type: 'ℝ' };
// Preserve the native worker's full application shape, including hidden arguments.
const numeral = (value: number): Expr => ({
  kind: 'app', fn: { kind: 'const', name: 'OfNat.ofNat' },
  args: [{ kind: 'const', name: 'Real' }, { kind: 'literal', value }, { kind: 'opaque', text: 'Real.ofNat' }],
  argumentKinds: ['type', 'value', 'instance'], standard: true, domain: 'real', type: 'ℝ',
  typeDescriptor: { kind: 'real', lean: 'ℝ' },
});
const negation = (value: Expr, standard = true): Expr => ({
  kind: 'app', fn: { kind: 'const', name: 'Neg.neg' },
  args: [{ kind: 'const', name: 'Real' }, { kind: 'opaque', text: 'Real.instNeg' }, value],
  argumentKinds: ['type', 'instance', 'value'], standard, domain: 'real', type: 'ℝ',
  typeDescriptor: { kind: 'real', lean: 'ℝ' },
});
const scene = (changes: Partial<BallScene> = {}): BallScene => ({
  id: 'metric', nodeId: 'clause', title: 'Metric condition', kind: 'ball', expression: radius,
  metric: 'sup2', dimension: 2, center, point, radius, boundary: 'open', scope: [], guards: [], context: [],
  ...changes,
});
const render = (changes: Partial<BallScene> = {}) => renderToStaticMarkup(createElement(MetricStatementFigure, { scene: scene(changes) }));

describe('independent statement geometry regressions', () => {
  it('never draws one object at two positions when the named point is the center', () => {
    const html = render({ point: { ...center }, boundary: 'sphere', radius: numeral(1) });
    expect(metricReading(scene({ point: { ...center } })).pointIsCenter).toBe(true);
    expect(html).toContain('c is the center and the named point.');
    expect(html).toContain('dist(c, c) = 0');
    expect(html).toContain('Membership condition: 0 = 1');
    expect(html).not.toContain('<svg');
    expect(html).not.toContain('class="metric-point"');
  });

  it('does not infer identity from two binders having the same display name', () => {
    const distinct: Expr = { ...center, id: 'different-binder' };
    expect(metricReading(scene({ point: distinct })).pointIsCenter).toBe(false);
    const html = render({ point: distinct, radius: numeral(1) });
    expect(html).toContain('class="metric-point"');
    expect(html).not.toContain('metric-self-condition');
  });

  it('keeps the self-membership condition valid at zero and negative radii', () => {
    for (const [boundary, relation] of [['open', '&lt;'], ['closed', '≤'], ['sphere', '=']] as const) {
      for (const [r, label] of [[numeral(0), '0'], [negation(numeral(1)), '−1']] as const) {
        const html = render({ point: center, boundary, radius: r });
        expect(html).toContain(`Membership condition: 0 ${relation} ${label}`);
        expect(html).not.toContain('<svg');
        expect(html).not.toContain('Positive-radius case');
      }
    }
  });

  it('shows the empty region for every negative-radius constructor without a witness point', () => {
    for (const boundary of ['open', 'closed', 'sphere'] as const) {
      const html = render({ boundary, radius: negation(numeral(1)) });
      expect(html).toContain('The region is empty. No point belongs to it.');
      expect(html).not.toContain('<svg');
      expect(html).not.toContain('Positive-radius case');
    }
  });

  it('distinguishes empty open balls from singleton closed balls and spheres at zero in all supported dimensions', () => {
    for (const [metric, dimension] of [['real', 1], ['sup2', 2], ['euclideanN', 21]] as const) {
      const common = { radius: numeral(0), metric, dimension };
      expect(render({ ...common, boundary: 'open' })).toContain('The region is empty.');
      for (const boundary of ['closed', 'sphere'] as const) {
        const html = render({ ...common, boundary });
        expect(html).toContain('Only the center c. Membership requires p = c.');
        expect(html).not.toContain('<svg');
      }
    }
  });

  it('makes all radius cases visible when the radius is symbolic', () => {
    for (const boundary of ['open', 'closed', 'sphere'] as const) {
      const html = render({ boundary });
      expect(html).toContain('Positive-radius case · r &gt; 0');
      expect(html).toContain('<b>r = 0</b>');
      expect(html).toContain('<b>r &lt; 0</b> empty region');
      expect(html).toContain(boundary === 'open' ? 'empty region' : 'only c');
      expect(html).not.toContain('Uses the local assumption');
    }
  });

  it('does not interpret a replacement Neg instance as ordinary real negation', () => {
    expect(literalSign(negation(numeral(1)))).toBe(-1);
    expect(literalSign(negation(numeral(1), false))).toBeUndefined();
    expect(render({ radius: negation(numeral(1), false) })).toContain('Positive-radius case');
  });

  it('uses a distance condition for high dimensions without choosing a projection', () => {
    const html = render({ metric: 'euclideanN', dimension: 21, radius: numeral(1) });
    expect(html).toContain('Distance from c · all 21 dimensions');
    expect(html).toContain('Distance condition, without choosing a projection or coordinates.');
    expect(html).not.toContain('class="metric-region');
    expect(html).not.toContain('class="metric-point"');
  });
});
