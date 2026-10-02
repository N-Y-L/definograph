import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { MathLabel } from './MathLabel';
import { expressionMathDisplay, identifierMathDisplay, mathDisplay, withMathProse } from '../notation/math-display';
import { estimatedMathLabelSize, measureMathLabel, sameMathLabelSize } from './math-label-measure';

describe('measured SVG mathematical labels', () => {
  it('emits local KaTeX HTML and MathML in XHTML with a separate baseline probe and source label', () => {
    const label = withMathProse(identifierMathDisplay('δ₁'), 'radius ');
    const html = renderToStaticMarkup(createElement('svg', {}, createElement('g', { 'data-reading-object': 'actual-source-id', role: 'button', tabIndex: 0 },
      createElement(MathLabel, { label, labelKey: 'radius', x: 100, y: 50, fontSize: 18 }))));
    expect(html).toContain('data-reading-object="actual-source-id"'); expect(html).toContain('role="button"');
    expect(html).toContain('data-diagram-source="radius δ₁"'); expect(html).toContain('data-math-baseline-y="50"');
    expect(html).toContain('<foreignObject'); expect(html).toContain('xmlns="http://www.w3.org/1999/xhtml"');
    expect(html).toContain('class="katex-html"'); expect(html).toContain('class="katex-mathml"'); expect(html).toContain('<msub>');
    expect(html).toContain('data-math-measure'); expect(html).toContain('data-math-baseline');
    expect(html).not.toContain('<script'); expect(html).not.toContain('<link');
  });
  it('retains a plain SVG source fallback for unsupported expressions or rejected TeX', () => {
    for (const label of [expressionMathDisplay({ kind: 'opaque', text: '<uninterpreted>' }), { ...identifierMathDisplay('x'), latex: '\\notARealCommand{x}' }]) {
      const html = renderToStaticMarkup(createElement('svg', {}, createElement(MathLabel, { label, labelKey: 'fallback', x: 30, y: 20 })));
      expect(html).toContain('data-math-fallback="source"'); expect(html).not.toContain('<foreignObject');
      expect(html).not.toContain('<a '); expect(html).not.toContain('href=');
    }
  });
  it('does not enable URLs or HTML even when a caller supplies untrusted TeX', () => {
    for (const latex of ['\\href{https://example.test}{x}', '\\includegraphics{https://example.test/x.png}', '\\htmlStyle{position:fixed}{x}']) {
      const html = renderToStaticMarkup(createElement('svg', {}, createElement(MathLabel, { label: { source: 'x', key: latex, latex }, labelKey: 'hostile', x: 30, y: 20 })));
      expect(html).not.toMatch(/<(?:a|img|script)\b/); expect(html).not.toContain('href='); expect(html).not.toContain('style="position:fixed');
    }
  });
  it('keeps identically named source groups independent of their mathematical glyphs', () => {
    const label = identifierMathDisplay('x');
    const html = renderToStaticMarkup(createElement('svg', {}, ['outer-x', 'inner-x'].map((id, index) => createElement('g', { key: id, 'data-reading-object': id }, createElement(MathLabel, { label, labelKey: id, x: index * 100, y: 30 })))));
    expect(html).toContain('data-reading-object="outer-x"'); expect(html).toContain('data-reading-object="inner-x"');
    expect((html.match(/<foreignObject/g) ?? []).length).toBe(2);
  });
  it('converts measured natural HTML dimensions and baseline to unscaled SVG units', () => {
    const natural = { getBoundingClientRect: () => ({ width: 240, height: 120, top: 60, bottom: 180 }) };
    const marker = { getBoundingClientRect: () => ({ top: 150 }) };
    const group = { querySelector: (selector: string) => selector === '[data-math-measure]' ? natural : marker,
      getScreenCTM: () => ({ a: 2, b: 0, c: 0, d: 3 }) } as unknown as SVGGElement;
    expect(measureMathLabel(group)).toEqual({ width: 120, height: 40, ascent: 30, descent: 10 });
    expect(sameMathLabelSize(measureMathLabel(group), { width: 120.1, height: 40, ascent: 30, descent: 10 })).toBe(true);
    expect(sameMathLabelSize(measureMathLabel(group), { width: 121, height: 40, ascent: 30, descent: 10 })).toBe(false);
  });
  it('keeps stacked fraction estimates finite for SSR before browser fonts resolve', () => {
    const label = mathDisplay({ kind: 'binary', operator: 'div', left: { kind: 'identifier', name: 'α' }, right: { kind: 'identifier', name: 'β' } });
    const html = renderToStaticMarkup(createElement('svg', {}, createElement(MathLabel, { label, labelKey: 'fraction', x: 100, y: 80, fontSize: 20 })));
    expect(html).toContain('class="mfrac"'); expect(html).not.toContain('NaN');
    expect(estimatedMathLabelSize(label.source, 20)).toMatchObject({ height: 36, ascent: 26, descent: 10 });
  });
});
