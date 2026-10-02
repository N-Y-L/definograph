import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode } from '../core';
import { compileSemanticDocument } from '../semantic';
import { compileReading } from '../reading';
import { StatementReadingView } from './StatementReadingView';
import { layoutContainedRelation, layoutRelationComparison } from './relation-diagram-layout';
import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';

const label = (width: number, height = 24): DiagramTextSize => ({ width, height, ascent: height * .8, descent: height * .2 });
const corners = (box: DiagramRect) => [[box.x, box.y], [box.x + box.width, box.y], [box.x, box.y + box.height], [box.x + box.width, box.y + box.height]];
const overlaps = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;
function ellipseValue(x: number, y: number, ellipse: { x: number; y: number; rx: number; ry: number }) {
  return ((x - ellipse.x) / ellipse.rx) ** 2 + ((y - ellipse.y) / ellipse.ry) ** 2;
}

describe('relation diagram label geometry', () => {
  it('contains actual glyph rectangles and keeps distinct labels separate for short, wide, and tall glyphs', () => {
    for (const nested of [false, true]) for (const first of [label(18), label(432), label(780, 60)]) for (const second of [label(22), label(460), label(910, 120)]) {
      const layout = layoutContainedRelation(first, second, nested);
      const { outer, inner } = layout;
      expect(overlaps(outer.label, inner.label)).toBe(false);
      for (const box of [outer.label, inner.label]) for (const [x, y] of corners(box)) {
        expect(ellipseValue(x, y, outer)).toBeLessThan(1);
        expect(x).toBeGreaterThan(0); expect(x).toBeLessThan(layout.width);
        expect(y).toBeGreaterThan(0); expect(y).toBeLessThan(layout.height);
      }
      if (nested) {
        for (const [x, y] of corners(inner.label)) expect(ellipseValue(x, y, inner)).toBeLessThan(1);
        expect(outer.label.y + outer.label.height).toBeLessThan(inner.y - inner.ry);
        // Read back the entire drawn inner boundary, not just its bounding box.
        for (let angle = 0; angle < 2 * Math.PI; angle += .01) {
          expect(ellipseValue(inner.x + inner.rx * Math.cos(angle), inner.y + inner.ry * Math.sin(angle), outer)).toBeLessThan(1);
        }
      } else {
        expect(inner.label.y).toBeGreaterThan(inner.y + 8);
        expect(outer.label.y + outer.label.height).toBeLessThan(inner.y - 8);
        expect(ellipseValue(inner.x, inner.y, outer)).toBeLessThan(1);
      }
    }
  });

  it('keeps comparison boxes apart and sizes each from its own measured label', () => {
    for (const left of [label(18), label(432), label(780, 60)]) for (const right of [label(22), label(460), label(910, 120)]) {
      const symbol = label(28, 32), layout = layoutRelationComparison(left, right, symbol);
      const boxes = [layout.left, layout.right];
      for (const [index, size] of [left, right].entries()) {
        const box = boxes[index];
        expect(box.labelX - size.width / 2).toBeGreaterThan(box.x);
        expect(box.labelX + size.width / 2).toBeLessThan(box.x + box.width);
        expect(box.labelY - size.ascent).toBeGreaterThan(box.y);
        expect(box.labelY + size.descent).toBeLessThan(box.y + box.height);
      }
      expect(layout.left.x + layout.left.width).toBeLessThan(layout.symbolX - symbol.width / 2);
      expect(layout.symbolX + symbol.width / 2).toBeLessThan(layout.right.x);
      expect(layout.right.x + layout.right.width).toBeLessThan(layout.width);
    }
  });

  it('uses measured figures in the real reader while retaining complete labels and object identity', () => {
    const wide = 'W'.repeat(36), unicode = '界'.repeat(36);
    const variable = (name: string, type = 'X'): Expr => ({ kind: 'var', id: name, name, type });
    const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: { kind: 'const', name }, args, argumentKinds: args.map(() => 'value') });
    const equality = { ...app('Eq', [variable(wide), variable(unicode)]), typeDescriptor: { kind: 'proposition' as const, lean: 'Prop' } };
    const wrapper: Expr = { kind: 'app', fn: variable('P', 'Prop → Prop'), args: [equality], argumentKinds: ['value'] };
    for (const [kind, expression] of [['membership', app('Set.Mem', [variable(wide, 'Set X'), variable(unicode)])], ['subset', app('Set.Subset', [variable(wide, 'Set X'), variable(unicode, 'Set X')])], ['equality', wrapper]] as const) {
      const tree: StatementNode = { id: 'unfamiliar', kind: 'predicate', label: 'condition', lean: 'condition', expression, children: [] };
      const document = compileSemanticDocument({ source: 'layout regression', tree, expression });
      const relation = document.relations.find(candidate => candidate.kind === kind)!;
      expect(relation).toBeDefined();
      const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading: compileReading(document), selectedRelationId: relation.id, onObjectSelect: () => undefined }));
      expect(html).toContain('data-diagram-label="first"');
      expect(html).toContain('data-diagram-label="second"');
      expect(html).toContain(`aria-label="${wide} :`);
      expect(html).toContain(`aria-label="${unicode} :`);
      for (const port of relation.ports) expect(html).toContain(`data-reading-object="${port.objectId}"`);
      if (kind === 'subset') expect(html).toContain('The sets may be equal');
      if (kind === 'equality') expect(html).toContain('This inner relation is not asserted separately');
    }
  });
});
