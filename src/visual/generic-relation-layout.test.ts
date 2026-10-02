import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';
import type { Expr, StatementNode } from '../core';
import { compileSemanticDocument } from '../semantic';
import { compileReading } from '../reading';
import { labelShape, layoutExpressionFlow, layoutRegionLink } from './generic-relation-layout';
import { expressionMapPath, StatementReadingView } from './StatementReadingView';

const size = (width: number, height = 24): DiagramTextSize => ({ width, height, ascent: height * .8, descent: height * .2 });
const overlap = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;
const variable = (name: string): Expr => ({ kind: 'var', name, id: name, type: 'X' });
const call = (fn: Expr, args: Expr[]): Expr => ({ kind: 'app', fn, args, argumentKinds: args.map(() => 'value') });

describe('generic measured relation layouts', () => {
  it('reserves full tall and wide labels in every flow column, without limiting ordered inputs', () => {
    for (const inputs of [[size(20)], [size(600, 130), size(25), size(900, 80), size(380, 66)]]) {
      for (const maps of [[], [size(850, 120)], [size(480), size(620, 75), size(720, 60)]]) {
        const layout = layoutExpressionFlow(inputs, maps, size(770, 110));
        const shapes = [...layout.inputs, ...layout.maps, layout.output];
        const labels = shapes.map(shape => ({ ...shape.label, x: shape.x + shape.label.x, y: shape.y + shape.label.y }));
        for (const [i, a] of labels.entries()) {
          expect(a.x).toBeGreaterThan(0); expect(a.y).toBeGreaterThan(0);
          expect(a.x + a.width).toBeLessThan(layout.width); expect(a.y + a.height).toBeLessThan(layout.height);
          for (const b of labels.slice(i + 1)) expect(overlap(a, b)).toBe(false);
        }
        for (const map of layout.maps) {
          expect(map.label.x).toBeGreaterThan(0);
          expect(map.label.y).toBeGreaterThan(0);
          expect(map.label.x + map.label.width).toBeLessThan(map.width);
          expect(map.label.y + map.label.height).toBeLessThan(map.height);
        }
        if (maps.length) expect(layout.inputs).toHaveLength(inputs.length);
      }
    }
  });

  it('keeps ellipse glyph corners inside and map labels above linked regions', () => {
    const left = labelShape(size(700, 120), 'ellipse'), right = labelShape(size(970, 170), 'ellipse');
    for (const shape of [left, right]) for (const x of [shape.label.x, shape.label.x + shape.label.width]) for (const y of [shape.label.y, shape.label.y + shape.label.height]) {
      expect(((x - shape.width / 2) / (shape.width / 2)) ** 2 + ((y - shape.height / 2) / (shape.height / 2)) ** 2).toBeLessThan(1);
    }
    const layout = layoutRegionLink(left, right, size(1500, 130));
    expect(layout.map.y + layout.map.height).toBeLessThan(Math.min(layout.left.y, layout.right.y));
    expect(layout.left.x + left.width).toBeLessThan(layout.map.x);
    expect(layout.map.x + layout.map.width).toBeLessThan(layout.right.x);
    expect(layout.right.x + right.width).toBeLessThan(layout.width);
  });

  it('aligns a membership input point with the contained output while retaining tall input labels', () => {
    const point = labelShape(size(400, 190), 'point'), region = { width: 550, height: 220 };
    const layout = layoutRegionLink(point, region, size(800, 90), point.pointY, 80);
    expect(layout.left.y + point.pointY!).toBe(layout.right.y + 80);
    expect(layout.left.y + point.height).toBeLessThan(layout.height);
    expect(layout.right.y + region.height).toBeLessThan(layout.height);
  });

  it('retains complete projected map expressions, inverse directions, and exact source IDs', () => {
    const name = 'owner.field_' + 'long'.repeat(20), x = variable('input_' + 'x'.repeat(40));
    const expression = call({ kind: 'const', name: 'Eq' }, [call(variable(name), [x]), variable('target_' + 'y'.repeat(40))]);
    const tree: StatementNode = { id: 'condition', kind: 'predicate', expression, label: 'condition', lean: 'condition', children: [] };
    const original = compileSemanticDocument({ source: 'measured flow', tree, expression });
    const application = original.relations.find(relation => relation.kind === 'application')!;
    const functionId = application.ports.find(port => port.role === 'function')!.objectId;
    const inverse = { ...application, kind: 'restricted-application' as const, restrictedDirection: 'inverse' as const,
      ports: application.ports.map(port => ({ ...port, role: port.role === 'function' ? 'map' : port.role === 'input 1' ? 'input' : port.role })) };
    const document = { ...original, relations: original.relations.map(relation => relation.id === application.id ? inverse : relation), objects: original.objects.map(object => object.id === functionId ? { ...object, provenance: [{ nodeId: tree.id, expressionPath: 'binder.structure.field', origin: 'elaborated-expression' as const }] } : object) };
    const equality = document.relations.find(relation => relation.kind === 'equality')!;
    const output = equality.ports.find(port => port.role === 'left')!.objectId;
    expect(expressionMapPath(output, document.relations).directions).toEqual(['inverse']);
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading: compileReading(document), onObjectSelect: () => undefined }));
    expect(html).toContain(`data-map-function="${functionId}"`);
    expect(html).toContain('data-map-direction="inverse"');
    expect(html).toContain(`data-diagram-source="(${name})⁻¹"`);
    expect(html).toContain(`data-reading-object="${functionId}"`);
    expect(html).toContain('msup');
    expect(html).not.toMatch(/data-diagram-source="[^"]*…/u);
  });

  it('retains every generic argument port, including one with the head identity', () => {
    const head: Expr = { kind: 'const', name: 'Unknown.predicate' };
    const expression = call(head, [head, variable('a'), variable('b'), variable('c'), variable('d')]);
    const tree: StatementNode = { id: 'generic', kind: 'predicate', expression, label: 'generic', lean: 'generic', children: [] };
    const document = compileSemanticDocument({ source: 'all argument ports', tree, expression });
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading: compileReading(document) }));
    for (let i = 0; i < 5; i++) expect(html).toContain(`data-diagram-label="argument:${i}"`);
    expect(html).toContain('data-diagram-source="Unknown.predicate"');
  });
});
