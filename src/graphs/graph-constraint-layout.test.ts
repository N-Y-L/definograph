import { describe, expect, it } from 'vitest';
import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';
import { layoutGraphAdjacency, layoutGraphRule, type GraphRuleText } from './graph-constraint-layout';

const size = (width: number, height = 19): DiagramTextSize => ({ width, height, ascent: height - 4, descent: 4 });
const overlaps = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;
function separatedWithin(boxes: DiagramRect[], width: number, height: number) {
  for (const [index, box] of boxes.entries()) {
    expect(box.x).toBeGreaterThanOrEqual(0);
    expect(box.y).toBeGreaterThanOrEqual(0);
    expect(box.x + box.width).toBeLessThanOrEqual(width);
    expect(box.y + box.height).toBeLessThanOrEqual(height);
    for (const other of boxes.slice(index + 1)) expect(overlaps(box, other)).toBe(false);
  }
}
const vertex = (x: number, y: number): DiagramRect => ({ x: x - 19, y: y - 19, width: 38, height: 38 });
function checkRule(kind: 'coloring' | 'map', text: GraphRuleText) {
  const layout = layoutGraphRule(kind, text);
  const labels = [...layout.endpoints, ...layout.outputs, layout.sourceAnnotation, layout.applyAnnotation, layout.resultAnnotation, ...(kind === 'coloring' ? [layout.inequality] : [])].map(label => label.box);
  const vertices = layout.x.map(x => vertex(x, layout.vertexY));
  separatedWithin([...labels, ...vertices, ...(kind === 'map' ? layout.x.map(x => vertex(x, layout.outputY)) : [])], layout.width, layout.height);
  // Read the drawn line segments against the glyph rectangles, independently
  // of the placement formula. A stroke may touch its own vertex, not a label.
  const lines = [
    { x1: layout.x[0] + 19, x2: layout.x[1] - 19, y1: layout.vertexY, y2: layout.vertexY },
    ...layout.x.map(x => ({ x1: x, x2: x, y1: layout.arrowTop, y2: layout.arrowBottom })),
    ...(kind === 'map' ? [{ x1: layout.x[0] + 19, x2: layout.x[1] - 19, y1: layout.outputY, y2: layout.outputY }] : []),
  ];
  for (const line of lines) for (const box of labels) {
    const crosses = line.x1 === line.x2
      ? line.x1 > box.x && line.x1 < box.x + box.width && line.y2 > box.y && line.y1 < box.y + box.height
      : line.y1 > box.y && line.y1 < box.y + box.height && line.x2 > box.x && line.x1 < box.x + box.width;
    expect(crosses).toBe(false);
  }
  if (kind === 'coloring') {
    separatedWithin([...layout.boxes, layout.inequality.box], layout.width, layout.height);
    for (const [index, label] of layout.outputs.entries()) {
      const box = layout.boxes[index];
      expect(label.box.x - box.x).toBeGreaterThanOrEqual(12);
      expect(box.x + box.width - label.box.x - label.box.width).toBeGreaterThanOrEqual(12);
      expect(label.box.y - box.y).toBeGreaterThanOrEqual(10);
      expect(box.y + box.height - label.box.y - label.box.height).toBeGreaterThanOrEqual(10);
    }
  }
  return layout;
}

describe('measured graph constraint geometry', () => {
  it.each(['coloring', 'map'] as const)('keeps %s labels, output footprints and arrows separated as glyph sizes change', kind => {
    for (const [width, height] of [[25, 19], [177, 19], [195, 22], [320, 33], [1240, 48]]) {
      checkRule(kind, { endpoints: [size(23, height), size(27, height + 3)], outputs: [size(width, height), size(width + 9, height + 3)], sourceAnnotation: size(190, 16), applyAnnotation: size(width + 110, height), resultAnnotation: size(180, 16), inequality: size(28, 36) });
    }
  });

  it('grows from measured output and map-caption footprints without changing the two column roles', () => {
    const text: GraphRuleText = { endpoints: [size(20), size(22)], outputs: [size(50), size(52)], sourceAnnotation: size(180), applyAnnotation: size(70), resultAnnotation: size(190), inequality: size(26, 35) };
    const small = checkRule('coloring', text);
    const large = checkRule('coloring', { ...text, outputs: [size(600), size(608)], applyAnnotation: size(980) });
    expect(large.width).toBeGreaterThan(small.width);
    expect(large.x[0]).toBeLessThan(large.center);
    expect(large.x[1]).toBeGreaterThan(large.center);
    expect(layoutGraphRule('coloring', text)).toEqual(small);
  });

  it('retains long actual endpoints and a single self-adjacent vertex', () => {
    for (const same of [false, true]) {
      const layout = layoutGraphAdjacency([size(840, 30), size(970, 34)], size(410, 21), same);
      const labels = (same ? [layout.labels[0]] : layout.labels).map(label => label.box);
      const vertices = (same ? [layout.x[0]] : layout.x).map(x => vertex(x, layout.vertexY));
      separatedWithin([...labels, ...vertices, layout.annotation.box], layout.width, layout.height);
      expect(layout.x[0] === layout.x[1]).toBe(same);
    }
  });
});
