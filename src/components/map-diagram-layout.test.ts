import { describe, expect, it } from 'vitest';
import { layoutMapDiagram, type DiagramPoint, type DiagramRect, type MapDiagramEdge } from './map-diagram-layout';

const label = (width: number, height = 22) => ({ width, height, ascent: height - 4, descent: 4 });
const edge = (id: string, from: string, to: string, width = 180): MapDiagramEdge => ({ id, from, to, label: label(width) });
const overlaps = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height;
// Independent readback of the drawn orthogonal segments against the actual
// label rectangles. Crossings between edges are deliberately allowed.
function crossesRect(a: DiagramPoint, b: DiagramPoint, box: DiagramRect) {
  if (a.x === b.x) return a.x > box.x && a.x < box.x + box.width && Math.max(a.y, b.y) > box.y && Math.min(a.y, b.y) < box.y + box.height;
  if (a.y === b.y) return a.y > box.y && a.y < box.y + box.height && Math.max(a.x, b.x) > box.x && Math.min(a.x, b.x) < box.x + box.width;
  throw new Error('Unexpected non-orthogonal segment');
}
function check(layout: ReturnType<typeof layoutMapDiagram>) {
  const boxes = layout.nodes.map(node => ({ ...node, x: node.x - node.width / 2 }));
  const labels = layout.edges.map(route => route.labelBox);
  for (const [i, box] of [...boxes, ...labels].entries()) {
    expect(box.x).toBeGreaterThanOrEqual(0);
    expect(box.y).toBeGreaterThanOrEqual(0);
    expect(box.x + box.width).toBeLessThanOrEqual(layout.width);
    expect(box.y + box.height).toBeLessThanOrEqual(layout.height);
    for (const other of [...boxes, ...labels].slice(i + 1)) expect(overlaps(box, other)).toBe(false);
  }
  for (const route of layout.edges) {
    for (let i = 1; i < route.points.length; i++) for (const box of labels) expect(crossesRect(route.points[i - 1], route.points[i], box)).toBe(false);
    const from = layout.nodes.find(node => node.id === route.from)!, to = layout.nodes.find(node => node.id === route.to)!;
    for (const [point, node] of [[route.points[0], from], [route.points.at(-1)!, to]] as const) {
      expect(Math.abs(point.x - node.x)).toBe(node.width / 2);
      expect(point.y).toBeGreaterThan(node.y);
      expect(point.y).toBeLessThan(node.y + node.height);
    }
  }
}

describe('map diagram geometry', () => {
  it('separates repeated self-map labels and retains every exact endpoint', () => {
    const nodes = [{ id: 'A', width: 68, height: 40 }], edges = Array.from({ length: 4 }, (_, i) => edge(`loop:${i}`, 'A', 'A', 188 + i));
    const layout = layoutMapDiagram(nodes, edges);
    check(layout);
    expect(layout.edges.map(route => [route.id, route.from, route.to])).toEqual(edges.map(route => [route.id, route.from, route.to]));
    expect(layoutMapDiagram(nodes, edges)).toEqual(layout);
  });

  it('avoids shared-midpoint labels and edge interference for long structural carriers', () => {
    const nodes = ['A', 'B', 'C'].map(id => ({ id, width: 310, height: 176 }));
    const edges = [edge('outer1', 'A', 'C', 264), edge('loop1', 'B', 'B', 263), edge('outer2', 'A', 'C', 266), edge('loop2', 'B', 'B', 265), edge('loop3', 'B', 'B', 267)];
    check(layoutMapDiagram(nodes, edges));
  });

  it('handles reverse and overlapping connections without imposing a ban on crossings', () => {
    const nodes = ['A', 'B', 'C', 'D'].map((id, i) => ({ id, width: 90 + i * 30, height: 40 + i * 20 }));
    const edges = [edge('ac', 'A', 'C', 300), edge('db', 'D', 'B', 75), edge('bc', 'B', 'C', 260), edge('aa', 'A', 'A', 225)];
    check(layoutMapDiagram(nodes, edges));
    expect(layoutMapDiagram(nodes, edges).edges.map(route => route.id)).toEqual(['ac', 'db', 'bc', 'aa']);
  });

  it('grows from measured text and rejects edges without declared endpoints', () => {
    const nodes = [{ id: 'A', width: 80, height: 40 }, { id: 'B', width: 120, height: 40 }];
    const small = layoutMapDiagram(nodes, [edge('ab', 'A', 'B', 30)]), large = layoutMapDiagram(nodes, [edge('ab', 'A', 'B', 480)]);
    check(small); check(large);
    expect(large.width).toBeGreaterThan(small.width);
    expect(() => layoutMapDiagram(nodes, [edge('missing', 'A', 'outside')])).toThrow('both declared endpoints');
    check(layoutMapDiagram(nodes, []));
  });
});
