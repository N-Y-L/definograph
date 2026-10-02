import { describe, expect, it } from 'vitest';
import { scopedFixture, fixture, leaf, call, variable } from '../reading/scoped-graph.test-fixtures';
import type { ScopedClauseGraph } from '../reading/scoped-graph';
import { layoutScopedGraph, type ScopedGraphNodeSize } from './scoped-graph-layout';
import { scopedGraphMathDisplay } from './scoped-graph-math';

const size = (width: number, height = 20) => ({ width, height, ascent: height * .8, descent: height * .2 });
function measured(graph: ScopedClauseGraph, wide = false) {
  return Object.fromEntries(graph.nodes.map((node, index) => [node.id, { label: size(wide ? 220 + index * 31 : 20 + node.label.length * 8), note: node.referenceNote ? size(160, 14) : undefined,
    ports: Object.fromEntries(node.ports.map(port => [port.id, size(20 + port.role.length * 7, 18)])) } satisfies ScopedGraphNodeSize]));
}
function validate(graph: ScopedClauseGraph, measurements = measured(graph)) {
  const layout = layoutScopedGraph(graph, measurements);
  expect(layout.nodes).toHaveLength(graph.nodes.length);
  expect(layout.edges).toHaveLength(graph.edges.length);
  for (const [index, box] of layout.nodes.entries()) {
    const text = measurements[box.id];
    expect(box.width).toBeGreaterThanOrEqual(text.label.width + 28);
    expect(box.height).toBeGreaterThanOrEqual(text.label.height + (text.note?.height ?? 0) + 22);
    for (const other of layout.nodes.slice(index + 1)) expect(box.x + box.width <= other.x || other.x + other.width <= box.x || box.y + box.height <= other.y || other.y + other.height <= box.y).toBe(true);
    for (const port of box.ports) {
      const text = measurements[box.id].ports[port.id];
      expect(port.labelY - text.ascent).toBeGreaterThan(box.y);
      expect(port.labelY + text.descent).toBeLessThanOrEqual(box.y + box.height);
    }
  }
  for (const edge of layout.edges) {
    for (const point of edge.points) { expect(point.x).toBeGreaterThanOrEqual(layout.x); expect(point.x).toBeLessThanOrEqual(layout.x + layout.width); expect(point.y).toBeGreaterThanOrEqual(0); expect(point.y).toBeLessThanOrEqual(layout.height); }
    // Independently check every routed segment against every unrelated box.
    for (const box of layout.nodes.filter(node => node.id !== edge.from && node.id !== edge.to)) for (let i = 1; i < edge.points.length; i++) {
      const a = edge.points[i - 1], b = edge.points[i];
      const intersects = a.x === b.x ? a.x > box.x && a.x < box.x + box.width && Math.max(a.y,b.y) > box.y && Math.min(a.y,b.y) < box.y + box.height
        : a.y > box.y && a.y < box.y + box.height && Math.max(a.x,b.x) > box.x && Math.min(a.x,b.x) < box.x + box.width;
      expect(intersects, `${edge.id} crosses ${box.id}`).toBe(false);
    }
  }
  return layout;
}
describe('bounded measured graph layout', () => {
  it('reserves actual long label bounds and routes around unrelated objects', () => {
    const graph = scopedFixture().model.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    const normal = validate(graph), long = validate(graph, measured(graph, true));
    expect(long.width).toBeGreaterThan(normal.width);
  });
  it('retains fan-in and repeated argument occurrences at distinct ports', () => {
    const source = scopedFixture(), x = variable(source.binders.point), fn = variable(source.binders.family);
    const application = { kind: 'app' as const, fn, args: Array.from({length:16}, () => x) };
    const value = fixture(leaf('many', 'many inputs', call('Eq', [application, application])));
    const graph = value.model.clauses[0].graphs[0], layout = validate(graph, measured(graph, true));
    const apply = layout.nodes.find(node => node.ports.length === 18)!;
    expect(new Set(apply.ports.filter(port => !port.output).map(port => port.y)).size).toBe(17);
    expect(new Set(layout.edges.map(edge => edge.portId)).size).toBe(layout.edges.length);
  });
  it('keeps cyclic supplied edges intact and routes them through reserved outer lanes', () => {
    const graph = scopedFixture().model.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    const edge = graph.edges[0], cyclic = { ...graph, edges: [...graph.edges, { ...edge, id:'cycle', portId:'cycle', from:edge.to, to:edge.from }] };
    validate(cyclic);
  });
  it('preserves open ball, closed ball and sphere constructors with opaque instances', () => {
    const source = scopedFixture();
    for (const name of ['Metric.ball','Metric.closedBall','Metric.sphere']) {
      const region = call(name, [{kind:'const',name:'X'},{kind:'opaque',text:'metric instance'},variable(source.binders.point),variable(source.binders.radius)], {argumentKinds:['type','instance','value','value']});
      const value = fixture(leaf('region',`${name} x δ ⊆ c i`,call('Set.Subset',[region,{kind:'app',fn:variable(source.binders.family),args:[variable(source.binders.index)]}])));
      const graph = value.model.clauses[0].graphs[0], relation = graph.nodes.find(n=>n.relation?.kind==='metric-region')!.relation!;
      const outputId = relation.ports.find(p=>p.role==='region')!.objectId;
      const display = scopedGraphMathDisplay(graph.nodes.find(n=>n.object?.id===outputId)!, graph)!;
      expect(display.latex).toContain(name);
      if(name!=='Metric.ball') expect(display.latex).not.toContain('Metric.ball');
    }
  });
  it('typesets admitted output roles without interpreting opaque arguments', () => {
    const graph = scopedFixture().model.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    const output = graph.nodes.find(node => node.object?.expression.kind === 'app' && node.object.expression.fn.kind === 'const' && node.object.expression.fn.name === 'Metric.ball')!;
    const opaque = { ...output, object: { ...output.object!, expression: {kind:'opaque' as const, text:'raw exact application'} } };
    const label = scopedGraphMathDisplay(opaque, graph)!;
    expect(label.latex).toContain('Metric.ball'); expect(label.latex).toContain('delta'); expect(label.source).toBe(output.object!.label);
    const predicateGraph = { ...graph, nodes: graph.nodes.map(node => node.relation?.kind === 'metric-region' ? {...node, relation:{...node.relation, kind:'predicate' as const}, ports:node.ports.map(port=>({...port,output:false}))}:node) };
    expect(scopedGraphMathDisplay(opaque,predicateGraph)!.latex).toBeUndefined();
  });
});
