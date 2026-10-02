import type { DiagramPoint, DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';
import type { ScopedClauseGraph, ScopedGraphNode } from '../reading/scoped-graph';

export interface ScopedGraphNodeSize { label: DiagramTextSize; note?: DiagramTextSize; ports: Readonly<Record<string, DiagramTextSize>> }
export interface PositionedScopedNode extends DiagramRect {
  id: string; labelX: number; labelY: number;
  ports: { id: string; x: number; y: number; labelX: number; labelY: number; output: boolean }[];
}

/** A bounded layered drawing with explicit ports. Adjacent layers route through
 * their gap; long, backward and cyclic edges have individual lanes above nodes.
 * Node/port glyph bounds reserve geometry before any route is placed. */
export function layoutScopedGraph(graph: ScopedClauseGraph, measurements: Readonly<Record<string, ScopedGraphNodeSize>>) {
  const byId = new Map(graph.nodes.map(node => [node.id, node]));
  const incoming = new Map(graph.nodes.map(node => [node.id, graph.edges.filter(edge => edge.to === node.id)]));
  const outgoing = new Map(graph.nodes.map(node => [node.id, graph.edges.filter(edge => edge.from === node.id)]));
  if (graph.edges.some(edge => !byId.has(edge.from) || !byId.has(edge.to))) throw new Error('A graph edge requires both supplied endpoints.');
  const indegree = new Map(graph.nodes.map(node => [node.id, incoming.get(node.id)!.length]));
  const rank = new Map(graph.nodes.map(node => [node.id, 0]));
  const queue = graph.nodes.filter(node => !indegree.get(node.id)).map(node => node.id);
  for (let index = 0; index < queue.length; index++) for (const edge of outgoing.get(queue[index])!) {
    rank.set(edge.to, Math.max(rank.get(edge.to)!, rank.get(edge.from)! + 1));
    indegree.set(edge.to, indegree.get(edge.to)! - 1);
    if (!indegree.get(edge.to)) queue.push(edge.to);
  }
  const cyclicRank = Math.max(0, ...rank.values()) + 1;
  graph.nodes.filter(node => indegree.get(node.id)! > 0).forEach(node => rank.set(node.id, cyclicRank));
  const ranks = [...new Set(rank.values())].sort((a, b) => a - b);
  for (const [id, value] of rank) rank.set(id, ranks.indexOf(value));
  const layers: ScopedGraphNode[][] = Array.from({ length: ranks.length }, () => []);
  for (const node of graph.nodes) layers[rank.get(node.id)!].push(node);
  const dimensions = new Map(graph.nodes.map(node => {
    const text = measurements[node.id];
    const inputs = node.ports.filter(port => !port.output), outputs = node.ports.filter(port => port.output);
    const inputWidth = Math.max(0, ...inputs.map(port => text.ports[port.id].width));
    const outputWidth = Math.max(0, ...outputs.map(port => text.ports[port.id].width));
    const rowHeight = Math.max(22, ...node.ports.map(port => text.ports[port.id].height + 8));
    return [node.id, { width: Math.max(node.kind === 'object' ? 44 : 92, Math.max(text.label.width, text.note?.width ?? 0) + 28, inputWidth + outputWidth + 46),
      height: text.label.height + (text.note ? text.note.height + 6 : 0) + 22 + Math.max(inputs.length, outputs.length) * rowHeight, rowHeight }] as const;
  }));
  const longEdges = graph.edges.filter(edge => rank.get(edge.to)! !== rank.get(edge.from)! + 1);
  const nodeTop = 24 + longEdges.length * 16;
  const gap = Math.max(66, graph.edges.length * 5 + 24);
  const widths = layers.map(layer => Math.max(0, ...(layer ?? []).map(node => dimensions.get(node.id)!.width)));
  const heights = layers.map(layer => (layer ?? []).reduce((sum, node) => sum + dimensions.get(node.id)!.height + 26, -26));
  const contentHeight = Math.max(0, ...heights);
  const lefts: number[] = [];
  let nextLeft = 20;
  for (const width of widths) { lefts.push(nextLeft); nextLeft += width + gap; }
  const positioned: PositionedScopedNode[] = [];
  for (const [layerIndex, layer] of layers.entries()) {
    let y = nodeTop + (contentHeight - (heights[layerIndex] ?? 0)) / 2;
    for (const node of layer ?? []) {
      const dimension = dimensions.get(node.id)!, text = measurements[node.id], x = lefts[layerIndex] + (widths[layerIndex] - dimension.width) / 2;
      const portRow = { input: 0, output: 0 };
      const ports = node.ports.map(port => {
        const size = text.ports[port.id], index = portRow[port.output ? 'output' : 'input']++;
        const centerY = y + text.label.height + 22 + (index + .5) * dimension.rowHeight;
        return { id: port.id, output: port.output, x: port.output ? x + dimension.width : x, y: centerY,
          labelX: port.output ? x + dimension.width - 11 : x + 11, labelY: centerY - size.height / 2 + size.ascent };
      });
      positioned.push({ id: node.id, x, y, width: dimension.width, height: dimension.height, labelX: x + dimension.width / 2, labelY: y + 11 + text.label.ascent, ports });
      y += dimension.height + 26;
    }
  }
  const boxes = new Map(positioned.map(node => [node.id, node]));
  const edges = graph.edges.map((edge, index) => {
    const from = boxes.get(edge.from)!, to = boxes.get(edge.to)!;
    const fromPort = from.ports.find(port => port.id === edge.portId), toPort = to.ports.find(port => port.id === edge.portId);
    const start = fromPort ? { x: fromPort.x, y: fromPort.y } : { x: from.x + from.width, y: from.y + from.height / 2 };
    const end = toPort ? { x: toPort.x, y: toPort.y } : { x: to.x, y: to.y + to.height / 2 };
    const fromRank = rank.get(edge.from)!, toRank = rank.get(edge.to)!;
    const stem = lefts[fromRank] + widths[fromRank] + 12 + index * 5;
    let points: DiagramPoint[];
    if (toRank === fromRank + 1) points = [start, { x: stem, y: start.y }, { x: stem, y: end.y }, end];
    else {
      const lane = 12 + longEdges.findIndex(candidate => candidate.id === edge.id) * 16;
      const endStem = lefts[toRank] - 12 - index * 5;
      points = [start, { x: stem, y: start.y }, { x: stem, y: lane }, { x: endStem, y: lane }, { x: endStem, y: end.y }, end];
    }
    return { ...edge, points, path: points.map((point, index) => `${index ? 'L' : 'M'}${point.x} ${point.y}`).join(' ') };
  });
  const minimumX = Math.min(0, ...edges.flatMap(edge => edge.points.map(point => point.x - 10)));
  const maximumX = Math.max(nextLeft - gap + 20, ...edges.flatMap(edge => edge.points.map(point => point.x + 10)));
  return { x: minimumX, width: maximumX - minimumX, height: nodeTop + contentHeight + 20, nodes: positioned, edges };
}
