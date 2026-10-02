export interface DiagramTextSize { width: number; height: number; ascent: number; descent: number }
export interface MapDiagramNode { id: string; width: number; height: number }
export interface MapDiagramEdge { id: string; from: string; to: string; label: DiagramTextSize }
export interface DiagramPoint { x: number; y: number }
export interface DiagramRect { x: number; y: number; width: number; height: number }
export interface PositionedMapNode extends MapDiagramNode { x: number; y: number }
export interface PositionedMapEdge extends MapDiagramEdge {
  path: string;
  points: DiagramPoint[];
  labelX: number;
  labelY: number;
  labelBox: DiagramRect;
}

/** Each map has its own horizontal lane. Ports occupy the sides of the type
 * columns, outside every label footprint, so stems can cross edges but never
 * unrelated labels. Text dimensions determine both column and lane spacing. */
export function layoutMapDiagram(nodes: readonly MapDiagramNode[], edges: readonly MapDiagramEdge[], minimumWidth = 660) {
  const padding = 20, labelGap = 8, laneGap = 16, portStep = 8;
  const labelWidth = Math.max(0, ...edges.map(edge => edge.label.width));
  const bodyWidth = Math.max(0, labelWidth, ...nodes.map(node => node.width));
  const maximumStem = bodyWidth / 2 + padding + edges.length * portStep;
  const spacing = 2 * maximumStem + labelWidth + 2 * padding;
  const width = Math.max(minimumWidth, nodes.length * spacing);
  const nodeTop = padding + edges.reduce((sum, edge) => sum + edge.label.height + labelGap + laneGap, 0);
  const positioned = nodes.map((node, index) => ({ ...node, x: (index + .5) * width / Math.max(nodes.length, 1), y: nodeTop }));
  const byId = new Map(positioned.map(node => [node.id, node]));
  const sides = edges.map(edge => {
    const from = byId.get(edge.from), to = byId.get(edge.to);
    if (!from || !to) throw new Error('A map diagram edge requires both declared endpoints.');
    const self = from.id === to.id, direction = to.x >= from.x ? 1 : -1;
    return { from, to, fromSide: self ? -1 : direction, toSide: self ? 1 : -direction };
  });
  const counts = new Map<string, number>();
  for (const side of sides) for (const [node, direction] of [[side.from, side.fromSide], [side.to, side.toSide]] as const) {
    const key = `${node.id}:${direction}`;
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }
  const slots = new Map<string, number>();
  const port = (node: PositionedMapNode, direction: number) => {
    const key = `${node.id}:${direction}`, slot = slots.get(key) ?? 0;
    slots.set(key, slot + 1);
    return {
      attachment: { x: node.x + direction * node.width / 2, y: node.y + 8 + (slot + .5) * Math.max(0, node.height - 16) / counts.get(key)! },
      stem: node.x + direction * (bodyWidth / 2 + padding + slot * portStep),
    };
  };
  let laneY = nodeTop - laneGap;
  const routes = edges.map((edge, index): PositionedMapEdge => {
    const side = sides[index], source = port(side.from, side.fromSide), target = port(side.to, side.toSide);
    const labelX = (side.from.x + side.to.x) / 2, labelY = laneY - labelGap - edge.label.descent;
    const points = [source.attachment, { x: source.stem, y: source.attachment.y }, { x: source.stem, y: laneY },
      { x: target.stem, y: laneY }, { x: target.stem, y: target.attachment.y }, target.attachment];
    const labelBox = { x: labelX - edge.label.width / 2, y: labelY - edge.label.ascent, width: edge.label.width, height: edge.label.height };
    laneY = labelBox.y - laneGap;
    return { ...edge, points, path: points.map((point, i) => `${i ? 'L' : 'M'}${point.x} ${point.y}`).join(' '), labelX, labelY, labelBox };
  });
  return { width, height: nodeTop + Math.max(0, ...nodes.map(node => node.height)) + padding, nodes: positioned, edges: routes };
}
