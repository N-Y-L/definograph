import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';

export interface LabelPlacement extends DiagramRect { baseline: number }
export interface LabelShape { width: number; height: number; label: LabelPlacement; pointY?: number }
export const labelPlacement = (size: DiagramTextSize, x: number, top: number): LabelPlacement => ({ x: x - size.width / 2, y: top, width: size.width, height: size.height, baseline: top + size.ascent });

/** Geometry is determined by the whole rendered label, including stacked math. */
export function labelShape(size: DiagramTextSize, kind: 'box' | 'point' | 'ellipse'): LabelShape {
  if (kind === 'point') {
    const width = Math.max(40, size.width + 24);
    return { width, height: 32 + size.height + 12, pointY: 12, label: labelPlacement(size, width / 2, 32) };
  }
  if (kind === 'ellipse') {
    // The label rectangle lies strictly inside this ellipse (including corners).
    const width = Math.max(150, (size.width + 24) * Math.SQRT2), height = Math.max(120, (size.height + 24) * Math.SQRT2);
    return { width, height, label: labelPlacement(size, width / 2, (height - size.height) / 2) };
  }
  const width = Math.max(72, size.width + 32), height = Math.max(54, size.height + 28);
  return { width, height, label: labelPlacement(size, width / 2, (height - size.height) / 2) };
}

export interface PositionedLabelShape extends LabelShape { x: number; y: number }
export function stackShapes(shapes: readonly LabelShape[], gap = 22) {
  const width = Math.max(0, ...shapes.map(shape => shape.width));
  let y = 0;
  const items = shapes.map(shape => {
    const item = { ...shape, x: (width - shape.width) / 2, y };
    y += shape.height + gap;
    return item;
  });
  return { width, height: Math.max(0, y - gap), items };
}

/** Columns reserve complete input/output labels, not just the point glyphs.
 * Arrows travel through the gaps between columns, outside every label. */
export function layoutExpressionFlow(inputs: readonly DiagramTextSize[], maps: readonly DiagramTextSize[], output: DiagramTextSize) {
  if (!maps.length) {
    const result = labelShape(output, 'box');
    return { width: result.width + 40, height: result.height + 32, inputs: [] as PositionedLabelShape[], maps: [] as PositionedLabelShape[], output: { ...result, x: 20, y: 16 }, arrowY: 16 + result.height / 2 };
  }
  const source = stackShapes(inputs.map(size => labelShape(size, 'point')));
  const functions = maps.map(size => labelShape(size, 'box')), result = labelShape(output, 'point');
  const arrowY = 16 + Math.max(source.height / 2, ...functions.map(shape => shape.height / 2), 12);
  const inputY = arrowY - source.height / 2;
  let x = 20 + source.width + 54;
  const positionedMaps = functions.map(shape => {
    const positioned = { ...shape, x, y: arrowY - shape.height / 2 };
    x += shape.width + 54;
    return positioned;
  });
  const positionedOutput = { ...result, x, y: arrowY - result.pointY! };
  const positionedInputs = source.items.map(shape => ({ ...shape, x: shape.x + 20, y: shape.y + inputY }));
  const height = Math.max(...positionedInputs.map(shape => shape.y + shape.height), ...positionedMaps.map(shape => shape.y + shape.height), positionedOutput.y + positionedOutput.height) + 16;
  return { width: x + result.width + 20, height, inputs: positionedInputs, maps: positionedMaps, output: positionedOutput, arrowY };
}

/** Put a complete map label above the space between two regions/objects. */
export function layoutRegionLink(left: { width: number; height: number }, right: { width: number; height: number }, map: DiagramTextSize, leftAnchor = left.height / 2, rightAnchor = right.height / 2) {
  const gap = Math.max(80, map.width + 32), top = 16 + map.height + 24;
  const above = Math.max(leftAnchor, rightAnchor), below = Math.max(left.height - leftAnchor, right.height - rightAnchor), arrowY = top + above;
  return { width: 40 + left.width + gap + right.width, height: arrowY + below + 36,
    left: { x: 20, y: arrowY - leftAnchor },
    right: { x: 20 + left.width + gap, y: arrowY - rightAnchor },
    map: labelPlacement(map, 20 + left.width + gap / 2, 16), arrowY };
}
