import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';

interface LabelBox extends DiagramRect { baseline: number }
interface EllipseLayout { x: number; y: number; rx: number; ry: number; label: LabelBox }
const labelAt = (size: DiagramTextSize, baseline: number): LabelBox => ({ x: -size.width / 2, y: baseline - size.ascent, width: size.width, height: size.height, baseline });

/** Reserve the entire glyph rectangle, including a margin, inside an ellipse.
 * A label near its top needs more horizontal room than one at its center. */
function radiusForLabel(label: LabelBox, centerY: number, radiusY: number) {
  const dy = Math.max(Math.abs(label.y - centerY), Math.abs(label.y + label.height - centerY)) + 8;
  return (label.width / 2 + 12) / Math.sqrt(1 - (dy / radiusY) ** 2);
}

export function layoutContainedRelation(outerText: DiagramTextSize, innerText: DiagramTextSize, nested: boolean) {
  const outerLabel = labelAt(outerText, 32 + outerText.ascent);
  const innerRadiusY = Math.max(52, innerText.height / 2 + 24);
  const innerY = outerLabel.y + outerLabel.height + 28 + (nested ? innerRadiusY : 6);
  const innerLabel = labelAt(innerText, nested ? innerY + (innerText.ascent - innerText.descent) / 2 : innerY + 18 + innerText.ascent);
  const height = Math.max(200, (nested ? innerY + innerRadiusY : innerLabel.y + innerLabel.height) + 32);
  const outerY = height / 2, outerRadiusY = outerY - 12;
  const innerRadiusX = nested ? Math.max(111.5, radiusForLabel(innerLabel, innerY, innerRadiusY)) : 6;
  // The triangle inequality in normalized ellipse coordinates guarantees the
  // full inner ellipse remains contained, including between its cardinal points.
  const nestedRadius = (innerRadiusX + 12) / (1 - Math.abs(innerY - outerY) / outerRadiusY);
  const outerRadiusX = Math.max(nested ? 180 : 156, radiusForLabel(outerLabel, outerY, outerRadiusY), nested ? nestedRadius : radiusForLabel(innerLabel, outerY, outerRadiusY));
  const width = Math.max(500, 2 * outerRadiusX + 40), x = width / 2;
  const move = (label: LabelBox): LabelBox => ({ ...label, x: label.x + x });
  const outer: EllipseLayout = { x, y: outerY, rx: outerRadiusX, ry: outerRadiusY, label: move(outerLabel) };
  const inner: EllipseLayout = { x, y: innerY, rx: innerRadiusX, ry: innerRadiusY, label: move(innerLabel) };
  return { width, height, outer, inner };
}

export function layoutRelationComparison(left: DiagramTextSize, right: DiagramTextSize, symbol: DiagramTextSize) {
  const boxHeight = Math.max(95, left.height + 32, right.height + 32, symbol.height + 24);
  const gap = Math.max(66, symbol.width + 40), leftWidth = Math.max(175, left.width + 36), rightWidth = Math.max(175, right.width + 36);
  const width = 40 + leftWidth + gap + rightWidth, height = boxHeight + 32;
  const place = (size: DiagramTextSize, x: number, boxWidth: number) => ({ x, y: 16, width: boxWidth, height: boxHeight,
    labelX: x + boxWidth / 2, labelY: 16 + (boxHeight - size.height) / 2 + size.ascent });
  return { width, height, left: place(left, 20, leftWidth), right: place(right, 20 + leftWidth + gap, rightWidth),
    symbolX: 20 + leftWidth + gap / 2, symbolY: 16 + (boxHeight - symbol.height) / 2 + symbol.ascent };
}
