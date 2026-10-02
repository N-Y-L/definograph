import type { DiagramTextSize } from '../components/map-diagram-layout';

/** Labels occupy separate rows outside the schematic region. Drawing positions
 * carry the same center/radius/point roles, without choosing coordinates. */
export function layoutMetricShape(labels: { center: DiagramTextSize; radius: DiagramTextSize; point?: DiagramTextSize }, sphere: boolean) {
  const padding = 24, pointOffset = sphere ? 0 : -30;
  const centerX = Math.ceil(Math.max(120, padding + labels.center.width / 2,
    labels.point ? padding - pointOffset + labels.point.width / 2 : 0));
  const width = Math.ceil(Math.max(460, centerX + labels.center.width / 2 + padding,
    centerX + 90 + labels.radius.width + padding, labels.point ? centerX + pointOffset + labels.point.width / 2 + padding : 0));
  const bodyExtent = Math.max(72, labels.radius.height / 2);
  const centerY = Math.max(100, padding + bodyExtent + (labels.point ? labels.point.height + 24 : 0));
  const centerLabelY = centerY + bodyExtent + 16 + labels.center.ascent;
  return { width, height: Math.ceil(Math.max(200, centerLabelY + labels.center.descent + padding)), centerX, centerY,
    centerLabelY, radiusX: centerX + 90, radiusY: centerY + (labels.radius.ascent - labels.radius.descent) / 2,
    pointX: centerX + pointOffset, pointY: centerY - (sphere ? 72 : 31),
    pointLabelY: centerY - bodyExtent - 20 - (labels.point?.descent ?? 0),
    pointLeaderTop: centerY - bodyExtent - 12 };
}

/** The distance-axis scale is schematic; measured rows do not change its meaning. */
export function layoutMetricDistance(labels: { title: DiagramTextSize; zero: DiagramTextSize; radius: DiagramTextSize; description: DiagramTextSize }) {
  const padding = 24, left = Math.max(80, padding + labels.zero.width / 2);
  const right = left + Math.max(240, (labels.zero.width + labels.radius.width) / 2 + 24);
  const axisWidth = Math.max(right + 70, right + labels.radius.width / 2 + padding);
  const width = Math.ceil(Math.max(460, axisWidth, labels.title.width + 2 * padding, labels.description.width + 2 * padding));
  const offset = (width - axisWidth) / 2;
  const titleY = padding + labels.title.ascent, axisY = Math.max(100, padding + labels.title.height + 24);
  const endpointY = axisY + 20 + Math.max(labels.zero.ascent, labels.radius.ascent);
  const descriptionY = endpointY + Math.max(labels.zero.descent, labels.radius.descent) + 16 + labels.description.ascent;
  return { width, height: Math.ceil(Math.max(200, descriptionY + labels.description.descent + padding)),
    leftX: left + offset, rightX: right + offset, axisY, titleY, endpointY, descriptionY };
}
