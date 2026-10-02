import type { DiagramTextSize } from '../components/map-diagram-layout';

interface IntervalLabels {
  left: DiagramTextSize;
  right: DiagramTextSize;
  center: DiagramTextSize;
  point?: DiagramTextSize;
}

/** Size the schematic interval from its complete labels. The endpoint formulas
 * share a row with clearance; center and point labels have separate rows. This
 * changes only drawing space, never the metric condition or a numerical model. */
export function layoutMetricInterval(labels: IntervalLabels, pointAtEndpoint: boolean) {
  const padding = 24, gap = 24;
  const span = Math.max(220, (labels.left.width + labels.right.width) / 2 + gap);
  // Preserve the existing illustrative point's relative position in the interval.
  const pointOffset = pointAtEndpoint ? -span / 2 : -span * 35 / 220;
  // Whole-unit extents avoid feeding subpixel font hinting back into the SVG scale.
  const halfWidth = Math.ceil(Math.max(230, span / 2 + 50 + padding,
    span / 2 + labels.left.width / 2 + padding, span / 2 + labels.right.width / 2 + padding,
    labels.center.width / 2 + padding, labels.point ? Math.abs(pointOffset) + labels.point.width / 2 + padding : 0));
  const axisY = Math.max(100, labels.point ? padding + labels.point.height + 16 : 0);
  const endpointY = axisY + 20 + Math.max(labels.left.ascent, labels.right.ascent);
  const centerY = endpointY + Math.max(labels.left.descent, labels.right.descent) + 12 + labels.center.ascent;
  return { width: 2 * halfWidth, height: Math.ceil(Math.max(200, centerY + labels.center.descent + padding)),
    leftX: halfWidth - span / 2, rightX: halfWidth + span / 2, centerX: halfWidth,
    axisY, endpointY, centerY, pointX: halfWidth + pointOffset, pointY: axisY - 16 - (labels.point?.descent ?? 0) };
}
