import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';

export interface GraphLabelPlacement { x: number; y: number; box: DiagramRect }
type Pair<T> = readonly [T, T];
const radius = 19, padding = 20, labelGap = 10;
const mapPair = <T, U>(pair: Pair<T>, transform: (item: T, index: 0 | 1) => U): Pair<U> => [transform(pair[0], 0), transform(pair[1], 1)];

function labelAt(size: DiagramTextSize, x: number, top: number): GraphLabelPlacement {
  return { x, y: top + size.ascent, box: { x: x - size.width / 2, y: top, width: size.width, height: size.height } };
}
const bottom = (label: GraphLabelPlacement) => label.box.y + label.box.height;

/** Endpoint columns grow with their visible glyphs. Positions remain schematic:
 * an actual self-adjacency has one vertex, while arbitrary slots remain two. */
export function layoutGraphAdjacency(endpoints: Pair<DiagramTextSize>, annotation: DiagramTextSize, sameEndpoint: boolean) {
  const columnWidth = Math.max(2 * radius, ...(sameEndpoint ? [endpoints[0]] : endpoints).map(label => label.width));
  const separation = Math.max(308, columnWidth + 32);
  const width = Math.max(560, annotation.width + 2 * padding, sameEndpoint ? columnWidth + 2 * padding : separation + columnWidth + 2 * padding);
  const center = width / 2;
  const x: Pair<number> = sameEndpoint ? [center, center] : [center - separation / 2, center + separation / 2];
  const sourceAnnotation = sameEndpoint ? undefined : labelAt(annotation, center, padding);
  const vertexY = sourceAnnotation ? bottom(sourceAnnotation) + 12 + radius : 87;
  const labels = mapPair(endpoints, (size, index) => labelAt(size, x[index], vertexY + radius + labelGap));
  const footer = sameEndpoint ? labelAt(annotation, center, bottom(labels[0]) + 14) : undefined;
  const height = Math.max(164, (footer ? bottom(footer) : Math.max(...labels.map(bottom))) + padding);
  return { width, height, center, x, vertexY, labels, annotation: sourceAnnotation ?? footer! };
}

export interface GraphRuleText {
  endpoints: Pair<DiagramTextSize>;
  outputs: Pair<DiagramTextSize>;
  sourceAnnotation: DiagramTextSize;
  applyAnnotation: DiagramTextSize;
  resultAnnotation: DiagramTextSize;
  inequality: DiagramTextSize;
}

/** A separate vertical lane holds the map caption between the two arrows.
 * Output label footprints determine both box sizes and column clearance. */
export function layoutGraphRule(kind: 'coloring' | 'map', text: GraphRuleText) {
  const outputWidths = mapPair(text.outputs, label => kind === 'coloring' ? Math.max(148, label.width + 24) : Math.max(2 * radius, label.width));
  const columnWidth = Math.max(2 * radius, ...text.endpoints.map(label => label.width), ...outputWidths);
  const separation = Math.max(308, columnWidth + (kind === 'coloring' ? text.inequality.width + 32 : 32), text.applyAnnotation.width + 32);
  const width = Math.max(560, separation + columnWidth + 2 * padding, text.sourceAnnotation.width + 2 * padding, text.resultAnnotation.width + 2 * padding);
  const center = width / 2;
  const x: Pair<number> = [center - separation / 2, center + separation / 2];
  const sourceAnnotation = labelAt(text.sourceAnnotation, center, 16);
  const vertexY = Math.max(55, bottom(sourceAnnotation) + 12 + radius);
  const endpoints = mapPair(text.endpoints, (size, index) => labelAt(size, x[index], vertexY + radius + labelGap));
  const arrowTop = Math.max(...endpoints.map(bottom)) + 10;
  const arrowBottom = arrowTop + Math.max(47, text.applyAnnotation.height + 24);
  const applyAnnotation = labelAt(text.applyAnnotation, center, (arrowTop + arrowBottom - text.applyAnnotation.height) / 2);
  const outputTop = arrowBottom + 12;
  const outputHeight = kind === 'coloring' ? Math.max(43, ...text.outputs.map(label => label.height + 20), text.inequality.height + 12) : 2 * radius;
  const outputY = outputTop + outputHeight / 2;
  const boxes = mapPair(outputWidths, (width, index) => ({ x: x[index] - width / 2, y: outputTop, width, height: outputHeight }));
  const outputs = mapPair(text.outputs, (size, index) => labelAt(size, x[index], kind === 'coloring' ? outputY - size.height / 2 : outputTop + outputHeight + labelGap));
  const inequality = labelAt(text.inequality, center, outputY - text.inequality.height / 2);
  const resultAnnotation = labelAt(text.resultAnnotation, center, Math.max(outputTop + outputHeight, ...outputs.map(bottom)) + 14);
  return { width, height: bottom(resultAnnotation) + 16, center, x, vertexY, endpoints, sourceAnnotation, arrowTop, arrowBottom, applyAnnotation, outputY, boxes, outputs, inequality, resultAnnotation };
}
