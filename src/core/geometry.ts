import { compareNumbers, evaluateExpression, metricDistance } from './expression';
import type { BallGeometry, BallScene, GraphScene, Point2, SamplePoint, Scenario, ScenarioValue, SliceGeometry, SliceView } from './types';

export function ballGeometry(scene: BallScene, scenario: Scenario): BallGeometry {
  const center = evaluateExpression(scene.center, scenario);
  const radius = evaluateExpression(scene.radius, scenario);
  if (center.status !== 'value') return center;
  if (radius.status !== 'value') return radius;
  if (typeof radius.value !== 'number') return { status: 'unknown', reason: 'The radius must be a scalar.' };
  let centerValue: ScenarioValue = center.value;
  // A standard point-valued zero may be serialized as a zero numeral without dimension.
  if (scene.dimension > 1 && centerValue === 0 && scene.center.kind === 'app' && scene.center.standard === true && scene.center.dimension === scene.dimension) centerValue = Array.from({ length: scene.dimension }, () => 0);
  if (scene.metric === 'real' ? typeof centerValue !== 'number' : !Array.isArray(centerValue) || centerValue.length !== scene.dimension) return { status: 'unknown', reason: 'The center does not have the recognized ambient dimension.' };
  const r = radius.value;
  const empty = r < 0 || (scene.boundary === 'open' && r === 0);
  const pointResult = scene.point && evaluateExpression(scene.point, scenario);
  const point = pointResult?.status === 'value' ? pointResult.value : undefined;
  const distance = point !== undefined ? metricDistance(scene.metric, point, centerValue) : undefined;
  const membership = distance === undefined ? undefined : compareNumbers(distance, r, scene.boundary === 'open' ? 'lt' : scene.boundary === 'closed' ? 'le' : 'eq');
  return { status: 'geometry', metric: scene.metric, dimension: scene.dimension, center: centerValue, radius: r, empty, singleton: !empty && r === 0, boundary: scene.boundary, point, membership };
}

/** A coordinate-plane INTERSECTION with fixed remaining coordinates, never an unlabeled projection. */
export function sliceGeometry(scene: BallScene, scenario: Scenario, view: SliceView = {}): SliceGeometry {
  const shape = ballGeometry(scene, scenario);
  if (shape.status === 'unknown') return shape;
  const n = shape.dimension;
  if (n < 2 || !Array.isArray(shape.center)) return { status: 'unknown', reason: 'Use the real-line view for a one-dimensional metric space.' };
  const axes = view.axes ?? [0, 1];
  if (axes[0] === axes[1] || axes.some(a => !Number.isSafeInteger(a) || a < 0 || a >= n)) return { status: 'unknown', reason: 'Choose two different coordinate axes within the ambient dimension.' };
  const fixed = Array.from({ length: n }, (_, i) => view.fixed?.[i] ?? 0);
  if (!fixed.every(Number.isFinite)) return { status: 'unknown', reason: 'Fixed slice coordinates must be finite.' };
  const center: Point2 = [shape.center[axes[0]]!, shape.center[axes[1]]!];
  const omitted = shape.center.map((c, i) => axes.includes(i) ? 0 : fixed[i]! - c);
  const isEuclidean = shape.metric === 'euclidean2' || shape.metric === 'euclideanN';
  const offset = isEuclidean ? Math.hypot(...omitted) : Math.max(...omitted.map(Math.abs));
  let radius = Math.max(0, shape.radius);
  let empty = shape.empty;
  let boundary = shape.boundary;
  let note = n > 2 ? `Coordinate slice through an ambient ${n}D space; all other coordinates are fixed. This is an intersection, not a projection.` : 'All ambient coordinates are displayed.';
  if (isEuclidean) {
    if (offset > shape.radius || (shape.boundary === 'open' && offset === shape.radius)) empty = true;
    if (shape.radius > 0 && offset <= shape.radius) {
      // Avoid overflow in r² and retain accuracy near tangency.
      const quotient = offset / shape.radius;
      radius = shape.radius * Math.sqrt(Math.max(0, (1 - quotient) * (1 + quotient)));
    } else radius = 0;
  } else {
    if (offset > shape.radius || (shape.boundary === 'open' && offset >= shape.radius)) empty = true;
    if (!empty && n > 2 && shape.boundary === 'sphere' && offset === shape.radius && shape.radius > 0) {
      boundary = 'closed';
      note += ' A fixed coordinate already reaches the max-norm radius, so this sphere intersects the plane in a filled square.';
    }
  }
  const singleton = !empty && radius === 0;
  const pointArray = Array.isArray(shape.point) && shape.point.length === n ? shape.point : undefined;
  const point: Point2 | undefined = pointArray ? [pointArray[axes[0]]!, pointArray[axes[1]]!] : undefined;
  const pointInSlice = pointArray?.every((x, i) => axes.includes(i) || x === fixed[i]);
  if (pointArray && !pointInSlice) note += ' The representative point lies outside this slice.';
  return { status: 'geometry', metric: shape.metric, center, radius, empty, singleton, boundary, ambientDimension: n, intrinsicDimension: shape.empty ? -1 : shape.radius === 0 ? 0 : shape.boundary === 'sphere' ? n - 1 : n, axes, fixed, isSlice: n > 2, point, pointInSlice, membership: shape.membership, note };
}

export function sampleGraph(scene: GraphScene, scenario: Scenario, options: { min?: number; max?: number; count?: number } = {}): SamplePoint[] {
  const min = options.min ?? -3, max = options.max ?? 3;
  const count = Math.max(2, Math.min(2000, Math.round(options.count ?? 181)));
  if (!Number.isFinite(min) || !Number.isFinite(max) || min >= max || !Number.isFinite(count)) return [];
  return Array.from({ length: count }, (_, i) => {
    const x = min + (max - min) * i / (count - 1);
    const value = evaluateExpression(scene.body, { ...scenario, [scene.input.id]: x });
    return { x, y: value.status === 'value' && typeof value.value === 'number' ? value.value : null };
  });
}
