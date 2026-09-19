import { ballGeometry, metricDistance } from '../core';
import type { BallScene, PredicateResult, Scenario } from '../core';

export type DistanceProfile = { status: 'unknown'; reason: string } | {
  status: 'profile'; dimension: number; absoluteDisplacements: number[]; distance: number; radius: number;
  metric: 'L2' | 'L∞'; membership?: PredicateResult;
};

/** Measure the complete representative vector; no projection or slice is used. */
export function distanceProfile(scene: BallScene, scenario: Scenario): DistanceProfile {
  const geometry = ballGeometry(scene, scenario);
  if (geometry.status === 'unknown') return geometry;
  if (!Array.isArray(geometry.center) || !Array.isArray(geometry.point) || geometry.point.length !== geometry.dimension) return { status: 'unknown', reason: 'Choose numerical values for the representative point to inspect its distance in all coordinates.' };
  const distance = metricDistance(scene.metric, geometry.point, geometry.center, geometry.dimension);
  if (distance === undefined || !Number.isFinite(distance)) return { status: 'unknown', reason: 'The full distance is outside the supported numerical range.' };
  const center = geometry.center;
  const absoluteDisplacements = geometry.point.map((coordinate, index) => Math.abs(coordinate - center[index]));
  return { status: 'profile', dimension: geometry.dimension, absoluteDisplacements, distance, radius: geometry.radius, metric: scene.metric.startsWith('sup') ? 'L∞' : 'L2', membership: geometry.membership };
}
