import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceHeadExposure } from './source-head-exposure';
import { sourceSnapshotValidation } from './source-snapshot';

export const MAX_SOURCE_HISTORY_BYTES = 16 * 1024 * 1024;
/** Exact data only; catches non-JSON fields before serialization and counts the aggregate. */
export function assertSourceHistoryLimit(value: unknown, reserveBytes = 0): void {
  if (!Number.isSafeInteger(reserveBytes) || reserveBytes < 0 || reserveBytes >= MAX_SOURCE_HISTORY_BYTES) throw new Error('Invalid history size reserve.');
  sourceSnapshotValidation.preflight(value, MAX_SOURCE_HISTORY_BYTES - reserveBytes, ['history'], false, 128, MAX_SOURCE_HISTORY_BYTES);
}

export interface HeadExposureBundle { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; record: SourceHeadExposure }
