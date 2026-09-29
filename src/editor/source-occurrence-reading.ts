import { compilePositionalComponent, type PositionalComponentReading } from '../packets/semantic';
import type { SourceOccurrence } from './source-occurrence';
import { recordedContextEntries } from './source-snapshot';

/** The caller has validated the occurrence attachment. The compiler separately
 * validates its positional syntax; retained typing outcomes do not select or
 * authorize a stronger interpretation. */
export function sourceOccurrenceReading(value: SourceOccurrence, target: 'term' | 'type'): PositionalComponentReading | undefined {
  if (value.checking.status !== 'captured' || !value.checking.selected) return undefined;
  return compilePositionalComponent(value.checking.selected, {
    sourceIdentity: `occurrence:${value.captureId}:${JSON.stringify(value.path)}`,
    sourcePath: ['checking', 'selected'], target,
    recordedContext: recordedContextEntries(value.checking.binding),
  });
}
