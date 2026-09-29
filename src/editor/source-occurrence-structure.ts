/** A validated occurrence's selected candidate has its own positional drawing.
 * Readback checks exact structure, independently of every kernel outcome.
 */
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing,
  type PositionalStructuralDrawing, type StructureLimits, type StructureResult } from '../packets/structure';
import type { SourceOccurrence } from './source-occurrence';

export function sourceOccurrenceDrawing(value: SourceOccurrence, limits?: Partial<StructureLimits>): StructureResult<PositionalStructuralDrawing> | undefined {
  if (value.checking.status !== 'captured' || !value.checking.selected) return undefined;
  const selected = value.checking.selected;
  const drawing = buildPositionalStructuralDrawing(selected, {
    sourceIdentity: `occurrence:${value.captureId}:${JSON.stringify(value.path)}`,
    sourcePath: ['checking', 'selected'], limits,
  });
  if (!drawing.ok) return drawing;
  const readback = readPositionalStructuralDrawing(drawing.value, limits);
  if (!readback.ok) return readback;
  const { canonical } = createExactJsonTools();
  if (canonical(readback.value as unknown as JsonValue) !== canonical(selected as unknown as JsonValue)) {
    return { ok: false, error: { code: 'malformed', message: 'The drawing does not reconstruct this selected term, type and context.', path: ['checking', 'selected'] } };
  }
  return drawing;
}
