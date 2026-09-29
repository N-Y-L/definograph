import { compilePositionalComponent } from '../packets/semantic';
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing } from '../packets/structure';
import { recordedContextEntries } from './source-snapshot';
import type { SourceHeadExposure } from './source-head-exposure';

/** Candidate availability is independent of every recorded typing outcome. */
export function headExposureReading(record: SourceHeadExposure) {
  if (record.checking.status !== 'captured' || record.checking.exposure?.status !== 'candidate') return undefined;
  return compilePositionalComponent(record.checking.exposure.result, {
    sourceIdentity: `head-exposure:${record.captureId}:${record.target}:after`,
    sourcePath: ['checking', 'exposure', 'result'], target: 'term', sourceOrigin: 'definition-head-exposure',
    recordedContext: recordedContextEntries(record.checking.binding),
  });
}

export function headExposureDrawing(record: SourceHeadExposure) {
  if (record.checking.status !== 'captured' || record.checking.exposure?.status !== 'candidate') return undefined;
  const input = record.checking.exposure.result;
  const drawing = buildPositionalStructuralDrawing(input, {
    sourceIdentity: `head-exposure:${record.captureId}:${record.target}:after`, sourcePath: ['checking', 'exposure', 'result'],
  });
  if (!drawing.ok) return drawing;
  const readback = readPositionalStructuralDrawing(drawing.value);
  if (!readback.ok) return readback;
  const { canonical } = createExactJsonTools();
  if (canonical(readback.value as unknown as JsonValue) !== canonical(input as unknown as JsonValue)) return {
    ok: false as const, error: { code: 'malformed' as const, message: 'The drawing does not reconstruct the exact exposure result.', path: ['checking', 'exposure', 'result'] },
  };
  return drawing;
}
