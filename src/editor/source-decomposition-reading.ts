import { compilePositionalComponent, type PositionalLogicalRoot } from '../packets/semantic';
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { buildPositionalStructuralDrawing, readPositionalStructuralDrawing, type PositionalStructuralInput } from '../packets/structure';
import { recordedContextEntries, sourceSnapshotValidation } from './source-snapshot';
import type { SourceOccurrenceStep } from './source-occurrence';
import type { SourceDecomposition } from './source-decomposition';

const edges: Record<string, Partial<Record<SourceOccurrenceStep, number>>> = {
  app: { appFun: 1, appArg: 2 }, lam: { lamDomain: 2, lamBody: 3 }, forallE: { piDomain: 2, piBody: 3 },
  letE: { letType: 2, letValue: 3, letBody: 4 }, proj: { projValue: 3 },
};
const constructors = new Set(['bvar', 'sort', 'const', 'app', 'lam', 'forallE', 'letE', 'lit', 'proj']);
const pathFor = (index: number): RawPath => ['checking', 'steps', index, 'output', 'result'];
function candidate(record: SourceDecomposition, index: number) {
  if (!Number.isSafeInteger(index) || index < 0 || record.checking.status !== 'captured') return undefined;
  const output = record.checking.steps[index]?.output;
  return output?.status === 'candidate' ? output : undefined;
}
/** Presentation includes partial/mismatched candidates. Continuation eligibility
 * is a separate, stricter model/host decision. */
/** The logical root is supplied by the caller from the accepted provenance module (null removes it); no step-local receipt reading exists here. */
export function decompositionReading(record: SourceDecomposition, index: number, target: 'term' | 'type', root: PositionalLogicalRoot | null) {
  const output = candidate(record, index); if (!output || record.checking.status !== 'captured') return undefined;
  const logicalRoot = target === 'term' && root ? root : undefined;
  return compilePositionalComponent(output.result, { sourceIdentity: `decomposition:${record.captureId}:${index}`,
    sourcePath: pathFor(index), target, sourceOrigin: 'decomposition-result', ...(logicalRoot ? { logicalRoot } : {}),
    recordedContext: recordedContextEntries(record.checking.binding) });
}
export function decompositionDrawing(record: SourceDecomposition, index: number) {
  const output = candidate(record, index); if (!output) return undefined;
  const path = pathFor(index), input = output.result;
  const drawing = buildPositionalStructuralDrawing(input, { sourceIdentity: `decomposition:${record.captureId}:${index}`, sourcePath: path });
  if (!drawing.ok) return drawing;
  const read = readPositionalStructuralDrawing(drawing.value); if (!read.ok) return read;
  const { canonical } = createExactJsonTools();
  if (canonical(read.value as unknown as JsonValue) !== canonical(input as unknown as JsonValue)) return {
    ok: false as const, error: { code: 'malformed' as const, message: 'The drawing does not reconstruct the exact decomposition result.', path },
  };
  return drawing;
}
/** Only actual ordinary edges rooted at result.term map to a focus request.
 * Carrier fields, telescope entries, binder names and universe fields do not. */
export function positionalResultPath(input: PositionalStructuralInput, sourcePath: RawPath, rawPath: RawPath): SourceOccurrenceStep[] | undefined {
  try {
    sourceSnapshotValidation.preflight({ sourcePath, rawPath }, 16384, []);
    const prefix = [...sourcePath, 'term'];
    if (rawPath.length < prefix.length || rawPath.length > prefix.length + 64 || !prefix.every((part, i) => part === rawPath[i])) return undefined;
    const drawing = buildPositionalStructuralDrawing(input, { sourceIdentity: 'positional-path', sourcePath });
    if (!drawing.ok) return undefined;
    let node = input.term as JsonValue[]; const result: SourceOccurrenceStep[] = [];
    for (const field of rawPath.slice(prefix.length)) {
      const edge = Object.entries(edges[String(node[0])] ?? {}).find(([, index]) => field === index);
      if (!edge) return undefined;
      result.push(edge[0] as SourceOccurrenceStep); node = node[field as number] as JsonValue[];
    }
    return constructors.has(String(node[0])) ? result : undefined;
  } catch { return undefined; }
}
export function decompositionResultPath(record: SourceDecomposition, index: number, rawPath: RawPath): SourceOccurrenceStep[] | undefined {
  const output = candidate(record, index);
  return output ? positionalResultPath(output.result, pathFor(index), rawPath) : undefined;
}
