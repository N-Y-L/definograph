import type { SourceDecomposition } from './source-decomposition';
import { SOURCE_PRESENTATION_NOTE, sourceResultPresentation } from './source-presentation';

/** React text children only: native notation is never markup or executable code. */
export function SourceResultPresentation({ record, stepIndex, presentation }: {
  record: SourceDecomposition; stepIndex: number; presentation: unknown;
}) {
  const result = sourceResultPresentation(record, stepIndex, presentation);
  return result.status === 'available' ? <>
    <pre aria-label="Readable Lean result"><code>{result.text}</code></pre>
    <p>{SOURCE_PRESENTATION_NOTE}</p>
  </> : <p role="status">{result.reason}</p>;
}
