import type { SourceDecomposition } from './source-decomposition';
import { SOURCE_PRESENTATION_NOTE, SOURCE_PRESENTATION_PROOF_MARK, SOURCE_PRESENTATION_PROOF_NOTE, sourceResultPresentation } from './source-presentation';

/** React text children only: native notation is never markup or executable code. */
export function SourceResultPresentation({ record, stepIndex, presentation }: {
  record: SourceDecomposition; stepIndex: number; presentation: unknown;
}) {
  const result = sourceResultPresentation(record, stepIndex, presentation);
  return result.status === 'available' ? <>
    <pre aria-label="Readable Lean result"><code>{result.text}</code></pre>
    <p>{SOURCE_PRESENTATION_NOTE}</p>
    {result.text.includes(SOURCE_PRESENTATION_PROOF_MARK) && <p data-presentation-proof-elided="">{SOURCE_PRESENTATION_PROOF_NOTE}</p>}
  </> : <p role="status">{result.reason}</p>;
}
