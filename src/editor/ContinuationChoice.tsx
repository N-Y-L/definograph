import type { SourceOccurrenceStep } from './source-occurrence';

const titles: Record<SourceOccurrenceStep, string> = {
  appFun: 'Function', appArg: 'Argument', lamDomain: 'Lambda domain', lamBody: 'Lambda body',
  piDomain: 'Product domain', piBody: 'Product body', letType: 'Let type', letValue: 'Let value',
  letBody: 'Let body', projValue: 'Projection value',
};
export function continuationPathTitle(path: SourceOccurrenceStep[]): string {
  return path.length ? path.map(step => titles[step]).join(' → ') : 'Whole result term';
}

/** Choosing a source position changes local focus only. Execution has its own button. */
export function ContinuationChoice({ path, onChooseRoot, onCheck }: {
  path: SourceOccurrenceStep[] | null; onChooseRoot: () => void; onCheck: (path: SourceOccurrenceStep[]) => void;
}) {
  return <div className="continuation-choice">
    <p>Choose a part of the result term in its guide or Structure, then check it. You can also inspect the type annotation and surrounding context; those fields do not start a new step.</p>
    <p className="occurrence-path" aria-live="polite">{path === null ? 'No eligible part chosen.' : continuationPathTitle(path)}</p>
    <div className="continuation-actions"><button type="button" className="quiet-button" onClick={onChooseRoot}>Choose whole result term</button>
      <button type="button" className="toolbar-button" disabled={path === null} onClick={() => { if (path !== null) onCheck([...path]); }}>Check chosen part</button></div>
    <p>Checking recomputes the chosen history from your current source. Earlier results and checks remain available.</p>
  </div>;
}
