import type { InterpretationReport } from '../semantic/coverage';
import './interpretation-coverage.css';

export function InterpretationCoverage({ report, busy = false, onNodeSelect, onExpand }: {
  report: InterpretationReport;
  busy?: boolean;
  onNodeSelect: (id: string) => void;
  onExpand: (name: string) => void;
}) {
  const { clauses } = report;
  return <section className="interpretation-report" aria-label="Interpretation coverage">
    <p className="coverage-intro">This reports the vocabulary used in the selected fragment. It does not measure understanding or establish the statement.</p>
    <dl className="coverage-counts">
      <div><dt>Interpreted</dt><dd>{clauses.interpreted}</dd></div>
      <div><dt>Partly interpreted</dt><dd>{clauses.partial}</dd></div>
      <div><dt>Structure only</dt><dd>{clauses.structural}</dd></div>
    </dl>
    {report.vocabulary.length > 0 && <><h3>Recognized constructions</h3><ul className="coverage-vocabulary">{report.vocabulary.map(item => <li key={item.id}><span>{item.label}</span><span>{item.relationCount} {item.relationCount === 1 ? 'relation' : 'relations'}</span></li>)}</ul></>}
    {report.gaps.length > 0 ? <><h3>Meaning still folded or uninterpreted</h3><p>Typed objects and surrounding logic remain visible. Looking inside a definition may expose constructions the reader knows.</p><div className="coverage-gaps">{report.gaps.slice(0, 24).map(gap => <article key={gap.id}>
      <code>{gap.name}</code><span>{gap.occurrences} {gap.occurrences === 1 ? 'occurrence' : 'occurrences'} · {gap.nodeIds.length} {gap.nodeIds.length === 1 ? 'clause' : 'clauses'}</span>
      <p>{gap.kind === 'opaque' ? 'The exporter retained this expression without inspectable internal structure.' : gap.canExpand ? 'A checked definition body is available for inspection.' : gap.kind === 'symbolic' ? 'This symbol has only its stated type and relationships.' : 'No visual rule currently interprets this operation.'}{gap.retainedRelationIds.length > 0 ? ' Recognized constructions inside it are still shown.' : ''}</p>
      <div className="coverage-actions"><button type="button" onClick={() => onNodeSelect(gap.nodeIds[0]!)}>Locate in statement</button>{gap.canExpand && gap.constant && <button type="button" disabled={busy} onClick={() => onExpand(gap.constant!)}>Look inside definition</button>}</div>
    </article>)}</div>{report.gaps.length > 24 && <p>{report.gaps.length - 24} further entries are retained in the exported coverage report.</p>}</> : <p>Every exported predicate fragment in this selection uses the installed visual vocabulary. This does not certify the completeness of the mathematical interpretation.</p>}
    {report.diagnostics.map((message, index) => <p key={index}>{message}</p>)}
  </section>;
}
