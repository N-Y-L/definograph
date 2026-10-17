import { proofWording as w, type ProofFold } from './source-proof-fold';
import { supplierWording } from './SourceSupplierReading';
import '../packets/structural-reading.css';
import './source-snapshot.css';

/** The one-line verdict and, when the recorded expected type is a different expression that holds no metavariable,
 * the line that says so.
 * The main panel and the leaf show the same two lines. `subject` names whose verdict it is where the leaf stands
 * for a different term. */
export function ProofVerdict({ fold, subject }: { fold: ProofFold; subject?: string }) {
  return <>
    <p data-proof-verdict={fold.basis}>{subject ? `${subject} ${w.verdict(fold)}` : w.verdict(fold)}</p>
    {fold.expected === 'differs' && <p data-proof-expected="differs">{w.expected}</p>}
  </>;
}

/** One closed leaf in place of a proof term. It labels the model's fields and draws no part of the term. The
 * statement comes first and largest, in the form `(⋯ : statement)` that Lean's own printer uses for an elided proof;
 * where no line of it is available, the leaf says so in its place. One line under it gives the verdict. A recorded
 * expected type that differs and holds no metavariable stays in view as one more line. Everything else sits behind one native disclosure,
 * closed until the reader opens it, whose label counts what is not drawn: what the leaf stands for, which frame was
 * checked, where the statement text comes from, what kernel acceptance means, and where the undrawn term is kept.
 * Every line is read from the prepared frame and its receipt, so the leaf that stands for the original term names
 * that frame at the start of its verdict and in the disclosure's label. The leaf's accessible name is the sentence
 * on what it stands for. */
export function ProofLeaf({ fold, original = false, onCheckStatement, checkStopped }: {
  fold: ProofFold; original?: boolean; onCheckStatement?: () => void;
  /** A whole-term check is retained without a checked pair, so the statement check is not offered again. */
  checkStopped?: boolean;
}) {
  const accepted = fold.typing.status === 'recorded' && fold.typing.outcome.tag === 'accepted';
  const unwritten = fold.statement.source === 'record';
  return <div className="struct-fold proof-leaf" role="group" aria-label={w.heading(fold)} data-proof-leaf={fold.basis}>
    <code className="proof-leaf-statement" data-proof-statement={fold.statement.source}>{w.closed(fold.statement)}</code>
    {unwritten && <p data-proof-statement-note="">{w.statement(fold.statement)}</p>}
    <ProofVerdict fold={fold} subject={original ? w.preparedSubject : undefined}/>
    {onCheckStatement ? <button type="button" className="toolbar-button" onClick={onCheckStatement}>{w.checkStatement}</button>
      : checkStopped && <p data-proof-check="stopped">{w.checkStopped}</p>}
    <details data-proof-checked="">
      <summary>{w.checked(fold, original)}</summary>
      <p>{w.heading(fold)}.</p>
      {original && <p data-proof-frame="original">{w.originalFrame}</p>}
      {!unwritten && <p>{w.statement(fold.statement)}</p>}
      <p data-proof-typing={fold.typing.status === 'recorded' ? fold.typing.outcome.tag : 'unrecorded'}>{w.typing(fold.typing)}</p>
      <p data-proof-axioms={fold.axioms.status}>{accepted ? `${w.axioms(fold.axioms)} ${supplierWording.environment}` : w.axioms(fold.axioms)}</p>
      <p data-proof-basis={fold.basis}>{w.basis(fold)}</p>
      {fold.expected === 'unresolved' && <p data-proof-expected="unresolved">{w.expectedUnresolved}</p>}
      <p>{w.data(fold)}</p>
      {onCheckStatement && <p>{w.checkStatementNote}</p>}
    </details>
  </div>;
}
