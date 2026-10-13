import { proofWording as w, type ProofFold } from './source-proof-fold';
import { supplierWording } from './SourceSupplierReading';
import '../packets/structural-reading.css';

/** One closed leaf in place of a proof term. It labels the model's fields and draws no part of the term. The form
 * `(⋯ : statement)` is the one Lean's own printer uses for an elided proof. Every line is read from the prepared
 * frame and its receipt, so the leaf that stands for the original term says so first. An accepted typing carries
 * the supply panel's own sentence on what kernel acceptance means. */
export function ProofLeaf({ fold, original, onCheckStatement, checkStopped }: {
  fold: ProofFold; original?: boolean; onCheckStatement?: () => void;
  /** A whole-term check is retained without a checked pair, so the statement check is not offered again. */
  checkStopped?: boolean;
}) {
  const accepted = fold.typing.status === 'recorded' && fold.typing.outcome.tag === 'accepted';
  return <div className="struct-fold" data-proof-leaf={fold.basis}>
    <strong>{w.heading(fold)}</strong>
    {original && <p data-proof-frame="original">{w.originalFrame}</p>}
    <p><code data-proof-statement={fold.statement.source}>{w.closed(fold.statement)}</code></p>
    {fold.expectedDiffers && <p data-proof-expected="differs">{w.expected}</p>}
    <p data-proof-typing={fold.typing.status === 'recorded' ? fold.typing.outcome.tag : 'unrecorded'}>{w.typing(fold.typing)}</p>
    <p data-proof-axioms={fold.axioms.status}>{accepted ? `${w.axioms(fold.axioms)} ${supplierWording.environment}` : w.axioms(fold.axioms)}</p>
    <p data-proof-basis={fold.basis}>{w.basis(fold)}</p>
    <p>{w.statement(fold.statement)} {w.data(fold)}</p>
    {onCheckStatement ? <><button type="button" className="toolbar-button" onClick={onCheckStatement}>{w.checkStatement}</button><p>{w.checkStatementNote}</p></>
      : checkStopped && <p data-proof-check="stopped">{w.checkStopped}</p>}
  </div>;
}
