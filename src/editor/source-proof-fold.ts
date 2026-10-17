/** Whether the selected term is shown closed as a proof, and what the retained
 * records say about it.
 *
 * Pure derivation over an already validated snapshot and, when one is retained,
 * the validated history. It creates no record, changes no validator and reruns
 * nothing. Two separate facts can close the term. The elaborator's report
 * (`Meta.isProp` on the inferred type) is a classification, not a receipt. The
 * kernel basis is the accepted supply reading of a type-component step taken on
 * the whole selected term: an accepted typing receipt for the term and an
 * established proposition formation for its type. Where the kernel establishes
 * that the type is not a proposition, the term is not closed, whatever the
 * elaborator reported. The typing verdict and the axiom list are the snapshot's
 * own component receipt and its audit, read as they were recorded. */
import { counted } from '../core/counted';
import { createExactJsonTools, type JsonValue } from '../packets/packet';
import { nameText } from '../packets/syntax';
import { scopedExpressionLabel } from './definition-occurrences';
import type { SelectionClass } from './selection-class';
import type { DecompositionHistory } from './source-decomposition';
import { sourceSnapshotDrawings, sourceSnapshotValidation, type SnapshotOutcome, type SourceSnapshot } from './source-snapshot';
import { supplierReading } from './source-supplier';

/** The statement text, when one line of it is available, and where that line comes from. `printed` is Lean's own
 * notation from the guided reading, which substitutes local definitions. `recorded` is written out from the exact
 * recorded inferred type, with every argument explicit. `record` means no line is shown: the type stays in the record. */
export type ProofStatement = { source: 'printed' | 'recorded'; text: string } | { source: 'record' };
export type ProofTyping = { status: 'recorded'; outcome: SnapshotOutcome } | { status: 'unrecorded'; reason: string };
/** Why a retained check of the statement established nothing. The first three are supply-reading statuses: no accepted
 * typing of the term, conflicting formation answers, or neither a proposition nor a type established. */
export type UnestablishedCheck = { attempt: number } & ({ outcome: 'annotation-only' | 'conflicting' | 'not-established' | 'no-reading' | 'unreadable' }
  | { outcome: 'unrecorded'; attempted: boolean; reason: string });
export type ExpectedComparison = 'absent' | 'same' | 'differs' | 'unresolved';
export type ProofAxioms = { status: 'recorded'; names: string[] } | { status: 'unrecorded'; reason: string };
export interface ProofFold {
  basis: 'elaborator' | 'kernel';
  /** Kernel basis only: the retained attempt and its numbered outcomes that the basis rests on, as a reader counts them. */
  established: { attempt: number; typingOutcome: number; formationOutcomes: number[] } | null;
  /** Elaborator basis only: every retained attempt that took a type-component step on the whole term and established
   * nothing about its statement, numbered as a reader counts them, with what its record says. */
  unestablished: UnestablishedCheck[];
  statement: ProofStatement;
  /** How the expected type recorded at this position compares, as exact data, with the prepared inferred type.
   * `same` and `differs` compare two recorded expressions. An expectation that is not the same and holds a
   * metavariable is `unresolved`: the snapshot keeps the expectation as Lean stored it, without filling in
   * metavariables (for `hp` in `⟨hp, hq⟩` it is one metavariable), so it is not reported as different.
   * `absent` means no expectation or no prepared frame was recorded. */
  expected: ExpectedComparison;
  typing: ProofTyping;
  axioms: ProofAxioms;
  /** Constructor nodes recorded for the prepared term in the checked raw drawing, or null without a prepared frame. */
  termNodes: number | null;
}
export interface ProofFoldInput {
  snapshot: SourceSnapshot;
  /** The elaborator's class reported with this capture, when the host supplied one. */
  selectionClass?: SelectionClass;
  /** Lean's printed statement for this selection, when the guided reading produced one. */
  printedStatement?: string;
  /** The validated history retained by the host, when the selection has one. */
  history?: DecompositionHistory;
}

export const PROOF_STATEMENT_CHARACTERS = 4096;

/** What the kernel established about the whole selected term's type, read from the first type-component step taken
 * directly on the original pair. A refused or unfinished reading establishes nothing; it is listed as a check that
 * established nothing, so the leaf never says that no check is recorded when one was taken. */
function kernelReading(history: DecompositionHistory): { proof: true; established: NonNullable<ProofFold['established']> } | { proof: false } | { unestablished: UnestablishedCheck[] } | undefined {
  if (history.occurrence.path.length !== 0 || history.seed) return undefined;
  let notProposition = false;
  const unestablished: UnestablishedCheck[] = [];
  for (const [position, entry] of history.attempts.entries()) {
    const record = entry.record, attempt = position + 1;
    if (record.operations[0]?.kind !== 'typeComponent') continue;
    if (record.checking.status !== 'captured') {
      unestablished.push({ attempt, outcome: 'unrecorded', attempted: record.checking.attempted, reason: record.checking.reason });
      continue;
    }
    let link;
    try { link = supplierReading(history, record.captureId, 0).links.find(item => item.from === 0); } catch { unestablished.push({ attempt, outcome: 'unreadable' }); continue; }
    if (link?.status === 'supplier') return { proof: true, established: { attempt, typingOutcome: link.typing.index + 1,
      formationOutcomes: link.formation.judgements.filter(group => group.established)
        .flatMap(group => group.receipts.filter(receipt => receipt.outcome === 'accepted').map(receipt => receipt.index + 1)) } };
    if (link?.status === 'value-of-type') notProposition = true;
    else unestablished.push({ attempt, outcome: link ? link.status : 'no-reading' });
  }
  return notProposition ? { proof: false } : unestablished.length ? { unestablished } : undefined;
}

function statementOf(snapshot: SourceSnapshot, printed: string | undefined): ProofStatement {
  const shown = (text: string | undefined) => text !== undefined && text.trim().length > 0 && [...text].length <= PROOF_STATEMENT_CHARACTERS;
  if (shown(printed)) return { source: 'printed', text: printed! };
  if (snapshot.prepared.status !== 'available') return { source: 'record' };
  try {
    // The same named-to-positional association the snapshot validator reconstructs; no inference and no reduction.
    const positional = sourceSnapshotValidation.positionalBinding(snapshot.prepared.frame, ['prepared', 'frame']);
    const text = scopedExpressionLabel({ home: { arity: positional.items.length, telescope: positional.telescope }, term: positional.term, type: positional.type }, 'type');
    return shown(text) ? { source: 'recorded', text } : { source: 'record' };
  } catch { return { source: 'record' }; }
}

function termNodeCount(snapshot: SourceSnapshot): number | null {
  const drawing = sourceSnapshotDrawings(snapshot).prepared;
  if (!drawing) return null;
  const nodes = new Map(drawing.nodes.map(node => [node.id, node]));
  const start = nodes.get(drawing.rootId)?.children.find(edge => edge.role === 'sourceTerm')?.nodeId;
  if (start === undefined) return null;
  let count = 0;
  for (const pending = [start]; pending.length;) {
    const node = nodes.get(pending.pop()!);
    if (!node) continue;
    count++;
    for (const edge of node.children) pending.push(edge.nodeId);
  }
  return count;
}

/** Whether recorded raw data holds a metavariable node: an expression or universe level whose constructor tag is `mvar`. */
function holdsMetavariable(value: JsonValue): boolean {
  for (const pending: JsonValue[] = [value]; pending.length;) {
    const current = pending.pop()!;
    if (Array.isArray(current)) { if (current[0] === 'mvar') return true; pending.push(...current); }
    else if (current !== null && typeof current === 'object') pending.push(...Object.values(current));
  }
  return false;
}

function expectedComparison(snapshot: SourceSnapshot): ExpectedComparison {
  if (snapshot.expectedType.status !== 'available' || snapshot.prepared.status !== 'available') return 'absent';
  const { canonical } = createExactJsonTools();
  if (canonical(snapshot.expectedType.expression) === canonical(snapshot.prepared.frame.sourceType)) return 'same';
  return holdsMetavariable(snapshot.expectedType.expression) ? 'unresolved' : 'differs';
}

/** Nothing says what the whole selected term is: no class was reported with the capture and no retained kernel
 * check reads its type. Such a term is drawn as recorded and may be a proof. */
export function selectionClassUnknown(input: ProofFoldInput): boolean {
  const kernel = input.history ? kernelReading(input.history) : undefined;
  return input.selectionClass === undefined && (kernel === undefined || 'unestablished' in kernel);
}

/** The closed-proof reading of the whole selected term, or undefined when the term is not shown as a proof. */
export function rootProofFold(input: ProofFoldInput): ProofFold | undefined {
  const { snapshot } = input, reading = input.history ? kernelReading(input.history) : undefined;
  const kernel = reading && 'proof' in reading ? reading : undefined;
  if (kernel ? !kernel.proof : input.selectionClass !== 'proof') return undefined;
  const checking = snapshot.checking;
  let typing: ProofTyping, axioms: ProofAxioms;
  if (checking.status === 'unavailable') {
    typing = { status: 'unrecorded', reason: checking.reason }; axioms = { status: 'unrecorded', reason: checking.reason };
  } else {
    // Receipt 1 of a named-source capture is the component: the prepared term at its inferred type, closed over the context.
    const receipt = checking.checks[1], audit = checking.audits[1];
    const stopped = checking.action.status === 'error' ? checking.action.reason : 'The capture retained no receipt for the term.';
    typing = receipt ? { status: 'recorded', outcome: receipt.outcome } : { status: 'unrecorded', reason: stopped };
    axioms = !audit ? { status: 'unrecorded', reason: stopped }
      : audit.result.tag === 'available' ? { status: 'recorded', names: audit.result.axioms.map(axiom => nameText(axiom)) }
        : { status: 'unrecorded', reason: audit.result.reason };
  }
  const fold: ProofFold = { basis: kernel?.proof ? 'kernel' : 'elaborator', established: kernel?.proof ? kernel.established : null,
    unestablished: reading && 'unestablished' in reading ? reading.unestablished : [],
    statement: statementOf(snapshot, input.printedStatement), expected: expectedComparison(snapshot), typing, axioms, termNodes: termNodeCount(snapshot) };
  createExactJsonTools().freeze(fold);
  return fold;
}

/** The drawer's line for a selection shown closed. It names the leaf only where a recorded frame draws one; where
 * neither frame of the term was recorded, it says so with the recorded reason instead. */
export function closedSelectionLine(fold: ProofFold, snapshot: SourceSnapshot): { frames: 'recorded' | 'unrecorded'; text: string } {
  const drawings = sourceSnapshotDrawings(snapshot);
  if (drawings.original || drawings.prepared) return { frames: 'recorded', text: proofWording.closedSelection(fold) };
  const reason = snapshot.prepared.status === 'unavailable' ? snapshot.prepared.reason
    : snapshot.original.status === 'unavailable' ? snapshot.original.reason : 'no raw drawing is available.';
  return { frames: 'unrecorded', text: proofWording.unrecordedSelection(fold, reason) };
}

/** Fixed sentences of the closed-proof leaf. A kernel verdict is worded as one only for a recorded accepted or
 * rejected declaration; everything the elaborator reported is worded as a report. Each line names the judgement it
 * is about: the typing of the prepared term, and the statement being a proposition. Neither says the statement holds.
 * The leaf shows the statement, the one-line verdict and the two warnings; every other sentence sits behind its one
 * disclosure, whose label counts the constructor nodes that are not drawn. */
export const proofWording = Object.freeze({
  /** What the leaf stands for. The term is called a proof term only on the kernel basis. */
  heading(fold: ProofFold): string { return fold.basis === 'kernel' ? 'Proof term, not drawn' : 'Term reported as a proof, not drawn'; },
  /** Display titles of the term and its type where the whole checked term is shown closed. */
  titles(fold: ProofFold): { term: string; type: string } {
    return fold.basis === 'kernel' ? { term: 'Selected proof term', type: 'Statement' } : { term: 'Selected term', type: 'Inferred type' };
  },
  /** What the selection is called outside the leaf, by the same rule as the heading. */
  selected(fold: ProofFold): string { return fold.basis === 'kernel' ? 'Selected proof term' : 'Selected term reported as a proof'; },
  openArguments: 'Proof arguments inside this term are not yet folded: they are drawn as ordinary structure and are not labelled as proofs.',
  /** The same limit for a selection shown closed: only the selected term itself is closed. */
  closedSelection(fold: ProofFold): string {
    return `${proofWording.selected(fold)}, closed at Source Term as ${proofWording.closed(fold.statement)}. Proof arguments inside the statement and in local definitions are still drawn as ordinary structure.`;
  },
  /** The drawer line where neither frame of the term was recorded, so no view below holds the term or its leaf.
   * `reason` is the recorded reason the frames are unavailable. */
  unrecordedSelection(fold: ProofFold, reason: string): string {
    return `${proofWording.selected(fold)}${fold.statement.source === 'record' ? '' : ` of ${fold.statement.text}`}, not drawn. Neither Original data nor Checker input could record it, so no view below shows it. Recorded reason: ${reason}${/[.!?]$/.test(reason) ? '' : '.'}`;
  },
  /** No class was reported and no kernel check reads the type. A live capture names the remedy. */
  unreported(live: boolean): string {
    return `${live ? 'Lean’s class of this selection was not reported' : 'This saved record does not hold Lean’s class of the selection'}: the term may be a proof, and no proof inside it is labelled.${live ? ' Rebuild the engine and install the matching extension, then run the selection again.' : ''}`;
  },
  closed(statement: ProofStatement): string { return statement.source === 'record' ? '⋯' : `(⋯ : ${statement.text})`; },
  /** The label of the one disclosure, which stays in view: what it holds, and how much of the term is not drawn. On
   * the leaf that stands for the original term it names the frame that was checked, whose nodes the count is of. */
  checked(fold: ProofFold, original: boolean): string {
    const undrawn = fold.termNodes === null ? 'term not drawn' : `${counted(fold.termNodes, 'constructor node')} not drawn`;
    return `${original ? 'What was checked: the prepared term' : 'What was checked'} · ${undrawn}`;
  },
  /** Opens the verdict on the leaf that stands for the original term: the verdict is the prepared term's. */
  preparedSubject: 'Prepared term.',
  /** Shown on the leaf that stands for the original term: every line is read from the prepared frame. */
  originalFrame: 'This position holds the original term, before preparation. It is not drawn and stays in the saved snapshot. Every line of this leaf is about the prepared term under Checker input; the record does not prove the two frames equivalent.',
  /** A comparison of two recorded expressions, and nothing about which of them holds. */
  expected: 'The expected type recorded for this selection is a different expression; see the Expected type tab of Source data.',
  /** Kept with the other details: the reader says neither that the two match nor that they differ, so nothing is said
   * in view. */
  expectedUnresolved: 'The expected type recorded for this selection holds a metavariable, a placeholder of Lean’s elaboration, so the reader does not say whether it matches the statement; see the Expected type tab of Source data.',
  statement(statement: ProofStatement): string {
    if (statement.source === 'printed') return 'Statement: the inferred type of the term, printed by Lean’s elaborator with local definitions substituted.';
    if (statement.source === 'recorded') return 'Statement: the recorded inferred type of the term, written out with every argument explicit.';
    return 'Statement: the recorded inferred type of the term. It is not written on one line here and stays in the record.';
  },
  typingLead(typing: ProofTyping): string {
    if (typing.status === 'unrecorded') return 'Typing: no kernel verdict is recorded.';
    if (typing.outcome.tag === 'accepted') return 'Typing: accepted by Lean’s kernel.';
    return typing.outcome.tag === 'unknown' ? 'Typing: no kernel verdict.' : 'Typing: rejected by Lean’s kernel.';
  },
  typing(typing: ProofTyping): string {
    const lead = proofWording.typingLead(typing);
    if (typing.status === 'unrecorded') return `${lead} ${typing.reason}`;
    const outcome = typing.outcome;
    if (outcome.tag === 'accepted') return `${lead} The recorded declaration gives the prepared term its recorded inferred type in the captured context.`;
    if (outcome.tag === 'unknown') return `${lead} The check ended without an answer: ${outcome.message}`;
    return outcome.kind === 'typeError' ? `${lead} Type error: ${outcome.detail}` : `${lead} The term and its recorded type are not convertible.`;
  },
  axiomsLead(axioms: ProofAxioms): string {
    return axioms.status === 'unrecorded' ? 'Axioms: not recorded.' : `Axioms: ${axioms.names.length ? axioms.names.join(', ') : 'none'}.`;
  },
  axioms(axioms: ProofAxioms): string {
    if (axioms.status === 'unrecorded') return `${proofWording.axiomsLead(axioms)} ${axioms.reason}`;
    return `Axioms recorded for that declaration: ${axioms.names.length ? axioms.names.join(', ') : 'none'}.`;
  },
  /** What is known about the statement being a proposition, and from whom. It is not a verdict on the statement. */
  basisLead(fold: ProofFold): string {
    return `Statement is a proposition: ${fold.established ? 'accepted by Lean’s kernel' : 'reported by Lean’s elaborator'}.`;
  },
  /** What one retained check that established nothing records, as a sentence that opens with its attempt. */
  unestablished(check: UnestablishedCheck): string {
    const opening = `Attempt ${check.attempt}`;
    switch (check.outcome) {
      case 'not-established': return `${opening} submitted this check and established neither that the statement is a proposition nor that it is a type.`;
      case 'conflicting': return `${opening} submitted this check, and its accepted results disagree, so nothing is established.`;
      case 'annotation-only': return `${opening} recorded no accepted typing of the term, so its check establishes nothing about this statement.`;
      case 'no-reading': return `${opening} recorded no step to the term’s type, so it establishes nothing about this statement.`;
      case 'unreadable': return `${opening} is kept, but its record could not be read here, so it establishes nothing about this statement.`;
      // `attempted` means only that the capture was requested; the record can be missing after a refusal or an error.
      case 'unrecorded': return `${opening} ${check.attempted ? 'was sent for checking, but no record of its checks is kept' : 'was not sent for checking'}: ${check.reason}`;
    }
  },
  basis(fold: ProofFold): string {
    const found = fold.established;
    if (!found && fold.unestablished.length) return `${proofWording.basisLead(fold)} ${fold.unestablished.map(check => proofWording.unestablished(check)).join(' ')}`;
    if (!found) return `${proofWording.basisLead(fold)} No kernel check of this is recorded.`;
    return `${proofWording.basisLead(fold)} Attempt ${found.attempt} records that check (${found.formationOutcomes.length === 1 ? 'outcome' : 'outcomes'} ${found.formationOutcomes.join(', ')}) and an accepted typing of the term (outcome ${found.typingOutcome}). Its supply reading lists the full conditions.`;
  },
  /** The one line under a statement: the typing outcome, the axioms, and whose word it is that the statement is a proposition. */
  verdict(fold: ProofFold): string {
    return `${proofWording.typingLead(fold.typing)} ${proofWording.axiomsLead(fold.axioms)} ${proofWording.basisLead(fold)}`;
  },
  /** Where the undrawn term can still be read. Check outcomes holds it only when a receipt for the term is recorded. */
  data(fold: ProofFold): string {
    const recorded = fold.termNodes === null ? 'The term' : `The prepared term, ${fold.termNodes} constructor ${fold.termNodes === 1 ? 'node' : 'nodes'},`;
    return `${recorded} is kept as data and is not drawn. Its exact form stays ${fold.typing.status === 'recorded' ? 'under Check outcomes and in the saved snapshot' : 'in the saved snapshot'}.`;
  },
  checkStatement: 'Check with the kernel that this statement is a proposition',
  /** Kept with the other details; the action it describes sits directly above the disclosure. */
  checkStatementNote: 'The check above reruns the current Lean buffer twice: once to check the whole selected term, once to inspect its type. The term stays closed.',
  checkStopped: 'The check of the whole selected term returned no checked pair, so its type was not inspected. Its record is under Chosen occurrence checks in Checker input.',
});
