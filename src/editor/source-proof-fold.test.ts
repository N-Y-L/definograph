import { readFileSync } from 'node:fs';
import { describe, expect, it, vi } from 'vitest';
import { validateSourceSnapshot, type SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionHistory, type DecompositionOperation, type SourceDecompositionBundle } from './source-decomposition';
import { isSelectionClass } from './selection-class';
import { proofSnapshot } from './source-proof-fold.test-fixtures';
import { PROOF_STATEMENT_CHARACTERS, proofWording, rootProofFold, selectionClassUnknown } from './source-proof-fold';

/** Constructed controls replace only the supply reading, to state what the accepted module returned; real captures use it unchanged. */
const supply = vi.hoisted(() => ({ links: undefined as undefined | ((captureId: string) => unknown[]) }));
vi.mock('./source-supplier', async original => {
  const actual = await original<typeof import('./source-supplier')>();
  return { ...actual, supplierReading: (...args: Parameters<typeof actual.supplierReading>) => supply.links ? { links: supply.links(args[1]) } : actual.supplierReading(...args) };
});
function withSupply<T>(links: (captureId: string) => unknown[], run: () => T): T {
  supply.links = links;
  try { return run(); } finally { supply.links = undefined; }
}
/** Only the fields the fold reads from a history: the whole-term path, the absent seed and each attempt's first operation. */
function historyOf(first: DecompositionOperation['kind'][], path: string[] = [], seed: unknown = null): DecompositionHistory {
  return { occurrence: { path }, seed, attempts: first.map((kind, index) => ({ record: { captureId: `attempt-${index + 1}`, operations: [{ kind }], checking: { status: 'captured' } } })) } as unknown as DecompositionHistory;
}
const link = (status: string) => ({ from: 0, to: 1, status, typing: { index: 5 },
  formation: { judgements: [{ established: status === 'supplier', receipts: [{ index: 7, outcome: 'accepted' }, { index: 9, outcome: 'rejected' }] }, { established: false, receipts: [{ index: 11, outcome: 'accepted' }] }] } });

describe('selection class', () => {
  it('admits exactly the three reported classes', () => {
    for (const value of ['proposition', 'proof', 'other']) expect(isSelectionClass(value)).toBe(true);
    for (const value of [undefined, null, '', 'proof-type', 'Proof', 1, {}, ['proof']]) expect(isSelectionClass(value)).toBe(false);
  });
});

describe('closed proof reading, constructed controls', () => {
  it('does not close a term that is not reported as a proof', () => {
    const snapshot = proofSnapshot();
    for (const selectionClass of [undefined, 'proposition', 'other'] as const) expect(rootProofFold({ snapshot, selectionClass })).toBeUndefined();
    expect(rootProofFold({ snapshot, selectionClass: 'other', printedStatement: 'P', history: historyOf(['logical', 'fields']) })).toBeUndefined();
  });
  it('closes a reported proof on the elaborator basis with the recorded verdict and axioms', () => {
    const fold = rootProofFold({ snapshot: proofSnapshot({ axioms: ['Classical.choice', 'propext', 'Quot.sound'] }), selectionClass: 'proof' })!;
    expect(fold).toEqual({ basis: 'elaborator', established: null, statement: { source: 'recorded', text: 'P' }, expectedDiffers: false,
      typing: { status: 'recorded', outcome: { tag: 'accepted' } }, axioms: { status: 'recorded', names: ['Classical.choice', 'propext', 'Quot.sound'] }, termNodes: 1 });
    expect(Object.isFrozen(fold) && Object.isFrozen(fold.axioms) && Object.isFrozen(fold.statement)).toBe(true);
    expect(proofWording.closed(fold.statement)).toBe('(⋯ : P)');
    expect(proofWording.heading(fold)).toBe('Term reported as a proof, not drawn');
    expect(proofWording.titles(fold)).toEqual({ term: 'Selected term', type: 'Inferred type' });
    // The accepted receipt is the prepared term's, and the line says so.
    expect(proofWording.typing(fold.typing)).toBe('Typing: accepted by Lean’s kernel. The recorded declaration gives the prepared term its recorded inferred type in the captured context.');
    expect(proofWording.axioms(fold.axioms)).toBe('Axioms recorded for that declaration: Classical.choice, propext, Quot.sound.');
    expect(proofWording.basis(fold)).toBe('Statement is a proposition: reported by Lean’s elaborator. No kernel check of this is recorded.');
    expect(proofWording.data(fold)).toBe('The prepared term, 1 constructor node, is kept as data and is not drawn. Its exact form stays under Check outcomes and in the saved snapshot.');
    expect(proofWording.verdict(fold)).toBe('Typing: accepted by Lean’s kernel. Axioms: Classical.choice, propext, Quot.sound. Statement is a proposition: reported by Lean’s elaborator.');
    // On the elaborator's report nothing calls the term a proof outright, and no kernel wording is attached to the proposition.
    for (const line of [proofWording.heading(fold), proofWording.titles(fold).term, proofWording.selected(fold), proofWording.verdict(fold), proofWording.closedSelection(fold)]) expect(line).not.toMatch(/proof term|^Proof/i);
    expect(`${proofWording.basis(fold)} ${proofWording.verdict(fold)}`).not.toContain('proposition: accepted by Lean’s kernel');
    // The drawer's line keeps the statement and states the remaining limit once.
    expect(proofWording.closedSelection(fold)).toBe('Selected term reported as a proof, closed at Source Term as (⋯ : P). Proof arguments inside the statement and in local definitions are still drawn as ordinary structure.');
  });
  it('gives the verdict as one line that claims no more than the detail lines behind the disclosure', () => {
    const kernel = withSupply(() => [link('supplier')], () => rootProofFold({ snapshot: proofSnapshot(), history: historyOf(['typeComponent']) }))!;
    const folds = [kernel, ...[{}, { axioms: ['sorryAx'] }, { outcome: { tag: 'rejected', kind: 'typeError', detail: 'type mismatch' } as const }, { outcome: { tag: 'unknown', message: 'heartbeats exhausted' } as const },
      { stoppedAfterContext: 'callback failed' }, { unchecked: 'The prepared context exceeds 128 declarations.' }, { unprepared: true }].map(options => rootProofFold({ snapshot: proofSnapshot(options), selectionClass: 'proof' })!)];
    const count = (text: string, phrase: string) => text.split(phrase).length - 1;
    for (const fold of folds) {
      const verdict = proofWording.verdict(fold), details = `${proofWording.typing(fold.typing)} ${proofWording.axioms(fold.axioms)} ${proofWording.basis(fold)}`;
      // Three short sentences: the typing outcome, the axioms, and whose word it is that the statement is a proposition.
      expect(verdict).toBe(`${proofWording.typingLead(fold.typing)} ${proofWording.axiomsLead(fold.axioms)} ${proofWording.basisLead(fold)}`);
      expect(verdict).toMatch(/^Typing: [^.]+\. Axioms: .+\. Statement is a proposition: [^.]+\.$/);
      expect(verdict).not.toMatch(/\n|not drawn|kept as data|captured environment/);
      // Every sentence of the verdict opens a detail line, so the kernel is named exactly as often as the details name it.
      for (const phrase of ['accepted by Lean’s kernel', 'rejected by Lean’s kernel', 'reported by Lean’s elaborator']) expect(count(verdict, phrase), `${phrase}: ${verdict}`).toBe(count(details, phrase));
      for (const lead of [proofWording.typingLead(fold.typing), proofWording.basisLead(fold)]) expect(details).toContain(lead);
    }
    expect(count(proofWording.verdict(kernel), 'accepted by Lean’s kernel')).toBe(2);
    expect(folds.slice(3).map(fold => count(proofWording.verdict(fold), 'accepted by Lean’s kernel'))).toEqual([0, 0, 0, 0, 0]);
    // The disclosure's label stays in view: it says what it holds and counts what is not drawn. On the leaf that
    // stands for the original term it names the frame, and that leaf's verdict opens with its subject.
    expect(proofWording.checked(kernel, false)).toBe('What was checked · 1 constructor node not drawn');
    expect(proofWording.checked(kernel, true)).toBe('What was checked: the prepared term · 1 constructor node not drawn');
    expect(proofWording.checked({ ...kernel, termNodes: 4 }, false)).toBe('What was checked · 4 constructor nodes not drawn');
    expect(proofWording.checked(folds.at(-1)!, false)).toBe('What was checked · term not drawn');
    expect(proofWording.preparedSubject).toBe('Prepared term.');
  });
  it('lists a placeholder axiom as recorded and never reads it for the verdict', () => {
    const fold = rootProofFold({ snapshot: proofSnapshot({ axioms: ['sorryAx'] }), selectionClass: 'proof' })!;
    expect(fold.typing).toEqual({ status: 'recorded', outcome: { tag: 'accepted' } });
    expect(proofWording.axioms(fold.axioms)).toBe('Axioms recorded for that declaration: sorryAx.');
    expect(proofWording.axioms(rootProofFold({ snapshot: proofSnapshot(), selectionClass: 'proof' })!.axioms)).toBe('Axioms recorded for that declaration: none.');
  });
  it('words a kernel verdict only for a recorded accepted or rejected declaration', () => {
    const rejected = rootProofFold({ snapshot: proofSnapshot({ outcome: { tag: 'rejected', kind: 'typeError', detail: 'type mismatch' } }), selectionClass: 'proof' })!;
    expect(proofWording.typing(rejected.typing)).toBe('Typing: rejected by Lean’s kernel. Type error: type mismatch');
    expect(rejected.axioms).toEqual({ status: 'unrecorded', reason: 'declaration was not installed' });
    const unknown = rootProofFold({ snapshot: proofSnapshot({ outcome: { tag: 'unknown', message: 'heartbeats exhausted' } }), selectionClass: 'proof' })!;
    expect(proofWording.typing(unknown.typing)).toBe('Typing: no kernel verdict. The check ended without an answer: heartbeats exhausted');
    const stopped = rootProofFold({ snapshot: proofSnapshot({ stoppedAfterContext: 'callback failed' }), selectionClass: 'proof' })!;
    expect(stopped.typing).toEqual({ status: 'unrecorded', reason: 'callback failed' }); expect(stopped.axioms).toEqual({ status: 'unrecorded', reason: 'callback failed' });
    const unchecked = rootProofFold({ snapshot: proofSnapshot({ unchecked: 'The prepared context exceeds 128 declarations.' }), selectionClass: 'proof' })!;
    expect(proofWording.typing(unchecked.typing)).toBe('Typing: no kernel verdict is recorded. The prepared context exceeds 128 declarations.');
    expect(proofWording.axioms(unchecked.axioms)).toBe('Axioms: not recorded. The prepared context exceeds 128 declarations.');
    for (const fold of [rejected, unknown, stopped, unchecked]) expect(`${proofWording.typing(fold.typing)} ${proofWording.verdict(fold)}`).not.toContain('Typing: accepted');
    expect(proofWording.verdict(rejected)).toBe('Typing: rejected by Lean’s kernel. Axioms: not recorded. Statement is a proposition: reported by Lean’s elaborator.');
    expect(proofWording.verdict(unknown)).toContain('Typing: no kernel verdict. Axioms: not recorded.');
    // Check outcomes holds the term only when a receipt for it is recorded.
    for (const fold of [stopped, unchecked]) expect(proofWording.data(fold)).toBe('The prepared term, 1 constructor node, is kept as data and is not drawn. Its exact form stays in the saved snapshot.');
    expect(proofWording.data(rejected)).toContain('under Check outcomes and in the saved snapshot');
  });
  it('shows Lean’s printed statement first, then the recorded type written out, then only the record', () => {
    const snapshot = proofSnapshot();
    const printed = rootProofFold({ snapshot, selectionClass: 'proof', printedStatement: 'p ∨ ¬p' })!.statement;
    expect(printed).toEqual({ source: 'printed', text: 'p ∨ ¬p' });
    for (const printedStatement of [undefined, '', '   ', 'x'.repeat(PROOF_STATEMENT_CHARACTERS + 1)])
      expect(rootProofFold({ snapshot, selectionClass: 'proof', printedStatement })!.statement).toEqual({ source: 'recorded', text: 'P' });
    // Whatever the source of the line, it is named as the inferred type of the term.
    expect(proofWording.statement(printed)).toBe('Statement: the inferred type of the term, printed by Lean’s elaborator with local definitions substituted.');
    expect(proofWording.statement({ source: 'recorded', text: 'P' })).toBe('Statement: the recorded inferred type of the term, written out with every argument explicit.');
    const unprepared = rootProofFold({ snapshot: proofSnapshot({ unprepared: true }), selectionClass: 'proof' })!;
    expect(unprepared.statement).toEqual({ source: 'record' }); expect(unprepared.termNodes).toBeNull();
    expect(proofWording.closed(unprepared.statement)).toBe('⋯');
    expect(proofWording.statement(unprepared.statement)).toContain('stays in the record');
    expect(proofWording.data(unprepared)).toBe('The term is kept as data and is not drawn. Its exact form stays in the saved snapshot.');
  });
  it('says when the recorded expected type is not the inferred type shown', () => {
    const truth = ['const', ['str', ['anonymous'], 'True'], []] as never;
    const same = rootProofFold({ snapshot: proofSnapshot({ expected: (_h, P) => P }), selectionClass: 'proof' })!;
    const differs = rootProofFold({ snapshot: proofSnapshot({ expected: () => truth }), selectionClass: 'proof' })!;
    expect(same.expectedDiffers).toBe(false); expect(differs.expectedDiffers).toBe(true);
    expect(rootProofFold({ snapshot: proofSnapshot(), selectionClass: 'proof' })!.expectedDiffers).toBe(false);
    expect(rootProofFold({ snapshot: proofSnapshot({ unprepared: true }), selectionClass: 'proof' })!.expectedDiffers).toBe(false);
    // The difference is its own short line beside the verdict, which stays the same.
    expect(proofWording.verdict(differs)).toBe(proofWording.verdict(same));
    // The sentence states a difference of recorded expressions and nothing about which one holds.
    expect(proofWording.expected).toBe('The expected type recorded for this selection is a different expression; see the Expected type tab of Source data.');
  });
  it('tells an unreported class from a class Lean reported and from a type the kernel read', () => {
    const snapshot = proofSnapshot();
    expect(selectionClassUnknown({ snapshot })).toBe(true);
    for (const selectionClass of ['proposition', 'proof', 'other'] as const) expect(selectionClassUnknown({ snapshot, selectionClass })).toBe(false);
    for (const status of ['value-of-type', 'supplier'])
      expect(withSupply(() => [link(status)], () => selectionClassUnknown({ snapshot, history: historyOf(['typeComponent']) }))).toBe(false);
    expect(withSupply(() => [link('not-established')], () => selectionClassUnknown({ snapshot, history: historyOf(['typeComponent']) }))).toBe(true);
    expect(selectionClassUnknown({ snapshot, history: historyOf(['logical']) })).toBe(true);
    expect(proofWording.unreported(true)).toBe('Lean’s class of this selection was not reported: the term may be a proof, and no proof inside it is labelled. Rebuild the engine and install the matching extension, then run the selection again.');
    expect(proofWording.unreported(false)).toBe('This saved record does not hold Lean’s class of the selection: the term may be a proof, and no proof inside it is labelled.');
  });
  it('takes the kernel basis from an accepted supply reading of a type-component step on the whole term', () => {
    const snapshot = proofSnapshot();
    const fold = withSupply(id => id === 'attempt-2' ? [link('supplier')] : [link('not-established')],
      () => rootProofFold({ snapshot, history: historyOf(['typeComponent', 'typeComponent']) }))!;
    expect(fold.basis).toBe('kernel'); expect(proofWording.heading(fold)).toBe('Proof term, not drawn');
    expect(proofWording.titles(fold)).toEqual({ term: 'Selected proof term', type: 'Statement' });
    expect(fold.established).toEqual({ attempt: 2, typingOutcome: 6, formationOutcomes: [8] });
    // The label names the judgement the kernel accepted: that the statement is a proposition, not the statement itself.
    expect(proofWording.basis(fold)).toBe('Statement is a proposition: accepted by Lean’s kernel. Attempt 2 records that check (outcome 8) and an accepted typing of the term (outcome 6). Its supply reading lists the full conditions.');
    expect(proofWording.verdict(fold)).toBe('Typing: accepted by Lean’s kernel. Axioms: none. Statement is a proposition: accepted by Lean’s kernel.');
    expect(proofWording.closedSelection(fold)).toMatch(/^Selected proof term, closed at Source Term as \(⋯ : P\)\./);
    expect(proofWording.checkStatement).toBe('Check with the kernel that this statement is a proposition');
    // The kernel basis needs no report from the elaborator, and a report does not change it.
    expect(withSupply(() => [link('supplier')], () => rootProofFold({ snapshot, selectionClass: 'other', history: historyOf(['typeComponent']) }))!.basis).toBe('kernel');
  });
  it('does not close a term whose type the kernel established as a type, whatever the elaborator reported', () => {
    const snapshot = proofSnapshot();
    expect(withSupply(() => [link('value-of-type')], () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['typeComponent']) }))).toBeUndefined();
  });
  it('keeps the elaborator basis where the kernel established nothing about the whole term', () => {
    const snapshot = proofSnapshot();
    for (const status of ['not-established', 'conflicting', 'annotation-only'])
      expect(withSupply(() => [link(status)], () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['typeComponent']) }))!.basis).toBe('elaborator');
    // A step that is not a type component of the original pair, a part of the term, a legacy seed and a refused reading contribute nothing.
    expect(withSupply(() => [link('supplier')], () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['logical', 'focus']) }))!.basis).toBe('elaborator');
    expect(withSupply(() => [link('supplier')], () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['typeComponent'], ['appArg']) }))!.basis).toBe('elaborator');
    expect(withSupply(() => [link('supplier')], () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['typeComponent'], [], {}) }))!.basis).toBe('elaborator');
    expect(withSupply(() => { throw new Error('refused'); }, () => rootProofFold({ snapshot, selectionClass: 'proof', history: historyOf(['typeComponent']) }))!.basis).toBe('elaborator');
    expect(withSupply(() => { throw new Error('refused'); }, () => rootProofFold({ snapshot, history: historyOf(['typeComponent']) }))).toBeUndefined();
  });
});

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  priorAttempts: SourceDecompositionBundle[];
  response: { selectionClass?: unknown; sourceSnapshot: SourceSnapshot; sourceDecomposition: SourceDecompositionBundle['record'] };
}
const location = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
const rows: Row[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
function captured(label: string) {
  const row = rows.filter(candidate => candidate.label === label).at(-1);
  if (!row) throw Error(`no acceptance rows for ${label}`);
  const snapshot = validateSourceSnapshot(row.parent.snapshot);
  const prior = validateDecompositionHistory({ snapshot, occurrence: row.parent.occurrence, seed: null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, prior);
  return { row, snapshot, history: validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] }) };
}
describe.skipIf(!rows.length)('closed proof reading on the acceptance corpus', () => {
  it('reports the class of each real selection and establishes a named theorem constant by the kernel', () => {
    const { row, snapshot, history } = captured('named theorem constant selected');
    expect(row.response.selectionClass).toBe('proof');
    const reported = rootProofFold({ snapshot, selectionClass: 'proof' })!;
    expect(reported.basis).toBe('elaborator'); expect(reported.typing).toEqual({ status: 'recorded', outcome: { tag: 'accepted' } });
    expect(reported.statement.source).toBe('recorded');
    const established = rootProofFold({ snapshot, history })!;
    expect(established.basis).toBe('kernel'); expect(established.established?.attempt).toBe(1);
    const attempt = history.attempts[0].record.checking;
    if (attempt.status !== 'captured') throw Error('missing checks');
    // The cited outcomes are the attempt's own accepted receipts: the selected component and the type component.
    expect(attempt.checks[established.established!.typingOutcome - 1]).toMatchObject({ label: 'component', outcome: { tag: 'accepted' } });
    for (const outcome of established.established!.formationOutcomes) expect(attempt.checks[outcome - 1]).toMatchObject({ label: 'component', outcome: { tag: 'accepted' } });
    expect(established.statement).toEqual(reported.statement); expect(reported.expectedDiffers).toBe(false);
    // `rfl` selected where `2 + 2 = 4` is expected: the inferred type shown is not the recorded expectation.
    expect(rootProofFold({ snapshot: captured('proof term selected').snapshot, selectionClass: 'proof' })!.expectedDiffers).toBe(true);
    expect(captured('statement selected').row.response.selectionClass).toBe('proposition');
    expect(captured('imported function applied').row.response.selectionClass).toBe('other');
  });
  it('carries the recorded axioms of a term that uses a lemma proved with a placeholder', () => {
    const { snapshot, history } = captured('term using a lemma proved with a placeholder');
    for (const fold of [rootProofFold({ snapshot, selectionClass: 'proof' })!, rootProofFold({ snapshot, history })!]) {
      expect(fold.typing).toEqual({ status: 'recorded', outcome: { tag: 'accepted' } });
      expect(fold.axioms).toEqual({ status: 'recorded', names: ['sorryAx'] });
    }
  });
  it('does not close an ordinary value whose type the kernel established as a type', () => {
    for (const label of ['imported function applied', 'variable named like the auxiliary entry']) {
      const { snapshot, history } = captured(label);
      expect(rootProofFold({ snapshot, history }), label).toBeUndefined();
      expect(rootProofFold({ snapshot, selectionClass: 'proof', history }), label).toBeUndefined();
    }
  });
  it('reads no kernel basis from a chain that takes no type-component step on the whole term', () => {
    for (const label of ['statement selected', 'second law of a structure', 'selection inside a binder']) {
      const { snapshot, history } = captured(label);
      expect(rootProofFold({ snapshot, history }), label).toBeUndefined();
    }
  });
});
