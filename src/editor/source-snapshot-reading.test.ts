import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { ProofLeaf, ProofVerdict } from './ProofLeaf';
import { SourceOccurrenceReading, SourceSnapshotReading } from './SourceSnapshotReading';
import { validateSourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import { parseEditorMessage } from './host';
import { proofWording, rootProofFold } from './source-proof-fold';
import { PROOF_CAPTURE, proofOccurrence, proofSnapshot } from './source-proof-fold.test-fixtures';
import { validateSourceOccurrence } from './source-occurrence';
import { supplierWording } from './SourceSupplierReading';
import { sourceOccurrenceDrawing } from './source-occurrence-structure';
import { readPositionalStructuralDrawing } from '../packets/structure';

const unavailable = { status: 'unavailable', kind: 'error', phase: 'original-inference', reason: 'The inferred type was unavailable.' };
const fixture = () => ({ schema: 'definograph.source-snapshot.v1',
  selection: { startByte: 0, endByte: 4, requestedStartByte: 0, requestedEndByte: 4, parentDeclaration: null },
  policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
  expectedType: { status: 'absent' }, original: unavailable, prepared: { ...unavailable, kind: 'prerequisite', phase: 'preparation' },
  checking: { ...unavailable, kind: 'prerequisite', phase: 'checking-prerequisite', attempted: false } });

describe('source snapshot reading boundaries', () => {
  it('does not promote saved data or unavailable inference into a checked source', () => {
    const snapshot = validateSourceSnapshot(fixture());
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot }));
    expect(html).toContain('Its origin is unverified');
    expect(html).toContain('Unavailable during original-inference');
    expect(html).toContain('Save source snapshot');
    expect(html).not.toContain('Exact constructor readback checked');
  });
  it('distinguishes no capture from an attempted call whose receipts are unavailable', () => {
    const value = fixture();
    let snapshot = validateSourceSnapshot(value);
    let html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'checking' }));
    expect(html).toContain('The source capture call did not begin');
    value.checking = { status: 'unavailable', kind: 'limit', phase: 'checking-output', reason: 'The complete record exceeded its budget.', attempted: true };
    snapshot = validateSourceSnapshot(value);
    html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'checking' }));
    expect(html).toContain('does not establish how many kernel checks ran or their outcomes');
    expect(html).not.toContain('kernel outcomes retained');
  });
});

describe('occurrence selection and result boundaries', () => {
  const raw = () => {
    const nat = ['const', ['str', ['anonymous'], 'Nat'], []];
    const n = ['str', ['anonymous'], 'n'];
    const frame = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: [],
      sourceTerm: ['lam', n, nat, ['bvar', ['nat', '0']], 'default'],
      sourceType: ['forallE', n, nat, nat, 'default'] };
    return validateSourceSnapshot({ ...fixture(), original: { status: 'available', typeOrigin: 'inferred', frame },
      prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame, checkerUniverseParams: [] } });
  };
  it('offers selection only on prepared term expression constructors with a host callback', () => {
    const snapshot = raw();
    const callback = () => undefined;
    for (const initialTab of ['original', 'expectedType', 'checking'] as const) {
      expect(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab, onCheckOccurrence: callback }))).not.toContain('Choose occurrence');
    }
    expect(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared' }))).not.toContain('Choose occurrence');
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared', onCheckOccurrence: callback }));
    expect(html.match(/aria-label="Choose occurrence:/g)).toHaveLength(3);
    expect(html).toContain('No occurrence chosen');
    expect(html).toContain('disabled=""');
    expect(html).not.toContain('data-reference-target');
  });
  it('shows attempted output omission without inventing a selected result or kernel success', () => {
    const snapshot = raw();
    const occurrence = validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1',
      parentCaptureId: '00000000-0000-0000-0000-000000000001', captureId: '00000000-0000-0000-0000-000000000002', path: ['lamBody'],
      policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
      checking: { status: 'unavailable', kind: 'limit', phase: 'occurrence-output', reason: 'Complete record exceeds the output limit.', attempted: true } }, snapshot);
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, occurrence, onCheckOccurrence: () => undefined }));
    expect(html).toContain('Chosen occurrence checks'); expect(html).toContain('Lambda body');
    expect(html).toContain('Its kernel outcomes are unavailable');
    expect(html).toContain('data-raw-selected="true"');
    expect(html).not.toContain('kernel outcomes retained'); expect(html).not.toContain('Exact dependent context');
  });
});

describe('a selected proof is shown closed with the statement it proves', () => {
  const idApplied = (h: unknown) => ['app', ['const', ['str', ['anonymous'], 'id'], []], h] as never;
  const axioms = ['Classical.choice', 'propext', 'Quot.sound'];
  const callback = () => undefined;
  const termPosition = (html: string) => html.split('data-raw-role="sourceTerm"')[1].split('data-raw-role="sourceType"')[0];
  /** The leaf at a term position: what a reader sees before opening anything, and the body of its one disclosure. */
  function leafParts(term: string) {
    const leaf = term.slice(term.indexOf('<div class="struct-fold proof-leaf"'));
    // A native disclosure without the `open` attribute is closed until the reader opens it.
    expect(leaf.match(/<details[^>]*>/g)).toEqual(['<details data-proof-checked="">']);
    const [before, rest] = leaf.split('<details data-proof-checked="">'), [checked, after] = rest.split('</details>');
    // The disclosure's own label is in view while it is closed.
    return { shown: before + after.slice(0, after.indexOf('</div>') + '</div>'.length), label: /^<summary>([^<]*)<\/summary>/.exec(checked)![1], checked };
  }
  it('draws no structure for the proof term and offers no occurrence choice inside it', () => {
    const snapshot = proofSnapshot({ axioms, term: idApplied });
    for (const initialTab of ['original', 'prepared'] as const) {
      const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab, selectionClass: 'proof', onCheckOccurrence: callback, onCheckStatement: callback }));
      const term = termPosition(html);
      expect(term).toContain('data-raw-closed="true"'); expect(term).toContain('data-proof-leaf="elaborator"');
      expect(term).not.toContain('data-raw-constructor'); expect(term).not.toContain('Exact fields and constructor path');
      expect(html).not.toContain('Choose occurrence'); expect(html).not.toContain('Choose a constructor inside the prepared term');
      // The statement comes first, then one line with the verdict, then the one action and the disclosure's label;
      // nothing else is in view. The leaf that stands for the original term names the verdict's subject first.
      const { shown, label, checked } = leafParts(term);
      expect(shown).toBe('<div class="struct-fold proof-leaf" role="group" aria-label="Term reported as a proof, not drawn" data-proof-leaf="elaborator"><code class="proof-leaf-statement" data-proof-statement="recorded">(⋯ : P)</code>'
        + `<p data-proof-verdict="elaborator">${initialTab === 'original' ? 'Prepared term. ' : ''}Typing: accepted by Lean’s kernel. Axioms: Classical.choice, propext, Quot.sound. Statement is a proposition: reported by Lean’s elaborator.</p>`
        + `<button type="button" class="toolbar-button">${proofWording.checkStatement}</button></div>`);
      // The fold keeps a label and a count in view: the constructor nodes of the term that are not drawn.
      expect(label).toBe(`What was checked${initialTab === 'original' ? ': the prepared term' : ''} · 4 constructor nodes not drawn`);
      expect(term).not.toContain('proposition: accepted by Lean’s kernel');
      // Behind the one disclosure, closed until opened: what the leaf stands for and every qualifier, worded as before.
      expect(checked.startsWith(`<summary>${label}</summary><p>Term reported as a proof, not drawn.</p>`)).toBe(true);
      expect(checked).toContain('<p data-proof-typing="accepted">Typing: accepted by Lean’s kernel. The recorded declaration gives the prepared term its recorded inferred type in the captured context.</p>');
      // An accepted typing carries the supply panel's own qualifier, directly after the axiom list.
      expect(checked).toContain(`<p data-proof-axioms="recorded">Axioms recorded for that declaration: Classical.choice, propext, Quot.sound. ${supplierWording.environment}</p>`);
      expect(checked).toContain('<p data-proof-basis="elaborator">Statement is a proposition: reported by Lean’s elaborator. No kernel check of this is recorded.</p>');
      expect(checked).toContain('<p>Statement: the recorded inferred type of the term, written out with every argument explicit.</p>');
      expect(checked).toContain(`<p>${proofWording.data(rootProofFold({ snapshot, selectionClass: 'proof' })!)}</p>`); expect(checked).toContain(`<p>${proofWording.checkStatementNote}</p>`);
      expect(checked.includes(`<p data-proof-frame="original">${proofWording.originalFrame}</p>`)).toBe(initialTab === 'original');
      // The declarations and the statement stay drawn around the closed term, and the drawing still holds every node.
      expect(html.split('data-raw-role="sourceType"')[1]).toContain('data-raw-constructor="fvar"');
      expect(html).toContain('data-raw-constructor="cdecl"'); expect(html).toContain('Exact constructor readback checked');
      // The drawer says first that the term is closed and that the limit still holds around it.
      expect(html).toContain(`data-proof-closed="elaborator">${proofWording.closedSelection(rootProofFold({ snapshot, selectionClass: 'proof' })!)}`);
      expect(html).not.toContain(proofWording.openArguments); expect(html).not.toContain('data-selection-class');
    }
  });
  it('says on the Original data tab that the leaf describes the prepared term', () => {
    // Preparation changed the term: the original is the hypothesis alone, the prepared term applies `id` to it.
    const snapshot = proofSnapshot({ axioms, term: idApplied, originalTerm: h => h }), fold = rootProofFold({ snapshot, selectionClass: 'proof' })!;
    if (snapshot.original.status !== 'available' || snapshot.prepared.status !== 'available') throw Error('fixture frames missing');
    expect(snapshot.original.frame.sourceTerm).not.toEqual(snapshot.prepared.frame.sourceTerm); expect(fold.termNodes).toBeGreaterThan(1);
    const original = termPosition(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'original', selectionClass: 'proof' })));
    expect(original).not.toContain('data-raw-constructor');
    // In view, the verdict opens with its subject and the disclosure's label names the frame whose nodes it counts.
    // Behind the disclosure, the first lines say what stands at this position.
    const { shown, label, checked } = leafParts(original);
    expect(shown).toContain('</code><p data-proof-verdict="elaborator">Prepared term. Typing: accepted by Lean’s kernel.');
    expect(label).toBe(`What was checked: the prepared term · ${fold.termNodes} constructor nodes not drawn`);
    expect(checked.startsWith(`<summary>${label}</summary><p>Term reported as a proof, not drawn.</p><p data-proof-frame="original">${proofWording.originalFrame}</p>`)).toBe(true);
    // Every figure and verdict on that leaf is worded as the prepared term's.
    expect(checked).toContain('Typing: accepted by Lean’s kernel. The recorded declaration gives the prepared term its recorded inferred type');
    expect(checked).toContain(`The prepared term, ${fold.termNodes} constructor nodes, is kept as data`);
    expect(proofWording.originalFrame).toContain('Every line of this leaf is about the prepared term under Checker input');
    expect(proofWording.originalFrame).toContain('does not prove the two frames equivalent');
    const prepared = leafParts(termPosition(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared', selectionClass: 'proof' }))));
    expect(prepared.label).toBe(`What was checked · ${fold.termNodes} constructor nodes not drawn`); expect(prepared.shown).not.toContain('Prepared term.');
    expect(prepared.checked).not.toContain('data-proof-frame'); expect(prepared.checked).toContain(`The prepared term, ${fold.termNodes} constructor nodes,`);
  });
  it('draws the statement beside a closed proof however large the proof term is', () => {
    const nested = (h: unknown) => { let term = h; for (let depth = 0; depth < 20; depth++) term = idApplied(term); return term as never; };
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ term: nested }), initialTab: 'prepared', selectionClass: 'proof' }));
    const type = html.split('data-raw-role="sourceType"')[1];
    expect(type).toContain('data-raw-constructor="fvar"'); expect(type).not.toContain('data-raw-fold');
    expect(termPosition(html)).not.toContain('data-raw-constructor');
  });
  it('points to the recorded expected type when it is not the inferred type shown', () => {
    const truth = ['const', ['str', ['anonymous'], 'True'], []] as never;
    const differs = termPosition(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ expected: () => truth }), initialTab: 'prepared', selectionClass: 'proof' })));
    // The warning stays in view as one line under the verdict; it is not behind the disclosure.
    expect(leafParts(differs).shown).toContain(`Lean’s elaborator.</p><p data-proof-expected="differs">${proofWording.expected}</p>`);
    expect(leafParts(differs).checked).not.toContain('data-proof-expected');
    expect(differs.indexOf('data-proof-statement')).toBeLessThan(differs.indexOf('data-proof-expected'));
    const same = termPosition(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ expected: (_h: unknown, P: unknown) => P as never }), initialTab: 'prepared', selectionClass: 'proof' })));
    expect(same).not.toContain('data-proof-expected');
    // An expectation that still holds a metavariable is not called a different expression: nothing in view, and one
    // line behind the disclosure says it was not compared.
    const metavariable = ['mvar', ['num', ['str', ['anonymous'], '_uniq'], ['nat', '19']]] as never;
    const unresolved = leafParts(termPosition(renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ expected: () => metavariable }), initialTab: 'prepared', selectionClass: 'proof' }))));
    expect(unresolved.shown).not.toContain('data-proof-expected');
    expect(unresolved.checked).toContain(`<p data-proof-expected="unresolved">${proofWording.expectedUnresolved}</p>`);
  });
  it('gives the main panel the same verdict and expected-type lines as the leaf', () => {
    const truth = ['const', ['str', ['anonymous'], 'True'], []] as never;
    const differs = rootProofFold({ snapshot: proofSnapshot({ expected: () => truth }), selectionClass: 'proof' })!, same = rootProofFold({ snapshot: proofSnapshot(), selectionClass: 'proof' })!;
    expect(renderToStaticMarkup(createElement(ProofVerdict, { fold: differs }))).toBe(`<p data-proof-verdict="elaborator">${proofWording.verdict(differs)}</p><p data-proof-expected="differs">${proofWording.expected}</p>`);
    expect(renderToStaticMarkup(createElement(ProofVerdict, { fold: same }))).toBe(`<p data-proof-verdict="elaborator">${proofWording.verdict(same)}</p>`);
    expect(renderToStaticMarkup(createElement(ProofLeaf, { fold: differs }))).toContain(renderToStaticMarkup(createElement(ProofVerdict, { fold: differs })));
    // The main panel draws these lines through the same component, so it cannot lose the warning by itself.
    expect(readFileSync(new URL('../App.tsx', import.meta.url), 'utf8')).toContain("selectionKind==='proof-type'&&<ProofVerdict fold={proofFold}/>");
  });
  it('does not point to a closed leaf when neither frame of the selected proof was recorded', () => {
    // A proof over the raw limits: both frames are unavailable, so no tab draws the term or its leaf.
    const snapshot = proofSnapshot({ unprepared: true });
    const fold = rootProofFold({ snapshot, selectionClass: 'proof', printedStatement: 'p ∧ q' })!;
    for (const initialTab of ['original', 'prepared'] as const) {
      const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab, selectionClass: 'proof', printedStatement: 'p ∧ q' }));
      expect(html).not.toContain('data-proof-leaf');
      expect(html).toContain(`data-proof-frames="unrecorded" data-proof-closed="elaborator">${proofWording.unrecordedSelection(fold, 'raw JSON depth limit exceeded')}</p>`);
      expect(html).not.toContain('closed at Source Term');
    }
    // The line names the tabs a reader sees, not internal frames, and ends as a sentence.
    expect(proofWording.unrecordedSelection(fold, 'raw JSON depth limit exceeded')).toBe('Selected term reported as a proof of p ∧ q, not drawn. Neither Original data nor Checker input could record it, so no view below shows it. Recorded reason: raw JSON depth limit exceeded.');
    expect(proofWording.unrecordedSelection(fold, 'The term is too deep.')).toMatch(/Recorded reason: The term is too deep\.$/);
    // Where a frame is drawn, the line still names the leaf it closes.
    const recorded = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot(), initialTab: 'prepared', selectionClass: 'proof' }));
    expect(recorded).toContain('data-proof-frames="recorded"'); expect(recorded).toContain('closed at Source Term');
  });
  it('says in view that a statement is not written on one line, in the statement’s place', () => {
    const fold = rootProofFold({ snapshot: proofSnapshot({ unprepared: true }), selectionClass: 'proof' })!;
    expect(fold.statement).toEqual({ source: 'record' });
    const leaf = renderToStaticMarkup(createElement(ProofLeaf, { fold }));
    expect(leaf).toContain('<code class="proof-leaf-statement" data-proof-statement="record">⋯</code><p data-proof-statement-note="">Statement: the recorded inferred type of the term. It is not written on one line here and stays in the record.</p>'
      + '<p data-proof-verdict="elaborator">Typing: no kernel verdict is recorded. Axioms: not recorded. Statement is a proposition: reported by Lean’s elaborator.</p><details data-proof-checked=""><summary>What was checked · term not drawn</summary>');
    expect(leaf.split(proofWording.statement(fold.statement))).toHaveLength(2);
    // A statement that is written out keeps its source note behind the disclosure.
    expect(renderToStaticMarkup(createElement(ProofLeaf, { fold: rootProofFold({ snapshot: proofSnapshot(), selectionClass: 'proof' })! }))).not.toContain('data-proof-statement-note');
  });
  it('offers the statement check only as a live action and shows Lean’s printed statement when one was reported', () => {
    const snapshot = proofSnapshot({ term: idApplied });
    const saved = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared', selectionClass: 'proof', printedStatement: 'p ∨ ¬p' }));
    expect(saved).toContain('<code class="proof-leaf-statement" data-proof-statement="printed">(⋯ : p ∨ ¬p)</code><p data-proof-verdict="elaborator">Typing: accepted by Lean’s kernel. Axioms: none. Statement is a proposition: reported by Lean’s elaborator.</p>');
    expect(leafParts(termPosition(saved)).checked).toContain('Statement: the inferred type of the term, printed by Lean’s elaborator with local definitions substituted.');
    // A saved record offers no check, so neither the action nor its note is shown.
    expect(saved).not.toContain(proofWording.checkStatement); expect(saved).not.toContain(proofWording.checkStatementNote);
    expect(leafParts(termPosition(saved)).checked).toContain('Axioms recorded for that declaration: none.');
    const unchecked = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ unchecked: 'The prepared context exceeds 128 declarations.' }),
      initialTab: 'prepared', selectionClass: 'proof', onCheckStatement: callback }));
    // Without a receipt the one line says so; the recorded reason is the Typing line behind the disclosure.
    expect(leafParts(termPosition(unchecked)).shown).toContain('<p data-proof-verdict="elaborator">Typing: no kernel verdict is recorded. Axioms: not recorded. Statement is a proposition: reported by Lean’s elaborator.</p>');
    expect(leafParts(termPosition(unchecked)).checked).toContain('<p data-proof-typing="unrecorded">Typing: no kernel verdict is recorded. The prepared context exceeds 128 declarations.</p>');
    expect(termPosition(unchecked)).not.toContain('accepted by Lean’s kernel'); expect(termPosition(unchecked)).not.toContain('data-raw-constructor');
    expect(termPosition(unchecked)).toContain('Statement is a proposition: reported by Lean’s elaborator. No kernel check of this is recorded.');
    // The snapshot's own check could not begin, so no rerun is offered, no acceptance is qualified and Check outcomes is not named as holding the term.
    expect(termPosition(unchecked)).not.toContain(proofWording.checkStatement); expect(termPosition(unchecked)).not.toContain(supplierWording.environment);
    expect(termPosition(unchecked)).toContain('Its exact form stays in the saved snapshot.'); expect(termPosition(unchecked)).not.toContain('under Check outcomes');
    const offered = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared', selectionClass: 'proof', onCheckStatement: callback }));
    expect(leafParts(termPosition(offered)).shown).toContain(`${proofWording.checkStatement}</button>`); expect(termPosition(offered)).toContain('under Check outcomes and in the saved snapshot');
  });
  it('does not offer the statement check again after a whole-term check that returned no checked pair', () => {
    const snapshot = proofSnapshot({ term: idApplied });
    const occurrence = validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1', parentCaptureId: PROOF_CAPTURE, captureId: '990e8400-e29b-41d4-a716-446655440000', path: [],
      policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
      checking: { status: 'unavailable', kind: 'limit', phase: 'occurrence-output', reason: 'Complete record exceeds the output limit.', attempted: true } }, snapshot);
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, origin: { captureId: PROOF_CAPTURE } as SourceSnapshotOrigin, occurrence, selectionClass: 'proof',
      onCheckOccurrence: callback, onCheckStatement: callback, onContinue: callback }));
    expect(html).toContain('Occurrence record unavailable during occurrence-output: Complete record exceeds the output limit.');
    expect(leafParts(termPosition(html)).shown).toContain(`<p data-proof-check="stopped">${proofWording.checkStopped}</p>`);
    expect(html).not.toContain(proofWording.checkStatement); expect(html).not.toContain(proofWording.checkStatementNote); expect(html).not.toContain('Inspect type of original selected term');
    expect(termPosition(html)).toContain('data-proof-leaf="elaborator"'); expect(html).not.toContain('Choose occurrence');
  });
  it('keeps the exact recorded term reachable as data under Check outcomes', () => {
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: proofSnapshot({ term: idApplied }), initialTab: 'checking', selectionClass: 'proof' }));
    expect(html).toContain('2 kernel outcomes retained');
    expect(html.match(/Exact declaration, outcome and resource bound/g)).toHaveLength(2);
    expect(html).toContain('Exact source binding'); expect(html).toContain('Save source snapshot');
  });
  it('leaves a selection that is not a proof exactly as it was, with the stated limit', () => {
    const snapshot = proofSnapshot({ axioms, term: idApplied });
    for (const selectionClass of [undefined, 'proposition', 'other'] as const) {
      const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab: 'prepared', selectionClass, onCheckOccurrence: callback, onCheckStatement: callback }));
      expect(termPosition(html)).toContain('data-raw-constructor="app"'); expect(termPosition(html)).not.toContain('data-raw-closed');
      expect(html.match(/aria-label="Choose occurrence:/g)).toHaveLength(3);
      expect(html).not.toContain('data-proof-leaf'); expect(html).not.toContain(proofWording.checkStatement); expect(html).not.toContain('data-proof-closed');
      // A reported class that is not a proof carries the limit on proof arguments; a missing class is said to be missing.
      expect(html.includes(`<p class="snapshot-context" data-proof-arguments-open="">${proofWording.openArguments}</p>`)).toBe(selectionClass !== undefined);
      expect(html.includes(`<p class="snapshot-context" data-selection-class="unreported">${proofWording.unreported(false)}</p>`)).toBe(selectionClass === undefined);
    }
  });
  it('says so when a live capture arrives without Lean’s class, where a proof would be drawn as ordinary structure', () => {
    const snapshot = proofSnapshot({ axioms, term: idApplied }), origin = { captureId: PROOF_CAPTURE } as SourceSnapshotOrigin;
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, origin, initialTab: 'prepared', onCheckOccurrence: callback, onCheckStatement: callback }));
    expect(html).toContain(`<p class="snapshot-context" data-selection-class="unreported">${proofWording.unreported(true)}</p>`);
    expect(proofWording.unreported(true)).toContain('the term may be a proof'); expect(proofWording.unreported(true)).toContain('install the matching extension');
    // The warning is a line of the drawer itself: no leaf is shown, so no disclosure can hold it.
    expect(html).not.toContain('data-proof-checked'); expect(html).not.toContain('data-proof-leaf');
    expect(html).not.toContain(proofWording.openArguments); expect(termPosition(html)).toContain('data-raw-constructor="app"');
    const reported = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, origin, initialTab: 'prepared', selectionClass: 'other', onCheckOccurrence: callback }));
    expect(reported).not.toContain('data-selection-class'); expect(reported).toContain(proofWording.openArguments);
  });
  it('reads the checked whole term through its statement and offers only the type inspection', () => {
    const snapshot = proofSnapshot({ axioms, term: idApplied }), occurrence = proofOccurrence(snapshot);
    const origin = { captureId: PROOF_CAPTURE } as SourceSnapshotOrigin;
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, origin, occurrence, selectionClass: 'proof',
      onCheckOccurrence: callback, onCheckStatement: callback, onExposeDefinitionHead: callback, onContinue: callback }));
    expect(html).toContain('Chosen occurrence checks'); expect(html).toContain('6 kernel outcomes retained');
    // The type is read first. On the elaborator's report the two targets keep their neutral titles.
    expect(html).toContain('aria-selected="false">Selected term</button>'); expect(html).toContain('aria-selected="true">Inferred type</button>');
    expect(html).toContain('aria-label="Inferred type reading"'); expect(html).toContain('data-occurrence-target="type"');
    expect(html).not.toContain('Selected proof'); expect(html).not.toContain('>Statement</button>');
    expect(html).toContain('Continue from the inferred type of the selected term.'); expect(html).toContain('The term is part of that comparison and is not drawn in either view.');
    expect(html).not.toContain('data-occurrence-target="term"');
    expect(html).toContain('Expose definition head of type'); expect(html).not.toContain('Expose definition head of term');
    expect(html).toContain('Inspect type of original selected term');
    for (const absent of ['Read logical structure of original selected term', 'Inspect fields of original occurrence', 'Check whole selected term', 'Choose occurrence', proofWording.checkStatement])
      expect(html, absent).not.toContain(absent);
    expect(html).toContain('Exact selected term');
    // Without the report the same record keeps every existing control.
    const open = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, origin, occurrence, onCheckOccurrence: callback, onExposeDefinitionHead: callback, onContinue: callback }));
    for (const present of ['aria-selected="true">Selected term</button>', 'data-occurrence-target="term"', 'Expose definition head of term', 'Read logical structure of original selected term',
      'Inspect fields of original occurrence', 'Check whole selected term', 'Choose occurrence', proofWording.unreported(true)]) expect(open, present).toContain(present);
    expect(open).not.toContain('is not drawn in either view');
  });
  it('closes the term root of the structure view and keeps its context and statement drawn', () => {
    const snapshot = proofSnapshot({ axioms, term: idApplied }), value = proofOccurrence(snapshot);
    const proof = rootProofFold({ snapshot, selectionClass: 'proof' })!;
    const section = (html: string, root: 'term' | 'type') => html.split(`data-structure-root="${root}"`)[1].split('</section>')[0];
    const closed = renderToStaticMarkup(createElement(SourceOccurrenceReading, { value, proof, initialView: 'structure' }));
    expect(section(closed, 'term')).toContain('data-root-closed="true"'); expect(section(closed, 'term')).toContain('data-proof-leaf="elaborator"');
    expect(section(closed, 'term')).not.toContain('data-node-id'); expect(section(closed, 'term')).toContain('<h4>Selected term</h4>');
    expect(section(closed, 'type')).toContain('data-constructor="bvar"'); expect(section(closed, 'type')).toContain('<h4>Inferred type</h4>');
    expect(closed.match(/data-context-declaration=/g)).toHaveLength(2);
    expect(closed).toContain('3 of 6 constructor nodes shown');
    expect(closed).toContain('Constructor roles in the type root and the shared context. The term root is not drawn.');
    expect(closed).toContain('The term is part of that comparison and is not drawn in either view.');
    // Only the kernel basis titles the two roots as a proof term and its statement.
    const established = renderToStaticMarkup(createElement(SourceOccurrenceReading, { value, initialView: 'structure',
      proof: { ...proof, basis: 'kernel', established: { attempt: 1, typingOutcome: 6, formationOutcomes: [8] } } }));
    expect(section(established, 'term')).toContain('<h4>Selected proof term</h4>'); expect(section(established, 'term')).toContain('<summary>What was checked · 4 constructor nodes not drawn</summary><p>Proof term, not drawn.</p>');
    expect(section(established, 'term')).toContain('<p data-proof-verdict="kernel">Typing: accepted by Lean’s kernel. Axioms: Classical.choice, propext, Quot.sound. Statement is a proposition: accepted by Lean’s kernel.</p>');
    expect(section(established, 'type')).toContain('<h4>Statement</h4>');
    const open = renderToStaticMarkup(createElement(SourceOccurrenceReading, { value, initialView: 'structure' }));
    expect(section(open, 'term')).toContain('data-constructor="app"'); expect(section(open, 'term')).not.toContain('data-root-closed');
    expect(open).toContain('6 of 6 constructor nodes shown'); expect(open).not.toContain('data-proof-leaf');
    expect(open).toContain('Constructor roles in the selected term, its inferred type, and their shared context.'); expect(open).not.toContain('is not drawn');
  });
});

const acceptanceCorpus = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
describe.skipIf(!acceptanceCorpus)('actual selections after a type-component step on the whole term', () => {
  const rows = acceptanceCorpus ? JSON.parse(readFileSync(acceptanceCorpus, 'utf8')) as { label: string; parent: Record<string, any>; priorAttempts: unknown[]; response: Record<string, any> }[] : [];
  /** The last row of a case through the host path, so the retained history is the one the reader receives. */
  function reading(label: string, reported: boolean) {
    const row = rows.filter(candidate => candidate.label === label).at(-1);
    if (!row) throw Error(`no acceptance rows for ${label}`);
    const recorded = row.parent.origin, document = { ...recorded.document, fileName: new URL(recorded.document.uri).pathname, selection: recorded.selection };
    const parsed = parseEditorMessage({ type: 'statementlens.error', requestId: '1', document, message: 'Independent guided export unavailable.',
      ...(reported ? { selectionClass: row.response.selectionClass } : {}),
      sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: recorded, sourceOccurrence: row.parent.occurrence,
      decompositions: [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }] });
    if (!parsed || parsed.type === 'statementlens.status' || !parsed.sourceSnapshot) throw Error(`host path rejected ${label}`);
    const callback = () => undefined;
    return { selectionClass: parsed.selectionClass, html: renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: parsed.sourceSnapshot, origin: parsed.sourceSnapshotOrigin,
      selectionClass: parsed.selectionClass, occurrence: parsed.sourceOccurrence, decompositions: parsed.decompositions,
      onCheckOccurrence: callback, onCheckStatement: callback, onExposeDefinitionHead: callback, onContinue: callback })) };
  }
  const termPosition = (html: string) => html.split('data-raw-role="sourceTerm"')[1].split('data-raw-role="sourceType"')[0];
  it('closes a whole selected proof on the kernel basis, with or without the elaborator’s report', () => {
    for (const reported of [true, false]) {
      const { selectionClass, html } = reading('term using a lemma proved with a placeholder', reported), term = termPosition(html);
      expect(selectionClass).toBe(reported ? 'proof' : undefined);
      expect(term).toContain('data-proof-leaf="kernel"'); expect(term).toContain('<p>Proof term, not drawn.</p>'); expect(term).not.toContain('data-raw-constructor');
      // The placeholder axiom is listed with the qualifier on what kernel acceptance means; the leaf never says the statement holds.
      expect(term).toContain('Typing: accepted by Lean’s kernel.'); expect(term).toContain(`Axioms recorded for that declaration: sorryAx. ${supplierWording.environment}`);
      expect(term).toContain('Statement is a proposition: accepted by Lean’s kernel. Attempt 1 records that check');
      expect(html).toContain('aria-selected="false">Selected proof term</button>');
      expect(term).not.toContain(proofWording.checkStatement);
      expect(html).toContain('aria-selected="true">Statement</button>'); expect(html).toContain('Inspect type of original selected term');
      for (const absent of ['Read logical structure of original selected term', 'Inspect fields of original occurrence', 'Check whole selected term', 'Choose occurrence', proofWording.openArguments])
        expect(html, absent).not.toContain(absent);
      // The statement reached by the type-component step is read as before, with its own continuation actions.
      expect(html).toContain('Step 2 · Read logical structure'); expect(html).toContain('Read logical structure of this term (one layer)');
      expect(html).toContain('is read as supplying a proof of');
    }
  });
  it('leaves an ordinary value open when the kernel established its type as a type', () => {
    for (const label of ['imported function applied', 'variable named like the auxiliary entry']) {
      const { selectionClass, html } = reading(label, true);
      expect(selectionClass, label).toBe('other'); expect(html, label).not.toContain('data-proof-leaf');
      expect(termPosition(html), label).toContain('data-raw-constructor');
      for (const present of ['aria-selected="true">Selected term</button>', 'Read logical structure of original selected term', 'Inspect fields of original occurrence', 'Check whole selected term', proofWording.openArguments])
        expect(html, `${label}: ${present}`).toContain(present);
    }
  });
});

const occurrenceCorpus = process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_CAPTURES;
describe.skipIf(!occurrenceCorpus)('actual occurrence result presentation', () => {
  it('shows all retained outcomes, including failed roots and accepted children', () => {
    const cases = JSON.parse(readFileSync(occurrenceCorpus!, 'utf8')) as { label: string; response: Record<string, unknown> }[];
    let mixed = false;
    for (const item of cases) {
      const snapshot = validateSourceSnapshot(item.response.sourceSnapshot);
      const occurrence = validateSourceOccurrence(item.response.sourceOccurrence, snapshot);
      const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, occurrence }));
      expect(html, item.label).toContain('Chosen occurrence checks');
      if (occurrence.checking.status === 'captured') {
        const outcomes = occurrence.checking.checks.map(check => check.outcome.tag);
        expect(html).toContain(`${outcomes.length} kernel outcomes retained`);
        const structure = sourceOccurrenceDrawing(occurrence);
        if (occurrence.checking.selected) {
          expect(structure?.ok, item.label).toBe(true);
          expect(html, item.label).toContain('reconstructs the exact selected term');
          if (structure?.ok) {
            expect(readPositionalStructuralDrawing(structure.value)).toEqual({ ok: true, value: occurrence.checking.selected });
            expect(structure.value.sourceIdentity).toContain(occurrence.captureId);
          }
          expect(sourceOccurrenceDrawing(occurrence, { maxNodes: 1 })).toMatchObject({ ok: false, error: { code: 'limit' } });
        } else {
          expect(structure).toBeUndefined();
          expect(html).not.toContain('reconstructs the exact selected term');
        }
        if (outcomes.includes('rejected') && outcomes.at(-1) === 'accepted') {
          mixed = true; expect(html).toContain('rejected'); expect(html).toContain('Selected component');
          expect(html).toContain('reconstructs the exact selected term');
        }
      } else {
        expect(sourceOccurrenceDrawing(occurrence)).toBeUndefined();
        expect(html).not.toContain('reconstructs the exact selected term');
      }
    }
    expect(mixed).toBe(true);
  });
});

const corpus = process.env.DEFINOGRAPH_SOURCE_SNAPSHOT_CAPTURES;
describe.skipIf(!corpus)('actual native source snapshot interface', () => {
  const cases = corpus ? JSON.parse(readFileSync(corpus, 'utf8')) as { label: string; response: Record<string, unknown> }[] : [];
  it('renders every available original/prepared frame and separate actual check outcome', () => {
    expect(cases.length).toBeGreaterThan(5);
    let captured = 0, unsupported = 0;
    for (const item of cases) {
      if (!item.response.sourceSnapshot) continue;
      const snapshot = validateSourceSnapshot(item.response.sourceSnapshot);
      for (const initialTab of ['original', 'prepared', 'expectedType', 'checking'] as const) {
        const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, initialTab }));
        expect(html, item.label).toContain('Selected source data');
        expect(html, item.label).not.toContain('data-reference-target');
        if (initialTab !== 'checking' && snapshot[initialTab].status === 'available') expect(html, item.label).toContain('Exact constructor readback checked');
        if (initialTab === 'checking' && snapshot.checking.status === 'captured') {
          captured++;
          expect(html, item.label).toContain(`${snapshot.checking.checks.length} kernel outcomes retained`);
          expect(html, item.label).toContain('do not certify this visualization');
        }
      }
      if (snapshot.checking.status === 'unavailable') unsupported++;
    }
    expect(captured).toBeGreaterThan(0); expect(unsupported).toBeGreaterThan(0);
  });
});
