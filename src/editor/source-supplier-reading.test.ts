import { readFileSync as readCorpusFile } from 'node:fs';
import type { SourceSnapshotOrigin as CorpusOrigin } from './source-origin';
import type { SourceOccurrence as CorpusOccurrence } from './source-occurrence';
import type { HeadExposureBundle as CorpusSeed } from './source-history';
import { validateDecompositionHistory as corpusValidateHistory, validateSourceDecomposition as corpusValidateRecord,
  type DecompositionOperation as CorpusOperation, type SourceDecompositionBundle as CorpusBundle } from './source-decomposition';
import { supplierReading as corpusSupplierReading } from './source-supplier';
import { occurrenceProvenance as corpusProvenance } from './source-provenance';
import { ProvenancePanel as CorpusProvenancePanel } from './SourceProvenanceReading';
import { savedSourceSnapshot as corpusSave } from './SourceSnapshotReading';
import { SourceDecompositionReading } from './SourceDecompositionReading';
import { initial as seededHistory } from './source-decomposition-chain.test-fixtures';

/** Constructed presentation controls inject independent readings without deriving
 * expected results from source terms or kernel receipts. */
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { JsonValue } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { nameText } from '../packets/syntax';
import type { DecompositionHistory } from './source-decomposition';
import type { SourceSnapshot } from './source-snapshot';
import type { EvidenceStatus, EnteredBinder, OccurrenceProvenance, ProvenanceOccurrence } from './source-provenance';
import type { FormationJudgement, FormationReceipt, HomeEntry, LinkStatus, Part, SupplierReading, TypeOfLink, TypingReceipt } from './source-supplier';
import { provenanceWording } from './SourceProvenanceReading';
import { SupplierPanel, deriveSupplier, joinPartsToLinks, supplierWording } from './SourceSupplierReading';
import { recordedName } from '../packets/recorded-name';

const CAPTURE = '770e8400-e29b-41d4-a716-000000000002';
const ORIGINAL = '770e8400-e29b-41d4-a716-000000000001';
const PARENT = '770e8400-e29b-41d4-a716-000000000000';
const S = 'is read as supplying a proof of';
const F1 = 'Kernel acceptance is a typing outcome in the captured environment, not a statement that the proposition is true.';
const F2 = 'Whether the term uses each listed entry is not read here.';
const F3 = 'The statement is the type inferred for this term at the captured universe levels, not read from a source ascription or an enclosing application.';
const END = 'Nothing is read about supply.';
const FORBIDDEN = /witness|there exists|there is |holds|\bverified\b|checked now|not a proposition|\binvalid\b|proves|supplier|\bvalid\b|\bfalse\b|\bfailed\b|\btrue\b|refuted|∀|∃|confirmed|unproved|checked proof|supplying the statement|no proof|\binstance\b|specialized|holds for|user name/i;
const OUTCOMES = ['accepted', 'rejected', 'unknown'] as const;
const named = (...components: (string | number)[]): JsonValue => components.reduce<JsonValue>((parent, part) =>
  typeof part === 'number' ? ['num', parent, ['nat', String(part)]] : ['str', parent, part], ['anonymous']);
const constant = (identifier: string): JsonValue => ['const', named(identifier), []];
const SORT_ZERO: JsonValue = ['sort', ['zero']];
const SORT_ONE: JsonValue = ['sort', ['succ', ['zero']]];
const SORT_GENERAL: JsonValue = ['sort', ['param', named('u')]];
const clone = <T>(value: T): T => JSON.parse(JSON.stringify(value)) as T;
function frozen<T>(value: T): T {
  if (value !== null && typeof value === 'object') {
    for (const child of Object.values(value)) frozen(child);
    Object.freeze(value);
  }
  return value;
}
const unavailable = { status: 'unavailable' as const, kind: 'prerequisite' as const, phase: 'constructed-render-control', reason: 'Raw checking is outside this injection control.' };
const snapshot: SourceSnapshot = {
  schema: 'definograph.source-snapshot.v1',
  selection: { startByte: 0, endByte: 1, requestedStartByte: 0, requestedEndByte: 1, parentDeclaration: null },
  policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
  expectedType: { status: 'absent' }, original: unavailable, prepared: unavailable, checking: { ...unavailable, attempted: false },
};
const HISTORY: DecompositionHistory = frozen({
  snapshot,
  occurrence: { schema: 'definograph.source-occurrence.v1', parentCaptureId: PARENT, captureId: ORIGINAL, path: [],
    policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
    checking: { ...unavailable, attempted: false } },
  seed: null,
  attempts: [{ snapshot, record: { schema: 'definograph.source-decomposition.v3', parentCaptureId: ORIGINAL, previousCaptureId: ORIGINAL, parentStepIndex: 0,
    captureId: CAPTURE, path: [], operations: [{ kind: 'typeComponent' }],
    policy: { id: 'bounded-decomposition-v3', operation: 'editor-decomposition-v3', preparation: 'Lean.instantiateMVars', universeSubstitution: 'structural',
      reduction: 'original-lambda-spine', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1', maxOperations: 8, maxChecks: 30, maxFields: 16, logicalInterpretation: 'lean-standard-core-v1' },
    checking: { ...unavailable, attempted: false } } }],
});

/** Tiny SSR fragment extractor, balanced on tag names; it does not flatten a
 * nested home/receipt li into its enclosing link li. No browser DOM is assumed. */
interface Element { tag: string; attributes: Record<string, string>; html: string }
function elements(html: string, attribute: string, value?: string): Element[] {
  const result: Element[] = [], stack: { tag: string; attributes: Record<string, string>; start: number; selected: boolean }[] = [];
  const voidTags = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr']);
  for (const match of html.matchAll(/<\/?([a-z][\w:-]*)\b[^>]*>/gi)) {
    const token = match[0], tag = match[1].toLowerCase(), at = match.index!;
    if (token.startsWith('</')) {
      const item = stack.pop();
      if (!item || item.tag !== tag) throw Error(`Unbalanced SSR fragment at ${token}`);
      if (item.selected) result.push({ tag, attributes: item.attributes, html: html.slice(item.start, at + token.length) });
    } else {
      const attributes: Record<string, string> = {};
      for (const attr of token.matchAll(/([\w:-]+)="([^"]*)"/g)) attributes[attr[1]] = attr[2];
      const item = { tag, attributes, start: at, selected: Object.hasOwn(attributes, attribute) && (value === undefined || attributes[attribute] === value) };
      if (voidTags.has(tag) || token.endsWith('/>')) { if (item.selected) result.push({ tag, attributes, html: token }); }
      else stack.push(item);
    }
  }
  return result;
}
const unescape = (html: string): string => html.replace(/&quot;/g, '"').replace(/&#x27;|&#39;/g, "'").replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
const text = (html: string): string => unescape(html.replace(/<[^>]+>/g, ' ')).replace(/\s+/g, ' ').trim();
const wording = (html: string): string => text(html.replace(/<code\b[^>]*>[\s\S]*?<\/code>/g, ' § '));
const phraseCount = (html: string, phrase = S): number => text(html).split(phrase).length - 1;
const render = (value: SupplierReading, currentOrigin = true): string => renderToStaticMarkup(createElement(SupplierPanel,
  { history: HISTORY, derived: { value: frozen(value) }, currentOrigin }));
function one(html: string, attribute: string, value?: string): Element {
  const found = elements(html, attribute, value);
  expect(found, `${attribute}=${value ?? '*'}`).toHaveLength(1);
  return found[0];
}
const linkElement = (html: string, edge: number): Element => one(html, 'data-supplier-link', String(edge));
const stateOf = (html: string): string => one(html, 'data-supplier-state').attributes['data-supplier-state'];
const references = (value: string): string[] => value ? value.split(',') : [];
function acceptedFormationReferences(link: TypeOfLink): string[] {
  // Rendering selection, not a formation rule: the injected module supplies the
  // established flag and each receipt outcome. No inferred type is inspected.
  return link.formation.judgements.filter(group => group.established).flatMap(group =>
    group.receipts.filter(receipt => receipt.outcome === 'accepted').map(receipt => `${receipt.captureId}#${receipt.index}`));
}
function visibleOwnVocabulary(html: string) {
  const prose = wording(html).replaceAll(F1, '').replaceAll(F2, '').replaceAll(F3, '');
  expect(prose).not.toMatch(FORBIDDEN);
  expect(prose.replaceAll(S, '')).not.toContain('a proof of');
  expect(prose).not.toMatch(/\bused\b|\bunused\b/);
}

const emptyPair = (): PositionalStructuralInput => ({ home: { arity: 0, telescope: ['nil'] }, term: constant('p'), type: constant('P') });
function occurrence(index: number, formation: EvidenceStatus = { status: 'unestablished' }): ProvenanceOccurrence {
  return { index, origin: index === 0 ? { kind: 'original', captureId: ORIGINAL } : { kind: 'step', captureId: CAPTURE, stepIndex: index - 1 },
    pair: emptyPair(), receipts: { captureId: CAPTURE, start: index === 0 ? 0 : 6 + 10 * (index - 1), count: index === 0 ? 6 : 2 },
    formation, domain: { status: 'unestablished' }, formations: [], inspections: [], catalogues: [] };
}
function provenance(count: number): OccurrenceProvenance {
  return { original: { captureId: ORIGINAL, path: [] }, prefix: { previousCaptureId: CAPTURE, parentStepIndex: Math.max(0, count - 2), route: 'attempt' },
    occurrences: Array.from({ length: count }, (_, index) => occurrence(index)),
    edges: Array.from({ length: count - 1 }, (_, index) => ({ from: index, to: index + 1, origin: { kind: 'step', captureId: CAPTURE, stepIndex: index },
      receipts: { captureId: CAPTURE, start: 6 + 10 * index, count: 2 }, relation: { kind: 'type-of' } })), excluded: null };
}
function typing(index: number, outcome: TypingReceipt['outcome'] = 'accepted', alsoFormation = false): TypingReceipt {
  return { captureId: CAPTURE, index, outcome, audit: { tag: 'available', axioms: [] }, alsoFormation };
}
function formationReceipt(index: number, outcome: FormationReceipt['outcome'], source: FormationReceipt['source'], entry: number): FormationReceipt {
  return { entry, source, captureId: CAPTURE, index, span: { captureId: CAPTURE, start: index - 1, count: 2 }, outcome, alsoTyping: source === 'typeComponent' };
}
type Cell = 'unestablished' | 'conflicting' | 'proposition' | 'type' | 'general-sort' | 'term';
const CELLS: Cell[] = ['unestablished', 'conflicting', 'proposition', 'type', 'general-sort', 'term'];
const KIND_TYPES = { proposition: SORT_ZERO, type: SORT_ONE, 'general-sort': SORT_GENERAL, term: constant('Nat') };
/** Explicit table of the accepted module's supplied statuses; the fixture does
 * not derive a status from syntax, receipt comparison, or provenance. */
const CELL_STATUS: Record<TypingReceipt['outcome'], Record<Cell, LinkStatus>> = {
  accepted: { unestablished: 'not-established', conflicting: 'conflicting', proposition: 'supplier', type: 'value-of-type', 'general-sort': 'not-established', term: 'not-established' },
  rejected: { unestablished: 'annotation-only', conflicting: 'annotation-only', proposition: 'annotation-only', type: 'annotation-only', 'general-sort': 'annotation-only', term: 'annotation-only' },
  unknown: { unestablished: 'annotation-only', conflicting: 'annotation-only', proposition: 'annotation-only', type: 'annotation-only', 'general-sort': 'annotation-only', term: 'annotation-only' },
};
function cellFixture(outcome: TypingReceipt['outcome'], cell: Cell): SupplierReading {
  const p = provenance(2), sourceTyping = typing(5, outcome), ownTyping = typing(7, cell === 'unestablished' ? 'unknown' : 'accepted', true);
  const evidence: EvidenceStatus = cell === 'unestablished' || cell === 'conflicting' ? { status: cell }
    : { status: 'established', kind: cell, inferredType: clone(KIND_TYPES[cell]) };
  const firstType = cell === 'unestablished' || cell === 'conflicting' ? SORT_ZERO : KIND_TYPES[cell];
  const judgements: FormationJudgement[] = [{ inferredType: clone(firstType), established: evidence.status === 'established',
    receipts: [formationReceipt(7, ownTyping.outcome, 'typeComponent', 0)] }];
  if (cell === 'conflicting') judgements.push({ inferredType: clone(SORT_ONE), established: false, receipts: [formationReceipt(9, 'accepted', 'logical', 1)] });
  p.occurrences[1].formation = evidence;
  p.occurrences[1].pair.term = clone(p.occurrences[0].pair.type);
  p.occurrences[1].pair.type = clone(firstType);
  p.occurrences[1].formations = judgements.flatMap(group => group.receipts.map(receipt => ({ source: receipt.source,
    kind: cell === 'unestablished' ? 'unestablished' : cell === 'conflicting' ? receipt.entry === 0 ? 'proposition' : 'type' : cell,
    inferredType: group.inferredType, outcome: receipt.outcome, origin: { kind: 'step', captureId: CAPTURE, stepIndex: receipt.entry }, receipts: receipt.span })));
  const link: TypeOfLink = { edge: 0, from: 0, to: 1, status: CELL_STATUS[outcome][cell], typing: sourceTyping,
    formation: { status: evidence.status, kind: evidence.status === 'established' ? evidence.kind : null, judgements },
    conditions: { home: [], binders: [], frames: [] } };
  return { provenance: p, occurrences: [{ index: 0, typing: sourceTyping, lineage: [] }, { index: 1, typing: ownTyping, lineage: [{ kind: 'type-of', edge: 0 }] }], links: [link], parts: [] };
}

describe('RC2b constructed supply-panel controls', () => {
  it('keeps the approved supply phrase frozen and uses the RC1 authority line', () => {
    expect(Object.isFrozen(supplierWording)).toBe(true);
    expect(supplierWording.supplyPhrase).toBe(S);
    const value = cellFixture('accepted', 'proposition');
    for (const currentOrigin of [true, false]) {
      const html = render(value, currentOrigin);
      expect(text(html)).toContain(provenanceWording.authorityTitle(currentOrigin));
      expect(elements(html, 'data-supplier-state')).toHaveLength(1);
      expect(html).not.toMatch(/<button\b|<input\b/);
    }
  });

  it('B1/B2/B6: renders all 18 outcome × formation cells without reclassifying the injected reading', () => {
    let cells = 0, supplied = 0;
    const neutralNotEstablished = new Map<Cell, string>();
    for (const outcome of OUTCOMES) for (const cell of CELLS) {
      const value = cellFixture(outcome, cell), html = render(value), block = linkElement(html, 0), visible = text(block.html), status = CELL_STATUS[outcome][cell];
      cells++;
      expect(block.attributes['data-supplier-status']).toBe(status);
      expect(phraseCount(html)).toBe(status === 'supplier' ? 1 : 0);
      expect(phraseCount(html, F1)).toBe(1);
      expect(visible).toContain(provenanceWording.statusTitle(value.provenance.occurrences[1].formation));
      expect(one(block.html, 'data-typing-capture').attributes).toMatchObject({ 'data-typing-capture': CAPTURE, 'data-typing-index': '5', 'data-typing-outcome': outcome });
      if (status === 'supplier') {
        supplied++;
        expect(stateOf(html)).toBe('reading');
        // All zero counts stay in the same visible link block as the claim.
        expect(visible).toMatch(/0 entries/); expect(visible).toMatch(/0 frames/);
        expect(visible).toContain(`${S} the statement at occurrence 2`);
        expect(visible).toContain(F2); expect(visible).toContain(F3);
        expect(one(block.html, 'data-supplier-axioms', 'available').html).toContain('none recorded');
        // Exact-data disclosures are allowed. The supply sentence itself must
        // remain outside them, along with its visible condition counts.
        const openText = text(block.html.replace(/<details\b[^>]*>[\s\S]*?<\/details>/g, ''));
        expect(openText).toContain(S); expect(openText).toMatch(/0 entries/); expect(openText).toMatch(/0 frames/);
      } else {
        expect(stateOf(html)).toBe('no-supply');
        const sentence = text(one(block.html, 'data-supplier-sentence').html);
        expect(sentence).toContain(provenanceWording.statusTitle(value.provenance.occurrences[1].formation));
        expect(sentence).toContain(outcome); expect(sentence).toContain(END);
        expect(visible).toContain(END);
        expect(visible).not.toContain('a proof of');
        if (status === 'annotation-only') expect(visible).toContain(outcome);
        if (outcome === 'accepted' && status === 'not-established') neutralNotEstablished.set(cell, sentence);
      }
      const targetIsProposition = cell === 'proposition';
      if (!targetIsProposition) expect(wording(block.html).replaceAll(F1, '').replaceAll(F3, '')).not.toMatch(/\bstatement\b/i);
      visibleOwnVocabulary(html);
    }
    expect(cells).toBe(18); expect(supplied).toBe(1);
    // In particular, an established general sort and an ordinary term must not
    // silently collapse into the unestablished case's sentence.
    expect(neutralNotEstablished.size).toBe(3);
    expect(new Set(neutralNotEstablished.values()).size).toBe(3);
    expect(neutralNotEstablished.get('general-sort')).toContain('established as a sort of general level');
    expect(neutralNotEstablished.get('term')).toContain('established as an ordinary term');
  });

  it('B3/A3: rests only on accepted receipts of the established judgement, retaining each other outcome separately', () => {
    const value = cellFixture('accepted', 'proposition'), link = value.links[0];
    // Rejected own type-component receipt, accepted logical receipt of the same
    // judgement, plus another rejected receipt and another non-established group.
    value.occurrences[1].typing.outcome = 'rejected';
    link.formation.judgements = [
      { inferredType: clone(SORT_ZERO), established: true, receipts: [formationReceipt(7, 'rejected', 'typeComponent', 0), formationReceipt(9, 'accepted', 'logical', 1), formationReceipt(11, 'unknown', 'logical', 2), formationReceipt(13, 'accepted', 'logical', 3)] },
      { inferredType: clone(SORT_ONE), established: false, receipts: [formationReceipt(15, 'rejected', 'logical', 4)] },
    ];
    const html = render(value), block = linkElement(html, 0);
    expect(references(block.attributes['data-supplier-rests-on'])).toEqual([`${CAPTURE}#9`, `${CAPTURE}#13`]);
    expect(references(block.attributes['data-supplier-rests-on'])).toEqual(acceptedFormationReferences(link));
    expect(phraseCount(html)).toBe(1);
    const groups = elements(block.html, 'data-judgement');
    expect(groups.map(group => [group.attributes['data-judgement'], group.attributes['data-established']])).toEqual([['0', 'true'], ['1', 'false']]);
    expect(elements(groups[0].html, 'data-formation-capture').map(row => [row.attributes['data-formation-index'], row.attributes['data-formation-outcome'], row.attributes['data-formation-also-typing']]))
      .toEqual([['7', 'rejected', 'true'], ['9', 'accepted', 'false'], ['11', 'unknown', 'false'], ['13', 'accepted', 'false']]);
    expect(elements(groups[1].html, 'data-formation-capture').map(row => [row.attributes['data-formation-index'], row.attributes['data-formation-outcome']])).toEqual([['15', 'rejected']]);
    expect(wording(groups[0].html)).toMatch(/one checked judgement/);
    expect(wording(groups[1].html)).not.toMatch(/independent confirmation/);
    expect(wording(block.html)).not.toMatch(/confirmed|agreed|overridden/i);
    const conflict = cellFixture('accepted', 'conflicting'), conflictBlock = linkElement(render(conflict), 0);
    expect(references(conflictBlock.attributes['data-supplier-rests-on'])).toEqual([]);
    expect(phraseCount(conflictBlock.html)).toBe(0);
    expect(wording(conflictBlock.html)).toContain(END);
  });

  it('B4: the displayed axiom line follows only the accepted typing declaration audit and never gates the phrase', () => {
    const original = cellFixture('accepted', 'proposition'), changed = clone(original);
    changed.links[0].typing.audit = { tag: 'available', axioms: [named('sorryAx'), named('Classical', 'choice')] };
    const before = render(original), after = render(changed);
    const oldLine = one(before, 'data-supplier-axioms'), newLine = one(after, 'data-supplier-axioms');
    expect(text(oldLine.html)).toContain('none recorded');
    expect([...newLine.html.matchAll(/<code\b[^>]*>([\s\S]*?)<\/code>/g)].map(match => text(match[1]))).toEqual(['sorryAx', 'Classical.choice']);
    expect(newLine.html).not.toMatch(/<details\b|\bhidden(?:=|\s|>)/);
    expect(phraseCount(before)).toBe(1); expect(phraseCount(after)).toBe(1);
    expect(after.replace(newLine.html, '[AXIOMS]')).toBe(before.replace(oldLine.html, '[AXIOMS]'));
    const unavailableAudit = clone(original);
    unavailableAudit.links[0].typing.audit = { tag: 'unavailable', reason: 'Recorded audit unavailable in this constructed control.' };
    const absent = render(unavailableAudit);
    expect(one(absent, 'data-supplier-axioms', 'unavailable').html).toContain('Recorded audit unavailable in this constructed control.');
    expect(phraseCount(absent)).toBe(1);
    expect(absent.replace(one(absent, 'data-supplier-axioms').html, '[AXIOMS]')).toBe(before.replace(oldLine.html, '[AXIOMS]'));
    for (const html of [before, after, absent]) {
      const sentence = one(html, 'data-supplier-sentence'), axioms = one(html, 'data-supplier-axioms');
      expect(text(sentence.html)).toBe('Relative to the captured environment, including its axioms, and the 0 entries and 0 frames listed, occurrence 1 is read as supplying a proof of the statement at occurrence 2.');
      expect(linkElement(html, 0).html).toContain(sentence.html + axioms.html);
    }
  });

  it('B2-8: writes 0, 1 and 2 entries, binders and frames with the noun in the right number', () => {
    const cases: [number, number, number, string, string][] = [
      [0, 0, 0, 'the 0 entries and 0 frames listed', 'Conditions: 0 ordered entries, 0 entered binders and 0 frames.'],
      [1, 1, 1, 'the 1 entry and 1 frame listed', 'Conditions: 1 ordered entry, 1 entered binder and 1 frame.'],
      [2, 2, 2, 'the 2 entries and 2 frames listed', 'Conditions: 2 ordered entries, 2 entered binders and 2 frames.'],
      // The recorded tutorial histories: claimed (one entry, no frame) and system.returns (three entries, one frame).
      [1, 0, 0, 'the 1 entry and 0 frames listed', 'Conditions: 1 ordered entry, 0 entered binders and 0 frames.'],
      [3, 0, 1, 'the 3 entries and 1 frame listed', 'Conditions: 3 ordered entries, 0 entered binders and 1 frame.'],
    ];
    for (const [entries, binders, frames, listed, conditions] of cases) {
      const value = cellFixture('accepted', 'proposition');
      value.links[0].conditions = {
        home: Array.from({ length: entries }, (_, position): HomeEntry => ({ position, kind: 'port', name: named(`x${position}`), origin: { kind: 'selection' } })),
        binders: Array.from({ length: binders }, (_, position): EnteredBinder => ({ position, step: 'piBody', name: named(`b${position}`), kind: 'port', role: null })),
        frames: Array.from({ length: frames }, (_, edge) => ({ kind: 'type-of' as const, edge })),
      };
      const block = linkElement(render(value), 0);
      expect(text(one(block.html, 'data-supplier-sentence').html)).toBe(`Relative to the captured environment, including its axioms, and ${listed}, occurrence 1 is read as supplying a proof of the statement at occurrence 2.`);
      expect(text(one(block.html, 'data-supplier-conditions').html)).toContain(conditions);
    }
  });

  it('keeps local definitions visible without presenting the internal port tag as a context role', () => {
    const value = cellFixture('accepted', 'proposition');
    value.links[0].conditions.home = [
      { position: 0, kind: 'port', name: named('port'), origin: { kind: 'context', declaration: 0, declarationKind: 'default' } },
      { position: 1, kind: 'let', name: named('local'), origin: { kind: 'selection' } },
    ];
    const html = render(value), home = one(html, 'data-supplier-home');
    const ordinary = one(home.html, 'data-home-position', '0'), definition = one(home.html, 'data-home-position', '1');
    expect(ordinary.attributes['data-home-kind']).toBe('port');
    expect(ordinary.html).toContain('<code>port</code>');
    expect(wording(ordinary.html)).not.toMatch(/\bport\b|local definition|hypothesis|parameter/);
    expect(definition.attributes['data-home-kind']).toBe('let');
    expect(wording(definition.html)).toContain('local definition');
    expect(wording(definition.html)).not.toMatch(/\bport\b|hypothesis|parameter/);
  });

  it('reads a let entry of a recorded nondefault kind by that kind and keeps its local definition note', () => {
    const value = cellFixture('accepted', 'proposition');
    value.links[0].conditions.home = [
      { position: 0, kind: 'let', name: named('helper'), origin: { kind: 'context', declaration: 0, declarationKind: 'auxDecl' } },
      { position: 1, kind: 'let', name: named('detail'), origin: { kind: 'context', declaration: 1, declarationKind: 'implDetail' } },
      { position: 2, kind: 'let', name: named('local'), origin: { kind: 'context', declaration: 2, declarationKind: 'default' } },
      { position: 3, kind: 'let', name: named('entered'), origin: { kind: 'selection' } },
    ];
    const home = one(render(value), 'data-supplier-home'), row = (position: number) => wording(one(home.html, 'data-home-position', String(position)).html);
    expect(row(0)).toContain('Auxiliary entry, recorded kind auxDecl · local definition');
    expect(row(1)).toContain('Context entry, recorded kind implDetail · local definition');
    expect(row(2)).toContain('Context entry, recorded kind default · local definition');
    expect(row(3)).toContain('Entry entered by the original selection · local definition');
    for (const position of [0, 1, 2, 3]) expect(row(position)).not.toMatch(/parameter|hypothesis|assumption/);
  });

  it('identifies linked occurrences by first appearance even when occurrence, step and fresh receipt records differ', () => {
    const value = twoHomeFixture();
    value.provenance.occurrences[2].origin = { kind: 'step', captureId: CAPTURE, stepIndex: 3 };
    value.provenance.occurrences[3].origin = { kind: 'step', captureId: CAPTURE, stepIndex: 4 };
    value.provenance.edges[1].relation = { kind: 'projection-of', index: 2, field: named('law') };
    value.links[1].typing.captureId = ORIGINAL;
    const html = render(value), block = linkElement(html, 2);
    const from = one(block.html, 'data-supplier-occurrence-reference', '2');
    const to = one(block.html, 'data-supplier-occurrence-reference', '3');
    expect(text(from.html)).toBe('Occurrence 3 · First appeared in attempt 1 (770e8400), step 4 · Relation 2 from occurrence 2 · Projected field 3 · law');
    expect(from.html).toContain('<code>law</code>');
    expect(wording(from.html)).not.toContain('law');
    expect(text(to.html)).toBe('Occurrence 4 · First appeared in attempt 1 (770e8400), step 5 · Relation 3 from occurrence 3 · Type of the previous occurrence');
    const original = one(linkElement(html, 0).html, 'data-supplier-occurrence-reference', '0');
    expect(text(original.html)).toBe('Occurrence 1 · First appeared in the original selected occurrence (770e8400)');
  });

  it('F3: keeps the first exposure origin distinct from its replay step and type-of target', () => {
    // Start with the accepted constructed seed provenance, then inject one
    // type-of edge for this presentation control; no expression is interpreted.
    const base = seededHistory(), seed = base.seed.captureId;
    const history: DecompositionHistory = { ...base.history, attempts: HISTORY.attempts };
    const value = cellFixture('accepted', 'proposition'), p = clone(corpusProvenance(base.history, seed, 0));
    const target = value.provenance.occurrences[1];
    target.index = 2; target.origin = { kind: 'step', captureId: CAPTURE, stepIndex: 1 };
    target.pair = { home: p.occurrences[1].pair.home, term: p.occurrences[1].pair.type, type: clone(SORT_ZERO) };
    p.prefix = { previousCaptureId: CAPTURE, parentStepIndex: 1, route: 'attempt' };
    p.occurrences.push(target);
    p.edges.push({ from: 1, to: 2, origin: target.origin, receipts: target.receipts, relation: { kind: 'type-of' } });
    value.provenance = p;
    value.links[0] = { ...value.links[0], edge: 1, from: 1, to: 2 };
    const before = JSON.stringify(value);
    const html = renderToStaticMarkup(createElement(SupplierPanel, { history, derived: { value: frozen(value) }, currentOrigin: true }));
    const expected = [
      [1, `Occurrence 2 · First appeared in the first exposure (${seed.slice(0, 8)}) · Relation 1 from occurrence 1 · Definition-head conversion of term · ForeignWrapper`],
      [2, 'Occurrence 3 · First appeared in attempt 1 (770e8400), step 2 · Relation 2 from occurrence 2 · Type of the previous occurrence'],
    ] as const;
    for (const [index, label] of expected) expect(text(one(html, 'data-supplier-occurrence-reference', String(index)).html)).toBe(label);
    expect(one(html, 'data-supplier-occurrence-reference', '1').html).toContain('<code>ForeignWrapper</code>');
    expect(JSON.stringify(value)).toBe(before);
  });

  it.each(['standalone', 'absent', 'refused'] as const)('F3: keeps endpoint identification as plain text with %s provenance', state => {
    const value = frozen(cellFixture('accepted', 'proposition'));
    const provenancePanel = state === 'standalone' ? null : createElement(CorpusProvenancePanel,
      state === 'absent' ? { currentOrigin: true } : { history: HISTORY, derived: { refusal: 'Selected prefix unavailable.' }, currentOrigin: true });
    const html = renderToStaticMarkup(createElement('div', {}, provenancePanel,
      createElement(SupplierPanel, { history: HISTORY, derived: { value }, currentOrigin: true })));
    const refs = elements(html, 'data-supplier-occurrence-reference');
    expect(refs.map(ref => text(ref.html))).toEqual([
      'Occurrence 1 · First appeared in the original selected occurrence (770e8400)',
      'Occurrence 2 · First appeared in attempt 1 (770e8400), step 1 · Relation 1 from occurrence 1 · Type of the previous occurrence',
    ]);
    expect(refs.every(ref => !/<a\b|href=/.test(ref.html))).toBe(true);
    expect(elements(html, 'data-provenance-occurrence')).toHaveLength(0);
    if (state !== 'standalone') expect(html).toContain(`data-provenance-${state}`);
  });

  it('scopes passive occurrence references to the matching panel instance and preserves saved-origin wording', () => {
    const value = frozen(cellFixture('accepted', 'proposition'));
    const html = renderToStaticMarkup(createElement('div', {}, ...['panel-one', 'panel-two'].flatMap(occurrenceAnchorPrefix => [
      createElement(CorpusProvenancePanel, { history: HISTORY, derived: { value: value.provenance }, currentOrigin: false, occurrenceAnchorPrefix }),
      createElement(SupplierPanel, { history: HISTORY, derived: { value }, currentOrigin: false, occurrenceAnchorPrefix }),
    ])));
    const ids = elements(html, 'data-provenance-occurrence').map(entry => entry.attributes.id);
    expect(ids).toEqual(['panel-one', 'panel-two'].flatMap(prefix => [`${prefix}-original-${ORIGINAL}-occurrence-0`, `${prefix}-step-${CAPTURE}-0-occurrence-1`]));
    const targets = elements(html, 'href').map(link => link.attributes.href.slice(1));
    expect(targets).toEqual(ids);
    expect(new Set(ids).size).toBe(ids.length);
    expect(elements(html, 'data-provenance-occurrence').every(entry => entry.attributes.tabindex === '-1')).toBe(true);
    expect(text(html)).toContain('saved history whose origin is unconfirmed');
    expect(html).not.toContain('class="head-exposure-action"');
  });

  it('B10: distinguishes no history, refusal, no type-of step, and links with no supply reading', () => {
    const absent = renderToStaticMarkup(createElement(SupplierPanel, { currentOrigin: true }));
    const refused = renderToStaticMarkup(createElement(SupplierPanel, { history: HISTORY, currentOrigin: true, derived: { refusal: 'The selected prefix is unavailable.' } }));
    const noLink = cellFixture('accepted', 'proposition');
    noLink.links = []; noLink.occurrences = noLink.occurrences.slice(0, 1); noLink.provenance.occurrences = noLink.provenance.occurrences.slice(0, 1); noLink.provenance.edges = [];
    noLink.provenance.prefix = { previousCaptureId: ORIGINAL, parentStepIndex: 0, route: 'original' };
    const noTypeOf = render(noLink), noSupply = render(cellFixture('rejected', 'proposition'));
    expect([absent, refused, noTypeOf, noSupply].map(stateOf)).toEqual(['no-history', 'refused', 'no-type-of', 'no-supply']);
    expect(text(refused)).toContain('The selected prefix is unavailable.');
    expect(text(noTypeOf)).toContain('This prefix contains no type-of step, so no supply reading is made.');
    for (const html of [absent, refused, noTypeOf, noSupply]) { expect(phraseCount(html)).toBe(0); expect(wording(html)).not.toMatch(/a proof of|no proof|supplier/i); }
    expect(deriveSupplier(undefined, ORIGINAL, 0)).toBeUndefined();
  });

  it('B7: classifies names structurally, independently of printed substrings', () => {
    const cases: [JsonValue, boolean][] = [
      [named('x'), false], [named('a', '_@', '_internal', '_hyg', 0), true], [named('a', '_@', 'M', '_hyg', 3, 5), true],
      [['anonymous'], true], [named('a', '_hyg', 'b'), false], [named('x_hyg'), false], [named('n', 0), false],
    ];
    for (const [value, unnamed] of cases) for (const noun of ['binder', 'context entry'] as const) {
      expect(recordedName(value, noun)).toBe(unnamed ? `unnamed ${noun}` : nameText(value));
    }
  });

  it('B8/B11: preserves each link’s ordered home, kinds, positions, and entered binders without a shared chain-end scope', () => {
    const value = twoHomeFixture(), html = render(value);
    for (const link of value.links) {
      const block = linkElement(html, link.edge), home = one(block.html, 'data-supplier-home');
      expect(elements(home.html, 'data-home-position').map(row => ({ position: Number(row.attributes['data-home-position']), kind: row.attributes['data-home-kind'], origin: row.attributes['data-home-origin'],
        ...(row.attributes['data-home-declaration'] === undefined ? {} : { declaration: Number(row.attributes['data-home-declaration']), declarationKind: row.attributes['data-home-declaration-kind'] }),
        ...(row.attributes['data-home-edge'] === undefined ? {} : { edge: Number(row.attributes['data-home-edge']), binder: Number(row.attributes['data-home-binder']), role: row.attributes['data-home-role'] }) })))
        .toEqual(link.conditions.home.map(entry => ({ position: entry.position, kind: entry.kind, origin: entry.origin.kind,
          ...(entry.origin.kind === 'context' ? { declaration: entry.origin.declaration, declarationKind: entry.origin.declarationKind ?? '' } : {}),
          ...(entry.origin.kind === 'entered' ? { edge: entry.origin.edge, binder: entry.origin.binder, role: entry.origin.role ?? 'none' } : {}) })));
      expect(wording(home.html)).not.toMatch(/assumption|hypothesis|assuming|used|unused/i);
      expect(text(home.html)).toMatch(/auxiliary entry.*recorded kind auxDecl/i);
      // Duplicate recorded identifiers remain unchanged; position/kind identifies
      // entries. In particular the default-kind identifier gains no suffix.
      const ordinary = one(home.html, 'data-home-position', '1');
      expect(ordinary.html).toContain('<code>same</code>');
      expect(ordinary.html).not.toMatch(/same[✝₀-₉]|same[._-]\d/);
      expect(home.html).not.toMatch(/<details\b|\bhidden(?:=|\s|>)/);
    }
    expect(elements(one(linkElement(html, 0).html, 'data-supplier-home').html, 'data-home-position')).toHaveLength(2);
    expect(elements(one(linkElement(html, 2).html, 'data-supplier-home').html, 'data-home-position')).toHaveLength(3);
    expect(text(linkElement(html, 0).html)).not.toContain('unnamed binder');
    expect(text(linkElement(html, 2).html)).toContain('unnamed binder');
    visibleOwnVocabulary(html);
  });

  it('B5/B10/D13: parts follow their root link, all four tiers remain visible, and no part row carries a typing verdict', () => {
    const value = fourTierFixture(), html = render(value), before = JSON.stringify(value);
    const joined = joinPartsToLinks(frozen(value));
    expect(joined).toHaveLength(value.parts.length);
    for (let index = 0; index < value.parts.length; index++) {
      expect(joined[index].part).toBe(value.parts[index]);
      const expected = value.links.find(link => link.to === value.parts[index].root) ?? null;
      expect(joined[index].link).toBe(expected);
      const row = one(html, 'data-supplier-part', String(value.parts[index].occurrence));
      expect(row.attributes['data-part-tier']).toBe(value.parts[index].tier);
      expect(wording(row.html)).not.toMatch(/accepted|rejected|unknown|a proof of|no proof|instance|specialized|holds for/i);
      if (value.parts[index].tier !== 'within-supplied-law') expect(wording(row.html)).not.toMatch(/\blaw\b/i);
    }
    expect(elements(html, 'data-supplier-part')).toHaveLength(4);
    expect(new Set(value.parts.map(part => part.tier)).size).toBe(4);
    expect(text(one(html, 'data-supplier-part', '1').html)).toContain('This prefix relates no term to that statement by a type-of step, so nothing is read about supply.');
    expect(text(one(html, 'data-supplier-part', '5').html)).toContain('Nothing is read about this part by itself.');
    expect(JSON.stringify(value)).toBe(before);
    const changed = clone(value);
    changed.links[0].status = 'annotation-only'; changed.links[0].typing.outcome = 'rejected';
    changed.parts.find(part => part.root === 4)!.tier = 'within-annotation'; changed.parts.find(part => part.root === 4)!.supplier = null;
    const after = render(changed);
    expect(phraseCount(html)).toBe(1); expect(phraseCount(after)).toBe(0);
    expect(one(after, 'data-supplier-part', '5').attributes['data-part-tier']).toBe('within-annotation');
    expect(text(linkElement(after, 3).html)).toContain(END);
  });

  it('B14: renders frozen injected values deterministically and changes neither their data nor label context', () => {
    const value = frozen(twoHomeFixture()), bytes = JSON.stringify(value), historyBytes = JSON.stringify(HISTORY);
    const first = render(value), second = render(value);
    expect(first).toBe(second); expect(JSON.stringify(value)).toBe(bytes); expect(JSON.stringify(HISTORY)).toBe(historyBytes);
  });
});

function twoHomeFixture(): SupplierReading {
  const value = cellFixture('accepted', 'proposition'), p = provenance(4), first = value.links[0];
  const base: HomeEntry[] = [
    { position: 0, kind: 'port', name: named('same'), origin: { kind: 'context', declaration: 0, declarationKind: 'auxDecl' } },
    { position: 1, kind: 'port', name: named('same'), origin: { kind: 'context', declaration: 1, declarationKind: 'default' } },
  ];
  const binder: EnteredBinder = { position: 0, step: 'piBody', name: ['anonymous'], kind: 'port', role: 'universal' };
  const frame = { kind: 'containment' as const, edge: 1, path: ['piBody' as const], role: null, binders: [binder] };
  first.conditions.home = clone(base);
  const second: TypeOfLink = clone(first);
  second.edge = 2; second.from = 2; second.to = 3; second.typing = typing(17);
  second.formation.judgements[0].receipts = [formationReceipt(27, 'accepted', 'typeComponent', 0)];
  second.conditions = { home: [...clone(base), { position: 2, kind: 'port', name: ['anonymous'], origin: { kind: 'entered', edge: 1, binder: 0, role: 'universal' } }],
    binders: [binder], frames: [{ kind: 'type-of', edge: 0 }, frame] };
  p.edges[1].relation = { kind: 'containment', path: ['piBody'], binders: [binder], role: null };
  p.occurrences[1].formation = { status: 'established', kind: 'proposition', inferredType: clone(SORT_ZERO) };
  p.occurrences[3].formation = { status: 'established', kind: 'proposition', inferredType: clone(SORT_ZERO) };
  value.provenance = p; value.links = [first, second];
  value.occurrences = [
    { index: 0, typing: first.typing, lineage: [] }, { index: 1, typing: typing(7, 'accepted', true), lineage: [{ kind: 'type-of', edge: 0 }] },
    { index: 2, typing: second.typing, lineage: second.conditions.frames }, { index: 3, typing: typing(27, 'accepted', true), lineage: [...second.conditions.frames, { kind: 'type-of', edge: 2 }] },
  ];
  return value;
}

function fourTierFixture(): SupplierReading {
  const p = provenance(8), value = cellFixture('accepted', 'proposition'), supplied = value.links[0], annotation = cellFixture('unknown', 'unestablished').links[0];
  p.occurrences[0].formation = { status: 'established', kind: 'proposition', inferredType: clone(SORT_ZERO) };
  p.occurrences[4].formation = { status: 'established', kind: 'proposition', inferredType: clone(SORT_ZERO) };
  for (const index of [0, 2, 4, 6]) p.edges[index].relation = { kind: 'containment', path: ['appArg'], binders: [], role: null };
  p.edges[1].relation = { kind: 'projection-of', index: 0, field: named('field') };
  supplied.edge = 3; supplied.from = 3; supplied.to = 4; supplied.typing = typing(27);
  supplied.formation.judgements[0].receipts = [formationReceipt(37, 'accepted', 'typeComponent', 0)];
  annotation.edge = 5; annotation.from = 5; annotation.to = 6; annotation.typing = typing(47, 'unknown');
  annotation.formation.judgements[0].receipts = [formationReceipt(57, 'unknown', 'typeComponent', 0)];
  const parts: Part[] = [
    { occurrence: 1, root: 0, supplier: null, tier: 'within-statement', path: ['appArg'], frames: [{ kind: 'containment', edge: 0, path: ['appArg'], role: null, binders: [] }] },
    { occurrence: 3, root: 2, supplier: null, tier: 'within-expression', path: ['appArg'], frames: [{ kind: 'containment', edge: 2, path: ['appArg'], role: null, binders: [] }] },
    { occurrence: 5, root: 4, supplier: 3, tier: 'within-supplied-law', path: ['appArg'], frames: [{ kind: 'containment', edge: 4, path: ['appArg'], role: null, binders: [] }] },
    { occurrence: 7, root: 6, supplier: null, tier: 'within-annotation', path: ['appArg'], frames: [{ kind: 'containment', edge: 6, path: ['appArg'], role: null, binders: [] }] },
  ];
  value.provenance = p; value.links = [supplied, annotation]; value.parts = parts;
  value.occurrences = p.occurrences.map(item => ({ index: item.index, typing: item.index === 3 ? supplied.typing : item.index === 5 ? annotation.typing : typing(item.index === 0 ? 5 : 7 + 10 * (item.index - 1), 'accepted', item.index === 4 || item.index === 6), lineage: [] }));
  return value;
}

interface CorpusRow {
  label: string;
  parent: { snapshot: SourceSnapshot; origin: CorpusOrigin; occurrence: CorpusOccurrence };
  seed: CorpusSeed | null;
  priorAttempts: CorpusBundle[];
  operation: CorpusOperation;
  previousCaptureId: string;
  parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: CorpusOrigin; sourceDecomposition: CorpusBundle['record'] };
}
function corpusLoad(variable: string): CorpusRow[] {
  const location = process.env[variable];
  return location ? JSON.parse(readCorpusFile(location, 'utf8')) as CorpusRow[] : [];
}
const corpusSets = [
  { name: 'v3 logical corpus', variable: 'DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES', rows: corpusLoad('DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES') },
  { name: 'RC3 acceptance corpus', variable: 'DEFINOGRAPH_ACCEPTANCE_FIXTURES', rows: corpusLoad('DEFINOGRAPH_ACCEPTANCE_FIXTURES') },
];
function corpusHistory(row: CorpusRow) {
  const prior = corpusValidateHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence,
    seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
    attempts: row.priorAttempts.map(bundle => ({ snapshot: bundle.snapshot, record: clone(bundle.record) })) });
  const record = corpusValidateRecord(clone(row.response.sourceDecomposition), row.response.sourceSnapshot, prior);
  const history = corpusValidateHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  return { history, record };
}
/** Every eligible prefix of the row's fresh record, including a candidate before
 * a later refusal. Original and seed routes are also exercised. Prior attempts
 * have their own rows in the corpora and are not silently replaced by chain ends. */
function corpusPrefixes(history: DecompositionHistory, record: CorpusBundle['record']) {
  const result: { previousCaptureId: string; parentStepIndex: number; route: 'original' | 'seed' | 'attempt' }[] = [
    { previousCaptureId: history.occurrence.captureId, parentStepIndex: 0, route: 'original' },
  ];
  if (history.seed) result.push({ previousCaptureId: history.seed.record.captureId, parentStepIndex: 0, route: 'seed' });
  if (record.checking.status !== 'captured') throw Error('The delivered corpus row has no captured step list.');
  for (const step of record.checking.steps) if (step.output.status === 'candidate') {
    result.push({ previousCaptureId: record.captureId, parentStepIndex: step.index, route: 'attempt' });
  }
  return result;
}
function corpusSaveBytes(row: CorpusRow): string {
  const bundles: CorpusBundle[] = [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }];
  return JSON.stringify(corpusSave(row.parent.snapshot, row.parent.origin, row.parent.occurrence, row.seed ?? undefined, undefined, bundles));
}
const corpusPanel = (history: DecompositionHistory, value: SupplierReading, currentOrigin = true): string => renderToStaticMarkup(createElement(SupplierPanel,
  { history, derived: { value }, currentOrigin }));
const corpusCodes = (html: string): string[] => [...html.matchAll(/<code\b[^>]*>([\s\S]*?)<\/code>/g)].map(match => text(match[1]));
function corpusUnfrozen(value: unknown, at = 'reading', seen = new Set<object>()): string[] {
  if (value === null || typeof value !== 'object' || seen.has(value)) return [];
  seen.add(value);
  return [...(Object.isFrozen(value) ? [] : [at]), ...Object.entries(value).flatMap(([key, child]) => corpusUnfrozen(child, `${at}.${key}`, seen))];
}
/** Independent recursive transcription of Name.hasMacroScopes: a terminal str
 * tests its component, a num asks its parent, anonymous has no macro scopes.
 * Top-level anonymous names are separately unnamed by the display contract.
 * This intentionally does not call recordedName or inspect the printed name. */
function corpusHasMacroScopes(value: JsonValue): boolean {
  if (!Array.isArray(value)) throw Error('The corpus supplied a non-structural name.');
  if (value[0] === 'anonymous') return false;
  if (value[0] === 'num') return corpusHasMacroScopes(value[1]);
  if (value[0] === 'str') return value[2] === '_hyg';
  throw Error('The corpus supplied an unsupported Name constructor.');
}
function corpusName(value: JsonValue, noun: 'binder' | 'context entry'): string {
  return Array.isArray(value) && value[0] === 'anonymous' || corpusHasMacroScopes(value) ? `unnamed ${noun}` : nameText(value);
}
function corpusExpectedHome(entry: HomeEntry): Record<string, string> {
  const result: Record<string, string> = { 'data-home-position': String(entry.position), 'data-home-kind': entry.kind, 'data-home-origin': entry.origin.kind };
  if (entry.origin.kind === 'context') Object.assign(result, { 'data-home-declaration': String(entry.origin.declaration), 'data-home-declaration-kind': entry.origin.declarationKind ?? 'none' });
  if (entry.origin.kind === 'entered') Object.assign(result, { 'data-home-edge': String(entry.origin.edge), 'data-home-binder': String(entry.origin.binder), 'data-home-role': entry.origin.role ?? 'none' });
  return result;
}
const corpusData = (attributes: Record<string, string>, prefix: string): Record<string, string> => Object.fromEntries(Object.entries(attributes).filter(([key]) => key.startsWith(prefix)).map(([key, value]) => [key, unescape(value)]));
function corpusExpectFrames(html: string, frames: TypeOfLink['conditions']['frames']) {
  expect(elements(html, 'data-frame-index').map(row => ({ index: Number(row.attributes['data-frame-index']), kind: row.attributes['data-frame-kind'], edge: Number(row.attributes['data-frame-edge']),
    ...(row.attributes['data-frame-path'] === undefined ? {} : { path: JSON.parse(unescape(row.attributes['data-frame-path'])) }) })))
    .toEqual(frames.map((frame, index) => ({ index, kind: frame.kind, edge: frame.edge, ...(frame.kind === 'containment' ? { path: frame.path } : {}) })));
}

interface CorpusCounts { prefixes: number; attemptPrefixes: number; links: number; suppliers: number; groups: number; multiReceiptGroups: number; parts: number;
  unnamedBinders: number; namedBinders: number; provenanceUnnamed: number; provenanceNamed: number; auxiliaryEntries: number; selectionEntries: number; letEntries: number; nonemptyAxiomLists: number; differingHomes: number }
function corpusExpectReading(history: DecompositionHistory, reading: SupplierReading, html: string, counts: CorpusCounts) {
  const p = reading.provenance, section = one(html, 'data-supplier-state');
  expect(section.attributes).toMatchObject({ 'data-supplier-route': p.prefix.route, 'data-supplier-prefix': p.prefix.previousCaptureId, 'data-supplier-step': String(p.prefix.parentStepIndex) });
  const suppliers = reading.links.filter(link => link.status === 'supplier');
  expect(stateOf(html)).toBe(!reading.links.length ? 'no-type-of' : suppliers.length ? 'reading' : 'no-supply');
  expect(phraseCount(html)).toBe(suppliers.length); expect(phraseCount(html, F1)).toBe(1);
  expect(elements(html, 'data-supplier-link').map(row => Number(row.attributes['data-supplier-link']))).toEqual(reading.links.map(link => link.edge));
  const provenanceHtml = renderToStaticMarkup(createElement(CorpusProvenancePanel, { history, derived: { value: p }, currentOrigin: true }));
  expect(phraseCount(provenanceHtml)).toBe(0);
  for (const edge of p.edges) if (edge.relation.kind === 'containment') {
    const block = one(provenanceHtml, 'data-provenance-edge', `${edge.from}-${edge.to}`);
    for (const binder of edge.relation.binders) {
      const row = one(block.html, 'data-binder-position', String(binder.position));
      const expectedName = corpusName(binder.name, 'binder');
      expect(corpusCodes(row.html)).toEqual([expectedName]);
      expect(text(row.html)).toContain(`constructor-path position ${binder.position + 1}`);
      if (expectedName === 'unnamed binder') counts.provenanceUnnamed++; else counts.provenanceNamed++;
    }
  }
  if (reading.links.length > 1 && new Set(reading.links.map(link => JSON.stringify(link.conditions.home))).size > 1) counts.differingHomes++;
  for (const link of reading.links) {
    counts.links++; if (link.status === 'supplier') counts.suppliers++;
    const block = linkElement(html, link.edge), data = block.attributes, conditions = one(block.html, 'data-supplier-conditions');
    expect(data).toMatchObject({ 'data-supplier-status': link.status, 'data-link-from': String(link.from), 'data-link-to': String(link.to),
      'data-typing-capture': link.typing.captureId, 'data-typing-index': String(link.typing.index), 'data-typing-outcome': link.typing.outcome });
    expect(references(data['data-supplier-rests-on'])).toEqual(link.status === 'supplier' ? acceptedFormationReferences(link) : []);
    const sentence = one(block.html, 'data-supplier-sentence');
    expect(phraseCount(sentence.html)).toBe(link.status === 'supplier' ? 1 : 0);
    if (link.status === 'supplier') {
      const entries = link.conditions.home.length, frames = link.conditions.frames.length;
      expect(text(sentence.html)).toContain(`${entries} ${entries === 1 ? 'entry' : 'entries'} and ${frames} ${frames === 1 ? 'frame' : 'frames'}`);
      expect(text(sentence.html)).toContain(`occurrence ${link.from + 1} ${S} the statement at occurrence ${link.to + 1}`);
      expect(text(one(block.html, 'data-supplier-usage').html)).toBe(F2);
      expect(text(one(block.html, 'data-supplier-inferred').html)).toBe(F3);
    } else {
      expect(text(sentence.html)).toContain(provenanceWording.statusTitle(p.occurrences[link.to].formation));
      expect(text(sentence.html)).toContain(link.typing.outcome); expect(text(sentence.html)).toContain(END);
      expect(text(sentence.html)).not.toContain('a proof of');
    }
    expect(conditions.attributes).toMatchObject({ 'data-home-count': String(link.conditions.home.length), 'data-binder-count': String(link.conditions.binders.length), 'data-frame-count': String(link.conditions.frames.length) });
    const home = one(conditions.html, 'data-supplier-home'), entries = elements(home.html, 'data-home-position');
    expect(entries.map(row => corpusData(row.attributes, 'data-home-'))).toEqual(link.conditions.home.map(corpusExpectedHome));
    expect(home.html).not.toMatch(/<details\b|\bhidden(?:=|\s|>)/);
    link.conditions.home.forEach((entry, index) => {
      const row = entries[index];
      expect(corpusCodes(row.html)).toEqual([corpusName(entry.name, 'context entry')]);
      expect(text(row.html)).toContain(`Context position ${entry.position + 1}`);
      expect(wording(row.html)).not.toMatch(/assumption|hypothesis|assuming|\bused\b|\bunused\b/i);
      if (entry.origin.kind === 'context') {
        expect(text(row.html)).toContain(`recorded kind ${entry.origin.declarationKind ?? 'not recorded'}`);
        expect(/auxiliary entry/i.test(wording(row.html))).toBe(entry.origin.declarationKind === 'auxDecl');
        if (entry.origin.declarationKind === 'auxDecl') counts.auxiliaryEntries++;
      } else if (entry.origin.kind === 'selection') counts.selectionEntries++;
      if (entry.kind === 'let') counts.letEntries++;
    });
    const binders = elements(conditions.html, 'data-supplier-binder');
    expect(binders.map(row => ({ index: Number(row.attributes['data-supplier-binder']), position: Number(row.attributes['data-binder-position']), role: row.attributes['data-binder-role'] })))
      .toEqual(link.conditions.binders.map((binder, index) => ({ index, position: binder.position, role: binder.role ?? 'none' })));
    const framedBinders = link.conditions.frames.flatMap(frame => frame.kind === 'containment' ? frame.binders.map(binder => ({ edge: frame.edge, binder })) : []);
    expect(framedBinders.map(item => item.binder)).toEqual(link.conditions.binders);
    link.conditions.binders.forEach((binder, index) => {
      const expectedName = corpusName(binder.name, 'binder'), row = binders[index], frame = framedBinders[index];
      expect(text(row.html)).toContain(`relation ${frame.edge + 1}`);
      expect(corpusCodes(row.html)).toEqual([expectedName]); expect(text(row.html)).toContain(`constructor-path position ${binder.position + 1}`);
      if (expectedName === 'unnamed binder') counts.unnamedBinders++; else counts.namedBinders++;
      const edge = p.edges[frame.edge], other = one(provenanceHtml, 'data-provenance-edge', `${edge.from}-${edge.to}`);
      const otherBinder = one(other.html, 'data-binder-position', String(binder.position));
      expect(corpusCodes(otherBinder.html)).toEqual([expectedName]);
      expect(otherBinder.attributes['data-binder-role']).toBe(binder.role ?? 'none');
      // The permission to say "Assuming" is an entered proof-binder role only.
      expect(/assuming/i.test(wording(row.html))).toBe(binder.role === 'proof');
    });
    corpusExpectFrames(conditions.html, link.conditions.frames);
    const groups = elements(block.html, 'data-judgement');
    expect(groups.map(row => [Number(row.attributes['data-judgement']), row.attributes['data-established']])).toEqual(link.formation.judgements.map((group, index) => [index, String(group.established)]));
    link.formation.judgements.forEach((group, index) => {
      counts.groups++; if (group.receipts.length > 1) counts.multiReceiptGroups++;
      const rows = elements(groups[index].html, 'data-formation-capture');
      expect(rows.map(row => corpusData(row.attributes, 'data-formation-'))).toEqual(group.receipts.map(receipt => ({
        'data-formation-capture': receipt.captureId, 'data-formation-index': String(receipt.index), 'data-formation-outcome': receipt.outcome, 'data-formation-also-typing': String(receipt.alsoTyping),
      })));
      group.receipts.forEach((receipt, receiptIndex) => {
        expect(text(rows[receiptIndex].html)).toContain(`Outcome ${receipt.index + 1} recorded by ${provenanceWording.recordTitle(history, receipt.captureId)}: ${receipt.outcome}`);
        expect(text(rows[receiptIndex].html)).toContain(receipt.source === 'logical' ? 'logical root' : 'type component');
        expect(/one receipt in two roles/.test(text(rows[receiptIndex].html))).toBe(receipt.alsoTyping);
      });
      if (group.receipts.length > 1) expect(text(groups[index].html)).toContain('one checked judgement');
    });
    const axiomLine = one(block.html, 'data-supplier-axioms');
    expect(axiomLine.attributes['data-supplier-axioms']).toBe(link.typing.audit.tag);
    if (link.typing.audit.tag === 'available') {
      expect(corpusCodes(axiomLine.html)).toEqual(link.typing.audit.axioms.map(axiom => nameText(axiom)));
      if (link.typing.audit.axioms.length) counts.nonemptyAxiomLists++; else expect(text(axiomLine.html)).toContain('none recorded');
    } else expect(text(axiomLine.html)).toContain(link.typing.audit.reason);
    expect(axiomLine.html).not.toMatch(/<details\b|\bhidden(?:=|\s|>)/);
  }
  expect(elements(html, 'data-supplier-typing').map(row => ({ occurrence: Number(row.attributes['data-supplier-typing']), capture: row.attributes['data-typing-capture'],
    index: Number(row.attributes['data-typing-index']), outcome: row.attributes['data-typing-outcome'] })))
    .toEqual(reading.occurrences.map(item => ({ occurrence: item.index, capture: item.typing.captureId, index: item.typing.index, outcome: item.typing.outcome })));
  expect(html.includes('No contained positions are recorded in this prefix.')).toBe(reading.parts.length === 0);
  const parts = elements(html, 'data-supplier-part');
  expect(parts.map(row => corpusData(row.attributes, 'data-part-'))).toEqual(reading.parts.map(part => ({
    'data-part-root': String(part.root), 'data-part-tier': part.tier, 'data-part-link': String(reading.links.find(link => link.to === part.root)?.edge ?? 'none'),
    'data-part-supplier': String(part.supplier ?? 'none'), 'data-part-path': JSON.stringify(part.path),
  })));
  expect(parts.map(row => Number(row.attributes['data-supplier-part']))).toEqual(reading.parts.map(part => part.occurrence));
  const joined = joinPartsToLinks(reading);
  expect(joined.map(item => [item.part.occurrence, item.link?.edge ?? null])).toEqual(reading.parts.map(part => [part.occurrence, reading.links.find(link => link.to === part.root)?.edge ?? null]));
  reading.parts.forEach((part, index) => {
    counts.parts++; expect(joined[index].part).toBe(part);
    expect(wording(parts[index].html)).not.toMatch(/accepted|rejected|unknown|a proof of|no proof|instance|specialized|holds for/i);
    if (part.tier !== 'within-supplied-law') expect(wording(parts[index].html)).not.toMatch(/\blaw\b/i);
    expect(phraseCount(parts[index].html)).toBe(0); corpusExpectFrames(parts[index].html, part.frames);
  });
  expect(elements(html, 'data-part-group').map(row => Number(row.attributes['data-part-group']))).toEqual([...new Set(reading.parts.map(part => part.root))]);
  expect(elements(html, 'data-supplier-excluded').map(row => row.attributes['data-supplier-excluded'])).toEqual(p.excluded ? [p.excluded.stepIndices.join(',')] : []);
  visibleOwnVocabulary(html);
}

for (const corpus of corpusSets) describe.skipIf(!corpus.rows.length)(`supply panel on ${corpus.name}`, () => {
  it('B2–B4/B6/B8–B11/B14: every eligible real prefix matches the accepted model without changing saved bytes', () => {
    const counts: CorpusCounts = { prefixes: 0, attemptPrefixes: 0, links: 0, suppliers: 0, groups: 0, multiReceiptGroups: 0, parts: 0,
      unnamedBinders: 0, namedBinders: 0, provenanceUnnamed: 0, provenanceNamed: 0, auxiliaryEntries: 0, selectionEntries: 0, letEntries: 0, nonemptyAxiomLists: 0, differingHomes: 0 };
    for (const row of corpus.rows) {
      const rawBytes = JSON.stringify(row), savedBytes = corpusSaveBytes(row), { history, record } = corpusHistory(row), historyBytes = JSON.stringify(history);
      const prefixes = corpusPrefixes(history, record);
      for (const prefix of prefixes) {
        const label = `${row.label}: ${prefix.previousCaptureId}#${prefix.parentStepIndex}`, value = corpusSupplierReading(history, prefix.previousCaptureId, prefix.parentStepIndex);
        const independentProvenance = corpusProvenance(history, prefix.previousCaptureId, prefix.parentStepIndex), before = JSON.stringify(value);
        expect(value.provenance, label).toEqual(independentProvenance); expect(corpusUnfrozen(value), label).toEqual([]);
        expect(deriveSupplier(history, prefix.previousCaptureId, prefix.parentStepIndex)?.value, label).toEqual(value);
        const html = corpusPanel(history, value), repeat = corpusPanel(history, value);
        expect(repeat, label).toBe(html); expect(JSON.stringify(value), label).toBe(before);
        corpusExpectReading(history, value, html, counts);
        const savedHtml = corpusPanel(history, value, false);
        expect(text(savedHtml), label).toContain(provenanceWording.authorityTitle(false));
        expect(savedHtml.replace(provenanceWording.authorityTitle(false), '[AUTHORITY]'), label).toBe(html.replace(provenanceWording.authorityTitle(true), '[AUTHORITY]'));
        expect(savedHtml, label).not.toMatch(/<button\b|<input\b/);
        counts.prefixes++; if (prefix.route === 'attempt') counts.attemptPrefixes++;
      }
      expect(JSON.stringify(row), row.label).toBe(rawBytes); expect(corpusSaveBytes(row), row.label).toBe(savedBytes); expect(JSON.stringify(history), row.label).toBe(historyBytes);
    }
    expect(counts.prefixes).toBeGreaterThan(corpus.rows.length); expect(counts.attemptPrefixes).toBeGreaterThan(0);
    expect(counts.links).toBeGreaterThan(0); expect(counts.suppliers).toBeGreaterThan(0); expect(counts.parts).toBeGreaterThan(0);
    expect(counts.groups).toBeGreaterThan(0); expect(counts.auxiliaryEntries).toBeGreaterThan(0);
    // Unnamed binders can occur below a type-of link rather than in its conditions.
    expect(counts.namedBinders).toBeGreaterThan(0);
    // The real hygienic entered binder occurs in acceptance's implication-to-True case.
    if (corpus.variable === 'DEFINOGRAPH_ACCEPTANCE_FIXTURES') expect(counts.provenanceUnnamed).toBeGreaterThan(0);
    console.log(`${corpus.name}: ${JSON.stringify(counts)}`);
  }, 480000);
});

describe.skipIf(!corpusSets[0].rows.length)('F3 selected-prefix endpoint controls', () => {
  function negatedOwner() {
    const row = [...corpusSets[0].rows].reverse().find(row => row.label === 'negated owner');
    if (!row) throw Error('Required negated-owner fixture missing');
    const { history, record } = corpusHistory(row);
    if (record.checking.status !== 'captured') throw Error('Required recorded steps missing');
    // Revalidation retains a new object. Use that exact object for the owner guard.
    const retained = history.attempts.at(-1)!.record;
    const bundle: CorpusBundle = { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: retained };
    return { history, record: retained, bundle };
  }

  it('F3: labels replayed projection-to-type endpoints after interposed fields and logical inspections', () => {
    const { history, record } = negatedOwner();
    expect(record.operations.map(operation => operation.kind)).toEqual(['logical', 'focus', 'fields', 'project', 'typeComponent', 'logical', 'focus', 'logical']);
    const value = corpusSupplierReading(history, record.captureId, 7), before = JSON.stringify(value);
    expect(value.provenance.occurrences.map(occurrence => occurrence.origin.kind === 'step' ? occurrence.origin.stepIndex : 'original')).toEqual(['original', 1, 3, 4, 6]);
    expect(value.provenance.edges).toHaveLength(4);
    const html = corpusPanel(history, value), block = linkElement(html, 2);
    const earlierProjection = history.attempts[3].record.captureId, earlierType = history.attempts[4].record.captureId;
    const expected = [
      [2, `Occurrence 3 · First appeared in attempt 4 (${earlierProjection.slice(0, 8)}), step 4 · Relation 2 from occurrence 2 · Projected field 3 · law`],
      [3, `Occurrence 4 · First appeared in attempt 5 (${earlierType.slice(0, 8)}), step 5 · Relation 3 from occurrence 3 · Type of the previous occurrence`],
    ] as const;
    for (const [index, label] of expected) expect(text(one(block.html, 'data-supplier-occurrence-reference', String(index)).html)).toBe(label);
    expect(one(block.html, 'data-supplier-occurrence-reference', '2').html).toContain('<code>law</code>');
    expect(block.attributes).toMatchObject({ 'data-supplier-link': '2', 'data-link-from': '2', 'data-link-to': '3', 'data-supplier-status': 'supplier',
      'data-typing-capture': record.captureId, 'data-typing-index': '11', 'data-typing-outcome': 'accepted' });
    expect(text(block.html)).toContain(`Outcome 12 recorded by attempt 8 (${record.captureId.slice(0, 8)}): accepted · typing of occurrence 3.`);
    expect(JSON.stringify(value)).toBe(before);
  });

  it('F3: gives two mounted continuation readers distinct targets in their own selected prefix', () => {
    const { history, record, bundle } = negatedOwner(), before = JSON.stringify(history);
    let calls = 0;
    const html = renderToStaticMarkup(createElement('div', {}, ...['one', 'two'].map(instance => createElement('div', { key: instance, 'data-clarity-instance': instance },
      createElement(SourceDecompositionReading, { attempts: [bundle], history, currentOrigin: true, onContinue: () => { calls++; } })))));
    const allTargets = elements(html, 'data-provenance-occurrence').map(row => unescape(row.attributes.id));
    expect(allTargets).toHaveLength(10);
    expect(new Set(allTargets).size).toBe(allTargets.length);
    for (const instance of ['one', 'two']) {
      const mounted = one(html, 'data-clarity-instance', instance).html;
      const provenance = one(mounted, 'data-provenance-route'), supply = one(mounted, 'data-supplier-route');
      expect(provenance.attributes).toMatchObject({ 'data-provenance-route': 'attempt', 'data-provenance-prefix': record.captureId, 'data-provenance-step': '7' });
      expect(supply.attributes).toMatchObject({ 'data-supplier-route': 'attempt', 'data-supplier-prefix': record.captureId, 'data-supplier-step': '7' });
      const targets = elements(provenance.html, 'data-provenance-occurrence'), references = elements(supply.html, 'data-supplier-occurrence-reference');
      expect(references).toHaveLength(2);
      for (const reference of references) {
        const anchor = one(reference.html, 'href'), id = unescape(anchor.attributes.href.slice(1));
        const target = targets.filter(row => unescape(row.attributes.id) === id);
        expect(target).toHaveLength(1);
        expect(target[0].attributes['data-provenance-occurrence']).toBe(reference.attributes['data-supplier-occurrence-reference']);
        expect(target[0].attributes.tabindex).toBe('-1');
        expect(id).toContain(`-${record.captureId}-7-`);
        expect(target[0].html).toContain(`<strong>Occurrence ${Number(reference.attributes['data-supplier-occurrence-reference']) + 1}</strong>`);
      }
    }
    expect(calls).toBe(0);
    expect(JSON.stringify(history)).toBe(before);
  });
});

const corpusAcceptance = corpusSets[1].rows;
function corpusEnd(label: string): CorpusRow {
  const row = [...corpusAcceptance].reverse().find(item => item.label === label);
  if (!row) throw Error(`Required RC2b acceptance fixture missing: ${label}`);
  return row;
}
function corpusLastReading(row: CorpusRow) {
  const { history, record } = corpusHistory(row);
  if (record.checking.status !== 'captured') throw Error('Missing captured steps.');
  const last = [...record.checking.steps].reverse().find(step => step.output.status === 'candidate');
  if (!last) throw Error(`No eligible prefix for ${row.label}`);
  return { history, value: corpusSupplierReading(history, record.captureId, last.index) };
}
describe.skipIf(!corpusAcceptance.length)('RC2b required real acceptance examples', () => {
  it('B4/D11: shows sorryAx from a real accepted typing declaration using a lemma proved with a placeholder', () => {
    const { history, value } = corpusLastReading(corpusEnd('term using a lemma proved with a placeholder'));
    const html = corpusPanel(history, value), link = value.links.find(item => item.status === 'supplier');
    expect(link).toBeDefined(); if (!link) throw Error('No supplied link in the required sorried-lemma fixture.');
    expect(link.typing.audit).toMatchObject({ tag: 'available', axioms: [named('sorryAx')] });
    expect(corpusCodes(one(linkElement(html, link.edge).html, 'data-supplier-axioms').html)).toEqual(['sorryAx']);
    expect(phraseCount(linkElement(html, link.edge).html)).toBe(1);
  });

  it('B8/A2: a real ordinary entry sharing the auxiliary name keeps its identifier and position; a kind swap changes labels only', () => {
    const { history, value } = corpusLastReading(corpusEnd('variable named like the auxiliary entry'));
    const link = value.links.find(item => item.conditions.home.some(entry => entry.origin.kind === 'context' && entry.origin.declarationKind === 'auxDecl'));
    expect(link).toBeDefined(); if (!link) throw Error('Missing real auxiliary entry.');
    const context = link.conditions.home.filter(entry => entry.origin.kind === 'context'), auxiliary = context.find(entry => entry.origin.kind === 'context' && entry.origin.declarationKind === 'auxDecl')!;
    const ordinary = context.find(entry => entry.origin.kind === 'context' && entry.origin.declarationKind === 'default' && JSON.stringify(entry.name) === JSON.stringify(auxiliary.name));
    expect(ordinary).toBeDefined(); if (!ordinary) throw Error('Missing same-name ordinary entry.');
    const before = corpusPanel(history, value), home = one(linkElement(before, link.edge).html, 'data-supplier-home');
    const auxRow = one(home.html, 'data-home-position', String(auxiliary.position)), ordinaryRow = one(home.html, 'data-home-position', String(ordinary.position));
    expect(corpusCodes(auxRow.html)).toEqual([nameText(auxiliary.name)]); expect(corpusCodes(ordinaryRow.html)).toEqual([nameText(ordinary.name)]);
    expect(text(auxRow.html)).toMatch(/Auxiliary entry, recorded kind auxDecl/); expect(text(ordinaryRow.html)).toMatch(/Context entry, recorded kind default/);
    const changed = clone(value), changedLink = changed.links.find(item => item.edge === link.edge)!;
    const a = changedLink.conditions.home[auxiliary.position], b = changedLink.conditions.home[ordinary.position];
    if (a.origin.kind !== 'context' || b.origin.kind !== 'context') throw Error('Unexpected context origins.');
    a.origin.declarationKind = 'default'; b.origin.declarationKind = 'auxDecl';
    const after = corpusPanel(history, frozen(changed)), swappedHome = one(linkElement(after, link.edge).html, 'data-supplier-home');
    expect(text(one(swappedHome.html, 'data-home-position', String(auxiliary.position)).html)).toMatch(/Context entry, recorded kind default/);
    expect(text(one(swappedHome.html, 'data-home-position', String(ordinary.position)).html)).toMatch(/Auxiliary entry, recorded kind auxDecl/);
    expect(corpusCodes(swappedHome.html)).toEqual(corpusCodes(home.html)); expect(phraseCount(after)).toBe(phraseCount(before));
    // This is explicitly a renderer injection, not a claim that the altered
    // home is a newly validated native record.
  });

  it('B8: the auxiliary entry inside a named theorem keeps the recorded name helper and its recorded kind', () => {
    const { history, value } = corpusLastReading(corpusEnd('term inside a named theorem')), html = corpusPanel(history, value);
    const link = value.links.find(item => item.conditions.home.some(entry => entry.origin.kind === 'context' && entry.origin.declarationKind === 'auxDecl'))!;
    expect(link).toBeDefined(); const entry = link.conditions.home.find(item => item.origin.kind === 'context' && item.origin.declarationKind === 'auxDecl')!;
    const row = one(one(linkElement(html, link.edge).html, 'data-supplier-home').html, 'data-home-position', String(entry.position));
    expect(corpusCodes(row.html)).toEqual(['helper']); expect(text(row.html)).toContain('Auxiliary entry, recorded kind auxDecl');
  });
});


it('keeps the maintained relation table aligned with the panel vocabulary', () => {
  const source = readCorpusFile(new URL('../../docs/reader-relations.md', import.meta.url), 'utf8');
  const rows = source.split('\n').filter(line => /^\| (Containment|Type-of|Projection|Conversion|Typing|Formation|Supply) \|/.test(line));
  expect(rows.map(line => line.split('|')[1].trim())).toEqual(['Containment', 'Type-of', 'Projection', 'Conversion', 'Typing', 'Formation', 'Supply']);
  const positiveReadings = rows.map(line => line.split('|')[2].trim()).join(' ');
  expect(positiveReadings.split(S)).toHaveLength(2);
  expect(positiveReadings.replace(S, '')).not.toMatch(/a proof of|checked proof|confirmed|unproved|supplying the statement|\bholds\b|\btrue\b|\bvalid\b/i);
  const prose = source.replace(/\s+/g, ' ');
  expect(prose).toContain(F1); expect(prose).toContain(F2);
});
