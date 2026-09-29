import { readFileSync, readdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import type { HeadExposureBundle } from './source-history';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionHistory, type DecompositionOperation,
  type SourceDecompositionBundle } from './source-decomposition';
import { occurrenceProvenance, type ContainmentRole, type EnteredBinder, type EvidenceStatus, type OccurrenceInspection, type OccurrenceProvenance, type ProvenanceRelation, type ReceiptSpan } from './source-provenance';
import type { FormationKind, LogicalForm } from './logical-inspection-reading';
import { parseEditorMessage, retainedDecompositionHistory } from './host';
import { SourceSnapshotReading } from './SourceSnapshotReading';
import { SourceDecompositionReading } from './SourceDecompositionReading';
import { ProvenancePanel, SourceProvenanceReading, deriveProvenance, guidedLogicalRoot, provenanceWording } from './SourceProvenanceReading';
import { savedSourceSnapshot } from './SourceSnapshotReading';
import { decompositionReading, positionalResultPath } from './source-decomposition-reading';
import { a, append, c, clone, errorStop, focus, id, initial, name, o, record, seedCheckpoint } from './source-decomposition-chain.test-fixtures';

const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
const panel = (props: Parameters<typeof SourceProvenanceReading>[0]) => renderToStaticMarkup(createElement(SourceProvenanceReading, props));
/** Attributes of every `<li data-provenance-…>` entry in document order, with the text of its block. */
function entries(html: string) {
  return html.split('<li data-provenance-').slice(1).filter(segment => segment.startsWith('occurrence=') || segment.startsWith('edge=')).map(segment => {
    const end = segment.indexOf('>'), attributes: Record<string, string> = {};
    for (const match of `data-provenance-${segment.slice(0, end)}`.matchAll(/([\w-]+)="([^"]*)"/g)) attributes[match[1]] = match[2];
    return { attributes, block: segment.slice(end + 1) };
  });
}
const binderRoles = (block: string) => [...block.matchAll(/<li data-binder-position="(\d+)" data-binder-role="([^"]*)">/g)].map(match => [Number(match[1]), match[2]] as const);
function expected(provenance: OccurrenceProvenance) {
  const origin = (item: { origin: OccurrenceProvenance['occurrences'][number]['origin']; receipts: OccurrenceProvenance['occurrences'][number]['receipts'] }) => ({
    'data-origin-kind': item.origin.kind, 'data-origin-capture': item.origin.captureId, ...(item.origin.kind === 'step' ? { 'data-origin-step': String(item.origin.stepIndex) } : {}),
    'data-receipt-capture': item.receipts.captureId, 'data-receipt-start': String(item.receipts.start), 'data-receipt-count': String(item.receipts.count) });
  const list: { attributes: Record<string, string>; binders: (readonly [number, string])[] }[] = [];
  for (const occurrence of provenance.occurrences) {
    for (const edge of provenance.edges.filter(edge => edge.to === occurrence.index)) list.push({
      attributes: { 'data-provenance-edge': `${edge.from}-${edge.to}`, 'data-relation-kind': edge.relation.kind, ...origin(edge) },
      binders: edge.relation.kind === 'containment' ? edge.relation.binders.map(binder => [binder.position, binder.role ?? 'none'] as const) : [] });
    list.push({ attributes: { 'data-provenance-occurrence': String(occurrence.index), ...origin(occurrence) }, binders: [] });
  }
  return list;
}
/** The rendered entries must equal the module output field for field; nothing may be derived or dropped in the UI. */
function expectFaithful(html: string, provenance: OccurrenceProvenance) {
  const rendered = entries(html);
  const anchors = rendered.flatMap(entry => entry.attributes.id ? [entry.attributes.id] : []);
  expect(new Set(anchors).size).toBe(anchors.length);
  expect(rendered.map(entry => {
    const { id: anchor, tabindex, ...attributes } = entry.attributes;
    if (anchor) {
      expect(anchor.endsWith(`-occurrence-${attributes['data-provenance-occurrence']}`)).toBe(true);
      expect(tabindex).toBe('-1');
    } else expect(tabindex).toBeUndefined();
    return { attributes, binders: binderRoles(entry.block) };
  })).toEqual(expected(provenance));
  expect(html.includes('data-provenance-excluded=')).toBe(provenance.excluded !== null);
  if (provenance.excluded) expect(html).toContain(`data-provenance-excluded="${provenance.excluded.stepIndices.join(',')}"`);
  expect(html).toContain(`data-provenance-route="${provenance.prefix.route}"`);
  expect(html).toContain(`data-provenance-step="${provenance.prefix.parentStepIndex}"`);
}
const FORBIDDEN = /witness|there exists|there is |holds|\bverified\b|checked now|not a proposition|\binvalid\b|proves|supplier|\bvalid\b/i;
/** The stricter vocabulary of the independent oracle, applied to the panel's own wording with identifiers set apart. */
const STRICT = /witness|there exists|there is |holds|\bverified\b|checked now|not a proposition|\binvalid\b|proves|supplier|\bvalid\b|\bfalse\b|\bfailed\b|\btrue\b|refuted|∀|∃/i;
/** Titles that state a logical reading; none may appear where no logical form is read. */
const READING = /universal|statement|proposition|implication|equality|conjunction|disjunction|equivalence|negat|alternative|existential|For every|For all/i;
const FORMS: LogicalForm[] = ['forall', 'implies', 'eq', 'and', 'or', 'iff', 'not', 'exists', 'true', 'false', 'unexpanded'];
const inspectionOf = (patch: Partial<OccurrenceInspection>): OccurrenceInspection => ({ origin: { kind: 'original', captureId: id(1) }, receipts: { captureId: id(1), start: 8, count: 2 },
  shape: 'standard', formation: 'unestablished', rootOutcome: 'accepted', inferredType: ['sort', ['zero']], domain: null, candidate: 'eq', form: null, proofBinder: false, bodyUsesBinder: null, operands: [], ...patch });
const DOMAIN = { proposition: { formation: 'proposition' as const, inferredType: ['sort', ['zero']] as JsonValue, outcome: 'accepted' as const },
  type: { formation: 'type' as const, inferredType: ['sort', ['succ', ['zero']]] as JsonValue, outcome: 'accepted' as const },
  rejected: { formation: 'unestablished' as const, inferredType: ['sort', ['zero']] as JsonValue, outcome: 'rejected' as const } };
const readForall = (patch: Partial<OccurrenceInspection>) => inspectionOf({ shape: 'forall', candidate: 'forall', form: 'forall', formation: 'proposition', bodyUsesBinder: true, ...patch });
/** Inspections with a form read, each as the accepted module produces it, with the exact title of its line. */
const PROOF_BINDER_ROWS: [OccurrenceInspection, string][] = [
  [readForall({ form: 'implies', domain: DOMAIN.proposition, proofBinder: true, bodyUsesBinder: false }), 'Logical inspection · shape forall · root outcome accepted · implication · binder domain a proposition, outcome accepted · proof binder, read from the occurrence’s formation and binder-domain formation'],
  [readForall({ domain: DOMAIN.proposition, proofBinder: true }), 'Logical inspection · shape forall · root outcome accepted · universal statement · binder domain a proposition, outcome accepted · proof binder, read from the occurrence’s formation and binder-domain formation'],
  // The occurrence's domain evidence comes from another inspection of the same occurrence; this inspection's own domain outcome was rejected.
  [readForall({ domain: DOMAIN.rejected, proofBinder: true }), 'Logical inspection · shape forall · root outcome accepted · universal statement · binder domain not established, outcome rejected · proof binder, read from the occurrence’s formation and binder-domain formation'],
  [readForall({ domain: { ...DOMAIN.rejected, outcome: 'unknown' }, proofBinder: true }), 'Logical inspection · shape forall · root outcome accepted · universal statement · binder domain not established, outcome unknown · proof binder, read from the occurrence’s formation and binder-domain formation'],
  // Accepted domain outcomes of the occurrence disagree, so no proof binder is read although this one is a proposition.
  [readForall({ domain: DOMAIN.proposition, proofBinder: false }), 'Logical inspection · shape forall · root outcome accepted · universal statement · binder domain a proposition, outcome accepted'],
  [readForall({ domain: DOMAIN.type, proofBinder: false }), 'Logical inspection · shape forall · root outcome accepted · universal statement · binder domain a type above Prop, outcome accepted'],
  [readForall({ form: 'implies', rootOutcome: 'rejected', domain: DOMAIN.proposition, proofBinder: true, bodyUsesBinder: false }),
    'Logical inspection · shape forall · root outcome rejected · implication, read from the occurrence formation, not from this root outcome · binder domain a proposition, outcome accepted · proof binder, read from the occurrence’s formation and binder-domain formation'],
];
/** The block of one occurrence, with the exact-pair disclosure cut off. */
const occurrenceBlock = (html: string, index: number) => { const entry = entries(html).find(entry => entry.attributes['data-provenance-occurrence'] === String(index)); if (!entry) throw Error(`missing occurrence ${index}`); return entry.block.split('<details')[0]; };
const introduction = (block: string) => block.match(/<p data-provenance-own-outcomes="">([^<]*)<\/p>/)?.[1];
const panelOf = (html: string) => { const start = html.indexOf('<section class="source-provenance"'); return start < 0 ? '' : html.slice(start, html.indexOf('</section>', start) + 10); };
/** Lean identifiers render as code and are exempt from the vocabulary controls, which govern the panel's own wording. */
const wording = (html: string) => html.replace(/<code>[^<]*<\/code>/g, '<code>§</code>');
/** What a reader sees: text nodes only, identifiers in code set apart. Attribute values are data for comparison, not wording. */
const visible = (html: string) => wording(html).replace(/<[^>]+>/g, ' ');

const document = { uri: 'file:///control.lean', fileName: '/control.lean', version: 3,
  selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } };
const origin = (captureId: string): SourceSnapshotOrigin => ({ kind: 'local-editor-process-snapshot', captureId, sourceSha256: '0'.repeat(64),
  engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
  project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
  document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' });
function argumentFocus(history: DecompositionHistory, attempt: number) {
  const result = seedCheckpoint(history).candidate.result;
  return record(history, { kind: 'focus', path: ['appArg'] }, focus({ home: result.home, term: a(result.term)[2], type: c('Nat') }), { id: attempt });
}
function hostFixture() {
  const base = initial(), history = append(base.history, argumentFocus(base.history, 1));
  const first = history.attempts[0].record;
  const seed: HeadExposureBundle = { snapshot: base.snapshot, origin: origin(base.seed.captureId), record: base.seed };
  const bundle: SourceDecompositionBundle = { snapshot: base.snapshot, origin: origin(first.captureId), record: first };
  const message = { type: 'statementlens.error', requestId: '4', document, message: 'Guided source export unavailable.',
    sourceSnapshot: base.snapshot, sourceSnapshotOrigin: origin(history.occurrence.captureId), sourceOccurrence: history.occurrence, headExposure: seed, decompositions: [bundle] };
  const parsed = parseEditorMessage(message);
  if (!parsed || parsed.type === 'statementlens.status' || !parsed.decompositions || !parsed.sourceOccurrence || !parsed.sourceSnapshotOrigin) throw Error('host fixture');
  return { base, history, first, seed, bundle, message, parsed, live: parsed.decompositions, occurrence: parsed.sourceOccurrence, hostOrigin: parsed.sourceSnapshotOrigin };
}

describe('provenance panel, constructed controls', () => {
  it('shows provenance only for the exact host-validated bundle array and reads it without any host request', () => {
    const f = hostFixture();
    const retained = retainedDecompositionHistory(f.live);
    expect(retained).toBeDefined();
    expect(retained!.attempts[0].record).toBe(f.live[0].record);
    expect(retainedDecompositionHistory([...f.live])).toBeUndefined();
    expect(retainedDecompositionHistory(structuredClone(f.live) as SourceDecompositionBundle[])).toBeUndefined();
    let calls = 0;
    // Window trap: no code path may acquire a host during a static render.
    const trapped = globalThis as { window?: unknown };
    trapped.window = { acquireVsCodeApi: () => { throw new Error('host acquired during static render'); } };
    let html: string;
    try {
      html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: f.parsed.sourceSnapshot!, origin: f.hostOrigin, occurrence: f.occurrence,
        headExposure: f.parsed.headExposure, decompositions: f.live, onContinue: () => { calls++; } }));
    } finally { delete trapped.window; }
    expect(calls).toBe(0);
    // Static no-host assertion: the reader files add no host command; the command union is exactly the known set.
    const editorSources = path.dirname(fileURLToPath(import.meta.url));
    for (const name of ['SourceProvenanceReading.tsx', 'SourceDecompositionReading.tsx']) expect(readFileSync(path.join(editorSources, name), 'utf8')).not.toMatch(/postMessage|acquireVsCodeApi|from '\.\/host'/);
    const commands = [...new Set([...readFileSync(path.join(editorSources, 'host.ts'), 'utf8').matchAll(/'statementlens\.([a-zA-Z]+)'/g)].map(match => match[1]))].sort();
    expect(commands).toEqual(['analysis', 'checkOccurrence', 'error', 'exposeDefinitionHead', 'exposeFocusedHead', 'focusExposedPart', 'inspectFields', 'inspectLogicalStructure', 'inspectTypeComponent', 'projectField', 'ready', 'refresh', 'reveal', 'status']);
    expect(html).toContain('Ordered provenance · through step 2 of this attempt');
    expect(html).toContain('Read from the validated history of this capture.');
    expect(html).toContain('First appeared in the first exposure ('); expect(html).toMatch(/Outcomes 7–9 recorded by attempt 1 \([0-9a-f]{8}\)/);
    expect(html).toMatch(/First appeared in attempt 1 \([0-9a-f]{8}\), step 2/);
    expect(html).toContain(id(1).slice(0, 8));
    expectFaithful(html, occurrenceProvenance(retained!, f.live[0].record.captureId, 1));
    expect(html.match(/data-provenance-route=/g)).toHaveLength(1);
    expect(visible(html)).not.toMatch(FORBIDDEN);
    // Existing occurrence content and exposure actions remain available beside the panels.
    expect(html).toContain('Expose definition head of term'); expect(html).toContain('Step 2 · Check part'); expect(html).toContain('Exact input pair');
  });

  it('marks saved histories as unverified and renders an explicit absence when no validated history is retained', () => {
    const f = hostFixture(), retained = retainedDecompositionHistory(f.live)!;
    const saved = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: f.live, history: retained, currentOrigin: false, onContinue: () => {} }));
    expect(saved).toContain('This saved history has an unverified origin.'); expect(saved).toContain('Outcomes are as recorded and nothing is re-checked here');
    expect(panelOf(saved)).not.toMatch(/fresh|\blive\b|verified|validated/i); expect(panelOf(saved)).not.toContain('<button');
    // The saved record bytes are unaffected by rendering with or without provenance.
    const before = JSON.stringify(savedSourceSnapshot(f.base.snapshot, undefined, f.occurrence, f.seed, undefined, f.live));
    renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: f.base.snapshot, occurrence: f.occurrence, headExposure: f.seed, decompositions: f.live }));
    expect(JSON.stringify(savedSourceSnapshot(f.base.snapshot, undefined, f.occurrence, f.seed, undefined, f.live))).toBe(before);
    const absent = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: f.live, currentOrigin: true, onContinue: () => {} }));
    expect(absent).toContain('data-provenance-absent'); expect(absent).not.toContain('Ordered provenance ·'); expect(absent).not.toContain('data-provenance-occurrence');
    const copied = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: f.base.snapshot, occurrence: f.occurrence, headExposure: f.seed, decompositions: [f.bundle], onContinue: () => {} }));
    expect(copied).toContain('unverified origin'); expect(copied).toContain('data-provenance-absent'); expect(copied).not.toContain('Check chosen part');
  });

  it('shows inherited identity through the actual sibling and fresh outcomes of the selected attempt, with the excluded suffix', () => {
    let history = initial().history;
    history = append(history, argumentFocus(history, 1));
    history = append(history, argumentFocus(history, 2));
    const after = history.attempts[1].record.checking.status === 'captured' && history.attempts[1].record.checking.steps[1].output.status === 'candidate'
      ? history.attempts[1].record.checking.steps[1].output.result : undefined;
    const carrier: JsonValue = ['sort', ['succ', ['zero']]];
    const exposure = { status: 'candidate', before: after!.type, result: { home: after!.home, term: c('Again'), type: carrier },
      definition: { name: name('Nat'), levelParams: [], type: carrier, value: c('Again'), hints: ['abbrev'], safety: 'safe' },
      actualLevels: [], arguments: [], betaApplications: 0, carrierSort: ['succ', ['succ', ['zero']]], checking: { status: 'completed' } };
    history = append(history, record(history, { kind: 'expose', target: 'type' }, exposure, { previous: id(2), index: 1, id: 3 }));
    const full = panel({ history, previousCaptureId: id(3), parentStepIndex: 2, currentOrigin: true });
    expectFaithful(full, occurrenceProvenance(history, id(3), 2));
    const third = entries(full).find(entry => entry.attributes['data-provenance-occurrence'] === '2')!;
    expect(third.attributes).toMatchObject({ 'data-origin-kind': 'step', 'data-origin-capture': id(2), 'data-origin-step': '1', 'data-receipt-capture': id(3) });
    expect(third.attributes['data-origin-capture']).not.toBe(id(1)); expect(third.attributes['data-origin-capture']).not.toBe(id(3));
    expect(third.block).toContain(`First appeared in attempt 2 (${id(2).slice(0, 8)}), step 2`); expect(third.block).toContain(`recorded by attempt 3 (${id(3).slice(0, 8)})`);
    expect(entries(full).find(entry => entry.attributes['data-provenance-occurrence'] === '1')!.block).toContain('First appeared in the first exposure');
    expect(full).toContain('Definition-head conversion of type · <code>Nat</code>');
    const prefix = panel({ history, previousCaptureId: id(3), parentStepIndex: 1, currentOrigin: true });
    expectFaithful(prefix, occurrenceProvenance(history, id(3), 1));
    expect(prefix).toContain('data-provenance-excluded="2"'); expect(prefix).toContain(`Step 3 of attempt 3 (${id(3).slice(0, 8)}) is outside this prefix and not read.`);
  });

  it('gives an explicit refusal for an ineligible prefix while the candidate stays inspectable, and keeps eligible earlier prefixes', () => {
    let history = append(initial().history, argumentFocus(initial().history, 1));
    const stopped = argumentFocus(history, 3); errorStop(stopped, 1, 0);
    history = append(history, stopped);
    const refused = panel({ history, previousCaptureId: id(3), parentStepIndex: 1, currentOrigin: true });
    expect(refused).toContain('data-provenance-refused'); expect(refused).toContain('Provenance unavailable for this step');
    expect(refused).toContain('not eligible'); expect(refused).not.toContain('data-provenance-occurrence'); expect(refused).not.toContain('data-provenance-route');
    const earlier = panel({ history, previousCaptureId: id(3), parentStepIndex: 0, currentOrigin: true });
    expectFaithful(earlier, occurrenceProvenance(history, id(3), 0));
    expect(earlier).toContain('data-provenance-excluded="1"');
    const stoppedBundle: SourceDecompositionBundle = { snapshot: history.snapshot, origin: origin(id(3)), record: history.attempts[1].record };
    const reading = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [stoppedBundle], history, currentOrigin: true, onContinue: () => {} }));
    expect(reading).toContain('callback failed'); expect(reading).toContain('data-provenance-refused'); expect(reading).not.toContain('data-provenance-occurrence');
    // A displayed record that is not the retained object (a mismatch clone) gets a refusal, never another prefix's chain.
    const mismatch = structuredClone(history.attempts[0].record);
    if (mismatch.checking.status !== 'captured') throw Error('missing checks');
    mismatch.checking.steps[1].replay = 'mismatch';
    const cloned = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [{ snapshot: history.snapshot, origin: origin(id(1)), record: mismatch }], history, currentOrigin: true, onContinue: () => {} }));
    expect(cloned).toContain('This result changed'); expect(cloned).toContain('data-provenance-refused'); expect(cloned).toContain('not the retained record');
    expect(cloned).not.toContain('data-provenance-occurrence');
    // The panel is a sibling after the step view, outside the term/type tabpanel.
    const live = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: [{ snapshot: history.snapshot, origin: origin(id(1)), record: history.attempts[0].record }], history, currentOrigin: true, onContinue: () => {} }));
    expect(live.indexOf('data-provenance-route')).toBeGreaterThan(live.indexOf('Exact input pair'));
    expect(live.slice(live.indexOf('role="tabpanel"'), live.indexOf('Exact input pair'))).not.toContain('data-provenance');
  });

  it('renders injected roles for every standard form with the contract operand wording and no derivation', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1));
    const base = occurrenceProvenance(history, id(1), 1);
    const forms: [LogicalForm, string, string][] = [['eq', 'left', 'left side'], ['and', 'required-right', 'required condition (not supplied)'], ['or', 'alternative-right', 'alternative (no case assumed)'],
      ['iff', 'equivalent-left', 'equivalent side'], ['not', 'negated', 'negated condition (no hypothesis inserted)'], ['unexpanded', 'body', 'body']];
    for (const [form, operand, wording] of forms) {
      const role: ContainmentRole = { form, operand, operandPath: ['appArg'], remainder: ['appFun'], inspection: 0 };
      const edge = { ...base.edges[1], relation: { kind: 'containment' as const, path: ['appArg', 'appFun'] as const, binders: [], role } };
      const injected: OccurrenceProvenance = { ...base, edges: [base.edges[0], edge as unknown as OccurrenceProvenance['edges'][number]] };
      const html = renderToStaticMarkup(createElement(ProvenancePanel, { history, derived: { value: injected }, currentOrigin: true }));
      expect(html).toContain(`Role: ${provenanceWording.formTitle(form)} · ${wording} · then Function, read as ordinary containment`);
      expect(html).toContain('data-containment-role="' + operand + '"');
      expect(wording ? html : '').not.toMatch(/assume |atomic|proves|supplier/i);
    }
  });

  it('keeps every label neutral: no status reads as false, no candidate as witness, no proof or implication without evidence', () => {
    const statuses: EvidenceStatus[] = [{ status: 'unestablished' }, { status: 'conflicting' },
      ...(['proposition', 'type', 'general-sort', 'term'] as const).map(kind => ({ status: 'established' as const, kind, inferredType: ['sort', ['zero']] as JsonValue }))];
    for (const status of statuses) { const text = provenanceWording.statusTitle(status); expect(text).not.toMatch(/false|invalid|failed|proof|witness/i); }
    for (const kind of ['proposition', 'type', 'general-sort', 'term', 'unestablished'] as FormationKind[]) expect(provenanceWording.kindTitle(kind)).not.toMatch(/false|proof/i);
    const forms: (LogicalForm | null)[] = ['forall', 'implies', 'eq', 'and', 'or', 'iff', 'not', 'exists', 'true', 'false', 'unexpanded', null];
    for (const form of forms) {
      const text = provenanceWording.formTitle(form);
      expect(/implication/.test(text)).toBe(form === 'implies'); expect(text).not.toMatch(/witness|proof/i);
    }
    const role = (form: LogicalForm): ContainmentRole => ({ form, operand: 'body', operandPath: ['piBody'], remainder: [], inspection: 0 });
    const binder = (position: number, assigned: EnteredBinder['role']): EnteredBinder => ({ position, step: 'piBody', name: name('x'), kind: 'port', role: assigned });
    for (const form of ['forall', 'implies', 'exists', null] as (LogicalForm | null)[]) for (const assigned of ['universal', 'proof', 'candidate', null] as EnteredBinder['role'][]) {
      const text = provenanceWording.binderTitle(binder(0, assigned), form ? role(form) : null);
      expect(text).not.toMatch(/witness|there exists|there is /i);
      expect(/proof/i.test(text)).toBe(assigned === 'proof');
      expect(/^For every/.test(text)).toBe(assigned === 'universal');
      expect(/^Candidate/.test(text)).toBe(assigned === 'candidate');
      if (assigned === null) expect(/^For all x, without a binder classification$/.test(text)).toBe(form === 'forall' || form === 'implies');
    }
    expect(provenanceWording.binderTitle(binder(1, null), role('forall'))).toBe('Bound name x entered here; lexical only, no logical role');
    const relations: ProvenanceRelation[] = [{ kind: 'type-of' }, { kind: 'conversion', target: 'term', head: name('Nat') }, { kind: 'projection-of', index: 2, field: name('law') },
      { kind: 'containment', path: ['appArg', 'lamBody'], binders: [], role: null }];
    for (const relation of relations) expect(provenanceWording.relationTitle(relation)).not.toMatch(/proof|supplier|witness|for every|candidate/i);
    // The introduction and the evidence-scope paragraph: every required fact, neither blanket exclusion of the earlier wording.
    const evidence = provenanceWording.evidenceTitle;
    for (const text of [provenanceWording.introTitle, evidence]) {
      expect(text).not.toMatch(STRICT); expect(text).not.toMatch(/For every|For all|proof|fresh|\blive\b|validated|assume |atomic/i);
      expect(text).not.toMatch(/only[^.]*at literal Sort zero|establish no formation|not formation evidence|typing checks, listed separately|combines every accepted outcome/);
    }
    expect(provenanceWording.introTitle).toMatch(/recorded outcomes of the selected record concern it/); expect(provenanceWording.introTitle).not.toMatch(/selected attempt/);
    for (const fact of [/read only from accepted logical-root and type-component outcomes/, /accepted outcomes that disagree give no reading/, /literal Sort zero reads as a proposition/, /a literal successor level as a type above Prop/,
      /any other level as a sort of general level/, /any other inferred type as an ordinary term/, /Binder-domain formation is a separate field, read from logical-domain outcomes/,
      /own line lists the checks the selected record made to produce it, which include its typing check; the relation that produced it lists the same recorded outcomes/,
      /produced by a type-component step these are also listed as its type-component formation outcome: the same recorded outcomes, not a second check/,
      /Checks made by selection, focus, projection or exposure are not read as formation under the current rule/]) expect(evidence).toMatch(fact);
    expect(evidence).not.toMatch(/introduc|selected attempt/);
    expect(provenanceWording.kindTitle('type')).toBe('a type above Prop'); expect(provenanceWording.kindTitle('general-sort')).toBe('a sort of general level'); expect(provenanceWording.kindTitle('term')).toBe('an ordinary term');
    // The own line: checks recorded at introduction; the same-span marker only when a formation entry names exactly the own span.
    const history = append(initial().history, argumentFocus(initial().history, 1)), own: ReceiptSpan = { captureId: id(1), start: 9, count: 2 };
    const base = provenanceWording.receiptTitle(history, own);
    expect(provenanceWording.occurrenceReceiptTitle(history, { receipts: own, formations: [] })).toBe(`${base} · the checks that record made to produce this occurrence`);
    expect(provenanceWording.occurrenceReceiptTitle(history, { receipts: own, formations: [{ receipts: { captureId: id(1), start: 11, count: 4 } }, { receipts: { ...own } }] }))
      .toBe(`${base} · the checks that record made to produce this occurrence, also listed below as a formation outcome: the same recorded outcomes, not a second check`);
    for (const other of [{ ...own, start: 8 }, { ...own, count: 3 }, { ...own, captureId: id(2) }])
      expect(provenanceWording.occurrenceReceiptTitle(history, { receipts: own, formations: [{ receipts: other }] })).toBe(`${base} · the checks that record made to produce this occurrence`);
    expect(provenanceWording.occurrenceReceiptTitle(history, { receipts: { ...own, count: 0 }, formations: [] })).toBe(provenanceWording.receiptTitle(history, { ...own, count: 0 }));
    for (const formations of [[], [{ receipts: own }]]) { const text = provenanceWording.occurrenceReceiptTitle(history, { receipts: own, formations }); expect(text).not.toMatch(STRICT); expect(text).not.toMatch(/typing checks|not formation evidence|untyped/i); }
    // Inspection titles. With no form read, the candidate is named as syntax only: the shape token, or a head constant set apart as an identifier.
    const heads: Partial<Record<LogicalForm, string>> = { eq: 'Eq', and: 'And', or: 'Or', iff: 'Iff', not: 'Not', exists: 'Exists', true: 'True', false: 'False' };
    for (const candidate of FORMS) for (const rootOutcome of ['accepted', 'rejected', 'unknown', 'missing'] as const) {
      const inspection = inspectionOf({ candidate, form: null, rootOutcome, shape: candidate === 'unexpanded' ? 'unexpanded' : candidate in heads ? 'standard' : 'forall' });
      const [before, head, after] = provenanceWording.inspectionParts(inspection), title = provenanceWording.inspectionTitle(inspection);
      expect(title).toBe(`${before}${head ?? ''}${after}`);
      expect(head).toBe(heads[candidate] ?? null);
      // An unexpanded shape records no candidate: nothing is named. Otherwise the syntax is named and marked as no reading.
      if (candidate === 'unexpanded') { expect(title).toMatch(/ · no logical form is read$/); expect(title).not.toContain('candidate'); expect(after).toBe(''); }
      else {
        expect(title).toMatch(/ · no logical form is read \(syntactic candidate .+, not a reading\)$/);
        expect(before.endsWith(head === null ? '(syntactic candidate forall' : '(syntactic candidate head constant ')).toBe(true);
        expect(after).toBe(', not a reading)');
      }
      for (const text of [before, after]) { expect(text).not.toMatch(READING); expect(text).not.toMatch(STRICT); }
    }
    // With a form read, the logical title is unchanged; beside a non-accepted root the form is attributed to the occurrence formation.
    for (const form of FORMS) {
      const accepted = provenanceWording.inspectionTitle(inspectionOf({ candidate: form, form, rootOutcome: 'accepted', formation: 'proposition' }));
      expect(accepted).toBe(`Logical inspection · shape standard · root outcome accepted · ${provenanceWording.formTitle(form)}`); expect(accepted).not.toContain('syntactic candidate');
      for (const rootOutcome of ['rejected', 'unknown'] as const) expect(provenanceWording.inspectionTitle(inspectionOf({ candidate: form, form, rootOutcome })))
        .toBe(`Logical inspection · shape standard · root outcome ${rootOutcome} · ${provenanceWording.formTitle(form)}, read from the occurrence formation, not from this root outcome`);
      // The stricter vocabulary holds for the wording of a read form too: the two constant propositions carry their constant in the code slot.
      for (const rootOutcome of ['accepted', 'rejected', 'unknown'] as const) {
        const [before, head, after] = provenanceWording.inspectionParts(inspectionOf({ candidate: form, form, rootOutcome }));
        expect(head).toBe(form === 'true' ? 'True' : form === 'false' ? 'False' : null);
        for (const text of [before, after]) expect(text).not.toMatch(STRICT);
      }
    }
    expect(provenanceWording.inspectionTitle(inspectionOf({ candidate: 'forall', shape: 'forall', form: null, domain: { formation: 'type', inferredType: ['sort', ['succ', ['zero']]], outcome: 'accepted' } })))
      .toBe('Logical inspection · shape forall · root outcome accepted · no logical form is read (syntactic candidate forall, not a reading) · binder domain a type above Prop, outcome accepted');
    // The proof-binder suffix follows the module's flag and nothing else. Every row is a state the module can produce.
    for (const [inspection, title] of PROOF_BINDER_ROWS) {
      expect(provenanceWording.inspectionTitle(inspection)).toBe(title);
      expect(/ · proof binder, read from the occurrence’s formation and binder-domain formation$/.test(title)).toBe(inspection.proofBinder); expect(/proof binder/.test(title)).toBe(inspection.proofBinder);
    }
    for (const candidate of FORMS) for (const form of [candidate, null]) for (const proofBinder of [true, false])
      expect(/proof binder/.test(provenanceWording.inspectionTitle(inspectionOf({ candidate, form, proofBinder })))).toBe(proofBinder);
  });

  it('renders the introduction, the evidence scope and the proof-binder suffix from the label table', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1)), base = occurrenceProvenance(history, id(1), 1), end = base.occurrences.length - 1;
    const html = panel({ history, previousCaptureId: id(1), parentStepIndex: 1, currentOrigin: true });
    // Isolate the approved introduction-only wording delta. Existing tests below
    // separately guard last-non-null inspection selection and term/type neutrality.
    const previousIntro = 'Each entry names where it first appeared, following the recorded parent links, and separately which recorded outcomes of the selected record concern it. The guided reading above uses the same reading. Nothing is re-checked, reduced or assumed here.';
    const approvedSentence = 'Any logical-root reading in the term view above comes from the last inspection of the displayed occurrence that reads a logical form.';
    expect(provenanceWording.introTitle).toBe(previousIntro.replace('The guided reading above uses the same reading.', approvedSentence));
    // Both paragraphs are rendered as written in the label table, in this order.
    const first = html.indexOf(`<p class="snapshot-context">${provenanceWording.introTitle}</p>`), second = html.indexOf(`<p class="snapshot-context" data-provenance-evidence="">${provenanceWording.evidenceTitle}</p>`);
    expect(first).toBeGreaterThan(0); expect(second).toBeGreaterThan(first);
    expect(visible(panelOf(html))).not.toMatch(STRICT);
    // Injected module-shaped values: the rendered inspection line is the title of the table, up to its origin.
    const own = base.occurrences[end].receipts, inject = (patch: Partial<OccurrenceProvenance['occurrences'][number]>): OccurrenceProvenance =>
      ({ ...base, occurrences: base.occurrences.map((occurrence, index) => index === end ? { ...occurrence, ...patch } : occurrence) });
    const render = (value: OccurrenceProvenance) => occurrenceBlock(renderToStaticMarkup(createElement(ProvenancePanel, { history, derived: { value }, currentOrigin: true })), end);
    for (const [inspection, title] of PROOF_BINDER_ROWS) {
      const block = render(inject({ formation: { status: 'established', kind: 'proposition', inferredType: ['sort', ['zero']] }, inspections: [inspection] }));
      expect(block).toContain(`<li data-inspection-form="${inspection.form}">${title} · first appeared in`);
    }
    // A type-component result: its formation entry names its own span, and the own line says so; a focus result carries no marker.
    const formation = { source: 'typeComponent' as const, kind: 'proposition' as const, inferredType: ['sort', ['zero']] as JsonValue, outcome: 'accepted' as const, origin: base.occurrences[end].origin, receipts: own };
    const marked = render(inject({ formation: { status: 'established', kind: 'proposition', inferredType: ['sort', ['zero']] }, formations: [formation] }));
    expect(introduction(marked)).toBe(`${provenanceWording.receiptTitle(history, own)} · the checks that record made to produce this occurrence, also listed below as a formation outcome: the same recorded outcomes, not a second check`);
    expect(introduction(render(base))).toBe(`${provenanceWording.receiptTitle(history, own)} · the checks that record made to produce this occurrence`);
    // A form read beside a rejected root outcome, with the accepted type-component outcome it rests on.
    const attributed = render(inject({ formation: { status: 'established', kind: 'proposition', inferredType: ['sort', ['zero']] }, formations: [formation],
      inspections: [inspectionOf({ shape: 'forall', candidate: 'forall', form: 'forall', rootOutcome: 'rejected', bodyUsesBinder: true })] }));
    expect(attributed).toContain('<li data-inspection-form="forall">Logical inspection · shape forall · root outcome rejected · universal statement, read from the occurrence formation, not from this root outcome · first appeared in');
  });

  it('renders a candidate as syntax when no form is read, and takes the guided root from the last inspection that reads a form', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1)), base = occurrenceProvenance(history, id(1), 1);
    const inject = (inspections: OccurrenceInspection[], formation: EvidenceStatus = { status: 'unestablished' }): OccurrenceProvenance =>
      ({ ...base, occurrences: base.occurrences.map((occurrence, index) => index === base.occurrences.length - 1 ? { ...occurrence, formation, inspections } : occurrence) });
    const render = (value: OccurrenceProvenance) => renderToStaticMarkup(createElement(ProvenancePanel, { history, derived: { value }, currentOrigin: true }));
    const end = base.occurrences.length - 1;
    // Unexpanded candidate with an unknown root: named as syntax, never as an unexpanded proposition.
    const unexpanded = occurrenceBlock(render(inject([inspectionOf({ shape: 'unexpanded', candidate: 'unexpanded', rootOutcome: 'unknown' })])), end);
    expect(unexpanded).toContain('<li data-inspection-form="none">Logical inspection · shape unexpanded · root outcome unknown · no logical form is read · first appeared in');
    expect(wording(unexpanded)).not.toMatch(READING); expect(unexpanded).not.toContain('candidate');
    // Standard candidates: the head constant is an identifier in code; the wording around it states no reading.
    for (const [candidate, head] of [['exists', 'Exists'], ['not', 'Not'], ['or', 'Or'], ['true', 'True'], ['false', 'False']] as [LogicalForm, string][]) {
      const block = occurrenceBlock(render(inject([inspectionOf({ candidate, rootOutcome: 'rejected' })])), end);
      expect(block).toContain(`root outcome rejected · no logical form is read (syntactic candidate head constant <code>${head}</code>, not a reading) · first appeared in`);
      expect(wording(block)).not.toMatch(READING); expect(visible(block)).not.toMatch(STRICT);
    }
    // A read constant proposition, beside an accepted and beside a rejected root: the constant is an identifier in code, and what the reader sees passes the stricter vocabulary.
    for (const [form, constant] of [['true', 'True'], ['false', 'False']] as [LogicalForm, string][]) for (const rootOutcome of ['accepted', 'rejected'] as const) {
      const block = occurrenceBlock(render(inject([inspectionOf({ candidate: form, form, rootOutcome, formation: 'proposition' })], { status: 'established', kind: 'proposition', inferredType: ['sort', ['zero']] })), end);
      expect(block).toContain(`<li data-inspection-form="${form}">Logical inspection · shape standard · root outcome ${rootOutcome} · the constant <code>${constant}</code> proposition${rootOutcome === 'accepted' ? '' : ', read from the occurrence formation, not from this root outcome'} · first appeared in`);
      expect(visible(block)).not.toMatch(STRICT); expect(visible(block)).not.toMatch(FORBIDDEN);
    }
    // A forall candidate over a type above Prop: no universal wording anywhere in the occurrence.
    const functionType = occurrenceBlock(render(inject([inspectionOf({ shape: 'forall', candidate: 'forall', formation: 'type', inferredType: ['sort', ['succ', ['zero']]] })],
      { status: 'established', kind: 'type', inferredType: ['sort', ['succ', ['zero']]] })), end);
    expect(functionType).toContain('Formation: established as a type above Prop'); expect(functionType).toContain('(syntactic candidate forall, not a reading)');
    expect(wording(functionType)).not.toMatch(/universal|statement|proposition|For every|For all/i);
    // Two inspections of one occurrence: the guided root is the last one that reads a form, whatever follows it.
    const read = inspectionOf({ shape: 'forall', candidate: 'forall', form: 'forall', formation: 'proposition', bodyUsesBinder: true });
    const equality = inspectionOf({ candidate: 'eq', form: 'eq', formation: 'proposition' }), unread = inspectionOf({ candidate: 'exists', form: null, rootOutcome: 'unknown' });
    expect(guidedLogicalRoot({ value: inject([read, unread]) })).toEqual({ form: 'forall', proofBinder: false, bodyUsesBinder: true });
    expect(guidedLogicalRoot({ value: inject([equality, read]) })).toEqual({ form: 'forall', proofBinder: false, bodyUsesBinder: true });
    expect(guidedLogicalRoot({ value: inject([read, equality]) })).toEqual({ form: 'eq', proofBinder: false });
    expect(guidedLogicalRoot({ value: inject([unread, unread]) })).toBeNull(); expect(guidedLogicalRoot({ value: inject([]) })).toBeNull();
    expect(guidedLogicalRoot({ refusal: 'refused' })).toBeNull(); expect(guidedLogicalRoot(undefined)).toBeNull();
  });

  it('is pure: rendering leaves the history unchanged and repeats identically', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1)), before = canonical(history);
    const first = panel({ history, previousCaptureId: id(1), parentStepIndex: 1, currentOrigin: true });
    expect(panel({ history, previousCaptureId: id(1), parentStepIndex: 1, currentOrigin: true })).toBe(first);
    expect(canonical(history)).toBe(before);
    expect(first).not.toContain('<button');
  });
});

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  seed: HeadExposureBundle | null; priorAttempts: SourceDecompositionBundle[]; operation: DecompositionOperation;
  previousCaptureId: string; parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: SourceSnapshotOrigin; sourceDecomposition: SourceDecompositionBundle['record'] };
}
const location = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES;
const rows: Row[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
const SORT_ZERO: JsonValue = ['sort', ['zero']], SORT_ONE: JsonValue = ['sort', ['succ', ['zero']]], SORT_GENERAL: JsonValue = ['sort', ['imax', ['succ', ['zero']], ['zero']]];
const renumber = (c: JsonObject) => {
  const checks = a(c.checks), audits = a(c.audits); let environment = 0;
  checks.forEach((check, index) => {
    const receipt = o(check), audit = o(audits[index]); receipt.envBefore = environment;
    if (o(receipt.outcome).tag === 'accepted') { environment++; audit.result = { tag: 'available', axioms: [] }; }
    else audit.result = { tag: 'unavailable', reason: 'declaration was not installed' };
    receipt.envAfter = environment; audit.environment = environment;
  });
  c.environmentSnapshotCount = environment + 1;
};
const verdict = (value: JsonObject, stepIndex: number, local: number, tag: 'rejected' | 'unknown') => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]);
  o(a(c.checks)[Number(step.receiptStart) + local]).outcome = tag === 'unknown' ? { tag: 'unknown', message: 'timeout control' } : { tag: 'rejected', kind: 'notConvertible' };
  renumber(c);
};
const setInferred = (value: JsonObject, stepIndex: number, local: 1 | 3, sort: JsonValue) => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]), output = o(step.output);
  (local === 1 ? o(output.formation) : o(output.domain)).inferredType = sort;
  const replayed = a(o(c.binding).expectedHistory)[stepIndex];
  if (replayed !== undefined) o(local === 1 ? o(o(replayed).candidate).formation : o(o(replayed).candidate).domain).inferredType = sort;
  const arity = Number(o(o(output.result).home).arity), index = Number(step.receiptStart) + local, receipt = o(a(c.checks)[index]), decl = clone(o(receipt.declaration));
  const rebody = (node: JsonValue, depth: number): JsonValue => {
    if (depth === 0) return sort;
    const n = a(node);
    return n[0] === 'letE' ? [n[0], n[1], n[2], n[3], rebody(n[4], depth - 1), n[5]] : [n[0], n[1], n[2], rebody(n[3], depth - 1), n[4]];
  };
  decl.type = rebody(decl.type, arity);
  receipt.declaration = decl; o(receipt.subject).declaration = decl; o(a(c.audits)[index]).subject = decl;
};
const setFormation = (value: JsonObject, stepIndex: number, sort: JsonValue) => setInferred(value, stepIndex, 1, sort);
const setDomain = (value: JsonObject, stepIndex: number, sort: JsonValue) => setInferred(value, stepIndex, 3, sort);
/** Validated history and record of a row, optionally after saved-data mutations of the record and its prior attempts. */
function fixture(row: Row, mutate: (record: JsonObject, priors: JsonObject[]) => void = () => {}) {
  const priors = row.priorAttempts.map(bundle => clone(bundle.record as unknown as JsonObject));
  const value = clone(row.response.sourceDecomposition as unknown as JsonObject);
  mutate(value, priors);
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence,
    seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
    attempts: row.priorAttempts.map((bundle, i) => ({ snapshot: bundle.snapshot, record: priors[i] })) });
  const record = validateSourceDecomposition(value, row.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  return { history, record, last: record.operations.length - 1 };
}
const last = (label: string) => { const row = [...rows].reverse().find(row => row.label === label); if (!row) throw Error(`missing ${label}`); return row; };
function message(row: Row) {
  const origin = row.parent.origin;
  return { type: 'statementlens.error', requestId: '4', message: 'Independent guided export unavailable.',
    document: { ...origin.document!, fileName: new URL(origin.document!.uri).pathname, selection: origin.selection },
    sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: row.parent.occurrence,
    decompositions: [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }] };
}

describe.skipIf(!location)('provenance panel on the actual v3 editor corpus', () => {
  it('renders every chain end field for field, including the eighth step, and never shows the current capture as an inherited origin', () => {
    expect(rows).toHaveLength(50);
    let replayed = 0, eighth = 0, catalogues = 0;
    for (const row of rows) {
      const { history, record, last: index } = fixture(row);
      const provenance = occurrenceProvenance(history, record.captureId, index);
      const html = panel({ history, previousCaptureId: record.captureId, parentStepIndex: index, currentOrigin: true });
      expectFaithful(html, provenance);
      expect(visible(html)).not.toMatch(FORBIDDEN);
      if (index === 7) eighth++;
      // Catalogue entries carry their own span and origin attributes; a fields step records zero kernel outcomes.
      for (const occurrence of provenance.occurrences) occurrence.catalogues.forEach((catalogue, i) => {
        expect(html).toContain(`data-provenance-catalogue="${i}" data-origin-kind="${catalogue.origin.kind}" data-origin-capture="${catalogue.origin.captureId}"`);
        expect(html).toContain(`data-receipt-capture="${catalogue.receipts.captureId}" data-receipt-start="${catalogue.receipts.start}" data-receipt-count="${catalogue.receipts.count}"`);
        if (catalogue.receipts.count === 0) { catalogues++; expect(html).toContain('no kernel outcomes recorded by'); }
      });
      for (const entry of entries(html)) {
        expect(entry.attributes['data-receipt-capture']).toBe(record.captureId);
        if (entry.attributes['data-origin-kind'] === 'step' && entry.attributes['data-origin-capture'] !== record.captureId) {
          replayed++; expect(entry.block).not.toContain(`First appeared in attempt ${history.attempts.length} (`); expect(entry.block).toContain(`(${entry.attributes['data-origin-capture'].slice(0, 8)})`);
        }
        if (entry.attributes['data-relation-kind'] && entry.attributes['data-relation-kind'] !== 'containment') {
          expect(entry.block).not.toMatch(/Role:|For every|For all|Candidate|Assumed/); expect(binderRoles(entry.block)).toEqual([]);
        }
      }
      // A chosen earlier prefix renders the excluded suffix explicitly.
      if (index > 0) {
        const earlier = panel({ history, previousCaptureId: record.captureId, parentStepIndex: index - 1, currentOrigin: true });
        expectFaithful(earlier, occurrenceProvenance(history, record.captureId, index - 1));
        expect(earlier).toContain(`data-provenance-excluded="${index}"`);
      }
    }
    expect(replayed).toBeGreaterThan(100); expect(eighth).toBe(3); expect(catalogues).toBeGreaterThan(0);
  }, 240000);

  it('reaches the same panel through the host parser with the retained history', () => {
    for (const row of rows.filter((row, index) => rows[index + 1]?.label !== row.label)) {
      const parsed = parseEditorMessage(message(row));
      if (!parsed || parsed.type === 'statementlens.status' || !parsed.decompositions || !parsed.sourceOccurrence || !parsed.sourceSnapshotOrigin) throw Error('parse');
      const retained = retainedDecompositionHistory(parsed.decompositions);
      expect(retained).toBeDefined();
      const record = parsed.decompositions.at(-1)!.record, index = record.operations.length - 1;
      let calls = 0;
      const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: parsed.sourceSnapshot!, origin: parsed.sourceSnapshotOrigin, occurrence: parsed.sourceOccurrence,
        decompositions: parsed.decompositions, onContinue: () => { calls++; } }));
      expect(calls).toBe(0);
      const viaHost = occurrenceProvenance(retained!, record.captureId, index), viaFixture = occurrenceProvenance(fixture(row).history, record.captureId, index);
      expect(canonical(viaHost)).toBe(canonical(viaFixture));
      expectFaithful(html, viaHost);
    }
  }, 240000);

  it('words binder roles, formation statuses and candidates only from the module evidence (saved-data mutation controls)', () => {
    const body = rows.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const render = (mutate?: (value: JsonObject, priors: JsonObject[]) => void) => {
      const { history, record, last: index } = fixture(body, mutate);
      return { html: panel({ history, previousCaptureId: record.captureId, parentStepIndex: index, currentOrigin: true }), provenance: occurrenceProvenance(history, record.captureId, index) };
    };
    const containment = (html: string) => entries(html).find(entry => entry.attributes['data-relation-kind'] === 'containment')!;
    const law = (html: string) => entries(html).find(entry => entry.attributes['data-provenance-occurrence'] === '2')!;
    const intact = render();
    expectFaithful(intact.html, intact.provenance);
    expect(containment(intact.html).block).toContain('Role: universal statement · body'); expect(containment(intact.html).block).toContain('For every <code>x</code>');
    expect(binderRoles(containment(intact.html).block)).toEqual([[0, 'universal']]);
    expect(law(intact.html).block).toContain('Formation: established as a proposition · Binder-domain formation: established as a type above Prop');
    expect(law(intact.html).block).toContain('These 2 accepted outcomes are receipts of one checked judgement in this capture, not independent confirmation.');
    const noDomain = render(value => verdict(value, 3, 3, 'rejected'));
    expect(binderRoles(containment(noDomain.html).block)).toEqual([[0, 'none']]);
    expect(containment(noDomain.html).block).toContain('Role: universal statement · body'); expect(containment(noDomain.html).block).toContain('For all <code>x</code>, without a binder classification');
    expect(wording(containment(noDomain.html).block)).not.toMatch(/For every|proof|implication/i);
    expect(law(noDomain.html).block).toContain('Binder-domain formation: not established'); expect(law(noDomain.html).block).toContain('data-formation-agreement');
    const general = render((value, priors) => { setDomain(priors[3], 3, SORT_GENERAL); setDomain(value, 3, SORT_GENERAL); });
    expect(binderRoles(containment(general.html).block)).toEqual([[0, 'none']]);
    expect(containment(general.html).block).toContain('For all <code>x</code>, without a binder classification');
    expect(law(general.html).block).toContain('Binder-domain formation: established as a sort of general level');
    const proof = render((value, priors) => { setDomain(priors[3], 3, SORT_ZERO); setDomain(value, 3, SORT_ZERO); });
    expect(binderRoles(containment(proof.html).block)).toEqual([[0, 'proof']]); expect(containment(proof.html).block).toContain('Assuming <code>x</code>, a proof binder');
    // The inspection line carries the proof-binder suffix exactly when the module reads one.
    expect(law(proof.html).block).toContain('<li data-inspection-form="forall">Logical inspection · shape forall · root outcome accepted · universal statement · binder domain a proposition, outcome accepted · proof binder, read from the occurrence’s formation and binder-domain formation · first appeared in');
    for (const variant of [intact, noDomain, general]) expect(law(variant.html).block).not.toContain('proof binder');
    const neither = render(value => { verdict(value, 2, 1, 'rejected'); verdict(value, 3, 1, 'unknown'); });
    expect(law(neither.html).block).toContain('Formation: not established'); expect(law(neither.html).block).toContain('data-formation-status="unestablished"');
    expect(law(neither.html).block).toContain('Type-component outcome rejected'); expect(law(neither.html).block).toContain('Logical root outcome unknown');
    expect(containment(neither.html).block).toContain('Role: none read; ordinary containment'); expect(binderRoles(containment(neither.html).block)).toEqual([[0, 'none']]);
    expect(containment(neither.html).block).toContain('Bound name <code>x</code> entered here; lexical only, no logical role');
    expect(wording(neither.html)).not.toMatch(/false|For every|For all|proof/i);
    const conflict = render((value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); });
    expect(law(conflict.html).block).toContain('Formation: conflicting: accepted outcomes disagree, so none is read');
    expect(law(conflict.html).block).toContain('data-formation-status="conflicting"');
    expect(binderRoles(containment(conflict.html).block)).toEqual([[0, 'none']]); expect(wording(conflict.html)).not.toMatch(/false|For every|For all|proof/i);
    for (const variant of [intact, noDomain, general, proof, neither, conflict]) expect(entries(variant.html).map(entry => entry.attributes['data-origin-capture'])).toEqual(entries(intact.html).map(entry => entry.attributes['data-origin-capture']));
  }, 240000);

  it('renders the evidence scope faithfully: a positive sort, a type-component result with its own receipt, a focus result, and a form beside a rejected root', () => {
    const show = (row: Row, mutate?: (value: JsonObject, priors: JsonObject[]) => void) => {
      const { history, record, last: index } = fixture(row, mutate);
      const html = panel({ history, previousCaptureId: record.captureId, parentStepIndex: index, currentOrigin: true });
      expectFaithful(html, occurrenceProvenance(history, record.captureId, index)); expect(visible(html)).not.toMatch(FORBIDDEN);
      expect(html).toContain(`<p class="snapshot-context" data-provenance-evidence="">${provenanceWording.evidenceTitle.replace(/’/g, '’')}</p>`);
      return { html, history, record, provenance: occurrenceProvenance(history, record.captureId, index) };
    };
    const where = (history: DecompositionHistory, span: ReceiptSpan) => provenanceWording.receiptTitle(history, span);
    // A positive sort: the ordinary function type is established as a type above Prop; its forall syntax is named as syntax only.
    const arrow = show(last('ordinary function type')), arrowBlock = occurrenceBlock(arrow.html, 0);
    expect(arrow.provenance.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'type' });
    expect(arrowBlock).toContain('Formation: established as a type above Prop · Binder-domain formation: established as a type above Prop');
    expect(arrowBlock).toContain('Logical root outcome accepted · a type above Prop');
    expect(arrowBlock).toContain('<li data-inspection-form="none">Logical inspection · shape forall · root outcome accepted · no logical form is read (syntactic candidate forall, not a reading) · binder domain a type above Prop, outcome accepted · first appeared in');
    expect(introduction(arrowBlock)).toBe(`${where(arrow.history, arrow.provenance.occurrences[0].receipts)} · the checks that record made to produce this occurrence`);
    expect(wording(arrowBlock)).not.toMatch(/universal|statement|proposition|For every|For all/i);
    expect(guidedLogicalRoot({ value: arrow.provenance })).toBeNull();
    // The other classifications, by saved-data mutation of the same row: a general level and a non-sort inferred type.
    const general = occurrenceBlock(show(last('ordinary function type'), value => setFormation(value, 0, SORT_GENERAL)).html, 0);
    expect(general).toContain('Formation: established as a sort of general level'); expect(general).toContain('(syntactic candidate forall, not a reading)');
    const term = occurrenceBlock(show(last('ordinary function type'), value => setFormation(value, 0, c('Nat'))).html, 0);
    expect(term).toContain('Formation: established as an ordinary term'); expect(term).toContain('Logical root outcome accepted · an ordinary term');
    for (const block of [general, term]) expect(wording(block)).not.toMatch(/universal|statement|proposition|For every|For all/i);
    // A genuine universal proposition keeps its logical wording.
    const body = rows.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const intact = show(body), law = occurrenceBlock(intact.html, 2), lawOccurrence = intact.provenance.occurrences[2];
    expect(law).toContain('<li data-inspection-form="forall">Logical inspection · shape forall · root outcome accepted · universal statement · binder domain a type above Prop, outcome accepted · first appeared in');
    expect(law).not.toContain('syntactic candidate');
    // A type-component result: its own span is the span of its type-component formation entry, said once, never denied.
    expect(lawOccurrence.formations[0]).toMatchObject({ source: 'typeComponent', outcome: 'accepted', receipts: lawOccurrence.receipts });
    expect(lawOccurrence.receipts).toMatchObject({ start: 9, count: 2 });
    expect(introduction(law)).toBe(`${where(intact.history, lawOccurrence.receipts)} · the checks that record made to produce this occurrence, also listed below as a formation outcome: the same recorded outcomes, not a second check`);
    expect(law).toContain(`Type-component outcome accepted · a proposition · first appeared in ${provenanceWording.originTitle(intact.history, lawOccurrence.formations[0].origin)} · ${where(intact.history, lawOccurrence.receipts).toLowerCase()}`);
    expect(law).toContain('These 2 accepted outcomes are receipts of one checked judgement in this capture, not independent confirmation.');
    expect(law).not.toMatch(/not formation evidence|establish no formation|typing checks/);
    // The marker stays when the type-component outcome is rejected: the entry is still listed, with its outcome.
    const rejectedOwn = occurrenceBlock(show(body, value => verdict(value, 2, 1, 'rejected')).html, 2);
    expect(introduction(rejectedOwn)).toBe(introduction(law));
    expect(rejectedOwn).toContain('Type-component outcome rejected · not established'); expect(rejectedOwn).toContain('Logical root outcome accepted · a proposition');
    expect(rejectedOwn).toContain('Formation: established as a proposition'); expect(rejectedOwn).not.toContain('data-formation-agreement');
    // A focus result with an accepted typing check: formation stays not established, and nothing says it is untyped.
    const focused = intact.provenance.occurrences[3], chain = intact.record;
    if (chain.checking.status !== 'captured') throw Error('missing checking');
    expect(focused.receipts).toMatchObject({ start: 15, count: 2 }); expect(focused.formations).toEqual([]);
    expect(chain.checking.checks.slice(15, 17).map(check => [check.label, check.outcome.tag])).toEqual([['context', 'accepted'], ['component', 'accepted']]);
    const focusBlock = occurrenceBlock(intact.html, 3);
    expect(introduction(focusBlock)).toBe(`${where(intact.history, focused.receipts)} · the checks that record made to produce this occurrence`);
    expect(focusBlock).toContain('data-formation-status="unestablished"'); expect(focusBlock).toContain('Formation: not established · Binder-domain formation: not established');
    expect(focusBlock).not.toContain('Formation outcomes'); expect(focusBlock).not.toContain('data-formation-agreement');
    // Inherited identity and the outcomes of the selected record stay apart: the occurrence first appeared in an earlier record, and its own line names the checks of the record read from.
    const projected = occurrenceBlock(intact.html, 1), projectedOccurrence = intact.provenance.occurrences[1];
    expect(projectedOccurrence.origin.captureId).not.toBe(projectedOccurrence.receipts.captureId);
    expect(projected).toContain(`First appeared in ${provenanceWording.originTitle(intact.history, projectedOccurrence.origin)}`);
    expect(introduction(projected)).toContain(`recorded by ${provenanceWording.recordTitle(intact.history, intact.record.captureId)} · the checks that record made to produce this occurrence`);
    expect(wording(projected)).not.toMatch(/introduc/i);
    // A focus result that is later inspected: its logical-root outcome is read as its formation, listed under it; its own line carries no marker.
    const inspectedRow = rows.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'logical' && row.parentStepIndex === 4)!, inspected = show(inspectedRow), inspectedBody = occurrenceBlock(inspected.html, 3);
    expect(inspected.provenance.occurrences[3].formations.map(formation => [formation.source, formation.outcome])).toEqual([['logical', 'accepted']]);
    expect(inspectedBody).toContain('Formation: established as a proposition'); expect(inspectedBody).toContain('Logical root outcome accepted · a proposition');
    expect(introduction(inspectedBody)).toBe(`${where(inspected.history, inspected.provenance.occurrences[3].receipts)} · the checks that record made to produce this occurrence`);
    expect(wording(focusBlock)).not.toMatch(/untyped|not typed|no typing|not formation evidence|establish no formation|false|invalid|failed/i);
    // The selected and the projected occurrence: the same own-line wording, no marker.
    for (const index of [0, 1]) expect(introduction(occurrenceBlock(intact.html, index))).toBe(`${where(intact.history, intact.provenance.occurrences[index].receipts)} · the checks that record made to produce this occurrence`);
    // A form read beside a rejected root outcome is attributed to the occurrence formation, in the rendered panel.
    const noRoot = show(body, value => verdict(value, 3, 1, 'rejected')), attributed = occurrenceBlock(noRoot.html, 2);
    expect(noRoot.provenance.occurrences[2].inspections[0]).toMatchObject({ form: 'forall', rootOutcome: 'rejected' });
    expect(attributed).toContain('<li data-inspection-form="forall">Logical inspection · shape forall · root outcome rejected · universal statement, read from the occurrence formation, not from this root outcome · binder domain a type above Prop, outcome accepted · first appeared in');
    expect(attributed).toContain('Type-component outcome accepted · a proposition'); expect(attributed).toContain('Logical root outcome rejected · not established');
    expect(attributed).not.toContain('data-formation-agreement');
    // A standard candidate on real data with its root rejected: the head constant as an identifier, no existential wording for the occurrence.
    const exists = show(last('universal then existential'), value => verdict(value, 2, 1, 'rejected')), unread = occurrenceBlock(exists.html, 1);
    expect(exists.provenance.occurrences[1].inspections[0]).toMatchObject({ shape: 'standard', candidate: 'exists', form: null, rootOutcome: 'rejected' });
    expect(unread).toContain('<li data-inspection-form="none">Logical inspection · shape standard · root outcome rejected · no logical form is read (syntactic candidate head constant <code>Exists</code>, not a reading) · first appeared in');
    expect(wording(unread)).not.toMatch(/existential|statement|proposition|Candidate/);
    // On every chain end: the marker appears exactly on the occurrences whose own span a formation entry names, and no form-null inspection carries a reading title.
    let marked = 0, unmarked = 0, formNull = 0;
    for (const row of rows.filter((row, index) => rows[index + 1]?.label !== row.label)) {
      const { html, provenance } = show(row);
      for (const occurrence of provenance.occurrences) {
        const block = occurrenceBlock(html, occurrence.index), listed = occurrence.formations.some(formation => canonical(formation.receipts) === canonical(occurrence.receipts));
        expect(/also listed below as a formation outcome/.test(introduction(block) ?? '')).toBe(listed);
        expect(listed).toBe(occurrence.formations.some(formation => formation.source === 'typeComponent'));
        if (listed) marked++; else unmarked++;
        if (occurrence.inspections.some(inspection => inspection.form === null)) { formNull++; if (occurrence.inspections.every(inspection => inspection.form === null)) expect(wording(block)).not.toMatch(/universal statement|For every|For all/); }
      }
    }
    console.log(`evidence scope on chain ends: ${marked} occurrences with the same-span marker, ${unmarked} without, ${formNull} with a form-null inspection`);
    expect(marked).toBeGreaterThan(0); expect(unmarked).toBeGreaterThan(marked); expect(formNull).toBeGreaterThan(0);
  }, 240000);

  it('feeds the guided reading from the same module inspection and keeps exact links through the existing positional path', () => {
    const steps: Record<string, number> = { appFun: 1, appArg: 2, lamDomain: 2, lamBody: 3, piDomain: 2, piBody: 3, letType: 2, letValue: 3, letBody: 4, projValue: 3 };
    let logicalSteps = 0, links = 0;
    for (const row of rows) {
      const { history, record, last: index } = fixture(row);
      if (record.checking.status !== 'captured') throw Error('missing checking');
      for (const step of record.checking.steps) {
        const derived = deriveProvenance(history, record.captureId, step.index), root = guidedLogicalRoot(derived);
        const reading = decompositionReading(record, step.index, 'term', root);
        // The panel's rule: the last inspection of the displayed occurrence that reads a form.
        const inspection = [...(derived?.value?.occurrences.at(-1)?.inspections ?? [])].reverse().find(item => item.form !== null);
        if (step.operation.kind === 'logical') {
          logicalSteps++;
          expect(root).toEqual(inspection && inspection.form !== null ? { form: inspection.form, proofBinder: inspection.proofBinder, ...(inspection.bodyUsesBinder === null ? {} : { bodyUsesBinder: inspection.bodyUsesBinder }) } : null);
          expect(reading?.document?.presentation?.logicalRootNodeId !== undefined).toBe(inspection?.form != null);
          expect(decompositionReading(record, step.index, 'type', root)?.document?.presentation?.logicalRootNodeId).toBeUndefined();
        }
      }
      const provenance = occurrenceProvenance(history, record.captureId, index);
      for (const edge of provenance.edges) if (edge.relation.kind === 'containment') {
        links++;
        const raw: (string | number)[] = ['term', ...edge.relation.path.map(step => steps[step])];
        expect(positionalResultPath(provenance.occurrences[edge.from].pair, [], raw)).toEqual(edge.relation.path);
      }
    }
    expect(logicalSteps).toBeGreaterThan(50); expect(links).toBeGreaterThan(20);
    // Under a rejected root beside an accepted type-component receipt the guided root follows the module, not the step's own receipt alone.
    const body = rows.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const noRoot = fixture(body, value => verdict(value, 3, 1, 'rejected'));
    expect(guidedLogicalRoot(deriveProvenance(noRoot.history, noRoot.record.captureId, 3))).toEqual({ form: 'forall', proofBinder: false, bodyUsesBinder: true });
    expect(decompositionReading(noRoot.record, 3, 'term', null)?.document?.presentation?.logicalRootNodeId).toBeUndefined();
    // Implication control: a proof binder unused in its body gives the guided root form implies, which differs from the syntactic candidate forall.
    const arrow = rows.find(row => row.label === 'ordinary function type')!;
    const implies = fixture(arrow, value => { setFormation(value, 0, SORT_ZERO); setDomain(value, 0, SORT_ZERO); });
    const impliesRoot = guidedLogicalRoot(deriveProvenance(implies.history, implies.record.captureId, 0));
    expect(impliesRoot).toEqual({ form: 'implies', proofBinder: true, bodyUsesBinder: false });
    expect(occurrenceBlock(panel({ history: implies.history, previousCaptureId: implies.record.captureId, parentStepIndex: 0, currentOrigin: true }), 0))
      .toContain('<li data-inspection-form="implies">Logical inspection · shape forall · root outcome accepted · implication · binder domain a proposition, outcome accepted · proof binder, read from the occurrence’s formation and binder-domain formation · first appeared in');
    expect(decompositionReading(implies.record, 0, 'term', impliesRoot)?.document?.presentation?.logicalRootNodeId).toBeDefined();
    const neither = fixture(body, value => { verdict(value, 2, 1, 'rejected'); verdict(value, 3, 1, 'rejected'); });
    expect(guidedLogicalRoot(deriveProvenance(neither.history, neither.record.captureId, 3))).toBeNull();
    // Static grep: the panel's value imports are exactly the render helpers and the accepted module; no non-test reader file reads receipts for provenance.
    const editorDir = path.dirname(fileURLToPath(import.meta.url));
    const panelSource = readFileSync(path.join(editorDir, 'SourceProvenanceReading.tsx'), 'utf8');
    const valueImports = [...panelSource.matchAll(/^import (?!type )[^;]*?from '([^']+)';/gm)].map(match => match[1]).sort();
    expect(valueImports).toEqual(['../packets/StructuralReading', '../packets/recorded-name', '../packets/syntax', './ContinuationChoice', './source-provenance', 'react']);
    expect(panelSource).not.toMatch(/logicalInspectionReading|typeComponentFormation|previousCaptureId ===|\.checks\[|receiptStart|replay ===|postMessage/);
    const readers = readdirSync(editorDir).filter(name => /\.(ts|tsx)$/.test(name) && !/\.test\.ts$|test-fixtures\.ts$/.test(name) && !['source-provenance.ts', 'logical-inspection-reading.ts'].includes(name));
    for (const name of readers) expect(readFileSync(path.join(editorDir, name), 'utf8'), name).not.toMatch(/logicalInspectionReading|typeComponentFormation/);
    expect(readers.length).toBeGreaterThan(10);
  }, 240000);

  it('reads a candidate only under the established Exists inspection and never as a witness', () => {
    const row = last('universal then existential');
    const render = (mutate?: (value: JsonObject) => void) => { const { history, record, last: index } = fixture(row, mutate); return panel({ history, previousCaptureId: record.captureId, parentStepIndex: index, currentOrigin: true }); };
    const intact = render(), exists = entries(intact).filter(entry => entry.attributes['data-relation-kind'] === 'containment')[1];
    expect(binderRoles(exists.block)).toEqual([[1, 'candidate']]); expect(exists.block).toContain('Candidate <code>y</code> within the existential statement');
    expect(exists.block).toContain('Role: existential statement · predicate · then Lambda body, read as ordinary containment');
    expect(wording(intact)).not.toMatch(/witness|there exists|there is /i);
    for (const tag of ['rejected', 'unknown'] as const) {
      const withdrawn = render(value => verdict(value, 2, 1, tag)), edge = entries(withdrawn).filter(entry => entry.attributes['data-relation-kind'] === 'containment')[1];
      expect(binderRoles(edge.block)).toEqual([[1, 'none']]); expect(edge.block).toContain('Bound name <code>y</code> entered here; lexical only, no logical role'); expect(edge.block).not.toContain('Candidate');
      expect(edge.block).toContain('Role: none read; ordinary containment');
      expect(entries(withdrawn).filter(entry => entry.attributes['data-relation-kind'] === 'containment')[0].block).toContain('Role: universal statement · body');
    }
    const negated = fixture(rows.find(row => row.label === 'negated owner' && row.operation.kind === 'focus' && row.parentStepIndex === 0)!);
    const negatedHtml = panel({ history: negated.history, previousCaptureId: negated.record.captureId, parentStepIndex: negated.last, currentOrigin: true });
    const under = entries(negatedHtml).find(entry => entry.attributes['data-relation-kind'] === 'containment')!;
    expect(under.block).toContain('Role: negation · negated condition (no hypothesis inserted) · then Argument → Lambda body → Argument, read as ordinary containment');
    expect(binderRoles(under.block)).toEqual([[2, 'none']]); expect(under.block).not.toContain('Candidate');
  }, 240000);
});

function rc2bPanel(html: string, className: 'source-provenance' | 'source-supplier'): string {
  const start = html.indexOf(`<section class="${className}"`);
  expect(start).toBeGreaterThanOrEqual(0);
  const end = html.indexOf('</section>', start);
  expect(end).toBeGreaterThan(start);
  return html.slice(start, end + '</section>'.length);
}

function rc2bOutcomeList(html: string, label: string): string {
  const start = html.indexOf(`<ol class="snapshot-checks" aria-label="${label}">`);
  expect(start).toBeGreaterThanOrEqual(0);
  const end = html.indexOf('</ol>', start);
  expect(end).toBeGreaterThan(start);
  return html.slice(start, end + '</ol>'.length);
}

function rc2bNumberedOutcomes(html: string, checking: { checks: { outcome: { tag: string } }[] }) {
  // The list must be exposed by an initially open details element, rather than
  // merely present in the HTML under a closed disclosure.
  expect(html).toMatch(/<details\b[^>]*\bopen=""[^>]*><summary>Recorded outcomes in this attempt \(\d+\)<\/summary><ol class="snapshot-checks" aria-label="All numbered outcomes of this attempt">/);
  const list = rc2bOutcomeList(html, 'All numbered outcomes of this attempt');
  const displayed = [...list.matchAll(/<li data-numbered-outcome="(\d+)"><strong>([^<]+)<\/strong> <span>([^<]+)<\/span>/g)]
    .map(match => ({ number: Number(match[1]), title: match[2], outcome: match[3] }));
  expect(displayed.map(row => row.number)).toEqual(checking.checks.map((_, index) => index + 1));
  expect(displayed.map(row => row.outcome)).toEqual(checking.checks.map(check => check.outcome.tag));
  displayed.forEach(row => expect(row.title).toMatch(new RegExp(`^Outcome ${row.number} · `)));
  return displayed;
}

describe('continuation reader authority and retained-record controls', () => {
  it.each([false, undefined])('suppresses direct saved continuation actions when currentOrigin is %s', currentOrigin => {
    const f = hostFixture(), history = retainedDecompositionHistory(f.live)!;
    const render = (currentOrigin: boolean | undefined) => renderToStaticMarkup(createElement(SourceDecompositionReading, {
      attempts: f.live, history, currentOrigin, onContinue: () => {},
    }));
    const actionNames = ['Expose definition head of term', 'Inspect fields', 'Inspect type of this term',
      'Read logical structure of this term (one layer)'];
    const live = render(true);
    expect(live).toContain('class="head-exposure-action"');
    for (const label of actionNames) expect(live).toContain(`>${label}</button>`);
    const before = canonical(f.live);
    const saved = render(currentOrigin);
    expect(saved).toContain('This saved history has an unverified origin.');
    expect(saved).not.toContain('class="head-exposure-action"');
    for (const label of actionNames) expect(saved).not.toContain(`>${label}</button>`);
    expect(saved).not.toContain('Check chosen part');
    expect(saved).toContain('Exact input pair');
    expect(saved).toContain('Complete continuation record');
    expect(saved).toContain('data-numbered-outcome="1"');
    expect(canonical(f.live)).toBe(before);
  });

  it.each([
    { name: 'provenance', className: 'source-provenance' as const, refusal: 'data-provenance-refused=""',
      route: 'data-provenance-route=', content: 'data-provenance-occurrence=' },
    { name: 'supply', className: 'source-supplier' as const, refusal: 'data-supplier-state="refused"',
      route: 'data-supplier-route=', content: 'data-supplier-typing=' },
  ])('refuses an equal-byte substituted record independently in the $name panel', control => {
    const f = hostFixture(), history = retainedDecompositionHistory(f.live)!;
    const original = f.live[0].record;
    expect(history.attempts.find(attempt => attempt.record.captureId === original.captureId)?.record).toBe(original);
    const render = (bundle: SourceDecompositionBundle) => renderToStaticMarkup(createElement(SourceDecompositionReading, {
      attempts: [bundle], history, currentOrigin: true,
    }));
    const retained = rc2bPanel(render(f.live[0]), control.className);
    expect(retained).toContain(control.route);
    expect(retained).toContain(control.content);
    expect(retained).not.toContain(control.refusal);
    // A replay mismatch or malformed field must not be responsible for refusal:
    // the only difference from the successful control is object identity.
    const replacement = structuredClone(original);
    expect(replacement).not.toBe(original);
    expect(canonical(replacement)).toBe(canonical(original));
    const before = canonical({ history, replacement });
    const html = render({ ...f.live[0], record: replacement });
    const refused = rc2bPanel(html, control.className);
    expect(refused).toContain(control.refusal);
    expect(refused).toContain('the displayed record is not the retained record of this history');
    expect(refused).not.toContain(control.route);
    expect(refused).not.toContain(control.content);
    expect(html).toContain('Exact input pair');
    expect(html).toContain('Complete continuation record');
    expect(html).toContain('data-numbered-outcome="1"');
    expect(canonical({ history, replacement })).toBe(before);
  });
});

describe.skipIf(!location)('logical outcome labels on validated stopped corpus records', () => {
  // Independent literal oracle: do not call operationOutcomeLabel to build the
  // expected display or the omitted-check sentence.
  const expected = ['Logical root context', 'Logical root component', 'Binder-domain context', 'Binder-domain component'];

  function logicalControl(retainedCount?: number) {
    const row = last('ordinary function type');
    const original = fixture(row);
    if (original.record.checking.status !== 'captured') throw Error('logical fixture has no captured checks');
    const originalStep = original.record.checking.steps[original.last];
    expect(originalStep.operation.kind).toBe('logical');
    expect(originalStep.receiptCount).toBe(4);
    expect(originalStep.output.status).toBe('candidate');
    if (originalStep.output.status !== 'candidate' || !('domain' in originalStep.output)) throw Error('missing logical candidate');
    expect(originalStep.output.domain).not.toBeNull();
    expect(originalStep.output.checking.status).toBe('completed');
    // errorStop's environment truncation assumes every preceding outcome was
    // accepted. Keep that precondition explicit for this real corpus fixture.
    expect(original.record.checking.checks.every(check => check.outcome.tag === 'accepted')).toBe(true);
    const value = retainedCount === undefined ? original : fixture(row, record => errorStop(record, original.last, retainedCount));
    // Use the exact object retained by the revalidated history, so the separate
    // identity guard cannot mask a label or stopped-check rendering regression.
    const record = value.history.attempts.at(-1)!.record;
    if (record.checking.status !== 'captured') throw Error('logical control has no captured checks');
    const step = record.checking.steps[value.last];
    const before = canonical(value.history);
    const html = renderToStaticMarkup(createElement(SourceDecompositionReading, {
      attempts: [{ snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record }],
      history: value.history, currentOrigin: true, onContinue: () => {},
    }));
    expect(canonical(value.history)).toBe(before);
    expect(html).not.toContain('not the retained record');
    expect(html).toContain('>Inspected term</button>');
    expect(html).toContain('role="tabpanel" aria-label="Inspected term"');
    return { html, record, checking: record.checking, step, index: value.last };
  }

  it.each([0, 1, 2, 3])('preserves a stopped logical prefix with %i of four outcomes', retainedCount => {
    const { html, checking, step, index } = logicalControl(retainedCount);
    expect(step.receiptCount).toBe(retainedCount);
    expect(checking.checks).toHaveLength(step.receiptStart + retainedCount);
    expect(html).toContain('Checking stopped: callback failed');
    expect(html).toContain(`<p data-unrecorded-logical-outcomes="">Not recorded for this logical inspection: ${expected.slice(retainedCount).join('; ')}.</p>`);
    expect(html.includes('No kernel outcomes were retained for this operation.')).toBe(retainedCount === 0);
    const selected = rc2bOutcomeList(html, `Step ${index + 1} outcomes`);
    expect([...selected.matchAll(/<strong>([^<]+)<\/strong>/g)].map(match => match[1]))
      .toEqual(expected.slice(0, retainedCount).map((label, offset) => `Outcome ${step.receiptStart + offset + 1} · ${label}`));
    expect(selected).not.toMatch(/\bConversion\b/i);
    const numbered = rc2bNumberedOutcomes(html, checking);
    expect(numbered.slice(step.receiptStart).map(row => row.title))
      .toEqual(expected.slice(0, retainedCount).map((label, offset) => `Outcome ${step.receiptStart + offset + 1} · Step ${index + 1} · ${label}`));
    expect(numbered.slice(step.receiptStart).map(row => row.title).join(' ')).not.toMatch(/\bConversion\b/i);
    expect(html).not.toContain('class="head-exposure-action"');
    expect(rc2bPanel(html, 'source-provenance')).toContain('data-provenance-refused=""');
    expect(rc2bPanel(html, 'source-provenance')).not.toContain('data-provenance-occurrence=');
    expect(rc2bPanel(html, 'source-supplier')).toContain('data-supplier-state="refused"');
    expect(rc2bPanel(html, 'source-supplier')).not.toContain('data-supplier-typing=');
  });

  it('resolves nonempty citations from both complete panels to visible numbered outcomes', () => {
    const { html, checking, step, index } = logicalControl();
    expect(html).not.toContain('data-unrecorded-logical-outcomes');
    const numbered = rc2bNumberedOutcomes(html, checking);
    expect(numbered.slice(step.receiptStart).map(row => row.title))
      .toEqual(expected.map((label, offset) => `Outcome ${step.receiptStart + offset + 1} · Step ${index + 1} · ${label}`));
    for (const className of ['source-provenance', 'source-supplier'] as const) {
      const block = rc2bPanel(html, className);
      const citations = [...block.matchAll(/\bOutcomes? (\d+)(?:–(\d+))? recorded by /gi)];
      // The successful control keeps this assertion non-vacuous; stopped panels
      // intentionally refuse and therefore contribute no receipt citations.
      expect(citations.length).toBeGreaterThan(0);
      for (const citation of citations) {
        const first = Number(citation[1]), last = Number(citation[2] ?? citation[1]);
        expect(first).toBeGreaterThan(0);
        expect(last).toBeGreaterThanOrEqual(first);
        expect(last).toBeLessThanOrEqual(numbered.length);
        for (let number = first; number <= last; number++) expect(numbered[number - 1].number).toBe(number);
      }
    }
  });
});
