import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { SourceSnapshotReading } from './SourceSnapshotReading';
import { validateSourceSnapshot } from './source-snapshot';
import { validateSourceOccurrence } from './source-occurrence';
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
