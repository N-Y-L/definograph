import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { JsonObject, JsonValue } from '../packets/packet';
import { StructuralReading } from '../packets/StructuralReading';
import { readPositionalStructuralDrawing } from '../packets/structure';
import { parseEditorMessage, type HeadExposureBundle } from './host';
import { validateSourceSnapshot } from './source-snapshot';
import { validateSourceOccurrence } from './source-occurrence';
import { validateSourceHeadExposure, type HeadExposureTarget } from './source-head-exposure';
import type { SourceSnapshotOrigin } from './source-origin';
import { SourceHeadExposureReading } from './SourceHeadExposureReading';
import { SourceSnapshotReading, savedSourceSnapshot } from './SourceSnapshotReading';
import { headExposureDrawing, headExposureReading } from './source-head-exposure-reading';

const name = (text: string): JsonValue => text.split('.').reduce<JsonValue>((prefix, part) => ['str', prefix, part], ['anonymous']);
const c = (text: string, levels: JsonValue[] = []): JsonValue => ['const', name(text), levels];
const app = (...parts: JsonValue[]): JsonValue => parts.slice(1).reduce<JsonValue>((fn, arg) => ['app', fn, arg], parts[0]);
const nat = c('Nat'), zero: JsonValue = ['lit', ['natVal', ['nat', '0']]], level: JsonValue = ['succ', ['zero']];
const pi: JsonValue = ['forallE', name('x'), nat, nat, 'default'];
const olderId = '550e8400-e29b-41d4-a716-446655440000', originalId = '550e8400-e29b-41d4-a716-446655440001', freshId = '550e8400-e29b-41d4-a716-446655440002';
const document = { uri: 'file:///control.lean', fileName: '/control.lean', version: 2,
  selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } } };
const origin = (captureId: string): SourceSnapshotOrigin => ({ kind: 'local-editor-process-snapshot', captureId,
  sourceSha256: '0'.repeat(64), engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
  project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
  document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' });

function receipts(prefix: string, operation: string, attempt: string, term: JsonValue, type: JsonValue,
  result?: { term: JsonValue; type: JsonValue; before: JsonValue; level: JsonValue }) {
  const declarations: { suffix: string; type: JsonValue; value: JsonValue; component: boolean; label: string }[] = [];
  for (const base of ['source', 'extraction.root', 'extraction.selected']) {
    declarations.push({ suffix: `${base}.context`, type: c('True'), value: c('True.intro'), component: false, label: 'context' });
    declarations.push({ suffix: `${base}.component`, type, value: term, component: true, label: 'component' });
  }
  if (result) declarations.push(
    { suffix: 'result.context', type: c('True'), value: c('True.intro'), component: false, label: 'context' },
    { suffix: 'result.component', type: result.type, value: result.term, component: true, label: 'component' },
    { suffix: 'conversion', type: app(c('Eq', [result.level]), result.type, result.before, result.term),
      value: app(c('Eq.refl', [result.level]), result.type, result.before), component: false, label: 'conversion' });
  const checks: JsonValue[] = [], audits: JsonValue[] = [];
  for (const [id, entry] of declarations.entries()) {
    const declarationName = name(`${prefix}.${entry.suffix}`);
    const declaration: JsonObject = { kind: entry.component ? 'defnDecl' : 'thmDecl', name: declarationName, levelParams: [],
      type: entry.type, value: entry.value, all: [declarationName], ...(entry.component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
    checks.push({ id, pair: operation, label: entry.label, displayLabel: entry.label, declaration,
      subject: { attempt, pair: operation, sequence: id, target: entry.label, declaration },
      envBefore: id, envAfter: id + 1, heartbeatBound: ['nat', '200000'], outcome: { tag: 'accepted' } });
    audits.push({ checkId: id, subject: declaration, environment: id + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } });
  }
  return { checks, audits, environmentSnapshotCount: checks.length + 1 };
}

function fixture(target: HeadExposureTarget = 'term') {
  const term = target === 'term' ? app(c('Wrapper'), zero) : c('value'), type = target === 'term' ? nat : c('Alias');
  const selected = { home: { arity: 0, telescope: ['nil'] }, term, type };
  const frame = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: [], sourceTerm: term, sourceType: type };
  const snapshot = validateSourceSnapshot({ schema: 'definograph.source-snapshot.v1',
    selection: { startByte: 0, endByte: 4, requestedStartByte: 0, requestedEndByte: 4, parentDeclaration: null },
    policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
    expectedType: { status: 'absent' }, original: { status: 'available', typeOrigin: 'inferred', frame },
    prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame, checkerUniverseParams: [] },
    checking: { status: 'unavailable', kind: 'unsupported', phase: 'control', reason: 'Synthetic source capture.', attempted: false } });
  const binding = (attempt: string, prefix: string, operation: string, sourceKind: string): JsonObject => ({
    schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt, operation, sourceKind,
    declarationPrefix: name(prefix), universeParams: [], initialEnvironment: 0,
    context: { arity: 0, telescope: ['nil'], registry: [], registryOrder: 'mostRecentFirst', originalDeclarations: [], originalDeclarationOrder: 'oldestFirst' },
    sourceTerm: term, sourceType: type, positionalTerm: term, positionalType: type, path: [],
  });
  const originalPrefix = `StatementLens.SourceOccurrence.${originalId}`;
  const occurrence = validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1', parentCaptureId: olderId, captureId: originalId, path: [],
    policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
    checking: { status: 'captured', action: { status: 'completed' }, binding: binding(originalId, originalPrefix, 'editor-occurrence', 'namedExtraction'),
      selected, ...receipts(originalPrefix, 'editor-occurrence', originalId, term, type) } }, snapshot);
  const before = selected[target], after = target === 'term' ? app(c('Nat.succ'), zero) : nat;
  const carrier: JsonValue = target === 'term' ? nat : ['sort', level], carrierSort: JsonValue = target === 'term' ? level : ['succ', level];
  const prefix = `StatementLens.SourceHeadExposure.${freshId}`;
  const raw = { schema: 'definograph.source-head-exposure.v1', parentCaptureId: originalId, captureId: freshId, path: [], target,
    policy: { id: 'safe-definition-head-v1', operation: 'editor-head-exposure', preparation: 'Lean.instantiateMVars', universeSubstitution: 'structural',
      reduction: 'original-lambda-spine', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
    checking: { status: 'captured', action: { status: 'completed' }, binding: { ...binding(freshId, prefix, 'editor-head-exposure', 'namedHeadExposure'), target, expectedSelected: selected }, selected,
      exposure: { status: 'candidate', before, result: { home: selected.home, term: after, type: carrier },
        definition: { name: name(target === 'term' ? 'Wrapper' : 'Alias'), levelParams: [], type: target === 'term' ? pi : ['sort', level],
          value: target === 'term' ? ['lam', name('x'), nat, app(c('Nat.succ'), ['bvar', ['nat', '0']]), 'default'] : nat, hints: ['abbrev'], safety: 'safe' },
        actualLevels: [], arguments: target === 'term' ? [zero] : [], betaApplications: target === 'term' ? 1 : 0, carrierSort, checking: { status: 'completed' } },
      ...receipts(prefix, 'editor-head-exposure', freshId, term, type, { term: after, type: carrier, before, level: carrierSort }) } };
  const record = validateSourceHeadExposure(raw, snapshot, { snapshot, occurrence });
  const bundle: HeadExposureBundle = { snapshot, origin: origin(freshId), record };
  const message = { type: 'statementlens.error', requestId: '7', document, message: 'Legacy guided export unavailable.',
    sourceSnapshot: snapshot, sourceSnapshotOrigin: origin(originalId), sourceOccurrence: occurrence, headExposure: bundle };
  return { snapshot, occurrence, bundle, raw, message };
}

describe('head exposure host and reader integration', () => {
  it('retains independent original and fresh process associations even on a guided error', () => {
    const { message } = fixture(), parsed = parseEditorMessage(message);
    expect(parsed?.type).toBe('statementlens.error');
    if (!parsed || parsed.type === 'statementlens.status') throw new Error('missing message');
    expect(parsed.sourceOccurrence).toEqual(message.sourceOccurrence);
    expect(parsed.sourceSnapshotOrigin?.captureId).toBe(originalId);
    expect(parsed.headExposure?.origin.captureId).toBe(freshId);
    expect(Object.isFrozen(parsed.headExposure?.record)).toBe(true);
    expect(Object.isFrozen(parsed.headExposure?.origin.engine)).toBe(true);
    for (const mutate of [
      (m: typeof message) => { m.headExposure.origin.captureId = originalId; },
      (m: typeof message) => { m.headExposure.origin.sourceSha256 = 'f'.repeat(64); },
      (m: typeof message) => { m.headExposure.origin.document!.version++; },
      (m: typeof message) => { m.headExposure.origin.engine.contextSha256 = 'f'.repeat(64); },
      (m: typeof message) => { m.headExposure.origin.project.libraryPaths.push('/other'); },
      (m: typeof message) => { m.headExposure.record.parentCaptureId = olderId; },
      (m: typeof message) => { (m.headExposure as unknown as Record<string, unknown>).extra = true; },
    ]) { const copy = structuredClone(message); mutate(copy); expect(parseEditorMessage(copy)).toBeUndefined(); }
    expect(parseEditorMessage({ ...message, sourceOccurrence: undefined })).toBeUndefined();
    expect(parseEditorMessage({ ...message, headExposureUnavailable: 'also absent' })).toBeUndefined();
  });

  it.each(['term', 'type'] as const)('uses real result pairs, exact source paths and new provenance for %s exposure', target => {
    const { bundle, occurrence } = fixture(target), reading = headExposureReading(bundle.record)!;
    const checking = bundle.record.checking;
    if (checking.status !== 'captured' || checking.exposure?.status !== 'candidate') throw new Error('missing candidate');
    expect(reading.document?.presentation?.target).toBe('term');
    expect(reading.sourceById[reading.targetNodeId!].path).toEqual(['checking', 'exposure', 'result', 'term']);
    expect(reading.sourceById[reading.targetNodeId!].syntax).toEqual(checking.exposure.result.term);
    expect(reading.document!.objects.flatMap(object => object.provenance).every(item => item.origin === 'definition-head-exposure')).toBe(true);
    const drawn = headExposureDrawing(bundle.record)!;
    expect(drawn.ok).toBe(true);
    if (drawn.ok) {
      const before = JSON.stringify(drawn.value);
      const html = renderToStaticMarkup(createElement(StructuralReading, { drawing: drawn.value,
        positionalRootTitles: { term: `Exposed ${target}`, type: 'Carrier annotation' } }));
      expect(html).toContain('Carrier annotation'); expect(html).not.toMatch(/inferred type/i);
      expect(JSON.stringify(drawn.value)).toBe(before);
      expect(readPositionalStructuralDrawing(drawn.value)).toEqual({ ok: true, value: checking.exposure.result });
    }
    const html = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle, original: occurrence }));
    expect(html).toContain(`Exposed ${target} begins here.`);
    expect(html).toContain('9 fresh kernel outcomes retained'); expect(html).toContain('Conversion');
    expect(html).not.toContain('Expose definition head of');
    const prior = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle, original: occurrence, initialSide: 'before' }));
    expect(prior).toContain(target === 'term' ? 'Original selected term' : 'Original inferred type');
  });

  it('keeps all six original outcomes beside the fresh nine and saves both as unverified data', () => {
    const { snapshot, occurrence, bundle } = fixture();
    let calls = 0;
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, occurrence, origin: origin(originalId), headExposure: bundle,
      onExposeDefinitionHead: () => { calls++; } }));
    expect(html).toContain('6 kernel outcomes retained'); expect(html).toContain('9 fresh kernel outcomes retained');
    expect(html).not.toContain('Expose definition head of term'); expect(html).toContain('Refresh to start another source/exposure history'); expect(calls).toBe(0);
    const saved = savedSourceSnapshot(snapshot, origin(originalId), occurrence, bundle);
    expect(saved.version).toBe(3); expect(saved.provenance).toBe('unverified-saved-record');
    expect(saved.occurrence).toEqual(occurrence); expect(saved.headExposure?.record).toEqual(bundle.record);
    const imported = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, occurrence, headExposure: bundle }));
    expect(imported).toContain('Its origin is unverified'); expect(imported).not.toContain('Expose definition head of');
  });

  it('distinguishes explicit omission from candidate/error availability without discarding original data', () => {
    const { snapshot, occurrence, bundle, message } = fixture();
    const omitted = { ...message, headExposure: undefined, headExposureUnavailable: 'Native output exceeded its budget.' };
    expect(parseEditorMessage(omitted)).toBeDefined();
    expect(parseEditorMessage({ ...omitted, headExposureUnavailable: 'x'.repeat(4097) })).toBeUndefined();
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot, occurrence, headExposureUnavailable: omitted.headExposureUnavailable }));
    expect(html).toContain('6 kernel outcomes retained'); expect(html).not.toContain('fresh kernel outcomes retained');
    const record = structuredClone(bundle.record);
    record.checking = { status: 'unavailable', kind: 'limit', phase: 'exposure-output', reason: 'The complete record was omitted.', attempted: true };
    const validated = validateSourceHeadExposure(record, snapshot, { snapshot, occurrence });
    expect(headExposureReading(validated)).toBeUndefined(); expect(headExposureDrawing(validated)).toBeUndefined();
    const absent = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle: { ...bundle, record: validated }, original: occurrence }));
    expect(absent).toContain('does not establish how many checks ran'); expect(absent).not.toContain('candidate exposes');
  });

  it.each([6, 7, 8, 9])('retains the candidate and every actual callback when a later error leaves %s receipts', count => {
    const { snapshot, occurrence, bundle } = fixture(), record = structuredClone(bundle.record);
    if (record.checking.status !== 'captured' || record.checking.exposure?.status !== 'candidate') throw new Error('missing fixture');
    record.checking.checks = record.checking.checks.slice(0, count); record.checking.audits = record.checking.audits.slice(0, count);
    record.checking.environmentSnapshotCount = count + 1;
    record.checking.exposure.checking = { status: 'error', reason: 'A later callback failed.' };
    const checked = validateSourceHeadExposure(record, snapshot, { snapshot, occurrence });
    const html = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle: { ...bundle, record: checked }, original: occurrence }));
    expect(html).toContain(`${count} fresh kernel outcomes retained`);
    expect(html).toContain('Candidate checks reported an error'); expect(html).toContain('After exposure');
    expect(html).toContain('Candidate availability does not mean that any check accepted.');
  });

  it('shows an unknown conversion separately and retains an outer zero-check error without success wording', () => {
    const { snapshot, occurrence, bundle } = fixture(), record = structuredClone(bundle.record);
    if (record.checking.status !== 'captured') throw new Error('missing fixture');
    record.checking.checks[8].outcome = { tag: 'unknown', message: 'Resource bound.' };
    record.checking.checks[8].envAfter = 8;
    record.checking.audits[8].environment = 8;
    record.checking.audits[8].result = { tag: 'unavailable', reason: 'declaration was not installed' };
    record.checking.environmentSnapshotCount = 9;
    const unknown = validateSourceHeadExposure(record, snapshot, { snapshot, occurrence });
    const html = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle: { ...bundle, record: unknown }, original: occurrence }));
    expect(html).toContain('<strong>Conversion</strong> <span>unknown</span>');
    record.checking.action = { status: 'error', reason: 'Initial capture failed.' };
    record.checking.selected = null; record.checking.exposure = null;
    record.checking.checks = []; record.checking.audits = []; record.checking.environmentSnapshotCount = 1;
    const failed = validateSourceHeadExposure(record, snapshot, { snapshot, occurrence });
    const failureHtml = renderToStaticMarkup(createElement(SourceHeadExposureReading, { bundle: { ...bundle, record: failed }, original: occurrence }));
    expect(failureHtml).toContain('No retained kernel checks establish acceptance.');
    expect(failureHtml).toContain('Initial capture failed.'); expect(failureHtml).not.toContain('After exposure');
  });
});
