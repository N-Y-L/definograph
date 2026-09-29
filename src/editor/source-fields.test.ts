import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { HeadExposureBundle } from './source-history';
import type { SourceOccurrence } from './source-occurrence';
import { validateDecompositionHistory, validateSourceDecomposition, decompositionPlan, type DecompositionOperation, type SourceDecompositionBundle } from './source-decomposition';
import { decompositionDrawing, decompositionReading, decompositionResultPath } from './source-decomposition-reading';
import { SourceSnapshotReading, savedSourceSnapshot } from './SourceSnapshotReading';
import { parseEditorMessage } from './host';

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  seed: HeadExposureBundle | null; priorAttempts: SourceDecompositionBundle[]; operation: DecompositionOperation;
  previousCaptureId: string; parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: SourceSnapshotOrigin; sourceDecomposition: SourceDecompositionBundle['record'] };
}
const location = process.env.DEFINOGRAPH_SOURCE_FIELD_FIXTURES;
const rows: Row[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
const o = (value: unknown) => value as JsonObject;
const a = (value: unknown) => value as JsonValue[];
const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
function fixture(row: Row) {
  const history = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, history);
  return { history, record };
}
function find(kind: DecompositionOperation['kind'], label = 'nested Envelope') {
  const row = rows.find(row => row.label === label && row.operation.kind === kind);
  if (!row) throw Error(`missing actual ${label}/${kind} control`); return row;
}
function cut(record: JsonObject, count: number) {
  const c = o(record.checking); c.checks = a(c.checks).slice(0, count); c.audits = a(c.audits).slice(0, count);
  c.environmentSnapshotCount = count ? Number(o(a(c.checks).at(-1)).envAfter) + 1 : 1;
}
function message(row: Row) {
  const origin = row.parent.origin;
  return { type: 'statementlens.error', requestId: '4', message: 'Independent guided export unavailable.',
    document: { ...origin.document!, fileName: new URL(origin.document!.uri).pathname, selection: origin.selection },
    sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: row.parent.occurrence,
    decompositions: [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }] };
}

describe.skipIf(!location)('actual v2 direct-field records', () => {
  it('validates fresh records and all named/primitive/check/source associations without a seed', () => {
    expect(rows.length).toBeGreaterThanOrEqual(33);
    for (const row of rows) {
      const { record } = fixture(row); expect(record.schema).toBe('definograph.source-decomposition.v2');
      if (record.checking.status !== 'captured') throw Error('missing checking');
      for (const step of record.checking.steps) if (step.output.status === 'candidate') {
        expect(decompositionDrawing(record, step.index)?.ok).toBe(true);
        expect(decompositionReading(record, step.index, 'term', null)).toBeDefined();
        expect(decompositionReading(record, step.index, 'type', null)).toBeDefined();
        expect(decompositionResultPath(record, step.index, ['checking', 'steps', step.index, 'output', 'result', 'term'])).toEqual([]);
        expect(decompositionResultPath(record, step.index, ['checking', 'steps', step.index, 'output', 'result', 'type'])).toBeUndefined();
        if (step.operation.kind === 'fields') { expect(step.receiptCount).toBe(0); expect(step.output.result).toEqual(step.input); }
        if (step.operation.kind === 'project') expect(step.output.result.home).toEqual(step.input.home);
      }
    }
  }, 60000);

  it('rejects altered metadata, ownership, order, universes and shape', () => {
    const row = find('fields'), { history } = fixture(row);
    const mutations: ((catalogue: JsonObject) => void)[] = [
      c => { o(c.structure).numParams = 0; }, c => { o(c.constructor).induct = ['str', ['anonymous'], 'Other']; },
      c => { o(c.structure).isUnsafe = true; }, c => { o(c.structure).numIndices = 1; },
      c => { o(c.constructor).numFields = 2; }, c => { c.omittedFields = 1; },
      c => { c.parameters = []; }, c => { c.actualLevels = [['succ', ['zero']]]; },
      c => { o(a(c.fields)[0]).index = 1; }, c => { o(o(a(c.fields)[0]).projectionInfo).index = 1; },
      c => { o(o(a(c.fields)[0]).declaration).kind = 'axiomDecl'; },
      c => { o(o(a(c.fields)[0]).declaration).name = ['str', ['anonymous'], 'Other']; },
      c => { o(o(a(c.fields)[0]).declaration).type = ['bvar', ['nat', '0']]; },
      c => { o(a(c.fields)[0]).parent = ['anonymous']; },
      c => { o(a(c.fields)[0]).name = ['str', ['str', ['anonymous'], 'Bad'], 'field']; },
      c => { c.fields = []; }, c => { c.extra = true; },
    ];
    for (const mutate of mutations) {
      const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
      mutate(o(o(a(o(value.checking).steps)[0]).output).catalogue as JsonObject);
      expect(() => validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toThrow();
    }
  });

  it('rejects changed named application, primitive owner/index, field and conversion declaration', () => {
    const row = find('project'), { history } = fixture(row);
    for (const change of ['named', 'primitive', 'owner', 'index', 'field', 'home', 'conversion']) {
      const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
      const c = o(value.checking), out = o(o(a(c.steps).at(-1)).output);
      if (change === 'named') o(out.result).term = ['sort', ['zero']];
      if (change === 'primitive') out.primitive = o(out.result).term;
      if (change === 'owner') a(out.primitive)[3] = ['sort', ['zero']];
      if (change === 'index') a(out.primitive)[2] = ['nat', '1'];
      if (change === 'field') o(out.field).binderInfo = 'implicit';
      if (change === 'home') o(o(out.result).home).arity = 0;
      if (change === 'conversion') o(o(a(c.checks).at(-1)).declaration).value = ['sort', ['zero']];
      expect(() => validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toThrow();
    }
  });

  it.each([0, 1, 2, 3])('retains an interrupted projection with exactly %s local receipts', count => {
    const row = find('project'), { history } = fixture(row);
    const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
    const c = o(value.checking), step = o(a(c.steps).at(-1)), out = o(step.output);
    step.receiptCount = count; step.replay = 'not-compared'; out.checking = { status: 'error', reason: 'callback interruption' };
    c.stop = { status: 'unavailable', kind: 'error', phase: 'operation-checking', reason: 'callback interruption' };
    cut(value, Number(step.receiptStart) + count);
    if (count < 2) o(out.result).type = ['sort', ['zero']]; // Scoped inference only, no component receipt yet.
    expect(validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toEqual(value);
  });

  it('compares a zero-receipt historical catalogue before any requested projection', () => {
    const row = find('project'), { history } = fixture(row);
    const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
    const c = o(value.checking), step = o(a(c.steps)[0]), out = o(step.output);
    o(a(o(out.catalogue).fields)[0]).binderInfo = 'implicit';
    step.replay = 'mismatch'; c.steps = [step]; cut(value, 6);
    c.stop = { status: 'unavailable', kind: 'prerequisite', phase: 'history-match', reason: 'changed catalogue' };
    expect(validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toEqual(value);
    c.stop = null; expect(() => validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toThrow();
  });

  it('limits original-root and field choices to v2 and their retained exact predecessor', () => {
    const row = find('fields'), { history } = fixture(row), id = row.parent.occurrence.captureId;
    expect(decompositionPlan(history, id, 0, { kind: 'fields' }, 2).expectedHistory).toEqual([]);
    for (const version of [1, 2] as const) expect(() => decompositionPlan(history, id, 0, { kind: 'project', index: 0 }, version)).toThrow();
    expect(() => decompositionPlan(history, id, 0, { kind: 'fields' }, 1)).toThrow();
    expect(() => decompositionPlan(history, id, 1, { kind: 'fields' }, 2)).toThrow();
    const selected = find('project'), retained = fixture(selected).history;
    expect(() => decompositionPlan(retained, selected.previousCaptureId, 0, { kind: 'project', index: 1 }, 2)).toThrow();
    expect(() => decompositionPlan(retained, selected.previousCaptureId, 0, { kind: 'project', index: 0 }, 1)).toThrow();
  });

  it('admits no-seed live histories, saves revision5, and renders metadata separately from typing', () => {
    const row = find('fields'), msg = message(row), parsed = parseEditorMessage(msg);
    expect(parsed?.type).toBe('statementlens.error'); expect(Object.isFrozen(parsed)).toBe(false);
    if (!parsed || parsed.type === 'statementlens.status') throw Error('no parsed result');
    expect(Object.isFrozen(parsed.decompositions)).toBe(true);
    let calls = 0;
    const props = { snapshot: row.parent.snapshot, origin: row.parent.origin, occurrence: row.parent.occurrence, decompositions: msg.decompositions, onContinue: () => { calls++; } };
    const html = renderToStaticMarkup(createElement(SourceSnapshotReading, props));
    expect(html).toContain('No field typing checks were requested'); expect(html).toContain('Check field payload');
    expect(html).toContain('the original selected occurrence'); expect(html).toContain('Inspect fields of original occurrence'); expect(calls).toBe(0);
    const saved = savedSourceSnapshot(props.snapshot, props.origin, props.occurrence, undefined, undefined, props.decompositions);
    expect(saved.version).toBe(5); expect(saved.provenance).toBe('unverified-saved-record'); expect(saved).not.toHaveProperty('headExposure');
    const readOnly = renderToStaticMarkup(createElement(SourceSnapshotReading, { ...props, origin: undefined }));
    expect(readOnly).not.toContain('Check field payload'); expect(calls).toBe(0);
    const bytes = canonical(msg.decompositions);
    for (const mutate of [
      (v: typeof msg) => { v.decompositions[0].origin.captureId = row.parent.origin.captureId; },
      (v: typeof msg) => { v.decompositions[0].origin.sourceSha256 = 'f'.repeat(64); },
      (v: typeof msg) => { v.decompositions[0].record.parentStepIndex = 1; },
      (v: typeof msg) => { v.sourceOccurrence = undefined as never; },
    ]) { const changed = structuredClone(msg); mutate(changed); expect(parseEditorMessage(changed)).toBeUndefined(); }
    expect(canonical(msg.decompositions)).toBe(bytes);
    const omitted = renderToStaticMarkup(createElement(SourceSnapshotReading, { ...props, decompositions: [], decompositionUnavailable: 'record exceeded bound', onCheckOccurrence: () => { calls++; } }));
    expect(omitted).not.toContain('Check chosen occurrence'); expect(omitted).toContain('Inspect fields of original occurrence'); expect(calls).toBe(0);

  });
});
