import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import type { JsonObject, JsonValue } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { validateSourceHeadExposure, type HeadExposureCandidate } from './source-head-exposure';
import { validateDecompositionHistory, validateSourceDecomposition, decompositionParent, decompositionPlan, isDecompositionFocusPath,
  type DecompositionHistory, type DecompositionOperation } from './source-decomposition';
import { decompositionDrawing, decompositionReading, decompositionResultPath, positionalResultPath } from './source-decomposition-reading';
import { headExposureFixture } from './source-decomposition.test-fixtures';
import { readPositionalStructuralDrawing } from '../packets/structure';

import { o, a, name, c, b, app, clone, id, close, initial, seedCheckpoint, focus, record, firstFocus, append, checking, stepAt, replaceDeclaration, truncate, errorStop } from './source-decomposition-chain.test-fixtures';

function expandedHistory(term: JsonValue, body: JsonValue): DecompositionHistory {
  const fixture = headExposureFixture(), value = fixture.value, exposure = o(checking(value).exposure), result = o(exposure.result);
  result.term = term; o(exposure.definition).value = body;
  const tel = o(result.home).telescope;
  replaceDeclaration(value, 7, d => { d.value = close(tel, term, 'lam'); });
  replaceDeclaration(value, 8, d => { d.type = close(tel, app(c('Eq', [exposure.carrierSort]), result.type, exposure.before, term), 'forallE'); });
  const seed = validateSourceHeadExposure(value, fixture.snapshot, fixture.parent);
  return validateDecompositionHistory({ ...fixture.parent, seed: { snapshot: fixture.snapshot, record: seed }, attempts: [] });
}
const lam = (label: string, type: JsonValue, body: JsonValue): JsonValue => ['lam', name(label), type, body, 'default'];
function typeExposure(pair: PositionalStructuralInput): HeadExposureCandidate {
  const carrier: JsonValue = ['sort', ['succ', ['zero']]];
  return { status: 'candidate', before: pair.type, result: { home: pair.home, term: c('Again'), type: carrier },
    definition: { name: name('Nat'), levelParams: [], type: carrier, value: c('Again'), hints: ['abbrev'], safety: 'safe' },
    actualLevels: [], arguments: [], betaApplications: 0, carrierSort: ['succ', ['succ', ['zero']]], checking: { status: 'completed' } };
}

describe('bounded decomposition records and historical replay', () => {
  it.each([false, true])('reconstructs owned dependent binders and genuine let/have flags %s', nondep => {
    const nat = c('Nat'), arrow: JsonValue = ['forallE', name('x'), nat, nat, 'default'];
    const expanded = lam('same', nat, ['letE', name('same'), nat, b(1), lam('same', app(c('Fin'), b(1)), app(b(5), b(1))), nondep]);
    const body = lam('x', arrow, lam('x', nat,
      lam('same', nat, ['letE', name('same'), nat, b(1), lam('same', app(c('Fin'), b(1)), app(b(4), b(1))), nondep])));
    const history = expandedHistory(expanded, body), base = seedCheckpoint(history).candidate.result.home;
    const first: JsonValue = ['port', base.telescope, { name: name('same'), info: 'default' }, nat];
    const second: JsonValue = ['letE', first, name('same'), nondep, nat, b(1)];
    const telescope: JsonValue = ['port', second, { name: name('same'), info: 'default' }, app(c('Fin'), b(1))];
    const result = { home: { arity: 6, telescope }, term: app(b(5), b(1)), type: nat };
    const value = record(history, { kind: 'focus', path: ['lamBody', 'letBody', 'lamBody'] }, focus(result));
    validateSourceDecomposition(value, history.snapshot, history);
    const partial = clone(value); errorStop(partial, 1, 0); o(o(stepAt(partial, 1).output).result).type = app(c('Fin'), b(0));
    validateSourceDecomposition(partial, history.snapshot, history);
    o(o(stepAt(partial, 1).output).result).type = b(6);
    expect(() => validateSourceDecomposition(partial, history.snapshot, history)).toThrow();
    // Repair all receipt copies while changing a genuine owned let flag: the
    // selected home still must be reconstructed from the original path.
    const altered = clone(result); a(a(altered.home.telescope)[1])[3] = !nondep;
    const corrupt = record(history, { kind: 'focus', path: ['lamBody', 'letBody', 'lamBody'] }, focus(altered));
    expect(() => validateSourceDecomposition(corrupt, history.snapshot, history)).toThrow(/association/);
  });
  it('permits eight alternating operations and exactly26 receipts, then refuses a ninth operation', () => {
    let history = initial().history, previous = history.seed!.record.captureId, index = 0;
    let value = firstFocus(history); history = append(history, value); previous = value.captureId as string; index = 1;
    for (let i = 2; i < 8; i++) {
      const parent = decompositionParent(history, previous, index);
      value = i % 2 === 0 ? record(history, { kind: 'expose', target: 'type' }, typeExposure(parent.result), { previous, index })
        : record(history, { kind: 'focus', path: [] }, focus({ ...parent.result, type: c('Nat') }), { previous, index });
      history = append(history, value); previous = value.captureId as string; index = i;
    }
    expect(a(checking(value).checks)).toHaveLength(26);
    expect(() => decompositionPlan(history, previous, index, { kind: 'expose', target: 'type' })).toThrow(/eight operations/);
  });
  it('validates expose/focus with the exact original let home, and freezes detached values', () => {
    const { history } = initial(), value = firstFocus(history), result = validateSourceDecomposition(value, history.snapshot, history);
    expect(result).toEqual(value); expect(Object.isFrozen(result)).toBe(true);
    expect(checking(value).environmentSnapshotCount).toBe(12);
    expect(o(stepAt(value, 1).output).result).toEqual({ home: seedCheckpoint(history).candidate.result.home, term: b(0), type: c('Nat') });
    o(stepAt(value, 1).output).result = null; expect(result.checking.status === 'captured' && result.checking.steps[1].output.status).toBe('candidate');
  });
  it.each([0, 1, 2])('preserves a focus candidate with %s actual local receipts', count => {
    const { history } = initial(), value = firstFocus(history); errorStop(value, 1, count);
    if (count < 2) o(o(stepAt(value, 1).output).result).type = c('IndependentlyObservedType');
    expect(validateSourceDecomposition(value, history.snapshot, history)).toEqual(value);
    const retained = append(history, value);
    expect(() => decompositionParent(retained, value.captureId as string, 1)).toThrow(/eligible/);
    expect(decompositionParent(retained, value.captureId as string, 0).operation!.kind).toBe('expose');
  });
  it('associates U only with the actual component receipt, and does not reuse the earlier carrier at empty path', () => {
    const { history } = initial(), value = firstFocus(history, 'empty'), step = stepAt(value, 1), output = o(step.output), result = o(output.result);
    result.type = c('DifferentInferredType');
    replaceDeclaration(value, 10, d => { d.type = close(o(result.home).telescope, c('DifferentInferredType'), 'forallE'); });
    validateSourceDecomposition(value, history.snapshot, history);
    expect(result.type).not.toEqual(o(step.input).type);
    replaceDeclaration(value, 10, d => { d.type = close(o(result.home).telescope, c('Nat'), 'forallE'); });
    expect(() => validateSourceDecomposition(value, history.snapshot, history)).toThrow(/association/);
  });
  it('replays expose/focus/expose and keeps the type exposure carrier distinct', () => {
    const { history } = initial(), focused = firstFocus(history), retained = append(history, focused);
    const pair = o(o(stepAt(focused, 1).output).result) as unknown as PositionalStructuralInput;
    const carrier: JsonValue = ['sort', ['succ', ['zero']]], carrierSort: JsonValue = ['succ', ['succ', ['zero']]];
    const output: HeadExposureCandidate = { status: 'candidate', before: pair.type,
      result: { home: pair.home, term: c('ExpandedNat'), type: carrier }, definition: { name: name('Nat'), levelParams: [], type: carrier,
        value: c('ExpandedNat'), hints: ['regular', 1], safety: 'safe' }, actualLevels: [], arguments: [], betaApplications: 0, carrierSort, checking: { status: 'completed' } };
    const value = record(retained, { kind: 'expose', target: 'type' }, output, { previous: focused.captureId as string, index: 1 });
    expect(validateSourceDecomposition(value, retained.snapshot, retained)).toEqual(value);
    expect(a(checking(value).checks)).toHaveLength(14);
    const next = append(retained, value), backtrack = decompositionPlan(next, value.captureId as string, 0, { kind: 'focus', path: ['appFun'] });
    expect(backtrack.operations).toHaveLength(2); expect(backtrack.expectedHistory).toHaveLength(1);
    expect(next.attempts).toHaveLength(2); expect(next.attempts[1].record).toEqual(value);
  });
  it.each([0, 1, 2, 3])('retains historical exposure candidate/checks before error after %s local receipts', count => {
    const { history } = initial(), value = firstFocus(history); errorStop(value, 0, count);
    expect(validateSourceDecomposition(value, history.snapshot, history)).toEqual(value);
  });
  it.each([0, 1, 2, 3, 4, 5, 6])('retains a coherent base extraction failure prefix %s', count => {
    const { history } = initial(), value = firstFocus(history); truncate(value, count);
    Object.assign(checking(value), { action: { status: 'error', reason: 'base failure' }, selected: null, steps: [], stop: null });
    expect(validateSourceDecomposition(value, history.snapshot, history)).toEqual(value);
  });
  it('keeps a genuine historical semantic mismatch and its receipts, but forbids continuation from it', () => {
    const { history } = initial(), value = firstFocus(history), first = stepAt(value, 0);
    // Same replayed result, different exact source definition hint is still a
    // semantic checkpoint mismatch, without inventing a different outcome.
    o(o(first.output).definition).hints = ['regular', 9]; first.replay = 'mismatch';
    checking(value).steps = [first]; truncate(value, 9);
    checking(value).stop = { status: 'unavailable', kind: 'prerequisite', phase: 'history-match', reason: 'changed definition trace' };
    validateSourceDecomposition(value, history.snapshot, history);
    const retained = append(history, value);
    expect(() => decompositionParent(retained, value.captureId as string, 0)).toThrow(/eligible/);
    first.replay = 'matched'; expect(() => validateSourceDecomposition(value, history.snapshot, history)).toThrow(/association/);
  });
  it('rejects a changed historic U even with repaired actual component receipt unless it stops at history-match', () => {
    const { history } = initial(), first = firstFocus(history), retained = append(history, first);
    const unavailable = { status: 'unavailable', kind: 'unsupported', phase: 'head', reason: 'bound variable' };
    const value = record(retained, { kind: 'expose', target: 'term' }, unavailable, { previous: first.captureId as string, index: 1 });
    const focused = stepAt(value, 1), result = o(o(focused.output).result); result.type = c('ChangedU');
    replaceDeclaration(value, 10, d => { d.type = close(o(result.home).telescope, c('ChangedU'), 'forallE'); });
    checking(value).steps = a(checking(value).steps).slice(0, 2); truncate(value, 11); focused.replay = 'mismatch';
    checking(value).stop = { status: 'unavailable', kind: 'prerequisite', phase: 'history-match', reason: 'changed U' };
    validateSourceDecomposition(value, history.snapshot, retained);
    const historical = append(retained, value);
    expect(decompositionParent(historical, value.captureId as string, 0).operation!.kind).toBe('expose');
    expect(() => decompositionParent(historical, value.captureId as string, 1)).toThrow(/eligible/);
  });
  it('allows a nonexistent ordinary path only as explicit unavailable output with zero local receipts', () => {
    const { history } = initial(), out = { status: 'unavailable', kind: 'error', phase: 'focus', reason: 'missing path' };
    const parent = decompositionParent(history, history.seed!.record.captureId, 0);
    expect(isDecompositionFocusPath(parent.result, ['piBody'])).toBe(false);
    expect(isDecompositionFocusPath(parent.result, ['appArg'])).toBe(true);
    expect(() => decompositionPlan(history, history.seed!.record.captureId, 0, { kind: 'focus', path: ['piBody'] })).toThrow(/ordinary occurrence/);
    const value = record(history, { kind: 'focus', path: ['piBody'] }, out);
    stepAt(value, 1).replay = 'not-compared'; checking(value).stop = out;
    validateSourceDecomposition(value, history.snapshot, history);
    stepAt(value, 1).output = focus({ ...seedCheckpoint(history).candidate.result }) as unknown as JsonValue;
    expect(() => validateSourceDecomposition(value, history.snapshot, history)).toThrow(/nonexistent/);
  });
  it.each(['span', 'count', 'index', 'input', 'operation', 'future', 'prefix', 'subject', 'audit', 'environment', 'completed', 'stop', 'path', 'expected', 'receipt surplus'])('rejects %s tampering', mutation => {
    const { history } = initial(), value = firstFocus(history), step = stepAt(value, 1), check = checking(value);
    switch (mutation) {
      case 'span': step.receiptStart = 8; break;
      case 'count': step.receiptCount = 3; break;
      case 'index': step.index = 0; break;
      case 'input': o(step.input).term = b(1); break;
      case 'operation': o(step.operation).path = ['appFun']; break;
      case 'future': value.previousCaptureId = id(50); break;
      case 'prefix': replaceDeclaration(value, 10, d => { d.name = name('wrong'); d.all = [d.name]; }); break;
      case 'subject': o(o(a(check.checks)[10]).subject).attempt = id(50); break;
      case 'audit': o(a(check.audits)[10]).environment = 9; break;
      case 'environment': check.environmentSnapshotCount = 13; break;
      case 'completed': truncate(value, 10); step.receiptCount = 1; break;
      case 'stop': check.stop = { status: 'unavailable', kind: 'error', phase: 'operation-checking', reason: 'invented' }; break;
      case 'path': value.path = ['appArg']; break;
      case 'expected': o(a(o(check.binding).expectedHistory)[0]).candidate = null; break;
      case 'receipt surplus': check.steps = a(check.steps).slice(0, 1); break;
    }
    expect(() => validateSourceDecomposition(value, history.snapshot, history)).toThrow();
  });
  it.each(['unknown', 'rejected'])('retains %s evidence independently of later operation availability', verdict => {
    const { history } = initial(), value = firstFocus(history), check = checking(value), checks = a(check.checks), audits = a(check.audits);
    o(checks[1]).outcome = verdict === 'unknown' ? { tag: 'unknown', message: 'timeout' } : { tag: 'rejected', kind: 'notConvertible' };
    o(checks[1]).envAfter = 1; o(audits[1]).result = { tag: 'unavailable', reason: 'declaration was not installed' };
    for (let i = 1; i < checks.length; i++) { o(audits[i]).environment = i; if (i > 1) { o(checks[i]).envBefore = i - 1; o(checks[i]).envAfter = i; } }
    check.environmentSnapshotCount = checks.length;
    const retained = append(history, value); expect(decompositionParent(retained, value.captureId as string, 1).operation!.kind).toBe('focus');
  });
  it('revalidates typed-looking parents and rejects reordered/future histories without recursive trust', () => {
    const { history } = initial(), first = firstFocus(history), retained = append(history, first), second = firstFocus(retained, 'appFun'), final = append(retained, second);
    const forged = clone(final); if (forged.attempts[0].record.checking.status === 'captured') forged.attempts[0].record.checking.checks[0].envAfter = 2;
    expect(() => decompositionParent(forged, second.captureId as string, 1)).toThrow();
    const duplicated = clone(final); duplicated.attempts.push(duplicated.attempts[0]);
    expect(() => validateDecompositionHistory(duplicated)).toThrow(/fresh/);
    // A dependent attempt cannot appear before the record it addresses.
    o(second).previousCaptureId = first.captureId; second.parentStepIndex = 1;
    expect(() => validateDecompositionHistory({ ...history, attempts: [{ snapshot: history.snapshot, record: second }, { snapshot: history.snapshot, record: first }] })).toThrow();
  });
  it.each(['getter', 'sparse', 'prototype', 'cycle', 'unsafe', 'oversize'])('rejects hostile %s before interpretation', mutation => {
    const { history } = initial(), value = firstFocus(history); let invoked = false;
    switch (mutation) {
      case 'getter': Object.defineProperty(value, 'checking', { enumerable: true, get() { invoked = true; return null; } }); break;
      case 'sparse': value.operations = new Array(2); break;
      case 'prototype': Object.setPrototypeOf(value, { inherited: true }); break;
      case 'cycle': value.checking = value; break;
      case 'unsafe': value.parentStepIndex = 2 ** 53; break;
      case 'oversize': value.extra = 'x'.repeat(2 * 1024 * 1024); break;
    }
    expect(() => validateSourceDecomposition(value, history.snapshot, history)).toThrow(); expect(invoked).toBe(false);
  });
  it('enforces count/path limits on requests and immutable newly appended operations', () => {
    const { history } = initial(); const op: DecompositionOperation = { kind: 'focus', path: ['appArg'] };
    const plan = decompositionPlan(history, history.seed!.record.captureId, 0, op); op.path.push('appArg');
    expect(plan.operations[1]).toEqual({ kind: 'focus', path: ['appArg'] }); expect(Object.isFrozen(op)).toBe(false);
    expect(() => decompositionPlan(history, history.seed!.record.captureId, 0, { kind: 'expose', target: 'term' })).toThrow(/alternate/);
    expect(() => decompositionPlan(history, history.seed!.record.captureId, 0, { kind: 'focus', path: Array(65).fill('appFun') })).toThrow();
    let retained = history;
    for (let i = 0; i < 8; i++) retained = append(retained, firstFocus(retained));
    expect(() => decompositionPlan(retained, retained.seed!.record.captureId, 0, { kind: 'focus', path: [] })).toThrow(/eight attempts/);
  });
});

describe('exact decomposition pair adapters', () => {
  it('reads both roots in their true home and maps only actual result-term constructor paths', () => {
    const { history } = initial(), value = validateSourceDecomposition(firstFocus(history), history.snapshot, history);
    const drawing = decompositionDrawing(value, 1); expect(drawing?.ok).toBe(true);
    if (!drawing?.ok || value.checking.status !== 'captured' || value.checking.steps[1].output.status !== 'candidate') throw Error('test');
    expect(readPositionalStructuralDrawing(drawing.value)).toEqual({ ok: true, value: value.checking.steps[1].output.result });
    const term = decompositionReading(value, 0, 'term', null), type = decompositionReading(value, 0, 'type', null);
    expect(term?.document?.presentation?.target).toBe('term'); expect(type?.document?.presentation?.target).toBe('type');
    const root = ['checking', 'steps', 0, 'output', 'result'];
    expect(decompositionResultPath(value, 0, [...root, 'term'])).toEqual([]);
    expect(decompositionResultPath(value, 0, [...root, 'term', 2])).toEqual(['appArg']);
    for (const path of [[...root, 'type'], [...root, 'home'], [...root, 'term', 2, 1], [...root, 'term', '2'], ['checking', 'steps', 1, 'output', 'result', 'term']]) {
      expect(decompositionResultPath(value, 0, path)).toBeUndefined();
    }
    expect(positionalResultPath(value.checking.steps[1].output.result, root, [...root, 'term'])).toEqual([]);
    expect(decompositionReading(value, -1, 'term', null)).toBeUndefined(); expect(decompositionDrawing(value, 99)).toBeUndefined();
  });
});

const fixtures = process.env.DEFINOGRAPH_SOURCE_DECOMPOSITION_FIXTURES;
describe.skipIf(!fixtures)('actual native decomposition records', () => {
  it('validates every record with its independently retained history and exact structural results', () => {
    const rows = JSON.parse(readFileSync(fixtures!, 'utf8')) as { label: string; parent: DecompositionHistory; seed: DecompositionHistory['seed']; priorAttempts: DecompositionHistory['attempts']; response: { sourceSnapshot: unknown; sourceDecomposition?: unknown } }[];
    let count = 0;
    for (const row of rows) {
      if (!row.response.sourceDecomposition) continue;
      const history = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence,
        seed: { snapshot: row.seed!.snapshot, record: row.seed!.record }, attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
      const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot as DecompositionHistory['snapshot'], history);
      if (record.checking.status === 'captured') record.checking.steps.forEach((step, i) => {
        if (step.output.status !== 'candidate') return;
        const drawing = decompositionDrawing(record, i); expect(drawing?.ok, row.label).toBe(true);
        if (drawing?.ok) expect(readPositionalStructuralDrawing(drawing.value), row.label).toEqual({ ok: true, value: step.output.result });
      });
      count++;
    }
    expect(count).toBeGreaterThan(0);
  });
});
