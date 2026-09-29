import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import type { HeadExposureBundle } from './source-history';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionHistory, type DecompositionOperation,
  type SourceDecompositionBundle } from './source-decomposition';
import { occurrenceProvenance, type OccurrenceOrigin, type OccurrenceProvenance, type ProvenanceEdge } from './source-provenance';
import { a, append, c, clone, errorStop, firstFocus, focus, id, initial, name, o, record, seedCheckpoint } from './source-decomposition-chain.test-fixtures';

/** A fresh attempt from the legacy seed focusing one application argument. */
function argumentFocus(history: DecompositionHistory, attempt: number) {
  const result = seedCheckpoint(history).candidate.result;
  return record(history, { kind: 'focus', path: ['appArg'] }, focus({ home: result.home, term: a(result.term)[2], type: c('Nat') }), { id: attempt });
}

const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
const withoutReceipts = (value: unknown): unknown => Array.isArray(value) ? value.map(withoutReceipts)
  : value && typeof value === 'object' ? Object.fromEntries(Object.entries(value).filter(([key]) => key !== 'receipts').map(([key, v]) => [key, withoutReceipts(v)])) : value;
const deepFrozen = (value: unknown): boolean => value === null || typeof value !== 'object' || Object.isFrozen(value) && Object.values(value).every(deepFrozen);
function skeleton(provenance: OccurrenceProvenance) {
  return { occurrences: provenance.occurrences.map(occurrence => withoutReceipts({ origin: occurrence.origin, pair: occurrence.pair })),
    edges: provenance.edges.map(edge => withoutReceipts({ from: edge.from, to: edge.to, origin: edge.origin, relation: edge.relation })) };
}

describe('constructed provenance controls', () => {
  it('reads the original route and the legacy seed route as inherited identities', () => {
    const { history } = initial();
    const original = occurrenceProvenance(history, history.occurrence.captureId, 0);
    expect(original.prefix.route).toBe('original');
    expect(original.occurrences).toHaveLength(1); expect(original.edges).toEqual([]); expect(original.excluded).toBeNull();
    expect(original.occurrences[0].origin).toEqual({ kind: 'original', captureId: history.occurrence.captureId });
    expect(original.occurrences[0].receipts.captureId).toBe(history.occurrence.captureId);
    const seed = occurrenceProvenance(history, history.seed!.record.captureId, 0);
    expect(seed.prefix.route).toBe('seed');
    expect(seed.occurrences.map(occurrence => occurrence.origin)).toEqual([
      { kind: 'original', captureId: history.occurrence.captureId }, { kind: 'seed', captureId: history.seed!.record.captureId }]);
    expect(seed.edges).toHaveLength(1);
    const exposure = history.seed!.record.checking.status === 'captured' && history.seed!.record.checking.exposure?.status === 'candidate' ? history.seed!.record.checking.exposure : undefined;
    expect(seed.edges[0].relation).toEqual({ kind: 'conversion', target: 'term', head: exposure!.definition.name });
    expect(seed.edges[0].origin).toEqual({ kind: 'seed', captureId: history.seed!.record.captureId });
    expect(seed.edges[0].receipts).toEqual({ captureId: history.seed!.record.captureId, start: 6, count: 3 });
    expect(seed.occurrences[1].pair).toEqual(history.seed!.record.checking.status === 'captured' && history.seed!.record.checking.exposure?.status === 'candidate'
      ? history.seed!.record.checking.exposure.result : undefined);
    expect(deepFrozen(seed)).toBe(true);
  });

  it('keeps sibling attempts with equal checkpoints as distinct origins while replayed steps inherit', () => {
    let history = initial().history;
    const first = argumentFocus(history, 1), second = argumentFocus(history, 2);
    history = append(history, first);
    const before = canonical(history);
    const alpha = occurrenceProvenance(history, id(1), 1);
    expect(alpha.occurrences.map(occurrence => occurrence.origin)).toEqual([
      { kind: 'original', captureId: history.occurrence.captureId }, { kind: 'seed', captureId: history.seed!.record.captureId }, { kind: 'step', captureId: id(1), stepIndex: 1 }]);
    expect(alpha.edges.map(edge => edge.relation.kind)).toEqual(['conversion', 'containment']);
    expect(alpha.edges.every(edge => edge.receipts.captureId === id(1))).toBe(true);
    expect(alpha.occurrences.every(occurrence => occurrence.receipts.captureId === id(1))).toBe(true);
    expect(alpha.edges[1].relation).toEqual({ kind: 'containment', path: ['appArg'], binders: [], role: null });
    expect(canonical(history)).toBe(before);
    const expectedAlpha = canonical(alpha);
    expect(canonical(occurrenceProvenance(history, id(1), 1))).toBe(expectedAlpha);
    // Each derivation owns its bounded canonicalization session: a module-level session failed at iteration 4301 on this fixture.
    for (let i = 0; i < 6000; i++) if (canonical(occurrenceProvenance(history, id(1), 1)) !== expectedAlpha) throw Error(`derivation ${i} differs`);
    // The second attempt replays the same seed and appends an equal checkpoint.
    const fresh = validateSourceDecomposition(second, history.snapshot, history);
    const step = fresh.checking.status === 'captured' ? fresh.checking.steps[1] : undefined;
    expect(step?.replay).toBe('new');
    history = validateDecompositionHistory({ ...history, attempts: [...history.attempts, { snapshot: history.snapshot, record: fresh }] });
    const beta = occurrenceProvenance(history, id(2), 1);
    expect(beta.occurrences[2].origin).toEqual({ kind: 'step', captureId: id(2), stepIndex: 1 });
    expect(beta.occurrences[2].pair).toEqual(alpha.occurrences[2].pair);
    expect(beta.occurrences[1].origin).toEqual(alpha.occurrences[1].origin);
    expect(beta.edges[0].receipts.captureId).toBe(id(2)); expect(alpha.edges[0].receipts.captureId).toBe(id(1));
  }, 30_000); // The 6000-derivation regression needs headroom on shared CI runners.

  it('refuses unknown parents, out-of-range steps, stopped steps and tampered histories', () => {
    let history = append(initial().history, firstFocus(initial().history, 'appArg'));
    expect(() => occurrenceProvenance(history, '660e8400-e29b-41d4-a716-000000000009', 0)).toThrow();
    expect(() => occurrenceProvenance(history, id(1), 2)).toThrow();
    expect(() => occurrenceProvenance(history, history.seed!.record.captureId, 1)).toThrow();
    const stopped = argumentFocus(history, 3);
    errorStop(stopped, 1, 0);
    history = append(history, stopped);
    expect(() => occurrenceProvenance(history, id(3), 1)).toThrow();
    const partial = occurrenceProvenance(history, id(3), 0);
    expect(partial.excluded).toEqual({ captureId: id(3), stepIndices: [1] });
    expect(partial.edges.map(edge => edge.origin)).toEqual([{ kind: 'seed', captureId: history.seed!.record.captureId }]);
    for (const mutate of [
      (value: JsonObject) => { o(o(a(value.attempts)[0]).record).previousCaptureId = id(7); },
      (value: JsonObject) => { o(a(o(o(o(a(value.attempts)[0]).record).checking).steps)[0]).replay = 'new'; },
      (value: JsonObject) => { o(o(a(value.attempts)[0]).record).parentStepIndex = 1; },
    ]) {
      const copy = clone(history as unknown as JsonObject); mutate(copy);
      expect(() => occurrenceProvenance(copy as unknown as DecompositionHistory, id(1), 1)).toThrow();
    }
    // Uniform precondition: an untampered but unregistered copy refuses before any reading.
    expect(() => occurrenceProvenance(clone(history as unknown as JsonObject) as unknown as DecompositionHistory, id(1), 1)).toThrow(/validated object/);
    expect(() => occurrenceProvenance(clone(history as unknown as JsonObject) as unknown as DecompositionHistory, history.seed!.record.captureId, 0)).toThrow(/validated object/);
  });

  it('inherits through the actual sibling when a replayed checkpoint is byte-equal in an earlier attempt', () => {
    let history = initial().history;
    history = append(history, argumentFocus(history, 1));
    history = append(history, argumentFocus(history, 2));
    const afterFocus = history.attempts[1].record.checking.status === 'captured' && history.attempts[1].record.checking.steps[1].output.status === 'candidate'
      ? history.attempts[1].record.checking.steps[1].output.result : undefined;
    // v1 records alternate expose/focus, so the third record's new operation is a constructed type exposure.
    const carrier: JsonValue = ['sort', ['succ', ['zero']]];
    const exposure = { status: 'candidate', before: afterFocus!.type, result: { home: afterFocus!.home, term: c('Again'), type: carrier },
      definition: { name: name('Nat'), levelParams: [], type: carrier, value: c('Again'), hints: ['abbrev'], safety: 'safe' },
      actualLevels: [], arguments: [], betaApplications: 0, carrierSort: ['succ', ['succ', ['zero']]], checking: { status: 'completed' } };
    history = append(history, record(history, { kind: 'expose', target: 'type' }, exposure, { previous: id(2), index: 1, id: 3 }));
    const third = history.attempts[2].record;
    expect(third.previousCaptureId).toBe(id(2)); expect(third.parentStepIndex).toBe(1);
    expect(third.checking.status === 'captured' ? third.checking.steps.map(step => step.replay) : []).toEqual(['matched', 'matched', 'new']);
    const chain = occurrenceProvenance(history, id(3), 2);
    expect(chain.occurrences.map(occurrence => occurrence.origin)).toEqual([
      { kind: 'original', captureId: history.occurrence.captureId }, { kind: 'seed', captureId: history.seed!.record.captureId },
      { kind: 'step', captureId: id(2), stepIndex: 1 }, { kind: 'step', captureId: id(3), stepIndex: 2 }]);
    // The earliest attempt with the same checkpoint is id(1); identity must not resolve there.
    expect(chain.occurrences[2].origin).not.toEqual({ kind: 'step', captureId: id(1), stepIndex: 1 });
    expect(chain.edges.map(edge => edge.relation.kind)).toEqual(['conversion', 'containment', 'conversion']);
    expect(chain.edges[2].relation).toEqual({ kind: 'conversion', target: 'type', head: name('Nat') });
    expect(chain.occurrences.every(occurrence => occurrence.receipts.captureId === id(3))).toBe(true);
    expect(occurrenceProvenance(history, id(3), 1).occurrences[2].origin).toEqual({ kind: 'step', captureId: id(2), stepIndex: 1 });
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
const byId = new Map(rows.map(row => [row.response.sourceDecomposition.captureId, row]));
function fixture(row: Row) {
  const history = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence,
    seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, history);
  return { history: validateDecompositionHistory({ ...history, attempts: [...history.attempts, { snapshot: row.response.sourceSnapshot, record }] }), record };
}
/** Independent oracle over the raw rows: follow the actual parent link at the same position. */
function oracle(row: Row, index: number): OccurrenceOrigin {
  const parent = byId.get(row.previousCaptureId);
  if (parent && index <= row.parentStepIndex) return oracle(parent, index);
  return { kind: 'step', captureId: row.response.sourceDecomposition.captureId, stepIndex: index };
}
const last = (label: string) => { const row = [...rows].reverse().find(row => row.label === label); if (!row) throw Error(`missing ${label}`); return row; };
const chainEnd = (row: Row) => { const { history, record } = fixture(row); return occurrenceProvenance(history, record.captureId, record.operations.length - 1); };
const containments = (provenance: OccurrenceProvenance) => provenance.edges.filter((edge): edge is ProvenanceEdge & { relation: { kind: 'containment' } } => edge.relation.kind === 'containment');
const SORT_ZERO: JsonValue = ['sort', ['zero']], SORT_ONE: JsonValue = ['sort', ['succ', ['zero']]];
const SORT_GENERAL: JsonValue = ['sort', ['imax', ['succ', ['zero']], ['zero']]];
/** Close a body over an exact telescope, oldest binder outermost; mirrors the receipt closure without calling it. */
function closeOver(telescope: JsonValue, body: JsonValue, tag: 'lam' | 'forallE'): JsonValue {
  const entries: JsonValue[][] = []; let tel = a(telescope);
  while (tel[0] !== 'nil') { entries.unshift(tel); tel = a(tel[1]); }
  return entries.reduceRight<JsonValue>((inner, item) => item[0] === 'port'
    ? [tag, o(item[2]).name, item[3], inner, o(item[2]).info] : ['letE', item[2], item[4], item[5], inner, item[3]], body);
}
/** Replace a new focus step's path and result by another ordinary occurrence of the same term, rebuilding its component receipt. */
const spliceFocus = (value: JsonObject, stepIndex: number, path: string[], type: JsonValue) => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]), input = o(step.input);
  const term = path.reduce<JsonValue>((node, part) => a(node)[({ appFun: 1, appArg: 2 } as Record<string, number>)[part]], input.term);
  o(a(value.operations)[stepIndex]).path = path; o(a(o(c.binding).operations)[stepIndex]).path = path; o(step.operation).path = path;
  o(step.output).result = { home: input.home, term, type };
  // Both focus receipts close over the result home, which for a non-binder path is the input home.
  const telescope = o(input.home).telescope, truth: JsonValue = ['const', name('True'), []], intro: JsonValue = ['const', name('intro', name('True')), []];
  for (const [local, declType, declValue] of [[0, truth, intro], [1, type, term]] as [number, JsonValue, JsonValue][]) {
    const index = Number(step.receiptStart) + local, receipt = o(a(c.checks)[index]), decl = clone(o(receipt.declaration));
    decl.type = closeOver(telescope, declType, 'forallE'); decl.value = closeOver(telescope, declValue, 'lam');
    receipt.declaration = decl; o(receipt.subject).declaration = decl; o(a(c.audits)[index]).subject = decl;
  }
};
const renameText = (value: JsonValue, from: string, to: string): JsonValue => typeof value === 'string' ? value === from ? to : value
  : Array.isArray(value) ? value.map(item => renameText(item, from, to)) : value && typeof value === 'object'
    ? Object.fromEntries(Object.entries(value).map(([key, item]) => [key, renameText(item, from, to)])) : value;
const checkpointOf = (step: JsonObject) => { const { checking: _checking, ...candidate } = o(step.output); void _checking; return { operation: step.operation, input: step.input, candidate }; };
const GRANDCHILD = '7d5b0c2e-4f6a-4b1c-9d3e-2a1b3c4d5e6f';
/** Saved-data construction: the row's single new focus becomes a second logical inspection of the same occurrence (child),
 * and a grandchild replays the child through that step and adds the original piBody focus. */
function secondInspection(row: Row, mutate: (child: JsonObject) => void) {
  const original = clone(row.response.sourceDecomposition as unknown as JsonObject), oc = o(original.checking);
  const focusStep = o(a(oc.steps)[4]), focusChecks = a(oc.checks).slice(15, 17), focusAudits = a(oc.audits).slice(15, 17);
  const value = clone(original), c = o(value.checking);
  a(value.operations)[4] = { kind: 'logical' }; a(o(c.binding).operations)[4] = { kind: 'logical' };
  const again = clone(o(a(c.steps)[3])); again.index = 4; again.receiptStart = 15; again.replay = 'new'; a(c.steps)[4] = again;
  c.checks = a(c.checks).slice(0, 15); c.audits = a(c.audits).slice(0, 15);
  for (let k = 0; k < 4; k++) {
    const receipt = o(renameText(clone(a(c.checks)[11 + k]), 'step3', 'step4')), audit = o(renameText(clone(a(c.audits)[11 + k]), 'step3', 'step4'));
    receipt.id = 15 + k; o(receipt.subject).sequence = 15 + k; audit.checkId = 15 + k;
    a(c.checks).push(receipt); a(c.audits).push(audit);
  }
  mutate(value); renumber(c);
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  const child = validateSourceDecomposition(value, row.response.sourceSnapshot, prior);
  const withChild = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record: child }] });
  const from = child.captureId, g = o(renameText(clone(value), from, GRANDCHILD)), gc = o(g.checking);
  g.previousCaptureId = from; g.parentStepIndex = 4;
  a(g.operations).push({ kind: 'focus', path: ['piBody'] }); o(gc.binding).operations = clone(g.operations);
  o(gc.binding).expectedHistory = a(c.steps).slice(0, 5).map(step => checkpointOf(o(step)) as unknown as JsonValue);
  a(gc.steps).forEach(step => { o(step).replay = 'matched'; });
  const last = clone(focusStep); last.index = 5; last.receiptStart = 19; last.replay = 'new'; a(gc.steps).push(last);
  focusChecks.forEach((check, k) => { const receipt = o(renameText(renameText(clone(check), from, GRANDCHILD), 'step4', 'step5')); receipt.id = 19 + k; o(receipt.subject).sequence = 19 + k; a(gc.checks).push(receipt); });
  focusAudits.forEach((audit, k) => { const copy = o(renameText(renameText(clone(audit), from, GRANDCHILD), 'step4', 'step5')); copy.checkId = 19 + k; a(gc.audits).push(copy); });
  renumber(gc);
  const snapshot = renameText(clone(row.response.sourceSnapshot as unknown as JsonValue), from, GRANDCHILD) as unknown as SourceSnapshot;
  const grand = validateSourceDecomposition(g, snapshot, withChild);
  const withGrand = validateDecompositionHistory({ ...withChild, attempts: [...withChild.attempts, { snapshot, record: grand }] });
  return { child: occurrenceProvenance(withChild, child.captureId, 4), grand: occurrenceProvenance(withGrand, grand.captureId, 5) };
}
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
/** Change one receipt outcome of a saved record; the audit/environment numbering follows. */
const verdict = (value: JsonObject, stepIndex: number, local: number, tag: 'rejected' | 'unknown') => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]);
  o(a(c.checks)[Number(step.receiptStart) + local]).outcome = tag === 'unknown' ? { tag: 'unknown', message: 'timeout control' } : { tag: 'rejected', kind: 'notConvertible' };
  renumber(c);
};
/** Consistently mutate a saved inferred type (root or domain) and its closed component declaration. Saved-data mutation only. */
const setInferred = (value: JsonObject, stepIndex: number, local: 1 | 3, sort: JsonValue) => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]), output = o(step.output);
  const slot = local === 1 ? o(output.formation) : o(output.domain); slot.inferredType = sort;
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
/** Validate a row's record after mutating it and/or its prior attempts, then derive its chain end. */
function mutated(row: Row, mutate: (record: JsonObject, priors: JsonObject[]) => void) {
  const priors = row.priorAttempts.map(bundle => clone(bundle.record as unknown as JsonObject));
  const value = clone(row.response.sourceDecomposition as unknown as JsonObject);
  mutate(value, priors);
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null,
    attempts: row.priorAttempts.map((bundle, i) => ({ snapshot: bundle.snapshot, record: priors[i] })) });
  const record = validateSourceDecomposition(value, row.response.sourceSnapshot, prior);
  const extended = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  return occurrenceProvenance(extended, record.captureId, record.operations.length - 1);
}

describe.skipIf(!location)('actual v3 editor corpus provenance', () => {
  it('derives every chain end and chosen prefix faithfully with inherited origins and fresh receipts', () => {
    expect(rows).toHaveLength(50);
    const creating = new Set(['focus', 'typeComponent', 'expose', 'project']);
    for (const row of rows) {
      expect(row.seed).toBeNull();
      const { history, record } = fixture(row), before = canonical(history);
      const end = occurrenceProvenance(history, record.captureId, record.operations.length - 1);
      expect(canonical(history)).toBe(before);
      expect(canonical(occurrenceProvenance(history, record.captureId, record.operations.length - 1))).toBe(canonical(end));
      expect(deepFrozen(end)).toBe(true);
      expect(end.prefix).toEqual({ previousCaptureId: record.captureId, parentStepIndex: record.operations.length - 1, route: 'attempt' });
      expect(end.excluded).toBeNull();
      expect(end.occurrences).toHaveLength(1 + record.operations.filter(operation => creating.has(operation.kind)).length);
      expect(end.edges.map(edge => edge.relation.kind)).toEqual(record.operations.filter(operation => creating.has(operation.kind))
        .map(operation => ({ focus: 'containment', typeComponent: 'type-of', expose: 'conversion', project: 'projection-of' } as Record<string, string>)[operation.kind]));
      if (record.checking.status !== 'captured') throw Error('missing checking');
      expect(end.occurrences[0].origin).toEqual({ kind: 'original', captureId: row.parent.occurrence.captureId });
      expect(end.occurrences[0].pair).toEqual(record.checking.selected);
      let cursor = 0;
      record.checking.steps.forEach((step, index) => {
        const origin = oracle(row, index), receipts = { captureId: record.captureId, start: step.receiptStart, count: step.receiptCount };
        if (step.output.status !== 'candidate') throw Error('missing candidate');
        if (creating.has(step.operation.kind)) {
          cursor++;
          expect(end.edges[cursor - 1]).toMatchObject({ from: cursor - 1, to: cursor, origin, receipts });
          expect(end.occurrences[cursor]).toMatchObject({ origin, receipts, pair: step.output.result });
          const op = step.operation, out = step.output as unknown as JsonObject;
          const expected = op.kind === 'focus' ? { kind: 'containment', path: op.path } : op.kind === 'typeComponent' ? { kind: 'type-of' }
            : op.kind === 'project' ? { kind: 'projection-of', index: op.index, field: o(out.field).name }
              : op.kind === 'expose' ? { kind: 'conversion', target: op.target, head: o(out.definition).name } : undefined;
          expect(expected).toBeDefined(); expect(end.edges[cursor - 1].relation).toMatchObject(expected!);
          if (op.kind !== 'focus') expect(Object.keys(end.edges[cursor - 1].relation).sort()).toEqual(op.kind === 'typeComponent' ? ['kind'] : op.kind === 'project' ? ['field', 'index', 'kind'] : ['head', 'kind', 'target']);
        } else {
          const annotations = step.operation.kind === 'fields' ? end.occurrences[cursor].catalogues : end.occurrences[cursor].inspections;
          expect(annotations.some(annotation => canonical(annotation.origin) === canonical(origin) && canonical(annotation.receipts) === canonical(receipts))).toBe(true);
        }
      });
      for (const occurrence of end.occurrences) {
        expect(occurrence.receipts.captureId).toBe(record.captureId);
        expect(occurrence.formations.every(formation => formation.outcome === 'accepted')).toBe(true);
        expect(occurrence.formation.status).toBe(occurrence.formations.length ? 'established' : 'unestablished');
        expect(occurrence.domain.status).toBe(occurrence.inspections.some(inspection => inspection.domain) ? 'established' : 'unestablished');
        for (const inspection of occurrence.inspections) { expect(inspection.rootOutcome).toBe('accepted'); if (inspection.domain) expect(inspection.domain.outcome).toBe('accepted'); }
      }
      // The chosen prefix read from the parent record is a skeleton prefix with the parent's own fresh receipts.
      const chosen = occurrenceProvenance(history, row.previousCaptureId, row.parentStepIndex);
      const parentRecord = row.priorAttempts.find(bundle => bundle.record.captureId === row.previousCaptureId)?.record;
      expect(chosen.prefix.route).toBe(parentRecord ? 'attempt' : 'original');
      const endSkeleton = skeleton(end), chosenSkeleton = skeleton(chosen);
      expect(canonical(endSkeleton.occurrences.slice(0, chosenSkeleton.occurrences.length))).toBe(canonical(chosenSkeleton.occurrences));
      expect(canonical(endSkeleton.edges.slice(0, chosenSkeleton.edges.length))).toBe(canonical(chosenSkeleton.edges));
      for (const item of [...chosen.occurrences, ...chosen.edges]) expect(item.receipts.captureId).toBe(parentRecord ? row.previousCaptureId : row.parent.occurrence.captureId);
    }
  }, 120000);

  it('shares inherited origins along a common prefix and keeps sibling suffixes apart', () => {
    for (const label of ['literal Rotor law', 'literal Mechanism law']) {
      const group = rows.filter(row => row.label === label);
      const body = group.find(row => row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
      const domain = group.find(row => row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piDomain']))!;
      // The domain branch backtracks from the longer six-operation sibling at step 3, not from the shared parent.
      expect(byId.get(domain.previousCaptureId)!.response.sourceDecomposition.operations).toHaveLength(6);
      expect(domain.parentStepIndex).toBe(3);
      expect(body.previousCaptureId).not.toBe(domain.previousCaptureId);
      const bodyChain = chainEnd(body), domainChain = chainEnd(domain);
      expect(skeleton(bodyChain).occurrences.slice(0, 3)).toEqual(skeleton(domainChain).occurrences.slice(0, 3));
      expect(skeleton(bodyChain).edges.slice(0, 2)).toEqual(skeleton(domainChain).edges.slice(0, 2));
      expect(bodyChain.occurrences[3].origin).toEqual({ kind: 'step', captureId: body.response.sourceDecomposition.captureId, stepIndex: 4 });
      expect(domainChain.occurrences[3].origin).toEqual({ kind: 'step', captureId: domain.response.sourceDecomposition.captureId, stepIndex: 4 });
      expect(bodyChain.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piBody'], role: { form: 'forall', operand: 'body', operandPath: ['piBody'], remainder: [] } });
      expect(domainChain.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piDomain'], binders: [], role: { form: 'forall', operand: 'domain', remainder: [] } });
      expect(bodyChain.edges[0].relation).toMatchObject({ kind: 'projection-of', index: 2 });
      expect(bodyChain.edges[1].relation).toEqual({ kind: 'type-of' });
      expect(bodyChain.occurrences[1].inspections).toEqual([]); expect(bodyChain.occurrences[1].formations).toEqual([]);
      expect(bodyChain.occurrences[0].catalogues).toHaveLength(1);
      const law = bodyChain.occurrences[2];
      expect(law.formations.map(formation => [formation.source, formation.kind])).toEqual([['typeComponent', 'proposition'], ['logical', 'proposition']]);
      expect(canonical(law.formations[0].inferredType)).toBe(canonical(law.formations[1].inferredType));
      expect(law.inspections[0]).toMatchObject({ shape: 'forall', form: 'forall', proofBinder: false });
      const binder = (bodyChain.edges[2].relation as { binders: { role: string | null; position: number; step: string }[] }).binders;
      expect(binder).toHaveLength(1); expect(binder[0]).toMatchObject({ position: 0, step: 'piBody', role: 'universal', name: a(law.pair.term)[1], kind: 'port' });
      // The abandoned suffix of the longer sibling is enumerable but never read.
      const longer = group.find(row => row.operation.kind === 'logical' && row.parentStepIndex === 4)!;
      const { history, record } = fixture(longer);
      const truncated = occurrenceProvenance(history, record.captureId, 3);
      expect(truncated.excluded).toEqual({ captureId: record.captureId, stepIndices: [4, 5] });
      expect(truncated.edges.map(edge => edge.relation.kind)).toEqual(['projection-of', 'type-of']);
      expect(truncated.occurrences[2].inspections).toHaveLength(1);
    }
  }, 120000);

  it('keeps outer roles on operand prefixes, marks the remaining descent neutral and gives candidates only under an inspected Exists', () => {
    const forallExists = containments(chainEnd(last('universal then existential')));
    expect(forallExists.map(edge => edge.relation.path)).toEqual([['piBody'], ['appArg', 'lamBody']]);
    expect(forallExists[0].relation.role).toMatchObject({ form: 'forall', operand: 'body', remainder: [] });
    expect(forallExists[0].relation.binders).toMatchObject([{ position: 0, step: 'piBody', role: 'universal' }]);
    expect(forallExists[1].relation.role).toMatchObject({ form: 'exists', operand: 'predicate', operandPath: ['appArg'], remainder: ['lamBody'] });
    const existsOccurrence = chainEnd(last('universal then existential')).occurrences[1];
    expect(forallExists[1].relation.binders).toMatchObject([{ position: 1, step: 'lamBody', role: 'candidate', name: a(a(existsOccurrence.pair.term)[2])[1], kind: 'port' }]);
    const existsForall = containments(chainEnd(last('existential then universal')));
    expect(existsForall.map(edge => edge.relation.path)).toEqual([['appArg', 'lamBody'], ['piBody']]);
    expect(existsForall[0].relation.binders).toMatchObject([{ position: 1, step: 'lamBody', role: 'candidate' }]);
    expect(existsForall[1].relation.binders).toMatchObject([{ position: 0, step: 'piBody', role: 'universal' }]);
    const owner = chainEnd(last('existential owner')), ownerEdges = containments(owner);
    expect(owner.edges.map(edge => edge.relation.kind)).toEqual(['containment', 'projection-of', 'type-of', 'containment']);
    expect(ownerEdges[0].relation).toMatchObject({ path: ['appArg', 'lamBody', 'appArg'],
      role: { form: 'exists', operand: 'predicate', operandPath: ['appArg'], remainder: ['lamBody', 'appArg'] }, binders: [{ position: 1, step: 'lamBody', role: 'candidate' }] });
    expect(ownerEdges[1].relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body' } });
    expect(owner.occurrences[2].inspections).toEqual([]); expect(owner.occurrences[2].formations).toEqual([]);
    expect(owner.occurrences[3].formations.map(formation => formation.source)).toEqual(['typeComponent', 'logical']);
    const negated = containments(chainEnd(last('negated owner')));
    expect(negated[0].relation).toMatchObject({ path: ['appArg', 'appArg', 'lamBody', 'appArg'],
      role: { form: 'not', operand: 'negated', operandPath: ['appArg'], remainder: ['appArg', 'lamBody', 'appArg'] }, binders: [{ position: 2, step: 'lamBody', role: null }] });
    const alternative = containments(chainEnd(last('alternative owner')));
    expect(alternative[0].relation).toMatchObject({ path: ['appFun', 'appArg', 'appArg', 'lamBody', 'appArg'],
      role: { form: 'or', operand: 'alternative-left', operandPath: ['appFun', 'appArg'], remainder: ['appArg', 'lamBody', 'appArg'] },
      binders: [{ position: 3, step: 'lamBody', role: null }] });
    for (const chain of [negated, alternative]) {
      const law = chain[1];
      expect(law.relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body' } });
    }
    const ordinary = chainEnd(last('ordinary function type'));
    expect(ordinary.occurrences[0].inspections[0]).toMatchObject({ shape: 'forall', formation: 'type', form: null });
    const abstract = chainEnd(last('abstract existential predicate'));
    expect(abstract.occurrences[0].inspections[0]).toMatchObject({ shape: 'standard', form: 'exists' });
    expect(abstract.edges).toEqual([]);
    for (const row of rows) for (const edge of chainEnd(row).edges) if (edge.relation.kind !== 'containment') expect(Object.keys(edge.relation)).not.toContain('role');
    // Every containment after an established inspection either matches an operand prefix with a role or is neutral; this corpus has no non-operand focus.
    let outside = 0;
    for (const row of rows) { const end = chainEnd(row); for (const edge of containments(end)) {
      const source = end.occurrences[edge.from], established = [...source.inspections].reverse().find(inspection => inspection.form !== null);
      if (!established) { expect(edge.relation.role).toBeNull(); continue; }
      const matched = established.operands.some(operand => operand.path.every((step, i) => edge.relation.path[i] === step));
      if (matched) expect(edge.relation.role).not.toBeNull(); else { outside++; expect(edge.relation.role).toBeNull(); }
    } }
    expect(outside).toBe(0);
  }, 120000);

  it('gates roles and formation on the exact accepted receipts, keeps every receipt visible and refuses to pick between conflicting formations', () => {
    const rotor = rows.filter(row => row.label === 'literal Rotor law');
    const body = rotor.find(row => row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const law = (provenance: OccurrenceProvenance) => provenance.occurrences[2];
    const roleOn = { kind: 'containment', path: ['piBody'], role: { form: 'forall', operand: 'body' } };
    const intact = mutated(body, () => {});
    expect(law(intact).formation).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(law(intact).domain).toMatchObject({ status: 'established', kind: 'type' });
    expect(law(intact).formations.map(formation => [formation.source, formation.kind, formation.outcome])).toEqual([['typeComponent', 'proposition', 'accepted'], ['logical', 'proposition', 'accepted']]);
    expect(intact.edges[2].relation).toMatchObject({ ...roleOn, binders: [{ position: 0, step: 'piBody', role: 'universal' }] });
    for (const tag of ['rejected', 'unknown'] as const) {
      const noRoot = mutated(body, value => verdict(value, 3, 1, tag));
      expect(law(noRoot).formations.map(formation => [formation.kind, formation.outcome])).toEqual([['proposition', 'accepted'], ['unestablished', tag]]);
      expect(law(noRoot).formation).toMatchObject({ status: 'established', kind: 'proposition' });
      expect(law(noRoot).inspections[0]).toMatchObject({ formation: 'unestablished', rootOutcome: tag, candidate: 'forall', form: 'forall' });
      expect(noRoot.edges[2].relation).toMatchObject({ ...roleOn, binders: [{ role: 'universal' }] });
      const noType = mutated(body, value => verdict(value, 2, 1, tag));
      expect(law(noType).formations.map(formation => [formation.kind, formation.outcome])).toEqual([['unestablished', tag], ['proposition', 'accepted']]);
      expect(law(noType).formation).toMatchObject({ status: 'established', kind: 'proposition' });
      expect(noType.edges[2].relation).toMatchObject({ ...roleOn, binders: [{ role: 'universal' }] });
      const neither = mutated(body, value => { verdict(value, 2, 1, tag); verdict(value, 3, 1, tag); });
      expect(law(neither).formation).toEqual({ status: 'unestablished' });
      expect(law(neither).formations).toHaveLength(2);
      expect(law(neither).inspections[0]).toMatchObject({ candidate: 'forall', form: null, proofBinder: false });
      expect(neither.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piBody'], role: null, binders: [{ position: 0, step: 'piBody', role: null }] });
      expect(neither.occurrences.map(occurrence => occurrence.origin)).toEqual(intact.occurrences.map(occurrence => occurrence.origin));
      expect(neither.edges.map(edge => edge.origin)).toEqual(intact.edges.map(edge => edge.origin));
    }
    const contextOnly = mutated(body, value => verdict(value, 3, 0, 'rejected'));
    expect(law(contextOnly).inspections[0]).toMatchObject({ formation: 'proposition', rootOutcome: 'accepted', form: 'forall' });
    // Domain evidence comes only from the logical domain receipt: the operand role survives, the binder reading does not.
    const noDomain = mutated(body, value => verdict(value, 3, 3, 'rejected'));
    expect(law(noDomain).domain).toEqual({ status: 'unestablished' });
    expect(law(noDomain).inspections[0]).toMatchObject({ form: 'forall', proofBinder: false, domain: { formation: 'unestablished', outcome: 'rejected' } });
    expect(noDomain.edges[2].relation).toMatchObject({ ...roleOn, binders: [{ position: 0, step: 'piBody', role: null }] });
    // Two accepted formations that disagree are a conflict: both stay visible, nothing is chosen, no role attaches.
    const conflict = mutated(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); });
    expect(law(conflict).formation).toEqual({ status: 'conflicting' });
    expect(law(conflict).formations.map(formation => [formation.source, formation.kind, formation.outcome])).toEqual([['typeComponent', 'proposition', 'accepted'], ['logical', 'type', 'accepted']]);
    expect(law(conflict).inspections[0]).toMatchObject({ formation: 'type', rootOutcome: 'accepted', candidate: 'forall', form: null, proofBinder: false });
    expect(conflict.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piBody'], role: null, binders: [{ role: null }] });
    expect(conflict.edges.map(edge => edge.origin)).toEqual(intact.edges.map(edge => edge.origin));
  }, 120000);

  it('reads proof binders and implications only from a domain receipt at literal Sort zero (saved-data mutation; the corpus has no such case)', () => {
    const rotor = rows.filter(row => row.label === 'literal Rotor law');
    const body = rotor.find(row => row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const proof = mutated(body, (value, priors) => { setDomain(priors[3], 3, SORT_ZERO); setDomain(value, 3, SORT_ZERO); });
    expect(proof.occurrences[2].domain).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(proof.occurrences[2].inspections[0]).toMatchObject({ form: 'forall', proofBinder: true, bodyUsesBinder: true, domain: { formation: 'proposition', outcome: 'accepted' } });
    expect(proof.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piBody'], role: { form: 'forall', operand: 'body' }, binders: [{ position: 0, step: 'piBody', role: 'proof' }] });
    const arrow = last('ordinary function type');
    const genuine = mutated(arrow, () => {});
    expect(genuine.occurrences[0].inspections[0]).toMatchObject({ formation: 'type', form: null, proofBinder: false, bodyUsesBinder: false });
    const implies = mutated(arrow, value => { setFormation(value, 0, SORT_ZERO); setDomain(value, 0, SORT_ZERO); });
    expect(implies.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(implies.occurrences[0].inspections[0]).toMatchObject({ formation: 'proposition', candidate: 'forall', form: 'implies', proofBinder: true, bodyUsesBinder: false, domain: { formation: 'proposition', outcome: 'accepted' } });
    const impliesNoDomain = mutated(arrow, value => { setFormation(value, 0, SORT_ZERO); setDomain(value, 0, SORT_ZERO); verdict(value, 0, 3, 'rejected'); });
    expect(impliesNoDomain.occurrences[0].inspections[0]).toMatchObject({ form: 'forall', proofBinder: false, domain: { formation: 'unestablished', outcome: 'rejected' } });
    const impliesNoRoot = mutated(arrow, value => { setFormation(value, 0, SORT_ZERO); setDomain(value, 0, SORT_ZERO); verdict(value, 0, 1, 'unknown'); });
    expect(impliesNoRoot.occurrences[0]).toMatchObject({ formation: { status: 'unestablished' }, domain: { status: 'established', kind: 'proposition' } });
    expect(impliesNoRoot.occurrences[0].inspections[0]).toMatchObject({ form: null, proofBinder: false });
    // An established general sort keeps the neutral binder reading: the operand role stays, the binder role is null.
    const general = mutated(body, (value, priors) => { setDomain(priors[3], 3, SORT_GENERAL); setDomain(value, 3, SORT_GENERAL); });
    expect(general.occurrences[2].domain).toMatchObject({ status: 'established', kind: 'general-sort' });
    expect(general.occurrences[2].inspections[0]).toMatchObject({ form: 'forall', proofBinder: false, domain: { formation: 'general-sort', outcome: 'accepted' } });
    expect(general.edges[2].relation).toMatchObject({ kind: 'containment', path: ['piBody'], role: { form: 'forall', operand: 'body' }, binders: [{ position: 0, step: 'piBody', role: null }] });
  }, 120000);

  it('keeps a non-operand focus after an established inspection neutral (saved-data splice)', () => {
    // The row whose single new operation is the focus after the Not inspection.
    const row = rows.find(row => row.label === 'negated owner' && row.operation.kind === 'focus' && row.parentStepIndex === 0)!;
    const spliced = mutated(row, value => spliceFocus(value, 1, ['appFun'], ['forallE', name('a'), SORT_ZERO, SORT_ZERO, 'default']));
    expect(spliced.occurrences[0].inspections[0]).toMatchObject({ form: 'not', candidate: 'not' });
    expect(spliced.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(spliced.edges).toHaveLength(1);
    expect(spliced.edges[0].relation).toEqual({ kind: 'containment', path: ['appFun'], binders: [], role: null });
    expect(a(spliced.occurrences[1].pair.term)[1]).toEqual(name('Not'));
  }, 120000);

  it('unions domain evidence over repeated inspections of one occurrence with distinct inherited origins (saved-data construction)', () => {
    const matches = rows.filter(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && row.parentStepIndex === 3 && canonical(row.operation.path) === canonical(['piBody']));
    expect(matches).toHaveLength(1);
    const row = matches[0];
    const parentId = row.previousCaptureId;
    const law = (provenance: OccurrenceProvenance) => provenance.occurrences[2];
    const intact = secondInspection(row, () => {});
    expect(law(intact.child).inspections.map(inspection => inspection.origin)).toEqual([
      { kind: 'step', captureId: parentId, stepIndex: 3 }, { kind: 'step', captureId: row.response.sourceDecomposition.captureId, stepIndex: 4 }]);
    expect(law(intact.child).inspections.map(inspection => inspection.receipts)).toEqual([
      { captureId: row.response.sourceDecomposition.captureId, start: 11, count: 4 }, { captureId: row.response.sourceDecomposition.captureId, start: 15, count: 4 }]);
    expect(law(intact.child).domain).toMatchObject({ status: 'established', kind: 'type' });
    expect(intact.grand.edges[2].relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body', inspection: 1 }, binders: [{ role: 'universal' }] });
    const conflicting = secondInspection(row, value => setDomain(value, 4, SORT_ZERO));
    expect(law(conflicting.child).domain).toEqual({ status: 'conflicting' });
    expect(law(conflicting.child).inspections.map(inspection => [inspection.domain!.formation, inspection.domain!.outcome])).toEqual([['type', 'accepted'], ['proposition', 'accepted']]);
    expect(law(conflicting.child).inspections.every(inspection => inspection.form === 'forall' && !inspection.proofBinder)).toBe(true);
    expect(conflicting.grand.edges[2].relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body' }, binders: [{ position: 0, step: 'piBody', role: null }] });
    const recovered = secondInspection(row, value => { verdict(value, 3, 3, 'rejected'); setDomain(value, 4, SORT_ZERO); });
    expect(law(recovered.child).domain).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(law(recovered.child).inspections.map(inspection => [inspection.domain!.formation, inspection.domain!.outcome, inspection.proofBinder])).toEqual([['unestablished', 'rejected', true], ['proposition', 'accepted', true]]);
    expect(recovered.grand.edges[2].relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body' }, binders: [{ position: 0, step: 'piBody', role: 'proof' }] });
    expect(recovered.grand.occurrences.map(occurrence => occurrence.origin)).toEqual(intact.grand.occurrences.map(occurrence => occurrence.origin));
  }, 120000);

  it('gives a candidate role only while the Exists inspection itself is established', () => {
    const row = last('universal then existential');
    const intact = mutated(row, () => {});
    expect(containments(intact)[1].relation).toMatchObject({ path: ['appArg', 'lamBody'], role: { form: 'exists', operand: 'predicate' }, binders: [{ position: 1, role: 'candidate' }] });
    for (const tag of ['rejected', 'unknown'] as const) {
      const noExists = mutated(row, value => verdict(value, 2, 1, tag));
      expect(noExists.occurrences[1].formation).toEqual({ status: 'unestablished' });
      expect(noExists.occurrences[1].inspections[0]).toMatchObject({ candidate: 'exists', rootOutcome: tag, form: null });
      expect(containments(noExists)[1].relation).toMatchObject({ path: ['appArg', 'lamBody'], role: null, binders: [{ position: 1, step: 'lamBody', role: null }] });
      expect(containments(noExists)[0].relation).toMatchObject({ path: ['piBody'], role: { form: 'forall', operand: 'body' } });
      expect(noExists.edges.map(edge => edge.origin)).toEqual(intact.edges.map(edge => edge.origin));
    }
  }, 120000);
});
