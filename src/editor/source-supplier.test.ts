import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import type { HeadExposureBundle } from './source-history';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionHistory, type DecompositionOperation, type SourceDecompositionBundle } from './source-decomposition';
import { supplierReading, type SupplierReading } from './source-supplier';
import { a, append, c, clone, close, focus, id, initial, name, o, record, seedCheckpoint } from './source-decomposition-chain.test-fixtures';

const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
function argumentFocus(history: DecompositionHistory, attempt: number) {
  const result = seedCheckpoint(history).candidate.result;
  return record(history, { kind: 'focus', path: ['appArg'] }, focus({ home: result.home, term: a(result.term)[2], type: c('Nat') }), { id: attempt });
}

/** Every object and array reachable from the value, with its path, that is not frozen. */
function unfrozen(value: unknown, path = 'reading', found: string[] = []): string[] {
  if (value === null || typeof value !== 'object') return found;
  if (!Object.isFrozen(value)) found.push(path);
  for (const [key, child] of Object.entries(value)) unfrozen(child, `${path}.${key}`, found);
  return found;
}
/** Every distinct object and array reachable from the value. */
function reachable(value: unknown, found: object[] = []): object[] {
  if (value === null || typeof value !== 'object' || found.includes(value)) return found;
  found.push(value);
  for (const child of Object.values(value)) reachable(child, found);
  return found;
}
/** Attempt to change, extend and shrink every structure the supplier module created, at every depth. Each attempt must throw, and
 * the reading must stay byte-identical to itself and to a fresh derivation. The provenance belongs to the accepted module. */
function expectImmutable(reading: SupplierReading, fresh: () => SupplierReading) {
  expect(unfrozen(reading)).toEqual([]);
  const before = canonical(reading), created = reachable([reading.occurrences, reading.links, reading.parts]).slice(1);
  expect(created.length).toBeGreaterThanOrEqual(3 + reading.occurrences.length * 2 + reading.links.length * 5 + reading.parts.length * 3);
  let attempts = 0;
  const refused = (attempt: () => void) => { expect(attempt).toThrow(TypeError); attempts++; };
  for (const target of [reading as object, ...created]) {
    if (Array.isArray(target)) {
      refused(() => { target.push(null); }); refused(() => { target.length = 0; });
      if (target.length > 0) { refused(() => { target[0] = null; }); refused(() => { target.pop(); }); }
    } else {
      const record = target as Record<string, unknown>, keys = Object.keys(record);
      expect(keys.length).toBeGreaterThan(0);
      for (const key of keys) { refused(() => { record[key] = 'changed'; }); refused(() => { delete record[key]; }); }
      refused(() => { record.added = true; });
    }
  }
  expect(attempts).toBeGreaterThan(created.length * 2);
  expect(canonical(reading)).toBe(before); expect(canonical(fresh())).toBe(before);
}
/** Compact view of a link's judgement groups: inferred type, whether the module reads it, and each receipt once with its outcome. */
const SORT_ZERO: JsonValue = ['sort', ['zero']];
const sortTitle = (type: JsonValue) => canonical(type) === canonical(SORT_ZERO) ? 'Sort 0' : canonical(type) === canonical(['sort', ['succ', ['zero']]]) ? 'Sort 1'
  : canonical(type) === canonical(['sort', ['succ', ['succ', ['zero']]]]) ? 'Sort 2' : canonical(type);
const groups = (reading: SupplierReading, link = 0) => reading.links[link].formation.judgements.map(judgement =>
  `${sortTitle(judgement.inferredType)}${judgement.established ? ' established' : ''}: ${judgement.receipts.map(receipt => `${receipt.source}#${receipt.index} ${receipt.outcome}${receipt.alsoTyping ? ' also-typing' : ''}`).join(', ')}`);
/** Compact view of a link's ordered home: name, kind and where the entry comes from. */
const homeOf = (reading: SupplierReading, link = 0) => reading.links[link].conditions.home.map(entry => {
  const origin = entry.origin, title = String(a(entry.name)[2]);
  return `${entry.position} ${entry.kind} ${title}: ${origin.kind === 'context' ? `context ${origin.declaration} ${origin.declarationKind}` : origin.kind === 'selection' ? 'selection' : `entered edge ${origin.edge} binder ${origin.binder} ${origin.role ?? 'no role'}`}`;
});
/** The home listed in a link's conditions is the source's exact home, entry for entry, with every origin accounted for. */
function expectExactHome(history: DecompositionHistory, reading: SupplierReading) {
  // The expected declarations come from the prepared frame of the parent snapshot, a source the implementation does not read.
  const prepared = history.snapshot.prepared;
  if (prepared.status !== 'available') throw Error('missing prepared frame');
  const context = { arity: prepared.frame.originalDeclarations.length, originalDeclarations: prepared.frame.originalDeclarations };
  // The original occurrence's binding, and the parent snapshot's own check record where it was kept, carry the same declarations.
  if (history.occurrence.checking.status !== 'captured') throw Error('missing original occurrence');
  expect(canonical(history.occurrence.checking.binding.context.originalDeclarations)).toBe(canonical(context.originalDeclarations));
  if (history.snapshot.checking.status === 'captured') expect(canonical(history.snapshot.checking.binding.context)).toBe(canonical(history.occurrence.checking.binding.context));
  for (const link of reading.links) {
    const source = reading.provenance.occurrences[link.from], home = link.conditions.home, nodes: JsonValue[][] = [];
    for (let node = a(source.pair.home.telescope); node[0] !== 'nil'; node = a(node[1])) nodes.unshift(node);
    expect(home.map(entry => entry.position)).toEqual(nodes.map((_, position) => position));
    expect(nodes.every(node => node[0] === 'port' || node[0] === 'letE')).toBe(true);
    expect(home.map(entry => [entry.kind, canonical(entry.name)])).toEqual(nodes.map(node => [node[0] === 'port' ? 'port' : 'let', canonical(node[0] === 'port' ? o(node[2]).name : node[2])]));
    const captured = home.filter(entry => entry.origin.kind === 'context'), entered = home.filter(entry => entry.origin.kind === 'entered');
    expect(captured.map(entry => entry.position)).toEqual(context.originalDeclarations.map((_, position) => position));
    captured.forEach((entry, position) => expect(entry.origin).toEqual({ kind: 'context', declaration: position, declarationKind: context.originalDeclarations[position].kind }));
    const binders = reading.provenance.edges.slice(0, link.from).flatMap((edge, position) => edge.relation.kind === 'containment'
      ? edge.relation.binders.map((binder, order) => ({ kind: 'entered', edge: position, binder: order, role: binder.role })) : []);
    expect(entered.map(entry => entry.origin)).toEqual(binders);
    expect(link.conditions.binders).toEqual(reading.provenance.edges.slice(0, link.from).flatMap(edge => edge.relation.kind === 'containment' ? edge.relation.binders : []));
    expect(home.filter(entry => entry.origin.kind === 'selection')).toHaveLength(reading.provenance.occurrences[0].pair.home.arity - context.arity);
    expect(home).toHaveLength(source.pair.home.arity);
  }
}
/** The typing receipt of every occurrence closes exactly that occurrence's own term and type over its own home, in the record
 * the prefix was read from, and is named as the component of the selection or of the operation that produced the occurrence. */
function expectExactTyping(history: DecompositionHistory, reading: SupplierReading) {
  for (const item of reading.occurrences) {
    const occurrence = reading.provenance.occurrences[item.index], typing = item.typing;
    const holder = [history.occurrence, history.seed?.record, ...history.attempts.map(entry => entry.record)].find(candidate => candidate?.captureId === typing.captureId)!;
    if (holder.checking.status !== 'captured') throw Error('missing checking');
    const recorded = holder.checking.checks[typing.index], declaration = recorded.declaration as unknown as JsonObject;
    expect(typing.captureId).toBe(occurrence.receipts.captureId); expect(typing.captureId).toBe(reading.provenance.prefix.previousCaptureId);
    expect(typing.index).toBe(occurrence.receipts.start + (item.index === 0 ? 5 : 1));
    expect(recorded.outcome.tag).toBe(typing.outcome); expect(recorded.label).toBe('component');
    // The audit is the record's own entry for the same receipt, by value.
    const audit = holder.checking.audits[typing.index];
    expect(audit.checkId).toBe(recorded.id); expect(canonical(typing.audit)).toBe(canonical(audit.result));
    expect(typing.audit.tag === 'available').toBe(typing.outcome === 'accepted');
    expect(canonical(declaration.value)).toBe(canonical(close(occurrence.pair.home.telescope as JsonValue, occurrence.pair.term as JsonValue, 'lam')));
    expect(canonical(declaration.type)).toBe(canonical(close(occurrence.pair.home.telescope as JsonValue, occurrence.pair.type as JsonValue, 'forallE')));
    const tail = (count: number) => { const parts: string[] = []; for (let node = declaration.name as JsonValue; Array.isArray(node) && node[0] === 'str' && parts.length < count; node = node[1]) parts.unshift(String(node[2])); return parts; };
    const relation = item.index === 0 ? null : reading.provenance.edges[item.index - 1].relation.kind;
    expect(relation === null ? tail(3) : tail(2)).toEqual(relation === null ? ['extraction', 'selected', 'component']
      : [{ containment: 'focus', 'type-of': 'typeComponent', 'projection-of': 'project', conversion: 'result' }[relation], 'component']);
  }
}
/** Durable association check: every cited formation receipt checks exactly the target's term, in the target's home, at its group's
 * inferred type; the references are distinct; one of them is the target's own typing receipt; and the groups agree with the status. */
function expectExactJudgements(history: DecompositionHistory, reading: SupplierReading) {
  for (const link of reading.links) {
    const target = reading.provenance.occurrences[link.to], own = reading.occurrences[link.to].typing, receipts = link.formation.judgements.flatMap(judgement => judgement.receipts);
    expect(receipts.length).toBe(target.formations.length); expect(receipts.length).toBeGreaterThan(0);
    expect(receipts.map(receipt => receipt.entry).sort((left, right) => left - right)).toEqual(target.formations.map((_, position) => position));
    expect(new Set(receipts.map(receipt => `${receipt.captureId}#${receipt.index}`)).size).toBe(receipts.length);
    expect(new Set(link.formation.judgements.map(judgement => canonical(judgement.inferredType))).size).toBe(link.formation.judgements.length);
    expect(receipts.filter(receipt => receipt.alsoTyping)).toEqual([expect.objectContaining({ source: 'typeComponent', captureId: own.captureId, index: own.index, outcome: own.outcome })]);
    expect(own.alsoFormation).toBe(true);
    for (const judgement of link.formation.judgements) for (const receipt of judgement.receipts) {
      const holder = [history.occurrence, history.seed?.record, ...history.attempts.map(entry => entry.record)].find(item => item?.captureId === receipt.captureId)!;
      if (holder.checking.status !== 'captured') throw Error('missing checking');
      const recorded = holder.checking.checks[receipt.index], declaration = recorded.declaration as unknown as JsonObject;
      expect(recorded.outcome.tag).toBe(receipt.outcome);
      expect(target.formations[receipt.entry]).toMatchObject({ source: receipt.source, outcome: receipt.outcome, receipts: receipt.span });
      expect(canonical(target.formations[receipt.entry].inferredType)).toBe(canonical(judgement.inferredType));
      if (receipt.alsoTyping) expect(canonical(judgement.inferredType)).toBe(canonical(target.pair.type));
      expect(receipt.span.captureId).toBe(receipt.captureId); expect(receipt.index).toBe(receipt.span.start + 1);
      expect(canonical(declaration.value)).toBe(canonical(close(target.pair.home.telescope as JsonValue, target.pair.term as JsonValue, 'lam')));
      expect(canonical(declaration.type)).toBe(canonical(close(target.pair.home.telescope as JsonValue, judgement.inferredType, 'forallE')));
    }
    const accepted = link.formation.judgements.filter(judgement => judgement.receipts.some(receipt => receipt.outcome === 'accepted'));
    expect(link.formation.judgements.filter(judgement => judgement.established)).toEqual(link.formation.status === 'established' ? accepted : []);
    expect(accepted.length).toBe(link.formation.status === 'established' ? 1 : link.formation.status === 'conflicting' ? Math.max(2, accepted.length) : 0);
    if (target.formation.status === 'established') expect(canonical(accepted[0].inferredType)).toBe(canonical(target.formation.inferredType));
  }
}

describe('supplier reading, constructed controls', () => {
  it('locates every typing receipt at the position the accepted span names, on every route', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1));
    const reading = supplierReading(history, id(1), 1);
    expect(reading.occurrences.map(occurrence => occurrence.typing)).toEqual([
      { captureId: id(1), index: 5, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: false },
      { captureId: id(1), index: 7, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: false },
      { captureId: id(1), index: 10, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: false }]);
    expect(reading.links).toEqual([]);
    expect(reading.parts).toEqual([{ occurrence: 2, root: 1, supplier: null, tier: 'within-expression', path: ['appArg'],
      frames: [{ kind: 'containment', edge: 1, path: ['appArg'], role: null, binders: [] }] }]);
    expect(reading.occurrences[2].lineage).toEqual([{ kind: 'conversion', edge: 0 }, { kind: 'containment', edge: 1, path: ['appArg'], role: null, binders: [] }]);
    const seed = supplierReading(history, history.seed!.record.captureId, 0);
    expect(seed.occurrences.map(occurrence => occurrence.typing)).toEqual([
      { captureId: history.seed!.record.captureId, index: 5, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: false },
      { captureId: history.seed!.record.captureId, index: 7, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: false }]);
    const original = supplierReading(history, history.occurrence.captureId, 0);
    expect(original.occurrences).toHaveLength(1); expect(original.occurrences[0].typing).toMatchObject({ captureId: history.occurrence.captureId, index: 5, outcome: 'accepted' });
    expect(canonical(supplierReading(history, id(1), 1))).toBe(canonical(reading));
    expect(Object.isFrozen(reading)).toBe(true);
    // Every newly created structure is frozen in depth; nested mutation throws and changes neither this reading nor a fresh derivation.
    expectImmutable(reading, () => supplierReading(history, id(1), 1));
    expectImmutable(seed, () => supplierReading(history, history.seed!.record.captureId, 0));
    expect(() => supplierReading(clone(history as unknown as JsonObject) as unknown as DecompositionHistory, id(1), 1)).toThrow(/validated object/);
  });
});

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  seed: HeadExposureBundle | null; priorAttempts: SourceDecompositionBundle[]; operation: DecompositionOperation;
  previousCaptureId: string; parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: SourceSnapshotOrigin; sourceDecomposition: SourceDecompositionBundle['record'] };
}
const load = (variable: string): Row[] => { const path = process.env[variable]; return path ? JSON.parse(readFileSync(path, 'utf8')) : []; };
const logical = load('DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES'), acceptance = load('DEFINOGRAPH_ACCEPTANCE_FIXTURES');
const SORT_ONE: JsonValue = ['sort', ['succ', ['zero']]];
const renumber = (check: JsonObject) => {
  const checks = a(check.checks), audits = a(check.audits); let environment = 0;
  checks.forEach((item, index) => {
    const receipt = o(item), audit = o(audits[index]); receipt.envBefore = environment;
    if (o(receipt.outcome).tag === 'accepted') { environment++; audit.result = { tag: 'available', axioms: [] }; }
    else audit.result = { tag: 'unavailable', reason: 'declaration was not installed' };
    receipt.envAfter = environment; audit.environment = environment;
  });
  check.environmentSnapshotCount = environment + 1;
};
const verdictAt = (value: JsonObject, index: number, tag: 'rejected' | 'unknown') => {
  const check = o(value.checking);
  o(a(check.checks)[index]).outcome = tag === 'unknown' ? { tag: 'unknown', message: 'timeout control' } : { tag: 'rejected', kind: 'notConvertible' };
  renumber(check);
};
const verdict = (value: JsonObject, stepIndex: number, local: number, tag: 'rejected' | 'unknown') => verdictAt(value, Number(o(a(o(value.checking).steps)[stepIndex]).receiptStart) + local, tag);
const setFormation = (value: JsonObject, stepIndex: number, sort: JsonValue) => {
  const check = o(value.checking), step = o(a(check.steps)[stepIndex]), output = o(step.output);
  o(output.formation).inferredType = sort;
  const replayed = a(o(check.binding).expectedHistory)[stepIndex];
  if (replayed !== undefined) o(o(o(replayed).candidate).formation).inferredType = sort;
  const arity = Number(o(o(output.result).home).arity), index = Number(step.receiptStart) + 1, receipt = o(a(check.checks)[index]), decl = clone(o(receipt.declaration));
  const rebody = (node: JsonValue, depth: number): JsonValue => {
    if (depth === 0) return sort;
    const n = a(node);
    return n[0] === 'letE' ? [n[0], n[1], n[2], n[3], rebody(n[4], depth - 1), n[5]] : [n[0], n[1], n[2], rebody(n[3], depth - 1), n[4]];
  };
  decl.type = rebody(decl.type, arity);
  receipt.declaration = decl; o(receipt.subject).declaration = decl; o(a(check.audits)[index]).subject = decl;
};
/** Validated history of a row after optional saved-data mutations of the record and its prior attempts; reading at the chain end unless a prefix is given. */
function historyOf(row: Row, mutate: (record: JsonObject, priors: JsonObject[]) => void = () => {}, parentSnapshot: SourceSnapshot = row.parent.snapshot) {
  const priors = row.priorAttempts.map(bundle => clone(bundle.record as unknown as JsonObject));
  const value = clone(row.response.sourceDecomposition as unknown as JsonObject);
  mutate(value, priors);
  const prior = validateDecompositionHistory({ snapshot: parentSnapshot, occurrence: row.parent.occurrence, seed: row.seed,
    attempts: row.priorAttempts.map((bundle, i) => ({ snapshot: bundle.snapshot, record: priors[i] })) });
  const recordValue = validateSourceDecomposition(value, row.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record: recordValue }] });
  return { history, record: recordValue, snapshot: row.response.sourceSnapshot };
}
function read(row: Row, mutate: (record: JsonObject, priors: JsonObject[]) => void = () => {}, prefix?: number): SupplierReading {
  const { history, record: recordValue } = historyOf(row, mutate);
  return supplierReading(history, recordValue.captureId, prefix ?? recordValue.operations.length - 1);
}
/** Append a second logical inspection of the same occurrence to a real saved chain that ends in a logical step, as a new attempt.
 * A construction over a real prefix, not a native capture: the new step's receipts repeat the recorded logical step's declarations
 * under the new step's names, and the whole history passes the production validators. */
function appendLogical(row: Row, attempt: number, mutate: (record: JsonObject, stepIndex: number) => void = () => {}, mutateEarlier: (priors: JsonObject[]) => void = () => {}) {
  // Saved-data changes of an earlier step are applied to the chain end and to every earlier attempt that holds the step, so the replay stays consistent.
  const base = historyOf(row, (record, priors) => mutateEarlier([...priors, record])), old = clone(base.record as unknown as JsonObject), value = clone(old), capture = id(attempt), previous = String(old.captureId);
  const index = a(value.operations).length, earlier = index - 1;
  const rename = (node: JsonValue): JsonValue => Array.isArray(node) ? node.map(rename) : node === previous ? capture : node;
  const restep = (node: JsonValue): JsonValue => Array.isArray(node) ? node.map(restep) : node === `step${earlier}` ? `step${index}` : node;
  const renameChecks = (checking: JsonObject) => a(checking.checks).forEach((item, position) => {
    const receipt = o(item), declaration = clone(o(receipt.declaration));
    declaration.name = rename(declaration.name); declaration.all = a(declaration.all).map(rename);
    receipt.declaration = declaration; o(receipt.subject).declaration = declaration; o(receipt.subject).attempt = capture; o(a(checking.audits)[position]).subject = declaration;
  });
  value.captureId = capture; value.previousCaptureId = previous; value.parentStepIndex = earlier;
  const checking = o(value.checking), binding = o(checking.binding), last = o(a(checking.steps)[earlier]);
  expect(o(last.operation).kind).toBe('logical');
  binding.attempt = capture; binding.declarationPrefix = rename(binding.declarationPrefix);
  binding.expectedHistory = a(o(old.checking).steps).map(item => { const candidate = clone(o(o(item).output)); delete candidate.checking; return { operation: o(item).operation, input: o(item).input, candidate }; });
  a(value.operations).push({ kind: 'logical' }); binding.operations = clone(value.operations);
  a(checking.steps).forEach(item => { o(item).replay = 'matched'; });
  renameChecks(checking);
  const start = a(checking.checks).length, count = Number(last.receiptCount);
  for (let local = 0; local < count; local++) {
    const receipt = clone(o(a(checking.checks)[Number(last.receiptStart) + local])), declaration = clone(o(receipt.declaration));
    declaration.name = restep(declaration.name); declaration.all = a(declaration.all).map(restep);
    receipt.id = start + local; receipt.declaration = declaration; receipt.subject = { ...o(receipt.subject), sequence: start + local, declaration };
    a(checking.checks).push(receipt);
    a(checking.audits).push({ ...clone(o(a(checking.audits)[Number(last.receiptStart) + local])), checkId: start + local, subject: declaration });
  }
  a(checking.steps).push({ ...clone(last), index, operation: { kind: 'logical' }, input: clone(o(last.output).result), receiptStart: start, receiptCount: count, replay: 'new' });
  renumber(checking);
  mutate(value, index);
  const snapshot = clone(base.snapshot as unknown as JsonObject), snapshotChecking = o(snapshot.checking);
  o(snapshotChecking.binding).attempt = capture; o(snapshotChecking.binding).declarationPrefix = rename(o(snapshotChecking.binding).declarationPrefix);
  renameChecks(snapshotChecking);
  const recordValue = validateSourceDecomposition(value, snapshot as unknown as SourceSnapshot, base.history);
  const history = validateDecompositionHistory({ ...base.history, attempts: [...base.history.attempts, { snapshot: snapshot as unknown as SourceSnapshot, record: recordValue }] });
  return { history, record: recordValue, index, reading: supplierReading(history, capture, index) };
}
/** Append one type-component step to the end of a real saved chain as a new attempt. The result is a construction over a real
 * prefix, not a native capture: both receipts of the new step are rebuilt from the exact context and the whole history passes
 * the production validators. `mutate` may change the new record before validation (saved-data controls). */
function appendTypeComponent(row: Row, attempt: number, mutate: (record: JsonObject, stepIndex: number) => void = () => {}) {
  const base = historyOf(row), old = clone(base.record as unknown as JsonObject), value = clone(old), capture = id(attempt), previous = String(old.captureId);
  const rename = (node: JsonValue): JsonValue => Array.isArray(node) ? node.map(rename) : node === previous ? capture : node;
  const renameChecks = (checking: JsonObject) => a(checking.checks).forEach((item, index) => {
    const receipt = o(item), declaration = clone(o(receipt.declaration));
    declaration.name = rename(declaration.name); declaration.all = a(declaration.all).map(rename);
    receipt.declaration = declaration; o(receipt.subject).declaration = declaration; o(receipt.subject).attempt = capture; o(a(checking.audits)[index]).subject = declaration;
  });
  value.captureId = capture; value.previousCaptureId = previous; value.parentStepIndex = a(old.operations).length - 1;
  const checking = o(value.checking), binding = o(checking.binding);
  binding.attempt = capture; binding.declarationPrefix = rename(binding.declarationPrefix);
  binding.expectedHistory = a(o(old.checking).steps).map(item => { const candidate = clone(o(o(item).output)); delete candidate.checking; return { operation: o(item).operation, input: o(item).input, candidate }; });
  const input = clone(o(o(a(checking.steps).at(-1)).output).result) as unknown as { home: { telescope: JsonValue }; term: JsonValue; type: JsonValue };
  expect(input.type).toEqual(['sort', ['zero']]);
  const result = { home: input.home, term: input.type, type: SORT_ONE };
  const operation = { kind: 'typeComponent' }, index = a(value.operations).length, start = a(checking.checks).length;
  a(value.operations).push(operation); binding.operations = clone(value.operations);
  a(checking.steps).forEach(item => { o(item).replay = 'matched'; });
  renameChecks(checking);
  const stepPrefix = name('typeComponent', name(`step${index}`, binding.declarationPrefix));
  for (const label of ['context', 'component']) {
    const component = label === 'component', declarationName = name(label, stepPrefix), local = component ? 1 : 0;
    const term: JsonValue = component ? result.term : ['const', name('intro', name('True')), []], type: JsonValue = component ? result.type : ['const', name('True'), []];
    const declaration: JsonObject = { kind: component ? 'defnDecl' : 'thmDecl', name: declarationName, levelParams: clone(o(o(a(checking.checks)[0]).declaration).levelParams),
      type: close(result.home.telescope, type, 'forallE'), value: close(result.home.telescope, term, 'lam'), all: [declarationName], ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
    const receipt = clone(o(a(checking.checks)[local]));
    receipt.id = start + local; receipt.label = label; receipt.displayLabel = label; receipt.declaration = declaration;
    receipt.subject = { attempt: capture, pair: receipt.pair, sequence: receipt.id, target: label, declaration }; receipt.outcome = { tag: 'accepted' };
    a(checking.checks).push(receipt);
    a(checking.audits).push({ checkId: receipt.id, subject: declaration, environment: 0, category: 'declarationCheck', result: { tag: 'available', axioms: [] } });
  }
  a(checking.steps).push({ index, operation, input: input as unknown as JsonValue, output: { status: 'candidate', result: result as unknown as JsonValue, checking: { status: 'completed' } }, receiptStart: start, receiptCount: 2, replay: 'new' });
  renumber(checking);
  mutate(value, index);
  const snapshot = clone(base.snapshot as unknown as JsonObject), snapshotChecking = o(snapshot.checking);
  o(snapshotChecking.binding).attempt = capture; o(snapshotChecking.binding).declarationPrefix = rename(o(snapshotChecking.binding).declarationPrefix);
  renameChecks(snapshotChecking);
  const recordValue = validateSourceDecomposition(value, snapshot as unknown as SourceSnapshot, base.history);
  const history = validateDecompositionHistory({ ...base.history, attempts: [...base.history.attempts, { snapshot: snapshot as unknown as SourceSnapshot, record: recordValue }] });
  return { history, record: recordValue, index, reading: supplierReading(history, capture, index), fresh: () => supplierReading(history, capture, index) };
}
const last = (rows: Row[], label: string) => { const row = [...rows].reverse().find(row => row.label === label); if (!row) throw Error(`missing ${label}`); return row; };

/** A copy of a row with the recorded declaration kinds replaced in every saved copy of the captured context. */
function relabel(row: Row, kinds: string[]) {
  const copy = clone(row as unknown as JsonObject); let copies = 0;
  const visit = (node: JsonValue) => {
    if (Array.isArray(node)) node.forEach(visit);
    else if (node !== null && typeof node === 'object') for (const [key, value] of Object.entries(node)) {
      if (key === 'originalDeclarations' && Array.isArray(value)) { copies++; value.forEach((declaration, position) => { o(declaration).kind = kinds[position]; }); }
      else visit(value);
    }
  };
  visit(copy);
  return { row: copy as unknown as Row, copies };
}
describe.skipIf(!logical.length)('supplier reading on the v3 editor corpus', () => {
  it('reads the field as the supplier of its law only with both receipts, conditional on nothing above it in the Rotor chain', () => {
    const body = logical.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const intact = read(body);
    expect(intact.links).toHaveLength(1);
    const link = intact.links[0];
    expect(link).toMatchObject({ edge: 1, from: 1, to: 2, status: 'supplier', typing: { index: 7, outcome: 'accepted', alsoFormation: false },
      formation: { status: 'established', kind: 'proposition' }, conditions: { binders: [], frames: [{ kind: 'projection-of', edge: 0 }] } });
    // The field's typing is checked over the whole home: the capture's auxiliary declaration, the owner it refers to, and an unused variable.
    // The kinds are the ones the capture recorded; nothing is classified by name and no entry is an assumption by being listed.
    expect(homeOf(intact)).toEqual(['0 port _example: context 0 auxDecl', '1 port owner: context 1 default', '2 port unused: context 2 default']);
    // Recorded kind, saved-data controls. The validators require every saved copy of the captured context to agree, but no checked
    // declaration carries a declaration kind: a saved history relabelled consistently in every copy validates, and the listing
    // follows it. So the kind is what the capture recorded, not something the kernel checked. Neither position nor name decides.
    for (const [kinds, listed] of [
      [['default', 'auxDecl', 'auxDecl'], ['0 port _example: context 0 default', '1 port owner: context 1 auxDecl', '2 port unused: context 2 auxDecl']],
      [['default', 'auxDecl', 'default'], ['0 port _example: context 0 default', '1 port owner: context 1 auxDecl', '2 port unused: context 2 default']],
      [['auxDecl', 'implDetail', 'default'], ['0 port _example: context 0 auxDecl', '1 port owner: context 1 implDetail', '2 port unused: context 2 default']]] as [string[], string[]][]) {
      const relabelled = relabel(body, kinds), { history, record: chain } = historyOf(relabelled.row);
      expect(relabelled.copies).toBe(24);
      const reading = supplierReading(history, chain.captureId, chain.operations.length - 1);
      expect(reading.links[0].status).toBe('supplier'); expect(homeOf(reading)).toEqual(listed);
      expectExactHome(history, reading);
      expect(canonical(reading.links.map(link => [link.status, link.formation, link.typing]))).toBe(canonical(intact.links.map(link => [link.status, link.formation, link.typing])));
    }
    // A relabelling of one copy only is refused by the validators before the supplier is asked: the occurrence record's own copy
    // of the context no longer equals the parent snapshot's frame. It is a control of the validators, not of the supplier.
    const exchanged = clone(body.parent.snapshot as unknown as JsonObject);
    for (const frame of [o(o(exchanged.original).frame), o(o(exchanged.prepared).frame), o(o(o(exchanged.checking).binding).context)])
      a(frame.originalDeclarations).forEach((declaration, position) => { o(declaration).kind = position === 0 ? 'default' : 'auxDecl'; });
    expect(() => historyOf(body, () => {}, exchanged as unknown as SourceSnapshot)).toThrow('checking.binding: exact constructor association differs');
    // Equal accepted type-component and logical checks: two physical receipts of one checked judgement, the first also the target's own typing receipt.
    const capture = intact.provenance.prefix.previousCaptureId;
    expect(link.formation.judgements).toEqual([{ inferredType: SORT_ZERO, established: true, receipts: [
      { entry: 0, source: 'typeComponent', captureId: capture, index: 10, span: { captureId: capture, start: 9, count: 2 }, outcome: 'accepted', alsoTyping: true },
      { entry: 1, source: 'logical', captureId: capture, index: 12, span: { captureId: capture, start: 11, count: 4 }, outcome: 'accepted', alsoTyping: false }] }]);
    expect(intact.occurrences[2].typing).toEqual({ captureId: capture, index: 10, outcome: 'accepted', audit: { tag: 'available', axioms: [] }, alsoFormation: true });
    expect(intact.links.some(link => link.from === 0)).toBe(false);
    expect(intact.parts).toEqual([{ occurrence: 3, root: 2, supplier: 1, tier: 'within-supplied-law', path: ['piBody'],
      frames: [{ kind: 'containment', edge: 2, path: ['piBody'], role: intact.provenance.edges[2].relation.kind === 'containment' ? intact.provenance.edges[2].relation.role : null,
        binders: intact.provenance.edges[2].relation.kind === 'containment' ? intact.provenance.edges[2].relation.binders : [] }] }]);
    expect(intact.parts[0].frames[0].kind === 'containment' && intact.parts[0].frames[0].binders[0].role).toBe('universal');
    // K1: projection component rejected → annotation only, no supplier; the law's formation is untouched; the body is a position within the annotation.
    const annotation = read(body, value => verdict(value, 1, 1, 'rejected'));
    expect(annotation.links[0]).toMatchObject({ status: 'annotation-only', typing: { outcome: 'rejected' }, formation: { status: 'established', kind: 'proposition' } });
    expect(annotation.parts[0]).toMatchObject({ tier: 'within-annotation', supplier: null });
    // K6: type-component receipt rejected with the logical root accepted → still a supplier. Formation rests on the accepted logical
    // receipt; the rejected type-component receipt stays listed in the same group with its outcome.
    const rootOnly = read(body, value => verdict(value, 2, 1, 'rejected'));
    expect(rootOnly.links[0]).toMatchObject({ status: 'supplier', formation: { status: 'established', kind: 'proposition' } });
    // Rejected own typing receipt and accepted logical check of the same judgement: one group, each outcome kept.
    expect(groups(rootOnly)).toEqual(['Sort 0 established: typeComponent#10 rejected also-typing, logical#12 accepted']);
    expect(rootOnly.occurrences[2].typing).toMatchObject({ outcome: 'rejected', alsoFormation: true });
    // K2: both formation receipts unknown → typed value with supplier not established; never a negative claim.
    const none = read(body, value => { verdict(value, 2, 1, 'unknown'); verdict(value, 3, 1, 'unknown'); });
    expect(none.links[0]).toMatchObject({ status: 'not-established', typing: { outcome: 'accepted' }, formation: { status: 'unestablished', kind: null } });
    expect(groups(none)).toEqual(['Sort 0: typeComponent#10 unknown also-typing, logical#12 unknown']);
    expect(none.parts[0].tier).toBe('within-annotation');
    // K7: conflicting formation → its own status.
    const conflict = read(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); });
    expect(conflict.links[0]).toMatchObject({ status: 'conflicting', formation: { status: 'conflicting', kind: null } });
    // Counterexample 1: accepted receipts of different inferred types are two judgements; neither is read and they are never one judgement.
    expect(groups(conflict)).toEqual(['Sort 0: typeComponent#10 accepted also-typing', 'Sort 1: logical#12 accepted']);
    // Counterexample 2: the own typing receipt rejected at Sort 0 beside a logical root accepted at Sort 1: a typed value, two judgements.
    const different = read(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); verdict(value, 2, 1, 'rejected'); });
    expect(different.links[0]).toMatchObject({ status: 'value-of-type', formation: { status: 'established', kind: 'type' } });
    expect(groups(different)).toEqual(['Sort 0: typeComponent#10 rejected also-typing', 'Sort 1 established: logical#12 accepted']);
    // The same with the own typing receipt unknown: unknown stays unknown and is never read as rejected.
    const unknownOwn = read(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); verdict(value, 2, 1, 'unknown'); });
    expect(unknownOwn.links[0].status).toBe('value-of-type');
    expect(groups(unknownOwn)).toEqual(['Sort 0: typeComponent#10 unknown also-typing', 'Sort 1 established: logical#12 accepted']);
    // The logical root rejected at a different type: the law stays read from the accepted type-component receipt alone.
    const rootElsewhere = read(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); verdict(value, 3, 1, 'rejected'); });
    expect(rootElsewhere.links[0]).toMatchObject({ status: 'supplier', formation: { status: 'established', kind: 'proposition' } });
    expect(groups(rootElsewhere)).toEqual(['Sort 0 established: typeComponent#10 accepted also-typing', 'Sort 1: logical#12 rejected']);
    // A single type-component receipt in both roles (the prefix ending at the type-component step): one receipt, listed once.
    const single = read(body, () => {}, 2);
    expect(single.links[0]).toMatchObject({ status: 'supplier', formation: { status: 'established', kind: 'proposition' } });
    expect(groups(single)).toEqual(['Sort 0 established: typeComponent#10 accepted also-typing']);
    expect(single.occurrences[2].typing).toMatchObject({ index: 10, outcome: 'accepted', alsoFormation: true });
    // Chosen record versus origin record. The projected field first appeared in attempt 2; its typing is read from the chosen record
    // (attempt 5), in both directions: the origin record's receipt rejected changes nothing, the chosen record's receipt rejected does.
    expect(intact.provenance.occurrences[1].origin).toMatchObject({ kind: 'step', captureId: body.priorAttempts[1].record.captureId, stepIndex: 1 });
    const originRejected = read(body, (_value, priors) => verdict(priors[1], 1, 1, 'rejected'));
    expect(originRejected.provenance.occurrences[1].origin).toEqual(intact.provenance.occurrences[1].origin);
    expect(originRejected.occurrences[1].typing).toEqual(intact.occurrences[1].typing);
    expect(originRejected.links[0]).toMatchObject({ status: 'supplier', typing: { captureId: capture, index: 7, outcome: 'accepted' } });
    expect(canonical(originRejected.links)).toBe(canonical(intact.links));
    expect(annotation.provenance.occurrences[1].origin).toEqual(intact.provenance.occurrences[1].origin);
    // A rejected declaration was not installed, so the record holds no axiom audit for it; the reason is carried as recorded.
    expect(annotation.links[0].typing).toEqual({ captureId: capture, index: 7, outcome: 'rejected', audit: { tag: 'unavailable', reason: 'declaration was not installed' }, alsoFormation: false });
    // Recorded axioms, saved-data control: the audit of the field's typing receipt lists an axiom. The list is carried as recorded
    // and changes nothing else: the same status, the same groups, the same conditions.
    const SORRY: JsonValue = ['str', ['anonymous'], 'sorryAx'], OTHER: JsonValue = ['str', ['str', ['anonymous'], 'Classical'], 'choice'];
    const withAxioms = read(body, value => { o(a(o(value.checking).audits)[7]).result = { tag: 'available', axioms: [SORRY, OTHER] }; });
    expect(withAxioms.links[0].typing).toEqual({ captureId: capture, index: 7, outcome: 'accepted', audit: { tag: 'available', axioms: [SORRY, OTHER] }, alsoFormation: false });
    expect(withAxioms.links[0].status).toBe('supplier');
    const withoutAudit = (reading: SupplierReading) => canonical({ links: reading.links.map(link => ({ ...link, typing: { ...link.typing, audit: null } })), parts: reading.parts,
      occurrences: reading.occurrences.map(item => ({ ...item, typing: { ...item.typing, audit: null } })) });
    expect(withoutAudit(withAxioms)).toBe(withoutAudit(intact)); expect(canonical(withAxioms)).not.toBe(canonical(intact));
    // The audit of another receipt is not the typing receipt's audit: axioms recorded for the context receipt beside it are not listed.
    const beside = read(body, value => { o(a(o(value.checking).audits)[6]).result = { tag: 'available', axioms: [SORRY] }; });
    expect(beside.links[0].typing.audit).toEqual({ tag: 'available', axioms: [] });
    expect(unfrozen(withAxioms)).toEqual([]); expectImmutable(withAxioms, () => read(body, value => { o(a(o(value.checking).audits)[7]).result = { tag: 'available', axioms: [SORRY, OTHER] }; }));
    // The same for the law's own receipts: the origin record of the type-component step (attempt 3) rejected, the chosen record accepted.
    const originFormationRejected = read(body, (_value, priors) => verdict(priors[2], 2, 1, 'rejected'));
    expect(groups(originFormationRejected)).toEqual(groups(intact)); expect(originFormationRejected.links[0].status).toBe('supplier');
    // A parent snapshot whose own check record is unavailable: the chain is still read, and so is the home, from the original occurrence's binding.
    const unchecked = clone(body.parent.snapshot as unknown as JsonObject);
    unchecked.checking = { status: 'unavailable', kind: 'limit', phase: 'named-source-checking', reason: 'saved-data control: the check record was not retained', attempted: true };
    const withoutRecord = historyOf(body, () => {}, unchecked as unknown as SourceSnapshot);
    expect(withoutRecord.history.snapshot.checking.status).toBe('unavailable');
    const stillRead = supplierReading(withoutRecord.history, withoutRecord.record.captureId, withoutRecord.record.operations.length - 1);
    expect(canonical(stillRead.provenance)).toBe(canonical(intact.provenance));
    expect(canonical(stillRead)).toBe(canonical(intact)); expect(homeOf(stillRead)).toEqual(homeOf(intact));
    expectExactHome(withoutRecord.history, stillRead);
    // K13: the owner's own typing does not rescue or remove the field's link.
    const ownerRejected = read(body, value => verdictAt(value, 5, 'rejected'));
    expect(ownerRejected.occurrences[0].typing).toMatchObject({ index: 5, outcome: 'rejected' });
    expect(ownerRejected.links[0].status).toBe('supplier');
    // K8: a prefix ending before the type-component step derives no link and no part.
    const short = read(body, () => {}, 1);
    expect(short.links).toEqual([]); expect(short.parts).toEqual([]); expect(short.provenance.excluded).toMatchObject({ stepIndices: [2, 3, 4] });
    // Frozen in depth on a real chain with a link and a part, in every status reached above.
    for (const reading of [intact, annotation, rootOnly, none, conflict, different, unknownOwn, rootElsewhere, single]) expect(unfrozen(reading)).toEqual([]);
    expectImmutable(intact, () => read(body)); expectImmutable(conflict, () => read(body, (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); }));
    // Every cited receipt checks exactly the target term in the target home at its group's type, in every variant above.
    const variants: ((value: JsonObject, priors: JsonObject[]) => void)[] = [() => {}, value => verdict(value, 2, 1, 'rejected'),
      (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); },
      (value, priors) => { setFormation(priors[3], 3, SORT_ONE); setFormation(value, 3, SORT_ONE); verdict(value, 2, 1, 'rejected'); }];
    for (const variant of variants) { const { history, record: chain } = historyOf(body, variant); expectExactJudgements(history, supplierReading(history, chain.captureId, chain.operations.length - 1)); }
  }, 240000);

  it('K12: a type-component step after the focused law body keeps the field-to-law reading and relates the body to its type as a typed value only', () => {
    const body = logical.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'focus' && canonical(row.operation.path) === canonical(['piBody']))!;
    const k12 = appendTypeComponent(body, 9002), reading = k12.reading, end = reading.provenance.occurrences.length - 1;
    expect(end).toBe(4);
    expect(reading.provenance.edges.map(edge => edge.relation.kind)).toEqual(['projection-of', 'type-of', 'containment', 'type-of']);
    expect(reading.links.map(link => [link.from, link.to, link.status])).toEqual([[1, 2, 'supplier'], [3, 4, 'value-of-type']]);
    // The new target is the body's type (Prop itself, a type above Prop): it is no part of the law, and the body is no specialized proof.
    expect(reading.parts.map(part => [part.occurrence, part.root, part.supplier, part.tier])).toEqual([[3, 2, 1, 'within-supplied-law']]);
    expect(reading.links[1]).toMatchObject({ typing: { captureId: id(9002), index: 16, outcome: 'accepted', alsoFormation: false }, formation: { status: 'established', kind: 'type' } });
    expect(reading.links[1].conditions.frames.map(frame => frame.kind)).toEqual(['projection-of', 'type-of', 'containment']);
    expect(reading.links[1].conditions.binders.map(binder => binder.role)).toEqual(['universal']);
    expect(homeOf(reading, 1)).toEqual([...homeOf(reading, 0), '3 port x: entered edge 2 binder 0 universal']);
    expectExactHome(k12.history, reading);
    expect(reading.occurrences[4].typing).toMatchObject({ captureId: id(9002), index: 18, outcome: 'accepted', alsoFormation: true });
    // The body's own typing receipt rejected: the appended link is a recorded annotation only; the field-to-law reading is untouched.
    const annotated = appendTypeComponent(body, 9003, (value, index) => verdict(value, index - 1, 1, 'rejected')).reading;
    expect(annotated.links.map(link => link.status)).toEqual(['supplier', 'annotation-only']);
    expect(groups(reading, 0)).toEqual(['Sort 0 established: typeComponent#10 accepted also-typing, logical#12 accepted']);
    expect(groups(reading, 1)).toEqual(['Sort 1 established: typeComponent#18 accepted also-typing']);
    expectExactJudgements(k12.history, reading);
    expectImmutable(reading, k12.fresh);
  }, 240000);

  it('splits three formation receipts of one target by the judgement each checks (two logical inspections)', () => {
    const inspected = logical.find(row => row.label === 'literal Rotor law' && row.operation.kind === 'logical' && row.parentStepIndex === 2)!;
    // Two logical inspections of the law, all three receipts accepted at Sort 0: one judgement, three receipts, still no independent confirmation.
    const agreeing = appendLogical(inspected, 9010);
    expect(agreeing.reading.provenance.occurrences[2].inspections).toHaveLength(2);
    expect(agreeing.reading.links[0]).toMatchObject({ status: 'supplier', formation: { status: 'established', kind: 'proposition' } });
    expect(groups(agreeing.reading)).toEqual(['Sort 0 established: typeComponent#10 accepted also-typing, logical#12 accepted, logical#16 accepted']);
    expectExactJudgements(agreeing.history, agreeing.reading);
    // The second inspection accepted at Sort 1: a conflict with a genuinely equal pair inside it. Two groups, none established, nothing read.
    const partial = appendLogical(inspected, 9011, (value, index) => setFormation(value, index, SORT_ONE));
    expect(partial.reading.links[0]).toMatchObject({ status: 'conflicting', formation: { status: 'conflicting', kind: null } });
    expect(groups(partial.reading)).toEqual(['Sort 0: typeComponent#10 accepted also-typing, logical#12 accepted', 'Sort 1: logical#16 accepted']);
    expectExactJudgements(partial.history, partial.reading);
    // The own typing receipt rejected at Sort 0, the first inspection accepted at Sort 0, the second at Sort 1: the rejected receipt
    // stays in the group of the judgement it checked, with its outcome, and the target is conflicting.
    const rejected = appendLogical(inspected, 9012, (value, index) => { setFormation(value, index, SORT_ONE); verdict(value, 2, 1, 'rejected'); });
    expect(rejected.reading.links[0]).toMatchObject({ status: 'conflicting', formation: { status: 'conflicting', kind: null } });
    expect(groups(rejected.reading)).toEqual(['Sort 0: typeComponent#10 rejected also-typing, logical#12 accepted', 'Sort 1: logical#16 accepted']);
    expect(rejected.reading.occurrences[2].typing).toMatchObject({ index: 10, outcome: 'rejected', alsoFormation: true });
    expectExactJudgements(rejected.history, rejected.reading);
    // Grouping is by the exact inferred type, not by its class: accepted receipts at Sort 1 and Sort 2 are both types above Prop
    // and still two judgements. The type-component receipt is rejected so that only the two logical receipts are accepted.
    const SORT_TWO: JsonValue = ['sort', ['succ', ['succ', ['zero']]]];
    const sameClass = appendLogical(inspected, 9013, (value, index) => { setFormation(value, 3, SORT_ONE); setFormation(value, index, SORT_TWO); verdict(value, 2, 1, 'rejected'); },
      priors => setFormation(priors[3], 3, SORT_ONE));
    expect(sameClass.reading.links[0]).toMatchObject({ status: 'conflicting', formation: { status: 'conflicting', kind: null } });
    expect(groups(sameClass.reading)).toEqual(['Sort 0: typeComponent#10 rejected also-typing', 'Sort 1: logical#12 accepted', 'Sort 2: logical#16 accepted']);
    expectExactJudgements(sameClass.history, sameClass.reading);
    // Types written differently stay in different groups even where they are definitionally equal: the comparison is syntactic.
    const MAX_A: JsonValue = ['sort', ['max', ['succ', ['zero']], ['succ', ['succ', ['zero']]]]], MAX_B: JsonValue = ['sort', ['max', ['succ', ['succ', ['zero']]], ['succ', ['zero']]]];
    const spelled = appendLogical(inspected, 9014, (value, index) => { setFormation(value, 3, MAX_A); setFormation(value, index, MAX_B); verdict(value, 2, 1, 'rejected'); },
      priors => setFormation(priors[3], 3, MAX_A));
    expect(spelled.reading.links[0].formation).toMatchObject({ status: 'conflicting', kind: null });
    expect(spelled.reading.links[0].formation.judgements.map(judgement => [canonical(judgement.inferredType), judgement.established, judgement.receipts.map(receipt => `${receipt.source}#${receipt.index} ${receipt.outcome}`)]))
      .toEqual([[canonical(SORT_ZERO), false, ['typeComponent#10 rejected']], [canonical(MAX_A), false, ['logical#12 accepted']], [canonical(MAX_B), false, ['logical#16 accepted']]]);
    for (const item of [agreeing, partial, rejected, sameClass, spelled]) expect(unfrozen(item.reading)).toEqual([]);
  }, 240000);

  it('keeps the same owner law conditional on its own frames under Exists, Not and Or', () => {
    const expectations: [string, string, string, string | null][] = [
      ['existential owner', 'exists', 'predicate', 'candidate'], ['negated owner', 'not', 'negated', null], ['alternative owner', 'or', 'alternative-left', null]];
    for (const [label, form, operand, binderRole] of expectations) {
      const reading = read(last(logical, label));
      const link = reading.links.find(link => link.status === 'supplier')!;
      expect(link).toMatchObject({ from: 2, to: 3 });
      const frame = link.conditions.frames.find(frame => frame.kind === 'containment')!;
      expect(frame.kind === 'containment' && frame.role).toMatchObject({ form, operand });
      expect(link.conditions.binders.map(binder => binder.role)).toEqual([binderRole]);
      expect(link.conditions.frames.map(frame => frame.kind)).toEqual(['containment', 'projection-of']);
      // A hypothetical owner is an entry of the home with the role the module reads for the binder that entered it, which may be none.
      expect(homeOf(reading, reading.links.indexOf(link))).toEqual(['0 port _example: context 0 auxDecl', `1 port owner: entered edge 0 binder 0 ${binderRole ?? 'no role'}`]);
      expect(reading.parts.find(part => part.occurrence === 4)).toMatchObject({ root: 3, supplier: 2, tier: 'within-supplied-law', path: ['piBody'] });
      expect(reading.parts.find(part => part.occurrence === 1)).toMatchObject({ root: 0, supplier: null, tier: 'within-statement' });
    }
  }, 240000);
});

describe.skipIf(!logical.length && !acceptance.length)('judgement groups on every real chain', () => {
  it('cites each formation receipt once, under the exact judgement it checks, on every prefix of every chain end', () => {
    let links = 0, several = 0, single = 0, readings = 0;
    for (const rows of [logical, acceptance]) for (const row of rows.filter((row, index) => rows[index + 1]?.label !== row.label)) {
      const { history, record: chain } = historyOf(row);
      if (chain.checking.status !== 'captured') throw Error('missing checking');
      for (const step of chain.checking.steps) {
        if (step.output.status !== 'candidate') continue;
        const reading = supplierReading(history, chain.captureId, step.index);
        expectExactJudgements(history, reading); expectExactHome(history, reading); expectExactTyping(history, reading); expect(unfrozen(reading)).toEqual([]); readings++;
        for (const link of reading.links) {
          links++;
          // Real captures never disagree with themselves: one judgement per target, of one or several receipts.
          expect(link.formation.judgements).toHaveLength(1);
          if (link.formation.judgements[0].receipts.length > 1) several++; else single++;
        }
      }
    }
    expect(readings).toBeGreaterThan(50); expect(links).toBeGreaterThan(20); expect(several).toBeGreaterThan(0); expect(single).toBeGreaterThan(0);
  }, 480000);

  it.skipIf(!acceptance.some(row => row.label === 'selection inside a binder'))('reads the typing of the selected pair from its own component, where the source and root components close a different pair', () => {
    // The original selection is a proper subterm: the three base components no longer close the same pair.
    const row = last(acceptance, 'selection inside a binder'), { history, record: chain } = historyOf(row);
    if (chain.checking.status !== 'captured') throw Error('missing checking');
    const selected = supplierReading(history, chain.captureId, chain.operations.length - 1).provenance.occurrences[0].pair;
    const closed = (index: number) => canonical((chain.checking as { checks: { declaration: JsonObject }[] }).checks[index].declaration.value);
    const own = canonical(close(selected.home.telescope as JsonValue, selected.term as JsonValue, 'lam'));
    expect(closed(5)).toBe(own); expect(closed(1)).not.toBe(own); expect(closed(3)).not.toBe(own);
    expect(chain.checking.checks.slice(0, 6).map(check => check.label)).toEqual(['context', 'component', 'context', 'component', 'context', 'component']);
    expectExactTyping(history, supplierReading(history, chain.captureId, chain.operations.length - 1));
    // Outcome level: only the selected component gates the link; the source and root components beside it do not.
    expect(read(row).links[0]).toMatchObject({ from: 0, to: 1, status: 'value-of-type', typing: { index: 5, outcome: 'accepted' } });
    for (const index of [1, 3]) expect(read(row, value => verdictAt(value, index, 'rejected')).links[0]).toMatchObject({ status: 'value-of-type', typing: { index: 5, outcome: 'accepted' } });
    expect(read(row, value => verdictAt(value, 5, 'rejected')).links[0]).toMatchObject({ status: 'annotation-only', typing: { index: 5, outcome: 'rejected' } });
  }, 240000);
});

describe.skipIf(!acceptance.length)('supplier reading on the RC3 acceptance corpus', () => {
  it('K9: a type-component step after a selected proposition relates the proposition object to its type as a typed value, never as a proof of itself', () => {
    const k9 = appendTypeComponent(last(acceptance, 'statement selected'), 9001), reading = k9.reading;
    expect(reading.provenance.occurrences).toHaveLength(2);
    expect(reading.provenance.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(reading.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'value-of-type']]);
    expect(reading.links[0]).toMatchObject({ typing: { index: 5, outcome: 'accepted', alsoFormation: false }, formation: { status: 'established', kind: 'type' } });
    expect(reading.links.some(link => link.status === 'supplier')).toBe(false); expect(reading.parts).toEqual([]);
    // A statement selected in a signature is captured with an empty context.
    expect(reading.links[0].conditions).toEqual({ home: [], binders: [], frames: [] });
    // The new step's component receipt unknown: no formation is read for the target, and no negative claim appears.
    const unknown = appendTypeComponent(last(acceptance, 'statement selected'), 9004, (value, index) => verdict(value, index, 1, 'unknown')).reading;
    expect(unknown.links[0]).toMatchObject({ status: 'not-established', formation: { status: 'unestablished', kind: null } });
    expect(groups(unknown)).toEqual(['Sort 1: typeComponent#9 unknown also-typing']);
    expect(groups(reading)).toEqual(['Sort 1 established: typeComponent#9 accepted also-typing']);
    expectExactJudgements(k9.history, reading);
    expectImmutable(reading, k9.fresh);
  }, 240000);

  it('lists a let entry of the home with its kind, entering edge and role, and reads a link below it', () => {
    // The body of a local definition is reached by entering the let; a type-component step after it gives a link whose source home has a let entry.
    const row = last(acceptance, 'local definition');
    expect(row.operation.kind).toBe('logical');
    const focused = acceptance.filter(item => item.label === 'local definition').find(item => item.operation.kind === 'focus')!;
    const below = appendTypeComponent(focused, 9020), reading = below.reading;
    expect(reading.provenance.edges.map(edge => edge.relation.kind)).toEqual(['containment', 'type-of']);
    expect(reading.links.map(link => [link.from, link.to, link.status])).toEqual([[1, 2, 'value-of-type']]);
    expect(homeOf(reading)).toEqual(['0 port _example: context 0 auxDecl', '1 let f: entered edge 0 binder 0 no role']);
    expect(reading.links[0].conditions.binders).toEqual([expect.objectContaining({ kind: 'let', step: 'letBody', role: null })]);
    expectExactHome(below.history, reading); expectExactTyping(below.history, reading); expectExactJudgements(below.history, reading);
    expectImmutable(reading, below.fresh);
  }, 240000);

  it('relates a proof term only to its own checked statement, and an ordinary value to a type above Prop', () => {
    const ascribed = read(last(acceptance, 'ascribed proof term selected'));
    expect(ascribed.links[0]).toMatchObject({ from: 0, to: 1, status: 'supplier', typing: { index: 5, outcome: 'accepted' } });
    expect(ascribed.provenance.occurrences[1].inspections[0].form).toBe('eq');
    // K3: the selected pair's own typing receipt gates the link; the other base receipts do not.
    expect(read(last(acceptance, 'ascribed proof term selected'), value => verdictAt(value, 5, 'rejected')).links[0]).toMatchObject({ status: 'annotation-only', typing: { outcome: 'rejected' } });
    for (const index of [1, 3, 4]) expect(read(last(acceptance, 'ascribed proof term selected'), value => verdictAt(value, index, 'rejected')).links[0].status).toBe('supplier');
    const bare = read(last(acceptance, 'proof term selected'));
    expect(bare.links[0]).toMatchObject({ status: 'supplier' });
    expect(bare.provenance.occurrences[1].inspections[0].form).toBe('forall');
    const value = read(last(acceptance, 'imported function applied'));
    expect(value.links[0]).toMatchObject({ status: 'value-of-type', formation: { kind: 'type' } });
    const law = read(last(acceptance, 'second law of a structure'));
    expect(law.links[0]).toMatchObject({ from: 1, to: 2, status: 'supplier', conditions: { frames: [{ kind: 'projection-of', edge: 0 }] } });
    expect(law.parts[0]).toMatchObject({ occurrence: 3, root: 2, supplier: 1, tier: 'within-supplied-law' });
    // The case was renamed in the second capture; the first corpus keeps its earlier id.
    const statement = read(last(acceptance, acceptance.some(row => row.label === 'proof binder not referenced by the body') ? 'proof binder not referenced by the body' : 'dependent proof binder'));
    expect(statement.links).toEqual([]);
    expect(statement.parts.map(part => [part.occurrence, part.root, part.tier])).toEqual([[1, 0, 'within-statement'], [2, 0, 'within-statement'], [3, 0, 'within-statement']]);
    expect(statement.parts[2].path).toEqual(['piBody', 'piBody', 'appArg', 'lamBody']);
    expect(statement.parts[2].frames.map(frame => frame.kind === 'containment' ? frame.binders.map(binder => binder.role) : null)).toEqual([['universal'], ['proof'], ['candidate']]);
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'term using a lemma proved with a placeholder'))('carries the recorded axioms of a typing receipt and never reads them for a status (real captures)', () => {
    // A lemma proved with a placeholder: the selected constant passes capture, its typing check is accepted, and its audit records the axiom.
    const claimed = read(last(acceptance, 'term using a lemma proved with a placeholder'));
    expect(claimed.provenance.occurrences[0].pair.term).toEqual(['const', ['str', ['anonymous'], 'claimed'], []]);
    expect(claimed.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'supplier']]);
    expect(claimed.links[0].typing).toMatchObject({ index: 5, outcome: 'accepted', audit: { tag: 'available', axioms: [['str', ['anonymous'], 'sorryAx']] } });
    // The statement's own formation receipts depend on no axiom.
    expect(claimed.occurrences[1].typing.audit).toEqual({ tag: 'available', axioms: [] });
    // An axiom the user declared: the audit records the axiom itself.
    const assumed = read(last(acceptance, 'term using a user axiom'));
    expect(assumed.links[0]).toMatchObject({ status: 'supplier', typing: { outcome: 'accepted', audit: { tag: 'available', axioms: [['str', ['anonymous'], 'assumed']] } } });
    // Every other real link of the corpus records no axiom.
    let links = 0;
    for (const row of acceptance.filter((row, index) => acceptance[index + 1]?.label !== row.label)) {
      if (row.label === 'term using a lemma proved with a placeholder' || row.label === 'term using a user axiom') continue;
      const { history, record: chain } = historyOf(row);
      if (chain.checking.status !== 'captured') throw Error('missing checking');
      const lastCandidate = [...chain.checking.steps].reverse().find(step => step.output.status === 'candidate');
      if (!lastCandidate) continue;
      for (const link of supplierReading(history, chain.captureId, lastCandidate.index).links) { links++; expect(link.typing.audit, row.label).toEqual({ tag: 'available', axioms: [] }); }
    }
    expect(links).toBeGreaterThan(8);
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'variable named like the auxiliary entry'))('classifies context entries by the recorded declaration kind, never by the name', () => {
    // Two entries share the name _example: the capture's auxiliary declaration and the variable the user wrote.
    const shadowed = read(last(acceptance, 'variable named like the auxiliary entry'));
    expect(shadowed.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'value-of-type']]);
    expect(homeOf(shadowed)).toEqual(['0 port _example: context 0 auxDecl', '1 port _example: context 1 default']);
    expect(shadowed.provenance.occurrences[0].pair.term).toEqual(['bvar', ['nat', '0']]);
    // Inside a named theorem the auxiliary declaration carries the theorem's name.
    const inside = read(last(acceptance, 'term inside a named theorem'));
    expect(homeOf(inside)).toEqual(['0 port helper: context 0 auxDecl', '1 port n: context 1 default']);
    expect(inside.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'supplier']]);
    expect(groups(inside)).toEqual(['Sort 0 established: typeComponent#7 accepted also-typing']);
  }, 240000);

  it('numbers entered binders by their edge and their place in it (two edges above one link source)', () => {
    const label = acceptance.some(row => row.label === 'proof binder not referenced by the body') ? 'proof binder not referenced by the body' : 'dependent proof binder';
    // The chain end after its second single-binder focus: logical, focus, logical, focus. One type-component step is appended.
    const second = acceptance.filter(row => row.label === label).find(row => row.operation.kind === 'focus' && row.parentStepIndex === 2)!;
    const below = appendTypeComponent(second, 9030), reading = below.reading;
    expect(reading.provenance.edges.map(edge => edge.relation.kind)).toEqual(['containment', 'containment', 'type-of']);
    expect(reading.links.map(link => [link.from, link.to, link.status])).toEqual([[2, 3, 'value-of-type']]);
    expect(homeOf(reading)).toEqual(['0 port _example: context 0 auxDecl', '1 port n: entered edge 0 binder 0 universal', '2 port h: entered edge 1 binder 0 proof']);
    expectExactHome(below.history, reading); expectExactTyping(below.history, reading);
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'two binders entered by one focus'))('numbers entered binders by their edge and their place in it (one edge entering two binders, real capture)', () => {
    const entered = read(last(acceptance, 'two binders entered by one focus'));
    expect(entered.provenance.edges.map(edge => edge.relation.kind)).toEqual(['containment', 'type-of']);
    expect(entered.links.map(link => [link.from, link.to, link.status])).toEqual([[1, 2, 'value-of-type']]);
    expect(homeOf(entered)).toEqual(['0 port _example: context 0 auxDecl', '1 port n: entered edge 0 binder 0 universal', '2 port h: entered edge 0 binder 1 no role']);
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'term under a context definition'))('lists a let entry of the context by its origin: entered by the selection, or a recorded declaration', () => {
    // Entered by the original selection: a let entry with no recorded declaration and no role.
    const entered = read(last(acceptance, 'selection inside a local definition'));
    expect(entered.provenance.original.path).toEqual(['letBody']);
    expect(entered.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'value-of-type']]);
    expect(homeOf(entered)).toEqual(['0 port _example: context 0 auxDecl', '1 let f: selection']);
    // Held in the captured context: a let entry that the capture records as a declaration of kind default.
    const held = read(last(acceptance, 'term under a context definition'));
    expect(held.provenance.original.path).toEqual([]);
    expect(held.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'value-of-type']]);
    expect(homeOf(held)).toEqual(['0 port _example: context 0 auxDecl', '1 let f: context 1 default']);
    for (const reading of [entered, held]) expect(reading.links[0].conditions).toMatchObject({ binders: [], frames: [] });
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'selection inside a binder'))('lists a binder entered by the original selection in the home without a role', () => {
    const inside = read(last(acceptance, 'selection inside a binder'));
    expect(inside.provenance.original.path).toEqual(['piBody']);
    expect(inside.links.map(link => [link.from, link.to, link.status])).toEqual([[0, 1, 'value-of-type']]);
    expect(homeOf(inside)).toEqual(['0 port _example: context 0 auxDecl', '1 port x: selection']);
    expect(inside.links[0].conditions).toMatchObject({ binders: [], frames: [] });
    expect(groups(inside)).toEqual(['Sort 1 established: typeComponent#9 accepted also-typing']);
  }, 240000);

  it.skipIf(!acceptance.some(row => row.label === 'named theorem constant selected'))('relates a named theorem constant to its declared statement only with both receipts', () => {
    const row = last(acceptance, 'named theorem constant selected'), named = read(row);
    expect(named.links).toHaveLength(1);
    expect(named.links[0]).toMatchObject({ from: 0, to: 1, status: 'supplier', typing: { index: 5, outcome: 'accepted', alsoFormation: false },
      formation: { status: 'established', kind: 'proposition' }, conditions: { binders: [], frames: [] } });
    expect(groups(named)).toEqual(['Sort 0 established: typeComponent#7 accepted also-typing, logical#9 accepted']);
    // The only home entry is the capture's auxiliary declaration carrying the enclosing statement; the constant does not refer to it.
    expect(homeOf(named)).toEqual(['0 port _example: context 0 auxDecl']);
    expect(JSON.stringify(named.provenance.occurrences[0].pair.term)).not.toContain('"bvar"');
    expect(named.provenance.occurrences[1].inspections[0].form).toBe('eq');
    // The constant's own typing receipt gates the reading; the formation receipts alone relate nothing.
    expect(read(row, value => verdictAt(value, 5, 'unknown')).links[0]).toMatchObject({ status: 'annotation-only', typing: { outcome: 'unknown' }, formation: { status: 'established', kind: 'proposition' } });
    // The type-component receipt unknown with the logical root accepted: still read, resting on the accepted receipt of the same judgement.
    const rootOnly = read(row, value => verdict(value, 0, 1, 'unknown'));
    expect(rootOnly.links[0]).toMatchObject({ status: 'supplier', formation: { status: 'established', kind: 'proposition' } });
    expect(groups(rootOnly)).toEqual(['Sort 0 established: typeComponent#7 unknown also-typing, logical#9 accepted']);
    // Both formation receipts rejected: a typed value whose statement is not established; never a negative claim.
    const unformed = read(row, value => { verdict(value, 0, 1, 'rejected'); verdict(value, 1, 1, 'rejected'); });
    expect(unformed.links[0]).toMatchObject({ status: 'not-established', formation: { status: 'unestablished', kind: null } });
    expect(groups(unformed)).toEqual(['Sort 0: typeComponent#7 rejected also-typing, logical#9 rejected']);
  }, 240000);
});
