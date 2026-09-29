/** Constructed parser controls only; no native execution or authority is implied. */
import type { JsonObject, JsonValue } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { validateSourceHeadExposure } from './source-head-exposure';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionHistory, type DecompositionOperation } from './source-decomposition';
import { headExposureFixture } from './source-decomposition.test-fixtures';
const o = (v: unknown) => v as JsonObject, a = (v: unknown) => v as JsonValue[];
const name = (s: string, prefix: JsonValue = ['anonymous']): JsonValue => ['str', prefix, s];
const c = (s: string, levels: JsonValue[] = []): JsonValue => ['const', name(s), levels];
const n = (v: number): JsonValue => ['nat', String(v)];
const b = (i: number): JsonValue => ['bvar', n(i)];
const app = (f: JsonValue, ...args: JsonValue[]) => args.reduce<JsonValue>((f, arg) => ['app', f, arg], f);
const clone = <T>(v: T): T => JSON.parse(JSON.stringify(v)) as T;
const id = (i: number) => `660e8400-e29b-41d4-a716-${String(i).padStart(12, '0')}`;
const prefix = (attempt: string) => name(attempt, name('SourceDecomposition', name('StatementLens')));

// Independent fixture closure reads the exact telescope oldest-first. It does
// not use model closure, selection, expected-declaration or plan helpers.
function close(telescope: JsonValue, body: JsonValue, tag: 'lam' | 'forallE'): JsonValue {
  const entries: JsonValue[][] = []; let tel = a(telescope);
  while (tel[0] !== 'nil') { entries.unshift(tel); tel = a(tel[1]); }
  return entries.reduceRight<JsonValue>((body, item) => item[0] === 'port'
    ? [tag, o(item[2]).name, item[3], body, o(item[2]).info]
    : ['letE', item[2], item[4], item[5], body, item[3]], body);
}
function declaration(base: JsonValue, label: string, pair: PositionalStructuralInput, type: JsonValue, value: JsonValue): JsonObject {
  const dn = name(label, base), component = label === 'component';
  return { kind: component ? 'defnDecl' : 'thmDecl', name: dn, levelParams: [], type: close(pair.home.telescope, type, 'forallE'),
    value: close(pair.home.telescope, value, 'lam'), all: [dn], ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
}
function receipts(checking: JsonObject, declarations: JsonObject[], labels: string[], attempt: string) {
  checking.checks = declarations.map((decl, index) => ({ id: index, pair: 'editor-decomposition', label: labels[index], displayLabel: labels[index], declaration: decl,
    subject: { attempt, pair: 'editor-decomposition', sequence: index, target: labels[index], declaration: decl },
    envBefore: index, envAfter: index + 1, heartbeatBound: n(200000), outcome: { tag: 'accepted' } }));
  checking.audits = declarations.map((decl, index) => ({ checkId: index, subject: decl, environment: index + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } }));
  checking.environmentSnapshotCount = declarations.length + 1;
}
function initial() {
  const fixture = headExposureFixture(), seed = validateSourceHeadExposure(fixture.value, fixture.snapshot, fixture.parent);
  const history = validateDecompositionHistory({ ...fixture.parent, seed: { snapshot: fixture.snapshot, record: seed }, attempts: [] });
  return { ...fixture, seed, history };
}
function seedCheckpoint(history: DecompositionHistory) {
  const check = history.seed!.record.checking;
  if (check.status !== 'captured' || check.exposure?.status !== 'candidate' || !check.selected) throw Error('test fixture');
  const { checking: _checking, ...candidate } = check.exposure; void _checking;
  return { operation: { kind: 'expose', target: history.seed!.record.target }, input: check.selected, candidate };
}
function focus(result: PositionalStructuralInput) { return { status: 'candidate', result, checking: { status: 'completed' } }; }
function record(history: DecompositionHistory, operation: DecompositionOperation, output: unknown, options: { previous?: string; index?: number; id?: number } = {}): JsonObject {
  const previous = options.previous ?? history.seed!.record.captureId, index = options.index ?? 0;
  const old = history.attempts.find(entry => entry.record.captureId === previous)?.record;
  const checkpoints = old?.checking.status === 'captured' ? old.checking.steps.slice(0, index + 1).map(step => {
    if (step.output.status !== 'candidate') throw Error('test checkpoint');
    const { checking: _checking, ...candidate } = step.output; void _checking; return { operation: step.operation, input: step.input, candidate };
  }) : [seedCheckpoint(history)];
  const outputs = [...checkpoints.map(cp => ({ ...cp.candidate, checking: { status: 'completed' } })), output];
  const operations = [...checkpoints.map(cp => cp.operation), operation], attempt = id(options.id ?? history.attempts.length + 1), base = prefix(attempt);
  const original = history.occurrence.checking;
  if (original.status !== 'captured' || !original.selected) throw Error('test original');
  const binding = { ...clone(original.binding), operation: 'editor-decomposition', sourceKind: 'namedDecomposition', attempt, declarationPrefix: base,
    expectedSelected: original.selected, operations, expectedHistory: checkpoints };
  const declarations: JsonObject[] = [], labels: string[] = [];
  const pair = original.selected;
  const truth = c('True'), intro: JsonValue = ['const', name('intro', name('True')), []];
  for (const p of [name('source', base), name('root', name('extraction', base)), name('selected', name('extraction', base))]) {
    declarations.push(declaration(p, 'context', pair, truth, intro), declaration(p, 'component', pair, pair.type, pair.term)); labels.push('context', 'component');
  }
  let input = pair;
  const steps = outputs.map((output, i) => {
    const out = o(output), op = operations[i], result = out.result as unknown as PositionalStructuralInput;
    const stepPrefix = name(`step${i}`, base), start = declarations.length;
    if (out.status === 'candidate') {
      const p = name(op.kind === 'expose' ? 'result' : 'focus', stepPrefix);
      declarations.push(declaration(p, 'context', result, truth, intro), declaration(p, 'component', result, result.type, result.term)); labels.push('context', 'component');
      if (op.kind === 'expose') {
        declarations.push(declaration(stepPrefix, 'conversion', result, app(c('Eq', [out.carrierSort]), result.type, out.before, result.term),
          app(['const', name('refl', name('Eq')), [out.carrierSort]], result.type, out.before))); labels.push('conversion');
      }
    }
    const step = { index: i, operation: op, input, output, receiptStart: start, receiptCount: declarations.length - start, replay: i < checkpoints.length ? 'matched' : 'new' };
    input = result; return step;
  });
  const checking: JsonObject = { status: 'captured', action: { status: 'completed' }, binding: binding as unknown as JsonValue, selected: pair as unknown as JsonValue,
    steps: steps as unknown as JsonValue, stop: null };
  receipts(checking, declarations, labels, attempt);
  return clone({ schema: 'definograph.source-decomposition.v1', parentCaptureId: history.occurrence.captureId, previousCaptureId: previous, parentStepIndex: index,
    captureId: attempt, path: history.occurrence.path, operations,
    policy: { id: 'bounded-decomposition-v1', operation: 'editor-decomposition', preparation: 'Lean.instantiateMVars', universeSubstitution: 'structural',
      reduction: 'original-lambda-spine', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1', maxOperations: 8 }, checking } as unknown as JsonObject);
}
function firstFocus(history: DecompositionHistory, path: 'appArg' | 'appFun' | 'empty' = 'appArg') {
  const result = seedCheckpoint(history).candidate.result;
  const focused = { home: result.home, term: path === 'empty' ? result.term : a(result.term)[path === 'appArg' ? 2 : 1],
    type: path === 'appFun' ? ['forallE', name('x'), c('Nat'), c('Nat'), 'default'] as JsonValue : c('Nat') };
  return record(history, { kind: 'focus', path: path === 'empty' ? [] : [path] }, focus(focused));
}
function append(history: DecompositionHistory, value: JsonObject) {
  const accepted = validateSourceDecomposition(value, history.snapshot, history);
  return validateDecompositionHistory({ ...history, attempts: [...history.attempts, { snapshot: history.snapshot, record: accepted }] });
}
const checking = (record: JsonObject) => o(record.checking);
const stepAt = (record: JsonObject, i: number) => o(a(checking(record).steps)[i]);
function replaceDeclaration(value: JsonObject, i: number, mutate: (decl: JsonObject) => void) {
  const check = checking(value), receipt = o(a(check.checks)[i]), decl = clone(o(receipt.declaration)); mutate(decl);
  receipt.declaration = decl; o(receipt.subject).declaration = decl; o(a(check.audits)[i]).subject = decl;
}
function truncate(value: JsonObject, count: number) {
  const check = checking(value); check.checks = a(check.checks).slice(0, count); check.audits = a(check.audits).slice(0, count); check.environmentSnapshotCount = count + 1;
}
function errorStop(value: JsonObject, index: number, count: number) {
  const step = stepAt(value, index), check = checking(value); step.receiptCount = count; step.replay = 'not-compared';
  o(step.output).checking = { status: 'error', reason: 'callback failed' };
  check.steps = a(check.steps).slice(0, index + 1); check.stop = { status: 'unavailable', kind: 'error', phase: 'operation-checking', reason: 'callback failed' };
  truncate(value, Number(step.receiptStart) + count);
}


export { o, a, name, c, n, b, app, clone, id, close, initial, seedCheckpoint, focus, record, firstFocus, append, checking, stepAt, replaceDeclaration, truncate, errorStop };
