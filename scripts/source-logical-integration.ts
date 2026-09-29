/** Fresh editor processes for type components, logical formation and v3 history. */
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { analyzeEditorContext, type EditorContextRequest, type EditorRange } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { validateSourceSnapshot } from '../src/editor/source-snapshot.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceOccurrence } from '../src/editor/source-occurrence.js';
import type { HeadExposureBundle } from '../src/editor/source-history.js';
import type { SourceOccurrenceStep } from '../src/editor/source-occurrence.js';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionOperation,
  type SourceDecompositionBundle } from '../src/editor/source-decomposition.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-logical-')));
const fileName = path.join(project, 'Main.lean');
const { canonical } = createExactJsonTools();
const exact = (a: unknown, b: unknown) => assert.equal(canonical(a as JsonValue), canonical(b as JsonValue));
const records: unknown[] = [];
let version = 0;
function range(source: string, selected: string): EditorRange {
  const start = source.lastIndexOf(selected); assert.ok(start >= 0);
  const position = (offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
  return { start: position(start), end: position(start + selected.length) };
}
async function seed(label: string, source: string, selected: string, selectedPath: SourceOccurrenceStep[] = []) {
  const request: EditorContextRequest = { engineDirectory: engine, fileName, source, selection: range(source, selected), workspaceTrusted: true,
    document: { uri: pathToFileURL(fileName).href, version: ++version } };
  const first = await analyzeEditorContext(request);
  const response = await analyzeEditorContext({ ...request, occurrence: {
    snapshot: validateSourceSnapshot(first.sourceSnapshot), origin: first.sourceSnapshotOrigin as SourceSnapshotOrigin, path: selectedPath,
  } });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const occurrence = validateSourceOccurrence(response.sourceOccurrence, snapshot);
  const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  const parent = { snapshot, origin, occurrence };
  assert.ok(occurrence.checking.status === 'captured' && occurrence.checking.action.status === 'completed' && occurrence.checking.selected, `${label}: original pair unavailable`);
  return { label, request, parent, original: occurrence.checking.selected, seed: null as HeadExposureBundle | null, attempts: [] as SourceDecompositionBundle[] };
}
type Session = Awaited<ReturnType<typeof seed>>;
async function append(session: Session, previousCaptureId: string, parentStepIndex: number, operation: DecompositionOperation, expectUnavailable = false) {
  const before = canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue);
  const request = { ...session.parent, seed: session.seed, attempts: session.attempts, previousCaptureId, parentStepIndex, operation, version: 3 as const };
  const response = await analyzeEditorContext({ ...session.request, decomposition: request });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const history = validateDecompositionHistory({ snapshot: session.parent.snapshot, occurrence: session.parent.occurrence,
    seed: session.seed ? { snapshot: session.seed.snapshot, record: session.seed.record } : null,
    attempts: session.attempts.map(bundle => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const record = validateSourceDecomposition(response.sourceDecomposition, snapshot, history);
  assert.equal(record.previousCaptureId, previousCaptureId); assert.equal(record.parentStepIndex, parentStepIndex);
  assert.notEqual(record.captureId, previousCaptureId);
  assert.equal(record.captureId, (response.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId);
  assert.ok(record.checking.status === 'captured', JSON.stringify(record.checking));
  assert.equal(record.checking.action.status, 'completed', JSON.stringify(record.checking.action));
  if (expectUnavailable) {
    assert.equal(record.checking.stop?.kind, 'unsupported', JSON.stringify(record.checking.stop));
    assert.equal(record.checking.steps.at(-1)!.output.status, 'unavailable');
  } else assert.equal(record.checking.stop, null, JSON.stringify(record.checking.stop));
  const count = record.checking.steps.reduce((n, step) => n + (step.output.status === 'unavailable' ? 0 : step.operation.kind === 'fields' ? 0 : step.operation.kind === 'logical' ? ((step.input.term as JsonValue[])[0] === 'forallE' ? 4 : 2) : step.operation.kind === 'focus' || step.operation.kind === 'typeComponent' ? 2 : 3), 6);
  assert.equal(record.checking.checks.length, count);
  assert.ok(record.checking.checks.every(check => check.outcome.tag === 'accepted'), JSON.stringify(record.checking.checks));
  assert.equal(record.checking.steps.at(-1)!.replay, expectUnavailable ? 'not-compared' : 'new');
  assert.ok(record.checking.steps.slice(0, -1).every(step => step.replay === 'matched'));
  assert.equal(canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue), before);
  const bundle = { snapshot, origin: response.sourceSnapshotOrigin as SourceSnapshotOrigin, record };
  records.push({ label: session.label, source: session.request.source, selection: session.request.selection,
    parent: session.parent, seed: session.seed, priorAttempts: [...session.attempts], operation, previousCaptureId, parentStepIndex, response });
  session.attempts.push(bundle);
  return record;
}
function result(record: Awaited<ReturnType<typeof append>>) {
  assert.ok(record.checking.status === 'captured');
  const output = record.checking.steps.at(-1)!.output;
  assert.ok(output.status === 'candidate');
  return output.result;
}
async function chain(session: Session, operations: DecompositionOperation[]) {
  let previous = session.parent.occurrence.captureId, step = 0;
  for (const operation of operations) {
    const record = await append(session, previous, step, operation);
    previous = record.captureId; step = record.operations.length - 1;
  }
  return session.attempts.at(-1)!.record;
}
try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(fileName, '-- Source buffers are submitted without editing this file.\n');
  const saved = await readFile(fileName);
  for (const [structure, map, law] of [['Rotor', 'turn', 'fixed'], ['Mechanism', 'transit', 'witness']]) {
    const source = `structure ${structure} where
  Carrier : Type
  ${map} : Carrier → Carrier
  ${law} : ∀ x, ${map} x = x
example (owner : ${structure}) (unused : Nat) : ${structure} := owner
`;
    const session = await seed(`literal ${structure} law`, source, 'owner');
    const record = await chain(session, [{ kind: 'fields' }, { kind: 'project', index: 2 }, { kind: 'typeComponent' },
      { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }]);
    assert.ok(record.checking.status === 'captured');
    assert.equal(record.checking.checks.length, 19);
    assert.equal(result(record).home.arity, session.original.home.arity + 1);
    exact((result(record).home.telescope as JsonValue[])[1], session.original.home.telescope);
    const suffix = canonical(record as unknown as JsonValue);
    await append(session, record.captureId, 3, { kind: 'focus', path: ['piDomain'] });
    assert.equal(canonical(record as unknown as JsonValue), suffix);
  }
  for (const [label, expression, firstPath, secondPath] of [
    ['universal then existential', '∀ x : Nat, ∃ y : Nat, y = x', ['piBody'], ['appArg', 'lamBody']],
    ['existential then universal', '∃ y : Nat, ∀ x : Nat, y = x', ['appArg', 'lamBody'], ['piBody']],
  ] as const) {
    const session = await seed(label, `example : Prop := ${expression}\n`, expression);
    const record = await chain(session, [{ kind: 'logical' }, { kind: 'focus', path: [...firstPath] },
      { kind: 'logical' }, { kind: 'focus', path: [...secondPath] }, { kind: 'logical' }]);
    assert.equal(result(record).home.arity, session.original.home.arity + 2);
  }
  const sourcePrefix = `structure Vessel where
  Carrier : Type
  act : Carrier → Carrier
  law : ∀ x, act x = x
def Condition (_owner : Vessel) : Prop := True
`;
  for (const [label, expression, ownerPath] of [
    ['existential owner', '∃ owner : Vessel, Condition owner', ['appArg', 'lamBody', 'appArg']],
    ['negated owner', '¬ (∃ owner : Vessel, Condition owner)', ['appArg', 'appArg', 'lamBody', 'appArg']],
    ['alternative owner', '(∃ owner : Vessel, Condition owner) ∨ False', ['appFun', 'appArg', 'appArg', 'lamBody', 'appArg']],
  ] as const) {
    const session = await seed(label, `${sourcePrefix}example : Prop := ${expression}\n`, expression);
    const record = await chain(session, [{ kind: 'logical' }, { kind: 'focus', path: [...ownerPath] },
      { kind: 'fields' }, { kind: 'project', index: 2 }, { kind: 'typeComponent' }, { kind: 'logical' },
      { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }]);
    assert.equal(result(record).home.arity, session.original.home.arity + 2);
  }
  const ordinary = await seed('ordinary function type', 'example : Type := Nat → Nat\n', 'Nat → Nat');
  await chain(ordinary, [{ kind: 'logical' }]);
  const abstract = await seed('abstract existential predicate', 'example (p : Nat → Prop) : Prop := Exists p\n', 'Exists p');
  await chain(abstract, [{ kind: 'logical' }]);
  assert.deepEqual(await readFile(fileName), saved);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_LOGICAL_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Keep generated captures outside the repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
  }
  console.log(`Verified ${records.length} fresh logical decomposition records with exact formation, owner/quantifier homes, replay, backtracking and unchanged source/build.`);
} catch (error) {
  if (process.env.DEFINOGRAPH_LOGICAL_CAPTURE_OUT) {
    await writeFile(`${path.resolve(process.env.DEFINOGRAPH_LOGICAL_CAPTURE_OUT)}.failed.json`, JSON.stringify(records, null, 2) + '\n');
  }
  throw error;
} finally { await rm(project, { recursive: true, force: true }); }
