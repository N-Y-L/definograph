/** Fresh editor processes for direct fields, nested proof pairs and v2 history. */
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
import { validateSourceHeadExposure } from '../src/editor/source-head-exposure.js';
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
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-fields-')));
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
  return { label, request, parent, seed: null as HeadExposureBundle | null, attempts: [] as SourceDecompositionBundle[] };
}
type Session = Awaited<ReturnType<typeof seed>>;
async function append(session: Session, previousCaptureId: string, parentStepIndex: number, operation: DecompositionOperation, expectUnavailable = false) {
  const before = canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue);
  const request = { ...session.parent, seed: session.seed, attempts: session.attempts, previousCaptureId, parentStepIndex, operation, version: 2 as const };
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
  const checkedOperations = expectUnavailable ? record.operations.slice(0, -1) : record.operations;
  const count = checkedOperations.reduce((n, op) => n + (op.kind === 'fields' ? 0 : op.kind === 'focus' ? 2 : 3), 6);
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
try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(fileName, '-- Source buffers are submitted without editing this file.\n');
  const saved = await readFile(fileName);
  for (const [outer, inner, law, wrap, map, proof] of [
    ['Envelope', 'Action', 'Maintains', 'Coincides', 'move', 'law'],
    ['Chest', 'Mechanism', 'Constraint', 'SameAt', 'transit', 'witness'],
  ]) {
    const source = `def ${wrap} {A : Type} (a b : A) : Prop := a = b
 def ${law} {A : Type} (f : A → A) : Prop := ∀ x, ${wrap} (f x) x
 structure ${inner} (A : Type) where
   ${map} : A → A
   ${proof} : ${law} ${map}
 structure ${outer} (A : Type) where
   payload : ${inner} A
 example (A : Type) (owner : ${outer} A) (unused : Nat) : ${outer} A := owner
`;
    const session = await seed(`nested ${outer}`, source, 'owner');
    let previous = session.parent.occurrence.captureId, step = 0;
    const ops: DecompositionOperation[] = [{ kind: 'fields' }, { kind: 'project', index: 0 }, { kind: 'fields' },
      { kind: 'project', index: 1 }, { kind: 'expose', target: 'type' }, { kind: 'focus', path: ['piBody'] }, { kind: 'expose', target: 'term' }];
    for (const op of ops) {
      const record = await append(session, previous, step, op); previous = record.captureId; step = record.operations.length - 1;
      if (op.kind === 'fields') { assert.ok(record.checking.status === 'captured'); assert.equal(record.checking.steps.at(-1)!.receiptCount, 0); }
      if (op.kind === 'project') { assert.ok(record.checking.status === 'captured'); exact(result(record).home, record.checking.steps.at(-1)!.input.home); }
    }
    const final = session.attempts.at(-1)!.record;
    assert.ok(final.checking.status === 'captured');
    assert.equal(final.checking.checks.length, 20); assert.ok(session.parent.occurrence.checking.status === 'captured' && session.parent.occurrence.checking.selected); assert.equal(result(final).home.arity, session.parent.occurrence.checking.selected.home.arity + 1);
    // Backtrack from the inner catalogue, preserving the old proof-law suffix.
    const old = canonical(final as unknown as JsonValue);
    const back = await append(session, final.captureId, 2, { kind: 'project', index: 0 });
    assert.equal(back.operations.length, 4); assert.equal(canonical(final as unknown as JsonValue), old);
    await assert.rejects(analyzeEditorContext({ ...session.request, source: source + '\n', decomposition: {
      ...session.parent, seed: null, attempts: [], version: 2, previousCaptureId: session.parent.occurrence.captureId,
      parentStepIndex: 0, operation: { kind: 'fields' },
    } }), /no longer matches/);
  }
  const internal = await seed('dependent internal carrier', `universe u
structure Bundle where
  Carrier : Type u
  map : Carrier → Carrier
  stable : ∀ x, map x = x
example (owner : Bundle.{u}) (unused : Nat) : Bundle.{u} := owner
`, 'owner');
  const internalFields = await append(internal, internal.parent.occurrence.captureId, 0, { kind: 'fields' });
  for (const index of [0, 1, 2]) await append(internal, internalFields.captureId, 0, { kind: 'project', index });
  const inherited = await seed('embedded inherited parent', `structure Base where
  value : Nat
structure Derived extends Base where
  witness : value = value
example (owner : Derived) : Derived := owner
`, 'owner');
  const parents = await append(inherited, inherited.parent.occurrence.captureId, 0, { kind: 'fields' });
  const parent = await append(inherited, parents.captureId, 0, { kind: 'project', index: 0 });
  await append(inherited, parent.captureId, 1, { kind: 'fields' });
  for (const keyword of ['let', 'have']) {
    const source = `structure Stored where
  value : Nat
example (owner : Stored) : Stored := ${keyword} held : Stored := owner; held
`;
    const owned = await seed(`owned ${keyword}`, source, `${keyword} held : Stored := owner; held`, ['letBody']);
    const listed = await append(owned, owned.parent.occurrence.captureId, 0, { kind: 'fields' });
    const projected = await append(owned, listed.captureId, 0, { kind: 'project', index: 0 });
    assert.equal((result(projected).home.telescope as JsonValue[])[0], 'letE');
  }
  const proposition = await seed('proof record', 'structure Pledge : Prop where\n  law : True\nexample (owner : Pledge) : Pledge := owner\n', 'owner');
  const pledge = await append(proposition, proposition.parent.occurrence.captureId, 0, { kind: 'fields' });
  await append(proposition, pledge.captureId, 0, { kind: 'project', index: 0 });
  for (const [label, source] of [
    ['alias refusal', 'structure Hidden where\n  value : Nat\ndef Alias := Hidden\nexample (owner : Alias) : Alias := owner\n'],
    ['nonstructure refusal', 'example (owner : Nat) : Nat := owner\n'],
  ]) {
    const unsupported = await seed(label, source, 'owner');
    await append(unsupported, unsupported.parent.occurrence.captureId, 0, { kind: 'fields' }, true);
  }
  for (const [label, fields] of [['empty record', ''], ['bounded fields', Array.from({length:17}, (_, i) => `  field${i} : Nat`).join('\n')]]) {
    const session = await seed(label, `structure Record where\n${fields}\nexample (owner : Record) : Record := owner\n`, 'owner');
    await append(session, session.parent.occurrence.captureId, 0, { kind: 'fields' });
  }
  const mixed = await seed('legacy prefix into v2 fields', 'structure Legacy where\n  value : Nat\ndef unwrap (x : Legacy) : Legacy := x\nexample (owner : Legacy) : Legacy := unwrap owner\n', 'unwrap owner');
  const legacyExposure = await analyzeEditorContext({ ...mixed.request, headExposure: { ...mixed.parent, target: 'term' } });
  const legacySnapshot = validateSourceSnapshot(legacyExposure.sourceSnapshot);
  mixed.seed = { snapshot: legacySnapshot, origin: legacyExposure.sourceSnapshotOrigin as SourceSnapshotOrigin,
    record: validateSourceHeadExposure(legacyExposure.sourceHeadExposure, legacySnapshot, { snapshot: mixed.parent.snapshot, occurrence: mixed.parent.occurrence }) };
  const legacyFocused = await analyzeEditorContext({ ...mixed.request, decomposition: { ...mixed.parent, seed: mixed.seed,
    attempts: [], previousCaptureId: mixed.seed.record.captureId, parentStepIndex: 0, operation: { kind: 'focus', path: [] } } });
  const legacyHistory = validateDecompositionHistory({ snapshot: mixed.parent.snapshot, occurrence: mixed.parent.occurrence,
    seed: { snapshot: mixed.seed.snapshot, record: mixed.seed.record }, attempts: [] });
  const legacyFresh = validateSourceSnapshot(legacyFocused.sourceSnapshot);
  mixed.attempts.push({ snapshot: legacyFresh, origin: legacyFocused.sourceSnapshotOrigin as SourceSnapshotOrigin,
    record: validateSourceDecomposition(legacyFocused.sourceDecomposition, legacyFresh, legacyHistory) });
  await append(mixed, mixed.attempts[0].record.captureId, 1, { kind: 'fields' });
  assert.deepEqual(await readFile(fileName), saved);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_FIELD_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Keep generated captures outside the repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
  }
  console.log(`Verified ${records.length} fresh direct-field decomposition records with exact replay, derived homes, backtracking, typing and unchanged source/build.`);
} finally { await rm(project, { recursive: true, force: true }); }
