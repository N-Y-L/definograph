/** Fresh editor processes for bounded derived focus and repeated head exposure. */
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
import { validateSourceHeadExposure, type HeadExposureTarget } from '../src/editor/source-head-exposure.js';
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionOperation,
  type SourceDecompositionBundle } from '../src/editor/source-decomposition.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-decomposition-')));
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
async function seed(label: string, source: string, selected: string, target: HeadExposureTarget = 'term') {
  const request: EditorContextRequest = { engineDirectory: engine, fileName, source, selection: range(source, selected), workspaceTrusted: true,
    document: { uri: pathToFileURL(fileName).href, version: ++version } };
  const first = await analyzeEditorContext(request);
  const response = await analyzeEditorContext({ ...request, occurrence: {
    snapshot: validateSourceSnapshot(first.sourceSnapshot), origin: first.sourceSnapshotOrigin as SourceSnapshotOrigin, path: [],
  } });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const occurrence = validateSourceOccurrence(response.sourceOccurrence, snapshot);
  const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  const parent = { snapshot, origin, occurrence };
  const exposed = await analyzeEditorContext({ ...request, headExposure: { ...parent, target } });
  const fresh = validateSourceSnapshot(exposed.sourceSnapshot);
  const record = validateSourceHeadExposure(exposed.sourceHeadExposure, fresh, { snapshot, occurrence });
  assert.ok(record.checking.status === 'captured' && record.checking.exposure?.status === 'candidate'
    && record.checking.exposure.checking.status === 'completed', `${label}: ${JSON.stringify(record.checking)}`);
  const head = { snapshot: fresh, origin: exposed.sourceSnapshotOrigin as SourceSnapshotOrigin, record };
  return { label, request, parent, seed: head, attempts: [] as SourceDecompositionBundle[] };
}
type Session = Awaited<ReturnType<typeof seed>>;
async function append(session: Session, previousCaptureId: string, parentStepIndex: number, operation: DecompositionOperation, expectUnavailable = false) {
  const before = canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue);
  const request = { ...session.parent, seed: session.seed, attempts: session.attempts, previousCaptureId, parentStepIndex, operation };
  const response = await analyzeEditorContext({ ...session.request, decomposition: request });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const history = validateDecompositionHistory({ snapshot: session.parent.snapshot, occurrence: session.parent.occurrence,
    seed: { snapshot: session.seed.snapshot, record: session.seed.record },
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
  const count = checkedOperations.reduce((n, op) => n + (op.kind === 'expose' ? 3 : 2), 6);
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
  for (const [outer, inner, A, B, f, x] of [['shroud','thread','A','B','f','x'], ['vault','cipher','U','V','map','point']]) {
    const source = `def ${inner} {${A} ${B} : Type} (${f} : ${A} → ${B}) (${x} : ${A}) : ${B} := ${f} ${x}\ndef ${outer} {${A} ${B} : Type} (${f} : ${A} → ${B}) : ${A} → ${B} := fun ${x} => ${inner} ${f} ${x}\nexample (${A} ${B} : Type) (${f} : ${A} → ${B}) (unused : Nat) : ${A} → ${B} := ${outer} ${f}\n`;
    const session = await seed(`nested ${outer}`, source, `${outer} ${f}`);
    const focus = await append(session, session.seed.record.captureId, 0, { kind: 'focus', path: ['lamBody'] });
    const focused = result(focus);
    const exposed = await append(session, focus.captureId, 1, { kind: 'expose', target: 'term' });
    exact(result(exposed).home, focused.home);
    assert.equal((result(exposed).term as JsonValue[])[0], 'app');
    const earlierBytes = canonical(exposed as unknown as JsonValue);
    const backtrack = await append(session, exposed.captureId, 0, { kind: 'focus', path: [] });
    assert.equal(backtrack.operations.length, 2);
    assert.equal(canonical(session.attempts[1]!.record as unknown as JsonValue), earlierBytes);
    assert.equal((result(backtrack).term as JsonValue[])[0], 'lam');
    await assert.rejects(analyzeEditorContext({ ...session.request, source: source + '\n', decomposition: {
      ...session.parent, seed: session.seed, attempts: session.attempts, previousCaptureId: focus.captureId,
      parentStepIndex: 1, operation: { kind: 'expose', target: 'term' },
    } }), /no longer matches/);
  }
  for (const keyword of ['let', 'have']) {
    const source = `def strand {A B : Type} (f : A → B) (x : A) : B := f x\ndef chamber {A B : Type} (f : A → B) : A → B := fun x => ${keyword} stored : A := x; strand f stored\nexample (A B : Type) (f : A → B) : A → B := chamber f\n`;
    const session = await seed(`owned ${keyword}`, source, 'chamber f');
    const focus = await append(session, session.seed.record.captureId, 0, { kind: 'focus', path: ['lamBody', 'letBody'] });
    const telescope = result(focus).home.telescope as JsonValue[];
    assert.ok(session.seed.record.checking.status === 'captured' && session.seed.record.checking.exposure?.status === 'candidate');
    const exposedLambda = session.seed.record.checking.exposure.result.term as JsonValue[];
    const originalLet = exposedLambda[3] as JsonValue[];
    assert.equal(originalLet[0], 'letE'); assert.equal(telescope[0], 'letE');
    assert.equal(telescope[3], originalLet[5], 'Preserve the actual elaborated let flag, independently of the surface keyword.');
    const exposed = await append(session, focus.captureId, 1, { kind: 'expose', target: 'term' });
    exact(result(exposed).home, result(focus).home);
  }
  const dependent = await seed('dependent type body', 'def Cell (n : Nat) : Type := Fin n\ndef Passage : Type := (n : Nat) → Cell n\nexample (f : Passage) : Passage := f\n', 'f', 'type');
  const family = await append(dependent, dependent.seed.record.captureId, 0, { kind: 'focus', path: ['piBody'] });
  const opened = await append(dependent, family.captureId, 1, { kind: 'expose', target: 'term' });
  exact(result(opened).home, result(family).home);
  assert.equal((result(opened).home.telescope as JsonValue[])[0], 'port');
  const empty = await seed('empty focus infers distinct type', 'def Carrier : Type := Nat\ndef grain : Carrier := Nat.zero\nexample : Carrier := grain\n', 'grain');
  const emptyFocus = await append(empty, empty.seed.record.captureId, 0, { kind: 'focus', path: [] });
  assert.ok(empty.seed.record.checking.status === 'captured' && empty.seed.record.checking.exposure?.status === 'candidate');
  assert.notEqual(canonical(result(emptyFocus).type), canonical(empty.seed.record.checking.exposure.result.type));
  exact(result(emptyFocus).term, empty.seed.record.checking.exposure.result.term);
  // Nat is an inductive head; retain the prior pair and explicit unsupported step.
  await append(empty, emptyFocus.captureId, 1, { kind: 'expose', target: 'type' }, true);
  assert.deepEqual(await readFile(fileName), saved);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_DECOMPOSITION_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Keep generated captures outside the repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
  }
  console.log(`Verified ${records.length} fresh decomposition records with exact replay, derived homes, backtracking, typing and unchanged source/build.`);
} finally { await rm(project, { recursive: true, force: true }); }
