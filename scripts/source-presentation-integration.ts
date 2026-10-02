/** Native presentation is separately associated with an unchanged exact result. */
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
import { validateDecompositionHistory, validateSourceDecomposition, type DecompositionOperation,
  type SourceDecompositionBundle } from '../src/editor/source-decomposition.js';
import { sanitizeSourcePresentation } from '../src/editor/source-presentation.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-source-presentation-')));
const fileName = path.join(project, 'Main.lean');
const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
const records: unknown[] = [];
let version = 0;
function range(source: string, selected: string): EditorRange {
  const start = source.lastIndexOf(selected); assert.ok(start >= 0);
  const position = (offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
  return { start: position(start), end: position(start + selected.length) };
}
async function seed(label: string, source: string, selected: string) {
  const request: EditorContextRequest = { engineDirectory: engine, fileName, source, selection: range(source, selected), workspaceTrusted: true,
    document: { uri: pathToFileURL(fileName).href, version: ++version },
    libraryPaths: (JSON.parse(configText).leanPath as string[]).filter(directory => !directory.startsWith(engine + path.sep)) };
  const first = await analyzeEditorContext(request);
  assert.ok(first.sourceSnapshot, `${label}: ${JSON.stringify(first).slice(0, 2000)}`);
  const response = await analyzeEditorContext({ ...request, occurrence: {
    snapshot: validateSourceSnapshot(first.sourceSnapshot), origin: first.sourceSnapshotOrigin as SourceSnapshotOrigin, path: [],
  } });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const occurrence = validateSourceOccurrence(response.sourceOccurrence, snapshot);
  const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  assert.ok(occurrence.checking.status === 'captured' && occurrence.checking.selected, `${label}: original pair unavailable`);
  return { label, request, parent: { snapshot, origin, occurrence }, attempts: [] as SourceDecompositionBundle[] };
}
type Session = Awaited<ReturnType<typeof seed>>;
async function append(session: Session, operation: DecompositionOperation, expectUnavailable = false) {
  const before = canonical({ parent: session.parent, attempts: session.attempts });
  const previous = session.attempts.at(-1)?.record;
  const request = { ...session.parent, seed: null, attempts: session.attempts, previousCaptureId: previous?.captureId ?? session.parent.occurrence.captureId,
    parentStepIndex: previous ? previous.operations.length - 1 : 0, operation, version: 3 as const };
  const response = await analyzeEditorContext({ ...session.request, decomposition: request });
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const history = validateDecompositionHistory({ snapshot: session.parent.snapshot, occurrence: session.parent.occurrence,
    seed: null, attempts: session.attempts.map(bundle => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const record = validateSourceDecomposition(response.sourceDecomposition, snapshot, history);
  assert.ok(record.checking.status === 'captured' && record.checking.action.status === 'completed', `${session.label}: ${JSON.stringify(record.checking)}`);
  assert.ok(record.checking.checks.every(check => check.outcome.tag === 'accepted'));
  const step = record.checking.steps.at(-1)!;
  assert.equal(step.output.status, expectUnavailable ? 'unavailable' : 'candidate');
  assert.equal(step.replay, expectUnavailable ? 'not-compared' : 'new');
  assert.ok(record.checking.steps.slice(0, -1).every(item => item.replay === 'matched'));
  assert.equal(canonical({ parent: session.parent, attempts: session.attempts }), before, 'Optional display must not mutate retained history.');
  const rawBefore = JSON.stringify(record);
  const presentation = sanitizeSourcePresentation(response.sourceDecompositionPresentation, record);
  assert.equal(JSON.stringify(record), rawBefore, 'Presentation admission must preserve the exact record bytes.');
  const bundle = { snapshot, origin: response.sourceSnapshotOrigin as SourceSnapshotOrigin, record, ...(presentation ? { presentation } : {}) };
  session.attempts.push(bundle);
  records.push({ label: session.label, source: session.request.source, selection: session.request.selection, parent: session.parent,
    priorAttempts: session.attempts.slice(0, -1), response });
  console.log(`${session.label}: ${presentation?.status === 'available' ? presentation.text.slice(0, 180) : presentation?.reason ?? 'presentation absent'}`);
  return bundle;
}
function available(bundle: Awaited<ReturnType<typeof append>>) {
  assert.equal(bundle.presentation?.status, 'available', JSON.stringify(bundle.presentation));
  if (bundle.presentation?.status !== 'available') throw new Error('Missing native notation.');
  assert.ok(bundle.record.checking.status === 'captured');
  const step = bundle.record.checking.steps.at(-1)!;
  assert.ok(step.operation.kind === 'expose' && step.output.status === 'candidate');
  assert.equal(bundle.presentation.captureId, bundle.record.captureId);
  assert.equal(bundle.presentation.stepIndex, step.index);
  assert.equal(bundle.presentation.target, step.operation.target);
  assert.equal(canonical(bundle.presentation.result), canonical(step.output.result));
  return bundle.presentation;
}
const imports = 'import Mathlib.Topology.MetricSpace.Pseudo.Lemmas\n';
try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(fileName, '-- Submitted fixture buffers do not modify this saved file.\n');
  const saved = await readFile(fileName);
  const ball = await seed('Metric.ball', `${imports}example {α : Type} [PseudoMetricSpace α] (x : α) (δ : ℝ) : Set α := Metric.ball x δ\n`, 'Metric.ball x δ');
  const ballBundle = await append(ball, { kind: 'expose', target: 'term' });
  const ballText = available(ballBundle).text;
  assert.match(ballText, /\{\s*y\s*\|\s*dist y x < δ\s*\}/u);
  assert.doesNotMatch(ballText, /∩|inter|setOf|LT\.lt/u);
  const transfer = await seed('UniformContinuousOn', `${imports}example {α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (s : Set α) : Prop := UniformContinuousOn f s\n`, 'UniformContinuousOn f s');
  const transferText = available(await append(transfer, { kind: 'expose', target: 'term' })).text;
  assert.match(transferText, /(?:Filter\.)?Tendsto/u);
  assert.doesNotMatch(transferText, /∀ ε|∃ δ|dist \(/u);
  const renamed = await seed('Renamed equivalent region', `${imports}def regionAround {A : Type} [PseudoMetricSpace A] (origin : A) (radius : ℝ) : Set A := { member | dist member origin < radius }\nexample {A : Type} [PseudoMetricSpace A] (origin : A) (radius : ℝ) : Set A := regionAround origin radius\n`, 'regionAround origin radius');
  assert.match(available(await append(renamed, { kind: 'expose', target: 'term' })).text, /dist member origin < radius/u);
  const nested = await seed('Owned shadowed lambda and let', 'def echo (same : Nat) : Nat := same\ndef chamber (same : Nat) : Nat → Nat := fun same => let same : Nat := same; echo same\nexample (same : Nat) : Nat → Nat := chamber same\n', 'chamber same');
  const nestedText = available(await append(nested, { kind: 'expose', target: 'term' })).text;
  assert.match(nestedText, /fun/u); assert.doesNotMatch(nestedText, /#\d|bvar/u);
  const focus = await append(nested, { kind: 'focus', path: ['lamBody', 'letBody'] });
  assert.equal(focus.presentation?.status, 'unavailable');
  const opened = await append(nested, { kind: 'expose', target: 'term' });
  assert.doesNotMatch(available(opened).text, /#\d|bvar/u);
  const dependent = await seed('Dependent partial application', 'def applyFamily {A : Type} (family : A → Type) (step : (x : A) → family x) : (x : A) → family x := fun x => step x\nexample (A : Type) (family : A → Type) (step : (x : A) → family x) : (x : A) → family x := applyFamily family step\n', 'applyFamily family step');
  assert.match(available(await append(dependent, { kind: 'expose', target: 'term' })).text, /fun .*step/u);
  const typeAlias = await seed('Inferred type exposure', 'def chosenCarrier (A : Type) (x : A) : Type := { y : A // y = x }\nexample (A : Type) (x : A) (w : chosenCarrier A x) : chosenCarrier A x := w\n', 'w');
  const typePresentation = available(await append(typeAlias, { kind: 'expose', target: 'type' }));
  assert.equal(typePresentation.target, 'type');
  assert.match(typePresentation.text, /\{\s*y\s*\/\/\s*y = x\s*\}/u);
  const explicit = [];
  for (const instance of ['first', 'second']) {
    const selected = `@Metric.ball α ${instance} x δ`;
    const session = await seed(`Explicit metric instance ${instance}`, `${imports}example (α : Type) (first second : PseudoMetricSpace α) (x : α) (δ : ℝ) : Set α := ${selected}\n`, selected);
    explicit.push(await append(session, { kind: 'expose', target: 'term' }));
  }
  const first = available(explicit[0]), second = available(explicit[1]);
  assert.notEqual(canonical(first.result.term), canonical(second.result.term), 'Explicit metric instances must remain distinct in exact syntax.');
  const swapped = { ...first, captureId: second.captureId, stepIndex: second.stepIndex, target: second.target };
  assert.equal(sanitizeSourcePresentation(swapped, explicit[1].record)?.status, 'unavailable', 'Same visible variable names cannot authorize a different exact instance.');
  assert.equal(sanitizeSourcePresentation(first, explicit[1].record)?.status, 'unavailable', 'Stale captures must not reuse native text.');
  for (const extra of [{ ...first, extra: true }, { ...first, results: [first.result] }])
    assert.equal(sanitizeSourcePresentation(extra, explicit[0].record)?.status, 'unavailable');
  const opaque = await seed('Unsupported opaque head', 'opaque hidden (n : Nat) : Nat := n\nexample (n : Nat) : Nat := hidden n\n', 'hidden n');
  assert.equal((await append(opaque, { kind: 'expose', target: 'term' }, true)).presentation?.status, 'unavailable');
  const huge = await seed('Display text budget', `def longText : String := "${'W'.repeat(9000)}"\nexample : String := longText\n`, 'longText');
  const budget = await append(huge, { kind: 'expose', target: 'term' });
  assert.equal(budget.presentation?.status, 'unavailable');
  assert.match(budget.presentation?.status === 'unavailable' ? budget.presentation.reason : '', /display text limit/u);
  const limited = await seed('Native printer step limit', 'def nestedPair (n : Nat) : Nat × Nat := (n, n)\nset_option pp.maxSteps 1 in\nexample (n : Nat) : Nat × Nat := nestedPair n\n', 'nestedPair n');
  const omission = await append(limited, { kind: 'expose', target: 'term' });
  assert.equal(omission.presentation?.status, 'unavailable');
  assert.match(omission.presentation?.status === 'unavailable' ? omission.presentation.reason : '', /printer omitted|notation is unavailable/u);
  assert.equal(JSON.stringify(ballBundle.record), JSON.stringify(ball.attempts[0].record));
  assert.deepEqual(await readFile(fileName), saved, 'The fixture file must remain unchanged.');
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_PRESENTATION_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Retain generated captures outside the repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
  }
  console.log(`Verified ${records.length} fresh native records with exact associations, generic notation, local fallbacks, distinct instances and unchanged histories.`);
} finally { await rm(project, { recursive: true, force: true }); }
