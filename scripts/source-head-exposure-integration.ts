/** Actual trusted editor processes, exact one-body exposure, and retained checks. */
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { analyzeEditorContext, type EditorContextRequest, type EditorRange } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { validateSourceSnapshot } from '../src/editor/source-snapshot.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceOccurrence, type SourceOccurrenceStep } from '../src/editor/source-occurrence.js';
import { validateSourceHeadExposure, type HeadExposureTarget } from '../src/editor/source-head-exposure.js';
import { compilePositionalComponent } from '../src/packets/semantic.js';
import { compileReading } from '../src/reading/compiler.js';
import { compileReadingCues } from '../src/reading/cues.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-head-exposure-')));
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
async function expose(label: string, source: string, selectedText: string, target: HeadExposureTarget, selectedPath: SourceOccurrenceStep[] = []) {
  const request: EditorContextRequest = { engineDirectory: engine, fileName, source, selection: range(source, selectedText), workspaceTrusted: true,
    document: { uri: pathToFileURL(fileName).href, version: ++version } };
  const first = await analyzeEditorContext(request);
  const occurrenceResponse = await analyzeEditorContext({ ...request, occurrence: {
    snapshot: validateSourceSnapshot(first.sourceSnapshot), origin: first.sourceSnapshotOrigin as SourceSnapshotOrigin, path: selectedPath,
  } });
  const snapshot = validateSourceSnapshot(occurrenceResponse.sourceSnapshot);
  const occurrence = validateSourceOccurrence(occurrenceResponse.sourceOccurrence, snapshot);
  const origin = occurrenceResponse.sourceSnapshotOrigin as SourceSnapshotOrigin;
  assert.ok(occurrence.checking.status === 'captured' && occurrence.checking.action.status === 'completed' && occurrence.checking.selected,
    `${label}: no retained original candidate`);
  const originalBytes = canonical(occurrence as unknown as JsonValue);
  const response = await analyzeEditorContext({ ...request, headExposure: { snapshot, origin, occurrence, target } });
  const fresh = validateSourceSnapshot(response.sourceSnapshot);
  const value = validateSourceHeadExposure(response.sourceHeadExposure, fresh, { snapshot, occurrence });
  assert.equal(value.parentCaptureId, origin.captureId); assert.notEqual(value.captureId, origin.captureId);
  assert.equal(value.captureId, (response.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId);
  assert.equal(value.target, target); exact(value.path, selectedPath);
  assert.equal(canonical(occurrence as unknown as JsonValue), originalBytes, 'Original outcomes must remain immutable.');
  records.push({ label, source, selection: request.selection, parent: { snapshot, origin, occurrence }, response });
  return { value, request, parent: { snapshot, origin, occurrence } };
}
function candidate(result: Awaited<ReturnType<typeof expose>>) {
  const { value } = result;
  assert.equal(value.checking.status, 'captured', JSON.stringify(value.checking));
  if (value.checking.status !== 'captured') throw new Error('Missing captured checks.');
  assert.equal(value.checking.action.status, 'completed', JSON.stringify(value.checking.action));
  const exposure = value.checking.exposure;
  assert.ok(exposure && exposure.status === 'candidate', JSON.stringify(exposure));
  assert.equal(exposure.checking.status, 'completed', JSON.stringify(exposure.checking));
  assert.equal(value.checking.checks.length, 9);
  assert.ok(value.checking.checks.every(receipt => receipt.outcome.tag === 'accepted'), JSON.stringify(value.checking.checks));
  exact(exposure.result.home, value.checking.selected!.home);
  exact(exposure.before, value.checking.selected![value.target]);
  const model = compilePositionalComponent(exposure.result, { target: 'term', sourceIdentity: `exposure:${value.captureId}`, sourcePath: ['checking', 'exposure', 'result'], sourceOrigin: 'definition-head-exposure' });
  assert.ok(model.document, model.reason);
  const reading = compileReading(model.document);
  return { exposure, model, reading };
}
try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(fileName, '-- Saved source deliberately differs from every submitted buffer.\n');
  const saved = await readFile(fileName);
  for (const labels of [['relay', 'A', 'B', 'C', 'weave', 'harbor', 'seed'], ['passage', 'U', 'V', 'W', 'cipher', 'lantern', 'origin']]) {
    const [head, A, B, C, f, g, x] = labels;
    const source = `def ${head} {${A} ${B} ${C} : Type} (${f} : ${A} → ${B}) (${g} : ${B} → ${C}) (${x} : ${A}) : ${C} := ${g} (${f} ${x})\nexample (${A} ${B} ${C} : Type) (${f} : ${A} → ${B}) (${g} : ${B} → ${C}) (${x} : ${A}) (unused : Nat) : ${C} := ${head} ${f} ${g} ${x}\n`;
    const result = candidate(await expose(`composition ${head}`, source, `${head} ${f} ${g} ${x}`, 'term'));
    assert.equal(result.model.document!.relations.filter(r => r.kind === 'application').length, 2);
    assert.equal(result.exposure.betaApplications, 6);
    const cues = compileReadingCues(result.reading, result.model.document!);
    assert.ok(JSON.stringify(cues).includes(f) && JSON.stringify(cues).includes(g));
  }
  const alias = candidate(await expose('function-type alias',
    'def Route (A B : Type) : Type := A → B\nexample (A B : Type) (f : Route A B) : Route A B := f\n', 'f', 'type'));
  assert.equal((alias.exposure.result.term as JsonValue[])[0], 'forallE');
  assert.equal((alias.exposure.result.type as JsonValue[])[0], 'sort');
  exact(alias.exposure.carrierSort, ['succ', (alias.exposure.result.type as JsonValue[])[1]]);
  candidate(await expose('dependent type alias',
    'def Fibre (n : Nat) : Type := Fin n\nexample (n : Nat) (x : Fibre n) : Fibre n := x\n', 'x', 'type'));
  candidate(await expose('recursive body remains one finite layer',
    'def recurseLayer : Nat → Nat\n  | 0 => 0\n  | n + 1 => recurseLayer n\nexample (n : Nat) : Nat := recurseLayer n\n', 'recurseLayer n', 'term'));
  const ownedText = 'fun (n : Nat) => have n : Nat := n; plain n';
  const owned = candidate(await expose('owned have retains exact original home',
    `def plain (n : Nat) : Nat := n\ndef owned := ${ownedText}\n`, ownedText, 'term', ['lamBody', 'letBody']));
  const home = owned.exposure.result.home.telescope as JsonValue[];
  assert.equal(home[0], 'letE'); assert.equal(home[3], true);
  for (const [label, source, selectedText] of [
    ['opaque definition', 'opaque hidden (n : Nat) : Nat := n\nexample (n : Nat) : Nat := hidden n\n', 'hidden n'],
    ['theorem head', 'theorem anchor : True := True.intro\nexample : True := anchor\n', 'anchor'],
    ['local head', 'example (n : Nat) : Nat := n\n', 'n'],
  ]) {
    const { value } = await expose(label, source, selectedText, 'term');
    assert.ok(value.checking.status === 'captured' && value.checking.exposure?.status === 'unavailable', JSON.stringify(value.checking));
    assert.equal(value.checking.checks.length, 6);
  }
  const stale = await expose('stale parent control', 'def plain (n : Nat) : Nat := n\nexample (n : Nat) : Nat := plain n\n', 'plain n', 'term');
  await assert.rejects(analyzeEditorContext({ ...stale.request, source: stale.request.source + '\n', headExposure: { ...stale.parent, target: 'term' } }), /no longer matches/);
  const cancelled = new AbortController(); cancelled.abort();
  await assert.rejects(analyzeEditorContext({ ...stale.request, signal: cancelled.signal, headExposure: { ...stale.parent, target: 'term' } }), /cancelled/);
  assert.deepEqual(await readFile(fileName), saved, 'Fixture source must stay unchanged.');
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_HEAD_EXPOSURE_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Store generated source captures outside the application repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
  }
  console.log(`Verified ${records.length} fresh definition-head records, exact replay/typing/conversion associations, explicit refusals, stale/cancellation gates and unchanged fixture/build.`);
} finally { await rm(project, { recursive: true, force: true }); }
