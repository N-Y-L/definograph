/** Actual InfoTree/source capture controls in a disposable Lean project. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { analyzeEditorContext, type EditorRange } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { runBoundedProcess } from '../server/worker.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceSnapshot } from '../src/editor/source-snapshot.js';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../src/packets/packet.js';
import { buildRawInspection, readRawInspection } from '../src/packets/raw.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const config = JSON.parse(configText);
const executable = path.join(engine, '.local/statementlens-context');
const executableSha256 = await hashContextExecutable(executable);
const expectedEngine = sourceCaptureEngine(config, executableSha256);
assert.ok(expectedEngine, 'Rebuild the context sidecar with the verified source capture dependency first.');
const helperURL = new URL('./source-capture-dependency.mjs', import.meta.url).href;
const { loadSourceCaptureDependency, fileSha256 }: {
  loadSourceCaptureDependency: (directory: string) => Promise<{ digest: string; manifest: { sourceCommit: string }; sources: { module: string; sha256: string }[] }>;
  fileSha256: (file: string) => Promise<string>;
} = await import(helperURL);
async function verifyBuildInputs() {
  const snapshot = await loadSourceCaptureDependency(path.join(engine, 'vendor/DefinographCapture'));
  const pins = config.sourceCapture;
  assert.equal(pins.sourceCommit, snapshot.manifest.sourceCommit);
  assert.equal(pins.packageSha256, snapshot.digest);
  assert.deepEqual(pins.artifacts.map((artifact: { module: string; sourceSha256: string }) => ({ module: artifact.module, sha256: artifact.sourceSha256 })),
    snapshot.sources.map(({ module, sha256 }) => ({ module, sha256 })));
  const buildDirectory = path.dirname(pins.libraryPath);
  for (const artifact of pins.artifacts) {
    const relative = artifact.module.replaceAll('.', '/');
    assert.equal(await fileSha256(path.join(buildDirectory, 'src', relative + '.lean')), artifact.sourceSha256);
    assert.equal(await fileSha256(path.join(pins.libraryPath, relative + '.olean')), artifact.oleanSha256);
    assert.equal(await fileSha256(path.join(buildDirectory, 'c', relative + '.c')), artifact.cSha256);
  }
  assert.equal(await fileSha256(config.leanExecutable), pins.leanSha256);
  assert.equal(await fileSha256(path.join(engine, 'lean/StatementLens/SourceSnapshot.lean')), pins.adapter.sourceSha256);
  assert.equal(await fileSha256(path.join(config.leanPath[0], 'StatementLens/SourceSnapshot.olean')), pins.adapter.oleanSha256);
  assert.equal(await fileSha256(path.join(buildDirectory, 'c/SourceSnapshot.c')), pins.adapter.cSha256);
  assert.equal(await fileSha256(path.join(engine, 'lean/StatementLens/Context.lean')), pins.contextSourceSha256);
  assert.equal(await fileSha256(path.join(engine, '.local/context.c')), pins.contextCSha256);
  assert.equal(await hashContextExecutable(executable), executableSha256);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
}
await verifyBuildInputs();
const fixture = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-source-snapshot-')));
const fileName = path.join(fixture, 'Main.lean');
const captures: { label: string; source: string; selection: EditorRange; response: unknown }[] = [];
const seenAttempts = new Set<string>();
const { canonical } = createExactJsonTools();
const sha = (value: string) => createHash('sha256').update(value).digest('hex');
const exactName = (value: string): JsonValue => value.split('.').reduce<JsonValue>((parent, part) => ['str', parent, part], ['anonymous']);
const object = (value: JsonValue): JsonObject => { assert.ok(value !== null && typeof value === 'object' && !Array.isArray(value)); return value; };
const array = (value: JsonValue): JsonValue[] => { assert.ok(Array.isArray(value)); return value; };
function position(source: string, offset: number) {
  const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length };
}
function selection(source: string, term: string): EditorRange {
  const start = source.lastIndexOf(term); assert.ok(start >= 0, term);
  return { start: position(source, start), end: position(source, start + term.length) };
}
function frame(snapshot: JsonObject, field: 'original' | 'prepared'): JsonObject {
  const section = object(snapshot[field]);
  assert.equal(section.status, 'available', `${field}: ${JSON.stringify(section)}`);
  return object(section.frame);
}
function declaration(input: JsonObject, name: string): JsonObject {
  const found = array(input.originalDeclarations).map(object).find(value => JSON.stringify(value.userName) === JSON.stringify(exactName(name)));
  assert.ok(found, `missing original declaration ${name}`); return found;
}
function hasConstant(value: JsonValue, label: string): boolean {
  if (value === null || typeof value !== 'object') return false;
  if (Array.isArray(value)) return value[0] === 'const' && JSON.stringify(value[1]) === JSON.stringify(exactName(label)) || value.some(child => hasConstant(child, label));
  return Object.values(value).some(child => hasConstant(child, label));
}
let expressionAssignments = 0, universeAssignments = 0;
async function analyze(label: string, source: string, selected: string) {
  const range = selection(source, selected), version = captures.length + 1;
  const document = { uri: pathToFileURL(fileName).href, version };
  const response = await analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: range,
    workspaceTrusted: true, document });
  captures.push({ label, source, selection: range, response });
  assert.ok(response.sourceSnapshot, `${label}: ${JSON.stringify(response)}`);
  const snapshot = validateSourceSnapshot(response.sourceSnapshot) as unknown as JsonObject;
  const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  assert.equal(origin.kind, 'local-editor-process-snapshot');
  assert.equal(origin.sourceSha256, sha(source));
  assert.deepEqual(origin.engine, expectedEngine);
  assert.deepEqual(origin.document, document);
  assert.deepEqual(origin.selection, range);
  assert.equal(origin.project.root, fixture);
  assert.equal(origin.project.dependencyTracking, 'snapshot-paths-only');
  assert.deepEqual(origin.project.libraryPaths, [path.join(fixture, '.lake/build/lib/lean')]);
  assert.ok(!seenAttempts.has(origin.captureId)); seenAttempts.add(origin.captureId);
  const selectedStart = source.lastIndexOf(selected) + selected.length - selected.trimStart().length;
  const expectedStart = Buffer.byteLength(source.slice(0, selectedStart));
  const expectedEnd = expectedStart + Buffer.byteLength(selected.trim());
  const selectedRange = object(snapshot.selection);
  assert.equal(selectedRange.requestedStartByte, expectedStart);
  assert.equal(selectedRange.requestedEndByte, expectedEnd);
  assert.equal(selectedRange.startByte, expectedStart);
  assert.equal(selectedRange.endByte, expectedEnd);
  assert.equal(object(snapshot.policy).preparation, 'Lean.instantiateMVars');
  const original = object(snapshot.original), prepared = object(snapshot.prepared);
  const metavariables: Record<string, { expression: number; level: number }> = {};
  for (const field of ['original', 'prepared'] as const) {
    const section = object(snapshot[field]);
    if (section.status !== 'available') continue;
    const built = buildRawInspection({ family: 'frame', value: section.frame }, { sourceIdentity: origin.sourceSha256, sourcePath: ['sourceSnapshot', field, 'frame'] });
    assert.ok(built.ok, `${label}/${field}: ${JSON.stringify(built)}`);
    const readback = readRawInspection(built.value);
    assert.ok(readback.ok, `${label}/${field}: ${JSON.stringify(readback)}`);
    assert.equal(readback.value.family, 'frame');
    assert.equal(canonical(readback.value.value), canonical(section.frame));
    metavariables[field] = {
      expression: built.value.nodes.filter(node => node.family === 'expression' && node.tag === 'mvar').length,
      level: built.value.nodes.filter(node => node.family === 'level' && node.tag === 'mvar').length,
    };
  }
  if (original.status === 'available' && prepared.status === 'available') {
    expressionAssignments += Math.max(0, metavariables.original.expression - metavariables.prepared.expression);
    universeAssignments += Math.max(0, metavariables.original.level - metavariables.prepared.level);
    const originalLocals = array(object(original.frame).originalDeclarations).map(object);
    const preparedLocals = array(object(prepared.frame).originalDeclarations).map(object);
    assert.deepEqual(preparedLocals.map(({ constructor, index, fvarId, userName, kind, binderInfo, nondep }) => ({ constructor, index, fvarId, userName, kind, binderInfo, nondep })),
      originalLocals.map(({ constructor, index, fvarId, userName, kind, binderInfo, nondep }) => ({ constructor, index, fvarId, userName, kind, binderInfo, nondep })));
    originalLocals.forEach((local, i) => {
      if (String(local.constructor) === 'ldecl' && local.nondep === true) assert.deepEqual(preparedLocals[i].value, local.value, 'opaque stored metadata must not be instantiated');
    });
  }
  const checking = object(snapshot.checking);
  if (checking.status === 'captured') {
    const binding = object(checking.binding), preparedFrame = frame(snapshot, 'prepared');
    assert.equal(binding.attempt, origin.captureId);
    assert.equal(binding.operation, 'editor-source');
    assert.deepEqual(binding.sourceTerm, preparedFrame.sourceTerm);
    assert.deepEqual(binding.sourceType, preparedFrame.sourceType);
    assert.deepEqual(object(binding.context).originalDeclarations, preparedFrame.originalDeclarations);
    assert.deepEqual(binding.universeParams, prepared.checkerUniverseParams);
    for (const check of array(checking.checks).map(object)) {
      assert.equal(object(check.subject).attempt, origin.captureId);
      assert.deepEqual(check.heartbeatBound, ['nat', '200000']);
    }
  }
  return { response, snapshot, checking, metavariables };
}
function accepted(checking: JsonObject) {
  assert.equal(checking.status, 'captured', JSON.stringify(checking));
  assert.equal(object(checking.action).status, 'completed');
  assert.ok(array(checking.checks).length > 0, 'completion alone is not checking evidence');
  assert.ok(array(checking.checks).map(object).every(check => object(check.outcome).tag === 'accepted'), JSON.stringify(checking.checks));
}

try {
  await mkdir(path.join(fixture, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(fixture, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(path.join(fixture, 'lakefile.toml'), 'name = "source_snapshot_control"\n[[lean_lib]]\nname = "Dep"\n');
  await writeFile(path.join(fixture, 'lake-manifest.json'), JSON.stringify({ version: '1.1.0', packagesDir: '.lake/packages', packages: [] }));
  await writeFile(path.join(fixture, 'Dep.lean'), 'namespace SnapshotControl\ndef Reflexive (n : Nat) : Prop := n = n\nend SnapshotControl\n');
  await writeFile(fileName, '-- The on-disk file deliberately differs from every active buffer.\n');
  await runBoundedProcess(config.leanExecutable, { args: ['-o', '.lake/build/lib/lean/Dep.olean', 'Dep.lean'], cwd: fixture,
    env: { ...process.env, LEAN_PATH: '' }, timeoutMs: 10_000 });
  const files = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Dep.lean', 'Main.lean', '.lake/build/lib/lean/Dep.olean'];
  const before = await Promise.all(files.map(async file => [file, await readFile(path.join(fixture, file))] as const));

  const proof = await analyze('selected proof remains a proof', 'example (P : Prop) (h : P) : P := by exact h\n', 'h');
  assert.equal(proof.response.ok, true);
  assert.equal((proof.response.provenance as Record<string, unknown>).selectionKind, 'proof-type');
  assert.equal(proof.response.pretty, 'P');
  const proofFrame = frame(proof.snapshot, 'prepared');
  assert.deepEqual(proofFrame.sourceTerm, ['fvar', declaration(proofFrame, 'h').fvarId]);
  assert.deepEqual(proofFrame.sourceType, ['fvar', declaration(proofFrame, 'P').fvarId]);
  assert.notDeepEqual(proofFrame.sourceTerm, proofFrame.sourceType); accepted(proof.checking);

  const dependent = await analyze('actual dependent local context', 'example (A : Type) (B : A → Type) (x : A) (y : B x) : y = y := rfl\n', 'y = y');
  const dependentFrame = frame(dependent.snapshot, 'prepared');
  assert.deepEqual(declaration(dependentFrame, 'y').type, ['app', ['fvar', declaration(dependentFrame, 'B').fvarId], ['fvar', declaration(dependentFrame, 'x').fvarId]]);
  accepted(dependent.checking);

  const letResult = await analyze('genuine local definition is retained', 'example (x : Nat) : True := by\n  let y : Nat := x\n  have h : y = x := rfl\n  exact True.intro\n', 'y = x');
  const letFrame = frame(letResult.snapshot, 'prepared'), y = declaration(letFrame, 'y');
  assert.equal(y.constructor, 'ldecl'); assert.equal(y.nondep, false);
  assert.deepEqual(y.value, ['fvar', declaration(letFrame, 'x').fvarId]); accepted(letResult.checking);

  const levels = await analyze('actual universe parameters', 'universe u v\nexample (A : Type u) (B : Type v) (x : A) (y : B) : x = x ∧ y = y := And.intro rfl rfl\n', 'x = x ∧ y = y');
  const parameters = array(object(levels.snapshot.prepared).checkerUniverseParams);
  assert.ok(parameters.some(name => JSON.stringify(name) === JSON.stringify(exactName('u'))));
  assert.ok(parameters.some(name => JSON.stringify(name) === JSON.stringify(exactName('v')))); accepted(levels.checking);

  for (const [label, source, selected] of [
    ['inferred application assignments', 'example (α : Type) (x : α) : id x = x := rfl\n', 'id x = x'],
    ['inferred lambda assignments', 'example (x : Nat) : (fun y => y) x = x := rfl\n', '(fun y => y) x = x'],
  ]) accepted((await analyze(label, source, selected)).checking);

  const imported = await analyze('active buffer uses compiled project dependency', 'import Dep\nexample (n : Nat) : SnapshotControl.Reflexive n := by rfl\n', 'SnapshotControl.Reflexive n');
  assert.equal(imported.response.ok, true); accepted(imported.checking);

  const laterError = await analyze('valid statement survives unrelated proof diagnostics', 'example (n : Nat) : n = n := by exact missingProof\n', 'n = n');
  assert.equal(laterError.response.ok, true);
  assert.ok(laterError.response.diagnostics.some(value => !!value && typeof value === 'object' && (value as { severity?: string }).severity === 'error'));
  accepted(laterError.checking);

  const sorry = await analyze('placeholder stays raw and checking remains unsupported', 'example (P : Prop) : P := by exact sorry\n', 'sorry');
  assert.equal(sorry.response.ok, false);
  assert.ok(hasConstant(frame(sorry.snapshot, 'prepared').sourceTerm, 'sorryAx'));
  assert.equal(sorry.checking.status, 'unavailable'); assert.equal(sorry.checking.kind, 'unsupported');
  assert.equal(sorry.checking.attempted, false);

  const nonProposition = await analyze('nonproposition survives guided refusal', 'def selectedNat (x : Nat) : Nat := Nat.succ x\n', 'Nat.succ x');
  assert.equal(nonProposition.response.ok, false);
  assert.ok(hasConstant(frame(nonProposition.snapshot, 'prepared').sourceTerm, 'Nat.succ'));
  accepted(nonProposition.checking);

  // These elaborators create real saved InfoTrees through the ordinary frontend;
  // the adapter does not receive a hand-constructed TermInfo or guessed assignment.
  const assigned = await analyze('assigned expression and universe in an actual InfoTree', [
    'import Lean', 'open Lean Meta Elab Term',
    'elab "snapshotAssigned" : term => do',
    '  let level ← mkFreshLevelMVar',
    '  assignLevelMVar level.mvarId! (.succ .zero)',
    '  let expression ← mkFreshExprMVar (some (.sort level))',
    '  expression.mvarId!.assign (mkConst ``Nat)',
    '  pure expression',
    'def assignedType : Type := snapshotAssigned', '',
  ].join('\n'), 'snapshotAssigned');
  assert.equal(array(frame(assigned.snapshot, 'original').sourceTerm)[0], 'mvar');
  assert.deepEqual(frame(assigned.snapshot, 'prepared').sourceTerm, ['const', exactName('Nat'), []]);
  assert.ok(assigned.metavariables.original.expression > assigned.metavariables.prepared.expression);
  assert.ok(assigned.metavariables.original.level > assigned.metavariables.prepared.level);
  accepted(assigned.checking);

  const metadata = await analyze('unsupported source metadata remains exact after guided refusal', [
    'import Lean', 'open Lean Meta Elab Term',
    'elab "snapshotMetadata" : term =>',
    '  pure (.mdata ⟨[(`note, .ofString "retained source metadata")]⟩ (mkRawNatLit 3))',
    'def metadataNumber : Nat := snapshotMetadata', '',
  ].join('\n'), 'snapshotMetadata');
  assert.equal(metadata.response.ok, false);
  assert.equal(array(frame(metadata.snapshot, 'original').sourceTerm)[0], 'mdata');
  assert.deepEqual(frame(metadata.snapshot, 'original').sourceTerm, frame(metadata.snapshot, 'prepared').sourceTerm);
  assert.ok(canonical(frame(metadata.snapshot, 'prepared').sourceTerm).includes('retained source metadata'));
  assert.equal(metadata.checking.status, 'unavailable');
  assert.equal(metadata.checking.kind, 'unsupported');
  assert.equal(metadata.checking.attempted, true);

  const unicode = await analyze('Unicode CRLF and trimmed selection', '-- 🧭 Unicode offsets\r\nexample (α : Type) (π : α) :  π = π  := rfl\r\n', '  π = π  ');
  assert.equal(unicode.response.ok, true); accepted(unicode.checking);

  const manyLocals = await analyze('128 locals retain raw input when check output exceeds depth limit',
    `#check fun (${Array.from({ length: 128 }, (_, i) => `x${i}`).join(' ')} : Nat) => x0\n`, 'x0');
  assert.equal(array(frame(manyLocals.snapshot, 'prepared').originalDeclarations).length, 128);
  assert.equal(manyLocals.checking.status, 'unavailable');
  assert.equal(manyLocals.checking.kind, 'limit');
  assert.equal(manyLocals.checking.phase, 'checking-output');
  assert.equal(manyLocals.checking.attempted, true);

  for (const [file, contents] of before) assert.deepEqual(await readFile(path.join(fixture, file)), contents, `${file} was changed`);
  await verifyBuildInputs();
  console.log(`Source snapshot integration: ${captures.length} actual InfoTree cases passed; observed instantiated expression occurrences=${expressionAssignments}, universe occurrences=${universeAssignments}; project files unchanged; ${config.sourceCapture.artifacts.length}-module package and native build hashes verified.`);
} finally {
  try {
    const output = process.env.DEFINOGRAPH_SOURCE_SNAPSHOT_CAPTURES;
    if (output) {
      const destination = path.resolve(output), relative = path.relative(engine, destination);
      assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Store generated source captures outside the application repository.');
      await mkdir(path.dirname(destination), { recursive: true });
      await writeFile(destination, JSON.stringify(captures, null, 2) + '\n');
    }
  } finally { await rm(fixture, { recursive: true, force: true }); }
}
