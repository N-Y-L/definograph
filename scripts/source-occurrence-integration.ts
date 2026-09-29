/** Real editor processes: dependent occurrence homes, refusals and parent identity. */
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { analyzeEditorContext, type EditorContextRequest, type EditorRange } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { validateSourceSnapshot, type SourceSnapshot } from '../src/editor/source-snapshot.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceOccurrence, type SourceOccurrence, type SourceOccurrenceStep } from '../src/editor/source-occurrence.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-source-occurrence-')));
const fileName = path.join(project, 'Main.lean');
const canonical = createExactJsonTools().canonical;
const exact = (a: unknown, b: unknown, message = 'Exact constructor data must agree.') => assert.equal(canonical(a as JsonValue), canonical(b as JsonValue), message);
const name = (value: string): JsonValue => value.split('.').reduce<JsonValue>((p, v) => ['str', p, v], ['anonymous']);
const captures: { label: string; source: string; selection: EditorRange; parent: unknown; response: unknown }[] = [];
let version = 0, refusals = 0;
function range(source: string, selected: string): EditorRange {
  const start = source.lastIndexOf(selected); assert.ok(start >= 0);
  const position = (offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
  return { start: position(start), end: position(start + selected.length) };
}
interface Parent { request: EditorContextRequest; snapshot: SourceSnapshot; origin: SourceSnapshotOrigin }
function contextArity(from: Parent): number {
  assert.equal(from.snapshot.prepared.status, 'available');
  if (from.snapshot.prepared.status !== 'available') throw new Error('missing prepared source');
  return from.snapshot.prepared.frame.originalDeclarations.length;
}
async function parent(source: string, selected: string): Promise<Parent> {
  const request = { engineDirectory: engine, fileName, source, selection: range(source, selected), workspaceTrusted: true,
    document: { uri: pathToFileURL(fileName).href, version: ++version } };
  const result = await analyzeEditorContext(request);
  return { request, snapshot: validateSourceSnapshot(result.sourceSnapshot), origin: result.sourceSnapshotOrigin as SourceSnapshotOrigin };
}
async function check(label: string, from: Parent, selectedPath: SourceOccurrenceStep[], replacement = from.snapshot): Promise<SourceOccurrence> {
  const result = await analyzeEditorContext({ ...from.request, occurrence: { snapshot: replacement, origin: from.origin, path: selectedPath } });
  const fresh = validateSourceSnapshot(result.sourceSnapshot);
  const occurrence = validateSourceOccurrence(result.sourceOccurrence, fresh);
  assert.equal(occurrence.parentCaptureId, from.origin.captureId);
  assert.notEqual(occurrence.captureId, from.origin.captureId);
  assert.equal(occurrence.captureId, (result.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId);
  exact(occurrence.path, selectedPath);
  captures.push({ label, source: from.request.source, selection: from.request.selection, parent: { snapshot: replacement, origin: from.origin }, response: result });
  return occurrence;
}
function selected(value: SourceOccurrence, arity: number) {
  assert.equal(value.checking.status, 'captured', JSON.stringify(value.checking));
  if (value.checking.status !== 'captured') throw new Error('missing checks');
  assert.equal(value.checking.action.status, 'completed', JSON.stringify(value.checking.action));
  assert.equal(value.checking.checks.length, 6);
  assert.ok(value.checking.selected);
  assert.equal(value.checking.selected.home.arity, arity);
  return value.checking.selected;
}
function allAccepted(value: SourceOccurrence) {
  assert.equal(value.checking.status, 'captured');
  if (value.checking.status === 'captured') assert.ok(value.checking.checks.every(r => r.outcome.tag === 'accepted'), JSON.stringify(value.checking.checks));
}
function unavailable(value: SourceOccurrence, phase: string, attempted: boolean) {
  assert.equal(value.checking.status, 'unavailable', JSON.stringify(value.checking));
  if (value.checking.status === 'unavailable') { assert.equal(value.checking.phase, phase); assert.equal(value.checking.attempted, attempted); }
}
try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(fileName, '-- Saved source deliberately differs from every submitted buffer.\n');
  const before = await readFile(fileName);
  const inc = await parent('def occurrenceInc : Nat → Nat := fun (n : Nat) => Nat.succ n\n', 'fun (n : Nat) => Nat.succ n');
  for (const [label, steps, arity, tag] of [
    ['root', [], 0, 'lam'], ['lambda domain', ['lamDomain'], 0, 'const'],
    ['lambda body', ['lamBody'], 1, 'app'], ['application function', ['lamBody', 'appFun'], 1, 'const'],
    ['application argument', ['lamBody', 'appArg'], 1, 'bvar'],
  ] as [string, SourceOccurrenceStep[], number, string][]) {
    const result = await check(label, inc, steps);
    const value = selected(result, contextArity(inc) + arity); assert.equal((value.term as JsonValue[])[0], tag); allAccepted(result);
    if (label === 'application argument') exact(value.term, ['bvar', ['nat', '0']]);
  }
  const prod = await parent('def occurrenceType : Type := ∀ (n : Nat), Fin n → Nat\n', '∀ (n : Nat), Fin n → Nat');
  for (const [label, steps, arity] of [
    ['dependent product domain', ['piBody', 'piDomain'], 1], ['dependent product body', ['piBody', 'piBody'], 2],
  ] as [string, SourceOccurrenceStep[], number][]) { const result = await check(label, prod, steps); selected(result, contextArity(prod) + arity); allAccepted(result); }

  for (const kind of ['let', 'have'] as const) {
    const term = `fun (n : Nat) => ${kind} n : Nat := n; fun (x : Fin n) => x`;
    const owned = await parent(`def occurrenceOwned := ${term}\n`, term);
    for (const [label, steps, arity] of [
      ['owned value', ['lamBody', 'letValue'], 1],
      ['dependent domain', ['lamBody', 'letBody', 'lamDomain'], 2],
      ['dependent body', ['lamBody', 'letBody', 'lamBody'], 3],
    ] as [string, SourceOccurrenceStep[], number][]) {
      const result = await check(`${kind}: ${label}`, owned, steps); const value = selected(result, contextArity(owned) + arity); allAccepted(result);
      if (arity > 1) {
        const home = value.home.telescope as JsonValue[];
        const letHome = (arity === 3 ? home[1] : home) as JsonValue[];
        assert.equal(letHome[0], 'letE'); assert.equal(letHome[3], kind === 'have');
      }
    }
  }
  const genuine = await parent('example (x : Nat) : True := by\n  let y : Nat := x\n  have h : y = x := rfl\n  exact True.intro\n', 'y = x');
  const genuineResult = await check('genuine external local definition', genuine, ['appArg']);
  assert.ok(genuineResult.checking.status === 'captured' && genuineResult.checking.selected);
  assert.equal((genuineResult.checking.selected.home.telescope as JsonValue[])[0], 'letE'); allAccepted(genuineResult);

  const universe = await parent('universe u\ndef occurrenceIdentity {A : Type u} : A → A := fun x => x\n', 'fun x => x');
  const universeResult = await check('universe polymorphic body', universe, ['lamBody']); selected(universeResult, contextArity(universe) + 1); allAccepted(universeResult);

  const projection = await parent(['import Lean', 'open Lean Meta Elab Term',
    'elab "occurrenceProjection" : term => do',
    '  let pair ← elabTerm (← `(term| ((3 : Nat), (4 : Nat)))) none',
    '  pure (.proj ``Prod 0 pair)',
    'def occurrenceFirst : Nat := occurrenceProjection', ''].join('\n'), 'occurrenceProjection');
  const projectionResult = await check('projection value', projection, ['projValue']); selected(projectionResult, contextArity(projection)); allAccepted(projectionResult);

  const metadata = await parent(['import Lean', 'open Lean Meta Elab Term',
    'elab "occurrenceMetadata" : term => pure (.mdata ⟨[(`note, .ofString "exact retained metadata")]⟩ (mkRawNatLit 3))',
    'def occurrenceMetadataNumber : Nat := occurrenceMetadata', ''].join('\n'), 'occurrenceMetadata');
  const metadataResult = await check('semantic metadata is explicitly unsupported', metadata, []);
  unavailable(metadataResult, 'occurrence-capture', true);
  if (metadataResult.checking.status === 'unavailable') assert.equal(metadataResult.checking.kind, 'unsupported');

  const assigned = await parent(['import Lean', 'open Lean Meta Elab Term',
    'elab "occurrenceAssigned" : term => do',
    '  let expression ← mkFreshExprMVar (some (mkConst ``Nat))',
    '  expression.mvarId!.assign (mkApp (mkConst ``Nat.succ) (mkRawNatLit 3))',
    '  pure expression', 'def occurrenceAssignedNumber : Nat := occurrenceAssigned', ''].join('\n'), 'occurrenceAssigned');
  assert.equal(assigned.snapshot.original.status, 'available');
  if (assigned.snapshot.original.status === 'available') assert.equal((assigned.snapshot.original.frame.sourceTerm as JsonValue[])[0], 'mvar');
  const assignedResult = await check('prepared path after expression assignment', assigned, ['appArg']);
  exact(selected(assignedResult, contextArity(assigned)).term, ['lit', ['natVal', ['nat', '3']]]); allAccepted(assignedResult);

  const rejected = await parent(['import Lean', 'open Lean Meta Elab Term',
    'elab "occurrenceIllTyped" : term => pure (mkApp (mkConst ``Nat.succ) (mkConst ``True.intro))',
    'def occurrenceBad : Nat := occurrenceIllTyped', ''].join('\n'), 'occurrenceIllTyped');
  const rejectedResult = await check('invalid root with valid selected child', rejected, ['appArg']);
  selected(rejectedResult, contextArity(rejected));
  assert.equal(rejectedResult.checking.status, 'captured');
  if (rejectedResult.checking.status === 'captured') {
    assert.equal(rejectedResult.checking.checks[1].outcome.tag, 'rejected');
    assert.equal(rejectedResult.checking.checks[3].outcome.tag, 'rejected');
    assert.equal(rejectedResult.checking.checks[5].outcome.tag, 'accepted');
  }
  const absent = await check('nonexistent path retains source receipts', inc, ['projValue']);
  assert.equal(absent.checking.status, 'captured');
  if (absent.checking.status === 'captured') {
    assert.equal(absent.checking.action.status, 'error'); assert.equal(absent.checking.checks.length, 2); assert.equal(absent.checking.selected, null);
  }
  const altered = structuredClone(inc.snapshot);
  assert.equal(altered.prepared.status, 'available');
  if (altered.prepared.status === 'available') altered.prepared.frame.sourceType = ['const', name('Nat'), []];
  // Remove old checks: they cannot be rebound to a modified frame.
  altered.checking = { status: 'unavailable', kind: 'prerequisite', phase: 'test-parent', reason: 'Parent mutation control.', attempted: false };
  unavailable(await check('changed prepared frame is refused', inc, [], validateSourceSnapshot(altered)), 'parent-match', false);
  const changedDeclaration = structuredClone(inc.snapshot); changedDeclaration.selection.parentDeclaration = name('DifferentDeclaration') as typeof changedDeclaration.selection.parentDeclaration;
  unavailable(await check('changed parent declaration is refused', inc, [], validateSourceSnapshot(changedDeclaration)), 'parent-match', false);

  for (const origin of [
    { ...inc.origin, sourceSha256: '0'.repeat(64) },
    { ...inc.origin, document: { ...inc.origin.document!, version: inc.origin.document!.version + 1 } },
    { ...inc.origin, engine: { ...inc.origin.engine, contextSha256: '0'.repeat(64) } },
  ]) {
    await assert.rejects(analyzeEditorContext({ ...inc.request, occurrence: { snapshot: inc.snapshot, origin, path: [] } })); refusals++;
  }
  const controller = new AbortController(); controller.abort();
  await assert.rejects(analyzeEditorContext({ ...inc.request, signal: controller.signal, occurrence: { snapshot: inc.snapshot, origin: inc.origin, path: [] } })); refusals++;
  assert.deepEqual(await readFile(fileName), before);
  assert.equal(await hashContextExecutable(executable), executableHash);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  if (process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_CAPTURES) await writeFile(process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_CAPTURES, JSON.stringify(captures, null, 2) + '\n');
  console.log(`Source occurrence integration: ${captures.length} actual captures and ${refusals} host/cancellation refusals passed; project source and engine unchanged.`);
} finally {
  if (process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_CAPTURES) await writeFile(process.env.DEFINOGRAPH_SOURCE_OCCURRENCE_CAPTURES, JSON.stringify(captures, null, 2) + '\n');
  await rm(project, { recursive: true, force: true });
}
