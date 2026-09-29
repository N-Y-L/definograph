/** Native adapter regression tests: only this temporary project is compiled. */
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeEditorContext, type EditorRange } from '../server/editor-context.js';
import { runBoundedProcess } from '../server/worker.js';
import { compileSemanticDocument } from '../src/semantic/index.js';
import { compileReading } from '../src/reading/index.js';
import type { Analysis, StatementNode } from '../src/core/types.js';
import { GUIDED_CONTEXT_CONTRACT } from '../src/editor/guided-context-contract.js';
const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(engine, '.local/config.json'), 'utf8'));
const fixture = await mkdtemp(path.join(os.tmpdir(), 'statementlens-editor-test-'));
const fileName = path.join(fixture, 'Main.lean');
const position = (source: string, index: number) => { const before = source.slice(0, index); const lines = before.split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
function selection(source: string, term: string): EditorRange { const start = source.lastIndexOf(term); assert.ok(start >= 0); return { start: position(source, start), end: position(source, start + term.length) }; }
function nodes(root: StatementNode): StatementNode[] { return [root, ...root.children.flatMap(nodes)]; }
let checks = 0;
async function analyze(source: string, term: string, options: { expansion?: { constants: string[]; maxDepth: number }; mathlib?: boolean; expectError?: boolean } = {}): Promise<Analysis> {
  const response = await analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: selection(source, term), workspaceTrusted: true,
    expansion: options.expansion, libraryPaths: options.mathlib ? config.leanPath.filter((entry: string) => !entry.includes('/leantex/')) : undefined });
  if (options.expectError) { assert.equal(response.ok, false, `Expected rejection: ${term}`); checks++; return response as unknown as Analysis; }
  assert.equal(response.ok, true, JSON.stringify(response)); checks++;
  const result = response as unknown as Analysis;
  assert.equal(result.guidedContextContract, GUIDED_CONTEXT_CONTRACT);
  const semantic = compileSemanticDocument(result), reading = compileReading(semantic);
  assert.equal(reading.nodes.length, nodes(result.tree).length);
  assert.equal(result.provenance?.inputMode, 'editor');
  assert.equal(result.validation, 'kernel-type-checked-context-fragment');
  assert.equal(result.source, source);
  return result;
}
try {
  await mkdir(path.join(fixture, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(fixture, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(path.join(fixture, 'lakefile.toml'), 'name = "editor_fixture"\n[[lean_lib]]\nname = "Dep"\n');
  await writeFile(path.join(fixture, 'lake-manifest.json'), JSON.stringify({ version: '1.1.0', packagesDir: '.lake/packages', packages: [] }));
  const dependency = 'namespace Fixture\ndef Reflexive (n : Nat) : Prop := n = n\nend Fixture\n';
  await writeFile(path.join(fixture, 'Dep.lean'), dependency);
  await writeFile(fileName, '-- Saved file is deliberately different from the editor buffer.\n');
  await runBoundedProcess(config.leanExecutable, { args: ['-o', '.lake/build/lib/lean/Dep.olean', 'Dep.lean'], cwd: fixture, env: { ...process.env, LEAN_PATH: '' }, timeoutMs: 10_000 });
  const originals = await Promise.all(['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Dep.lean', 'Main.lean'].map(async name => [name, await readFile(path.join(fixture, name), 'utf8')] as const));

  const source = 'import Dep\nopen Fixture\nexample (n : Nat) (h : n = 2) : Reflexive n := by rfl\n';
  const exact = await analyze(source, 'Reflexive n');
  assert.equal(exact.tree.kind, 'parameter');
  assert.equal(exact.tree.binder?.name, 'n');
  assert.equal(exact.tree.children[0]?.kind, 'implies');
  assert.equal(exact.tree.children[0]?.binder?.role, 'assumption');
  assert.ok(exact.definitions?.some(definition => definition.name === 'Fixture.Reflexive' && definition.module === 'Dep'));
  assert.equal(exact.provenance?.mathlibRevision, undefined);
  const expanded = await analyze(source, 'Reflexive n', { expansion: { constants: ['Fixture.Reflexive'], maxDepth: 2 } });
  assert.ok(nodes(expanded.tree).some(node => node.expansion?.constant === 'Fixture.Reflexive'));
  assert.ok(compileSemanticDocument(expanded).relations.some(relation => relation.kind === 'equality'));
  await writeFile(path.join(engine, '.local/editor-preview-fixture.json'), JSON.stringify({ analysis: expanded, document: { uri: `file://${fileName}`, version: 7, fileName, selection: selection(source, 'Reflexive n') } }));

  const incomplete = await analyze('import Dep\nexample (n : Nat) : Fixture.Reflexive n := by\n  exact unknownProof\n', 'Fixture.Reflexive n');
  assert.ok(incomplete.diagnostics.some((d: any) => d.severity === 'error'));
  await analyze('example (n : Nat) : missingPredicate n := by rfl\n', 'missingPredicate n', { expectError: true });
  const proof = await analyze('example (P : Prop) (h : P) : P := by exact h\n', 'h');
  assert.equal(proof.provenance?.selectionKind, 'proof-type');
  assert.ok(nodes(proof.tree).some(node => node.binder?.name === 'h' && node.binder.role === 'assumption'));
  const auxiliaryCases = [
    { name: 'proposition-valued example', ordinaryCount: 0, source: 'example : 2 + 2 = 4 := rfl\n', term: 'rfl' },
    { name: 'named theorem', ordinaryCount: 1, source: 'theorem helper (n : Nat) : n = n := rfl\n', term: 'rfl' },
    { name: 'genuine hypothesis', ordinaryCount: 2, source: 'example (P : Prop) (h : P) : P := h\n', term: 'h' },
    { name: 'tactic hypothesis', ordinaryCount: 2, source: 'example (P : Prop) (h : P) : P := by exact h\n', term: 'h' },
    { name: 'explicit __h parameter', ordinaryCount: 2, source: 'example (P : Prop) (__h : P) : P := __h\n', term: '__h' },
    { name: 'lambda implementation detail', ordinaryCount: 2, source: 'example (P : Prop) (h : P) : P := (fun (__h : P) => __h) h\n', term: '__h' },
    { name: 'tactic have implementation detail', ordinaryCount: 2, source: 'example (P : Prop) (h : P) : P := by\n  have __h : P := h\n  exact __h\n', term: '__h' },
    { name: 'term let implementation detail', ordinaryCount: 2, source: 'example (P : Prop) (h : P) : P := let __h : P := h; __h\n', term: '__h' },
    { name: 'recursive reference', ordinaryCount: 2, source: 'def recur (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | k + 1 => if recur k = 0 then 0 else recur k\n', term: 'recur k = 0' },
    { name: 'duplicate names', ordinaryCount: 1, source: 'example (_example : Nat) : _example = _example := rfl\n', term: 'rfl' },
  ];
  const auxiliaryCaptures: { name: string; analysis: Analysis }[] = [];
  for (const control of auxiliaryCases) {
    const analysis = await analyze(control.source, control.term);
    const all = nodes(analysis.tree), entries = all.filter(node => node.binder?.role === 'auxiliary');
    assert.equal(analysis.tree.kind, 'auxiliary', control.name);
    assert.equal(analysis.tree.binder?.declarationKind, 'auxDecl');
    assert.equal(entries.length, ['lambda implementation detail', 'tactic have implementation detail'].includes(control.name) ? 2 : 1);
    for (const entry of entries) {
      assert.equal(entry.kind, 'auxiliary');
      assert.equal(entry.children.length, 1, 'recorded entries have no premise child');
      assert.equal(entry.expression.kind, 'lambda');
      assert.equal(entry.binder?.structure, undefined);
      assert.equal(entry.binder?.typeExpansion, undefined);
      assert.ok(!all.some(node => node.binder?.dependsOn.includes(entry.binder!.id)));
    }
    assert.equal(analysis.provenance?.auxiliaryContextEntries, entries.length);
    assert.equal(analysis.provenance?.contextParameters, control.ordinaryCount);
    if (control.name === 'genuine hypothesis' || control.name === 'tactic hypothesis')
      assert.ok(all.some(node => node.binder?.name === 'h' && node.binder.role === 'assumption' && node.children.length === 2));
    if (control.name === 'explicit __h parameter') assert.ok(all.some(node => node.binder?.name === '__h' && node.binder.role === 'assumption'));
    if (['lambda implementation detail', 'tactic have implementation detail'].includes(control.name)) assert.ok(entries.some(node => node.binder?.name === '__h' && node.binder.declarationKind === 'implDetail'));
    if (control.name === 'term let implementation detail') assert.ok(!all.some(node => node.binder?.name === '__h'), 'the legacy guided view substitutes this local let');
    if (control.name === 'recursive reference') {
      const selected = all.at(-1)!;
      assert.ok(JSON.stringify(selected.expression).includes(`"id":"${analysis.tree.binder!.id}"`), 'recursive reference retains the recorded binder identity');
    }
    const semantic = compileSemanticDocument(analysis), reading = compileReading(semantic);
    const entryIds = new Set(entries.map(node => node.binder!.id));
    assert.ok(semantic.choices.every(choice => !entryIds.has(choice.binderId)));
    assert.ok(reading.nodes.filter(node => entries.some(entry => entry.id === node.id)).every(node => !/\b(assume|assumption|hypothesis|given|premise)\b/i.test(node.phrase)));
    auxiliaryCaptures.push({ name: control.name, analysis });
  }
  if (process.env.DEFINOGRAPH_AUXILIARY_CAPTURES) await writeFile(process.env.DEFINOGRAPH_AUXILIARY_CAPTURES, JSON.stringify(auxiliaryCaptures, null, 2) + '\n', { flag: 'wx' });
  for (const guidedContextContract of [undefined, 'unsupported']) {
    const resultFile = path.join(fixture, 'incompatible-result.json');
    await runBoundedProcess(config.contextExecutable, { cwd: fixture,
      input: JSON.stringify({ source: '#check True\n', fileName, mainModule: 'Main', captureId: '550e8400-e29b-41d4-a716-446655440000', startByte: 7, endByte: 11, guidedContextContract }) + '\n',
      env: { ...process.env, LEAN_PATH: config.leanPath.join(path.delimiter), STATEMENTLENS_LEAN_SYSROOT: config.leanSysroot, STATEMENTLENS_CONTEXT_RESULT: resultFile }, timeoutMs: 10_000 });
    const refused = JSON.parse(await readFile(resultFile, 'utf8'));
    assert.equal(refused.ok, false);
    assert.match(refused.error, /Incompatible guided context format/);
    assert.equal(refused.guidedContextContract, GUIDED_CONTEXT_CONTRACT);
    assert.ok(refused.sourceSnapshot, 'contract refusal retains the separate raw capture');
    assert.equal(refused.tree, undefined);
    checks++;
  }
  const dependent = await analyze('example (A : Type) (B : A → Type) (x : A) (y : B x) : y = y := rfl\n', 'y = y');
  assert.deepEqual(nodes(dependent.tree).flatMap(node => node.binder ? [node.binder.name] : []), ['A', 'B', 'x', 'y']);
  assert.ok(JSON.stringify(dependent.tree).includes('context.body.body.binder'));
  const unicode = await analyze('-- 🧭 Unicode offset\nexample (α : Type) (π : α) : π = π := rfl\n', 'π = π');
  assert.equal(unicode.sourceTerms?.[0]?.startByte, Buffer.byteLength(unicode.source.slice(0, unicode.source.lastIndexOf('π = π'))));
  await analyze('def sample : Prop := let P : Prop := sorry; P\n', 'P', { expectError: true });
  await analyze('example : True := let h : True := by sorry; h\n', 'h', { expectError: true });
  await analyze('def bad : Prop := by sorry\n#check bad\n', 'bad', { expansion: { constants: ['bad'], maxDepth: 1 }, expectError: true });
  await analyze('example (x : Nat) : x = x := rfl\n', 'x', { expectError: true });
  const fake = await analyze('def Set (A : Type) := A\nexample (x : Set Nat) : x = x := rfl\n', 'x = x');
  assert.equal(fake.tree.binder?.typeDescriptor?.kind, 'structure');
  assert.equal(fake.tree.expression.kind, 'lambda');
  assert.ok(JSON.stringify(fake.tree).includes('"canonical":false'));
  const fakeBall = await analyze('namespace Metric\ndef ball (x r : Nat) : Nat := x\nend Metric\nexample (x r : Nat) : Metric.ball x r = x := rfl\n', 'Metric.ball x r = x');
  assert.ok(!compileSemanticDocument(fakeBall).relations.some(relation => relation.kind === 'metric-region'));
  const canonicalSet = await analyze('import Mathlib.Data.Set.Operations\n#check ∀ (s t : Set Nat), s ∪ t = s ∪ t\n', '∀ (s t : Set Nat), s ∪ t = s ∪ t', { mathlib: true });
  assert.ok(compileSemanticDocument(canonicalSet).relations.some(relation => relation.kind === 'set-construction'));
  const customUnion = await analyze('import Mathlib.Data.Set.Operations\ninstance (priority := 2000) : Union (Set Nat) := ⟨fun a _ => a⟩\n#check ∀ (s t : Set Nat), s ∪ t = s\n', '∀ (s t : Set Nat), s ∪ t = s', { mathlib: true });
  assert.ok(!compileSemanticDocument(customUnion).relations.some(relation => relation.kind === 'set-construction'));
  const metric = await analyze('import Mathlib.Topology.MetricSpace.Basic\n#check ∀ (x r : ℝ), x ∈ Metric.ball x r\n', '∀ (x r : ℝ), x ∈ Metric.ball x r', { mathlib: true });
  assert.ok(nodes(metric.tree).filter(node => node.binder).every(node => node.binder?.domain === 'unknown'));
  assert.ok(JSON.stringify(metric.tree).includes('"metric":"unknown"'));

  const cursor = position(source, source.lastIndexOf('Reflexive n') + 'Reflexive '.length);
  const atCursor = await analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: {start: cursor, end: cursor}, workspaceTrusted: true });
  assert.equal(atCursor.ok, true); assert.equal((atCursor.provenance as any).selectionKind, 'proposition'); checks++;
  await analyze('#eval IO.println "project console output"\n#check True\n', 'True');
  const slow = '#eval IO.sleep 2000\n#check True\n';
  await assert.rejects(analyzeEditorContext({engineDirectory:engine,fileName,source:slow,selection:selection(slow,'True'),workspaceTrusted:true,timeoutMs:50}), /time|seconds/); checks++;
  const liveCancellation = new AbortController();
  const running = analyzeEditorContext({engineDirectory:engine,fileName,source:slow,selection:selection(slow,'True'),workspaceTrusted:true,signal:liveCancellation.signal});
  const cancellationTimer = setTimeout(()=>liveCancellation.abort(),50);
  try { await assert.rejects(running,/cancelled/); checks++; } finally {clearTimeout(cancellationTimer);}

  await assert.rejects(analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: selection(source, 'Reflexive n'), workspaceTrusted: false }), /Workspace Trust/); checks++;
  await writeFile(path.join(fixture, 'lean-toolchain'), 'leanprover/lean4:v4.27.0\n');
  await assert.rejects(analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: selection(source, 'Reflexive n'), workspaceTrusted: true }), /4.28.0/); checks++;
  await writeFile(path.join(fixture, 'lean-toolchain'), originals[0]![1]);
  const cancellation = new AbortController(); cancellation.abort();
  await assert.rejects(analyzeEditorContext({ engineDirectory: engine, fileName, source, selection: selection(source, 'Reflexive n'), workspaceTrusted: true, signal: cancellation.signal }), /cancelled/); checks++;
  for (const [name, contents] of originals) assert.equal(await readFile(path.join(fixture, name), 'utf8'), contents, `${name} was modified`);
  console.log(`Editor context integration: ${checks} native/boundary cases passed; project source/config remained unchanged.`);
} finally { await rm(fixture, { recursive: true, force: true }); }
