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
