import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import type { Analysis } from '../src/core/types.ts';
import { inspectSmallDefinitions } from '../src/semantic/inspection.ts';
import { compileSemanticDocument } from '../src/semantic/compiler.ts';
import { compileReading, compileReadingCues } from '../src/reading/index.ts';
import { createWorkerBackend } from '../server/worker.ts';
import { analyzeEditorContext } from '../server/editor-context.ts';

const root = process.cwd();
const backend = createWorkerBackend({ rootDir: root });
let passed = 0;
const check = (name: string) => { passed++; console.log(`PASS ${name}`); };
try {
  const source = '∀ (A B : Type) (f : A → B) (g : B → A), Function.LeftInverse g f';
  const raw = await backend.analyze(source, undefined, { previewDefinitions: true });
  assert.equal(raw.ok, true, JSON.stringify(raw));
  const analysis = raw as unknown as Analysis;
  assert.ok(analysis.definitionPreviews?.some(preview => preview.constant === 'Function.LeftInverse'));
  const inspected = inspectSmallDefinitions(analysis);
  assert.equal(inspected.automaticInspection?.constant, 'Function.LeftInverse');
  assert.equal(inspected.source, source);
  assert.equal(inspected.originalExpression, analysis.expression);
  const doc = compileSemanticDocument(inspected);
  assert.ok(doc.relations.some(relation => relation.kind === 'equality'));
  assert.ok(compileReadingCues(compileReading(doc), doc).cues.some(cue => cue.intent === 'compare'));
  check('a native left-inverse definition becomes a scoped map-comparison reading');

  const original = await backend.analyze(source);
  assert.equal(original.ok, true);
  assert.ok(!original.definitionPreviews || !(original.definitionPreviews as unknown[]).length);
  assert.equal(inspectSmallDefinitions(original as unknown as Analysis).automaticInspection, undefined);
  check('native previews are optional and do not leak into later requests');

  const explicit = await backend.analyze(source, undefined, { previewDefinitions: true, expansion: { constants: ['Function.LeftInverse'], maxDepth: 1 } });
  assert.equal(explicit.ok, true);
  assert.ok(!explicit.definitionPreviews || !(explicit.definitionPreviews as unknown[]).length);
  check('explicit inspection bypasses automatic candidate exploration');

  const known = await backend.analyze('∀ (A B : Type) (f : A → B), Function.Injective f', undefined, { previewDefinitions: true });
  assert.equal(known.ok, true);
  assert.equal(inspectSmallDefinitions(known as unknown as Analysis).automaticInspection, undefined);
  check('an already interpreted function property remains folded');

  const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-preview-test-'));
  try {
    const fileName = path.join(temporary, 'Main.lean'), counter = path.join(temporary, 'counter.txt');
    await writeFile(path.join(temporary, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
    await writeFile(counter, '');
    const selected = 'Wrapped (n = n)';
    const lines = ['import Lean', 'def Wrapped (P : Prop) : Prop := P',
      `#eval do IO.FS.writeFile ${JSON.stringify(counter)} ((← IO.FS.readFile ${JSON.stringify(counter)}) ++ ".")`,
      `example (n : Nat) : ${selected} := by rfl`];
    const source = lines.join('\n');
    await writeFile(fileName, source);
    const start = lines[3]!.indexOf(selected);
    const result = await analyzeEditorContext({ engineDirectory: root, fileName, source, workspaceTrusted: true, previewDefinitions: true,
      selection: { start: { line: 3, character: start }, end: { line: 3, character: start + selected.length } } });
    assert.equal(result.ok, true, JSON.stringify(result));
    assert.equal((result as unknown as Analysis).validation, 'kernel-type-checked-context-fragment');
    const expanded = inspectSmallDefinitions(result as unknown as Analysis);
    assert.equal(expanded.automaticInspection?.constant, 'Wrapped');
    assert.equal(await readFile(counter, 'utf8'), '.', 'The trusted source command executes exactly once despite optional previews');
    assert.equal(await readFile(fileName, 'utf8'), source);
    check('editor previews reuse the checked context without replaying source commands');
  } finally { await rm(temporary, { recursive: true, force: true }); }
} finally { backend.close?.(); }
console.log(`${passed}/5 native automatic-inspection checks passed.`);
