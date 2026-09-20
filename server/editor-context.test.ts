import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { analyzeEditorContext, positionOffset, resolveEditorProject } from './editor-context.js';

test('editor coordinates use UTF-16, preserve CRLF and reject surrogate halves', () => {
  const source = 'α🧭\r\nπ = π\n';
  assert.equal(positionOffset(source, { line: 0, character: 3 }), 3);
  assert.equal(positionOffset(source, { line: 1, character: 4 }), 9);
  assert.throws(() => positionOffset(source, { line: 0, character: 2 }), /Unicode/);
  assert.throws(() => positionOffset(source, { line: 0, character: 4 }), /outside/);
  assert.throws(() => positionOffset(source, { line: 3, character: 0 }), /outside/);
});
test('trust refusal happens before source or engine filesystem access', async () => {
  await assert.rejects(analyzeEditorContext({ engineDirectory: '/nonexistent', fileName: '/nonexistent/Main.lean', source: 'True', selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } }, workspaceTrusted: false }), /Workspace Trust/);
});
test('project discovery reads standard and path dependency libraries without evaluating lakefile', async () => {
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-project-paths-'));
  try {
    const root = path.join(temporary, 'project');
    await mkdir(path.join(root, '.lake/build/lib/lean'), { recursive: true });
    await mkdir(path.join(temporary, 'dependency/.lake/build/lib/lean'), { recursive: true });
    await writeFile(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
    const lakefile = '-- This file must never be evaluated by project discovery.\n';
    await writeFile(path.join(root, 'lakefile.lean'), lakefile);
    await writeFile(path.join(root, 'lake-manifest.json'), JSON.stringify({ packages: [{ type: 'path', name: 'dependency', dir: '../dependency' }] }));
    const result = await resolveEditorProject(path.join(root, 'Main.lean'));
    assert.equal(result.libraries.length, 2);
    assert.ok(result.libraries[0]?.endsWith('/project/.lake/build/lib/lean'));
    assert.ok(result.libraries[1]?.endsWith('/dependency/.lake/build/lib/lean'));
    assert.equal(await readFile(path.join(root, 'lakefile.lean'), 'utf8'), lakefile);
    await writeFile(path.join(root, 'lean-toolchain'), 'leanprover/lean4:nightly\n');
    await assert.rejects(resolveEditorProject(path.join(root, 'Main.lean')), /requires leanprover\/lean4:v4.28.0/);
  } finally { await rm(temporary, { recursive: true, force: true }); }
});
