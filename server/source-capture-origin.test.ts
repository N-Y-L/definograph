import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { hashContextExecutable, sourceCaptureEngine } from './source-capture-origin.js';
import { WorkerError } from './protocol.js';

const helperURL = new URL('../scripts/source-capture-dependency.mjs', import.meta.url).href;
const { buildFingerprint }: { buildFingerprint: (value: unknown) => string } = await import(helperURL);
const hash = (text: string) => createHash('sha256').update(text).digest('hex');
const manifest = JSON.parse(await readFile(new URL('../vendor/DefinographCapture/UPSTREAM.json', import.meta.url), 'utf8'));

// These are transport/build consistency controls, never evidence of Lean checks.
function identity(contextSha256 = hash('test-only executable')) {
  return { sourceCommit: manifest.sourceCommit, packageSha256: hash('test-only package'),
    leanVersion: 'Lean (version 4.28.0, test)', leanSha256: hash('test-only compiler'),
    artifacts: manifest.modules.map((entry: { module: string; sha256: string }) => ({ module: entry.module,
      sourceSha256: entry.sha256, oleanSha256: hash(entry.module + '/test-only olean'), cSha256: hash(entry.module + '/test-only C') })),
    adapter: { module: 'StatementLens.SourceSnapshot', sourceSha256: hash('adapter source'), oleanSha256: hash('adapter olean'), cSha256: hash('adapter C') },
    contextSourceSha256: hash('context source'), contextCSha256: hash('context C'), contextSha256 };
}

test('host build fingerprints agree with the dependency builder independently of object key order', () => {
  const fields = identity();
  const pins = { ...fields, buildFingerprint: buildFingerprint(fields), libraryPath: '/not-imported/build-library' };
  const expected = { contextSha256: fields.contextSha256, buildFingerprint: pins.buildFingerprint,
    packageSha256: fields.packageSha256, leanSha256: fields.leanSha256 };
  assert.deepEqual(sourceCaptureEngine({ sourceCapture: pins }, fields.contextSha256), expected);
  const reordered = Object.fromEntries(Object.entries(pins).reverse());
  assert.deepEqual(sourceCaptureEngine({ sourceCapture: reordered }, fields.contextSha256), expected);
  assert.deepEqual(sourceCaptureEngine({ sourceCapture: { ...pins, libraryPath: '/another/unused/path' } }, fields.contextSha256), expected);
});

test('changed executable, compiler, adapter or library artifact invalidates the old build record', () => {
  const fields = identity(), pins = { ...fields, buildFingerprint: buildFingerprint(fields), libraryPath: '/unused' };
  for (const change of [
    (v: typeof pins) => { v.contextSha256 = hash('replacement executable'); },
    (v: typeof pins) => { v.leanSha256 = hash('replacement compiler'); },
    (v: typeof pins) => { v.packageSha256 = hash('replacement source package'); },
    (v: typeof pins) => { v.adapter.sourceSha256 = hash('replacement adapter'); },
    (v: typeof pins) => { v.artifacts[0].oleanSha256 = hash('replacement library'); },
    (v: typeof pins) => { v.artifacts.reverse(); },
  ]) {
    const altered = structuredClone(pins); change(altered);
    assert.throws(() => sourceCaptureEngine({ sourceCapture: altered }, fields.contextSha256),
      (error: unknown) => error instanceof WorkerError && error.code === 'EDITOR_CONFIG');
  }
  assert.throws(() => sourceCaptureEngine({ sourceCapture: pins }, hash('different actual executable')), /fingerprint/);
});

test('legacy builds have no source origin and malformed capture records are refused', () => {
  assert.equal(sourceCaptureEngine({}, hash('legacy executable')), undefined);
  for (const value of [null, [], false, {}, { ...identity(), adapter: null },
    { ...identity(), buildFingerprint: 'not a hash' }]) {
    assert.throws(() => sourceCaptureEngine({ sourceCapture: value }, hash('test-only executable')), WorkerError);
  }
});

test('the executable hash describes exact file bytes and refuses non-file inputs', async () => {
  const directory = await mkdtemp(path.join(os.tmpdir(), 'definograph-origin-test-'));
  try {
    const file = path.join(directory, 'context');
    await writeFile(file, 'one\0two\n');
    assert.equal(await hashContextExecutable(file), hash('one\0two\n'));
    await writeFile(file, 'two\0one\n');
    assert.equal(await hashContextExecutable(file), hash('two\0one\n'));
    await assert.rejects(hashContextExecutable(directory), WorkerError);
  } finally { await rm(directory, { recursive: true, force: true }); }
});
