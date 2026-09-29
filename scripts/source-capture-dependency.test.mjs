import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cp, mkdtemp, readFile, readdir, realpath, rm, symlink, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';
import { SOURCE_CAPTURE_COMMIT, buildFingerprint, compileSourceCaptureDependency, fileSha256, loadSourceCaptureDependency, sourceImports } from './source-capture-dependency.mjs';

const vendor = fileURLToPath(new URL('../vendor/DefinographCapture', import.meta.url));
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
async function temporary(t) {
  const root = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-dependency-test-')));
  t.after(() => rm(root, { recursive: true, force: true }));
  return root;
}
async function copySnapshot(t) {
  const root = await temporary(t), directory = path.join(root, 'vendor');
  await cp(vendor, directory, { recursive: true });
  const manifest = JSON.parse(await readFile(path.join(directory, 'UPSTREAM.json'), 'utf8'));
  const save = () => writeFile(path.join(directory, 'UPSTREAM.json'), JSON.stringify(manifest));
  return { root, directory, manifest, save };
}

test('vendored files form the exact ordered SourceCapture dependency closure', async () => {
  const snapshot = await loadSourceCaptureDependency(vendor);
  assert.equal(snapshot.manifest.sourceCommit, SOURCE_CAPTURE_COMMIT);
  assert.equal(snapshot.digest, digest(await readFile(path.join(vendor, 'UPSTREAM.json'))));
  assert.equal(snapshot.sources.length, 26);
  assert.equal(snapshot.sources.at(-1).module, 'SourceCapture');
  assert.ok(snapshot.sources.every(source => digest(source.bytes) === source.sha256));
  assert.deepEqual(snapshot.sources.filter(source => ['Fixtures', 'PacketWorker', 'OpenBodies', 'Coordination', 'CoherenceCheck'].includes(source.module)), []);
});

test('import extraction respects nested comments, strings, public imports and source order', () => {
  const source = '/- import False /- nested -/ -/\nprelude\npublic import Lean -- comment\nimport Init Std\ndef example := "import Fake"\n';
  assert.deepEqual(sourceImports(Buffer.from(source)), ['Lean', 'Init', 'Std']);
  assert.throws(() => sourceImports(Buffer.from('/- incomplete')), /unterminated/);
  assert.throws(() => sourceImports(Buffer.from('import ../../Escape')), /unsupported import/);
  assert.throws(() => sourceImports(Buffer.from([0xff])), /encoded data|encoding/i);
});

test('changed or missing source bytes cannot enter the build snapshot', async t => {
  const { directory, manifest } = await copySnapshot(t);
  const file = path.join(directory, manifest.modules[0].source);
  await writeFile(file, (await readFile(file)) + '\n');
  await assert.rejects(loadSourceCaptureDependency(directory), /checksum mismatch/);
  await rm(file);
  await assert.rejects(loadSourceCaptureDependency(directory), /ENOENT/);
});

test('module ordering and declared imports must match the real headers', async t => {
  const { directory, manifest, save } = await copySnapshot(t);
  const last = manifest.modules.length - 1;
  [manifest.modules[0], manifest.modules[last]] = [manifest.modules[last], manifest.modules[0]];
  await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /import order/);
  [manifest.modules[0], manifest.modules[last]] = [manifest.modules[last], manifest.modules[0]];
  manifest.modules[0].imports.push('Lean.Meta');
  await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /import inventory/);
});

test('even repaired hashes cannot admit an outside import or unrelated module', async t => {
  const { directory, manifest, save } = await copySnapshot(t);
  const entry = manifest.modules.at(-1), file = path.join(directory, entry.source), original = await readFile(file);
  let replacement = Buffer.from('import UnreviewedLibrary\n' + original);
  await writeFile(file, replacement); entry.sha256 = digest(replacement); entry.imports = sourceImports(replacement); await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /outside the closure/);
  replacement = Buffer.from('import Lean\ndef isolated : Nat := 1\n');
  await writeFile(file, replacement); entry.sha256 = digest(replacement); entry.imports = sourceImports(replacement); await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /outside the entry import closure/);
});

test('snapshot inventory excludes unlisted files, duplicate entries and wrong commits', async t => {
  const { directory, manifest, save } = await copySnapshot(t);
  const extra = path.join(directory, 'src', 'Unlisted.lean');
  await writeFile(extra, 'import Lean\n');
  await assert.rejects(loadSourceCaptureDependency(directory), /unlisted source/);
  await rm(extra);
  const first = manifest.modules[0]; manifest.modules[0] = manifest.modules[1]; await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /duplicate module/);
  manifest.modules[0] = first; manifest.sourceCommit = '0'.repeat(40); await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /snapshot identity/);
});

test('source paths and symlinks cannot redirect compilation outside the snapshot', async t => {
  const { root, directory, manifest, save } = await copySnapshot(t);
  const entry = manifest.modules[0], originalPath = entry.source;
  entry.source = '../outside.lean'; await save();
  await assert.rejects(loadSourceCaptureDependency(directory), /source path/);
  entry.source = originalPath; await save();
  const file = path.join(directory, originalPath), outside = path.join(root, 'outside.lean');
  await writeFile(outside, await readFile(file)); await rm(file); await symlink(outside, file);
  await assert.rejects(loadSourceCaptureDependency(directory), /fixed location/);
});

test('all modules compile from one verified snapshot with an isolated import path and hashed outputs', async t => {
  const buildDirectory = await temporary(t), snapshot = await loadSourceCaptureDependency(vendor), calls = [];
  const previous = process.env.LEAN_PATH; process.env.LEAN_PATH = '/unreviewed/imports';
  try {
    const result = await compileSourceCaptureDependency({ snapshot, buildDirectory, leanExecutable: '/verified/lean',
      run: async (command, args, options) => {
        calls.push(args.at(-1)); assert.equal(command, '/verified/lean');
        assert.equal((await readdir(options.cwd)).length, 26, 'stage the entire source snapshot before compilation');
        assert.equal(options.env.LEAN_PATH, path.join(path.dirname(options.cwd), 'lib'));
        const source = await readFile(path.join(options.cwd, args.at(-1)));
        await writeFile(args[1], Buffer.concat([Buffer.from('test-only olean\n'), source]));
        await writeFile(args[3], Buffer.concat([Buffer.from('test-only C\n'), source]));
      } });
    assert.deepEqual(calls, snapshot.sources.map(source => source.module + '.lean'));
    assert.equal(result.cFiles.length, 26); assert.equal(result.artifacts.length, 26);
    for (let i = 0; i < result.artifacts.length; i++) {
      assert.equal(result.artifacts[i].sourceSha256, snapshot.sources[i].sha256);
      assert.equal(result.artifacts[i].cSha256, await fileSha256(result.cFiles[i]));
    }
    const identity = { packageSha256: snapshot.digest, artifacts: result.artifacts };
    assert.equal(buildFingerprint(identity), buildFingerprint({ artifacts: result.artifacts, packageSha256: snapshot.digest }));
    assert.notEqual(buildFingerprint(identity), buildFingerprint({ ...identity, packageSha256: 'different' }));
    assert.notEqual(buildFingerprint(identity), buildFingerprint({ ...identity, artifacts: result.artifacts.slice(1) }));
  } finally { if (previous === undefined) delete process.env.LEAN_PATH; else process.env.LEAN_PATH = previous; }
});

test('modified in-memory input and successful compiler calls without outputs are refused', async t => {
  const buildDirectory = await temporary(t), snapshot = await loadSourceCaptureDependency(vendor);
  snapshot.sources[0].bytes[0] ^= 1;
  let calls = 0;
  await assert.rejects(compileSourceCaptureDependency({ snapshot, buildDirectory, leanExecutable: '/verified/lean', run: () => { calls++; } }), /snapshot changed/);
  assert.equal(calls, 0);
  const fresh = await loadSourceCaptureDependency(vendor);
  await assert.rejects(compileSourceCaptureDependency({ snapshot: fresh, buildDirectory, leanExecutable: '/verified/lean', run: () => { calls++; } }), /ENOENT/);
  assert.equal(calls, 1);
});
