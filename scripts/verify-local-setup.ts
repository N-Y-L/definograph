/** Check the configured local build and one native capture without rebuilding it. */
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { access, mkdir, mkdtemp, readFile, readdir, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import { loadWorkerConfig } from '../server/config.js';
import { analyzeEditorContext } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { isSourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceSnapshot } from '../src/editor/source-snapshot.js';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const exec = promisify(execFile);
const sha = (bytes: Buffer | string) => createHash('sha256').update(bytes).digest('hex');
const helperURL = new URL('./source-capture-dependency.mjs', import.meta.url).href;
const { loadSourceCaptureDependency, fileSha256 }: {
  loadSourceCaptureDependency: (directory: string) => Promise<{ digest: string; manifest: { sourceCommit: string }; sources: { module: string; sha256: string }[] }>;
  fileSha256: (file: string) => Promise<string>;
} = await import(helperURL);

try {
  const [major, minor] = process.versions.node.split('.').map(Number);
  assert.ok(major! > 22 || major === 22 && minor! >= 12, 'Use Node.js 22.12 or newer.');
  const configFile = path.join(root, '.local/config.json');
  const configText = await readFile(configFile, 'utf8');
  const config = JSON.parse(configText);
  const checked = await loadWorkerConfig(configFile);
  const executable = path.join(root, '.local/statementlens-context');
  const engine = sourceCaptureEngine(config, await hashContextExecutable(executable));
  assert.ok(engine, 'Rebuild the Lean engine with source capture support: npm run setup:lean.');
  const pins = config.sourceCapture;
  const dependency = await loadSourceCaptureDependency(path.join(root, 'vendor/DefinographCapture'));
  assert.equal(pins.sourceCommit, dependency.manifest.sourceCommit, 'Rebuild: source capture revision changed.');
  assert.equal(pins.packageSha256, dependency.digest, 'Rebuild: source capture manifest changed.');
  assert.deepEqual(pins.artifacts.map((v: { module: string; sourceSha256: string }) => ({ module: v.module, sha256: v.sourceSha256 })), dependency.sources.map(({ module, sha256 }) => ({ module, sha256 })), 'Rebuild: source capture inputs changed.');
  const verifiedFiles: Record<string, string> = {};
  async function matches(file: string, expected: string) {
    const digest = await fileSha256(file);
    assert.equal(digest, expected, `Rebuild: recorded artifact differs: ${file}`);
    verifiedFiles[file] = digest;
  }
  const nativeBuild = path.dirname(pins.libraryPath);
  for (const artifact of pins.artifacts) {
    const name = artifact.module.replaceAll('.', '/');
    await matches(path.join(nativeBuild, 'src', name + '.lean'), artifact.sourceSha256);
    await matches(path.join(pins.libraryPath, name + '.olean'), artifact.oleanSha256);
    await matches(path.join(nativeBuild, 'c', name + '.c'), artifact.cSha256);
  }
  await matches(checked.leanExecutable, pins.leanSha256);
  await matches(path.join(root, 'lean/StatementLens/SourceSnapshot.lean'), pins.adapter.sourceSha256);
  await matches(path.join(checked.leanPath[0]!, 'StatementLens/SourceSnapshot.olean'), pins.adapter.oleanSha256);
  await matches(path.join(nativeBuild, 'c/SourceSnapshot.c'), pins.adapter.cSha256);
  await matches(path.join(root, 'lean/StatementLens/Context.lean'), pins.contextSourceSha256);
  await matches(path.join(root, '.local/context.c'), pins.contextCSha256);
  await matches(executable, pins.contextSha256);
  const leanVersion = (await exec(checked.leanExecutable, ['--version'], { timeout: 10_000 })).stdout.trim();
  assert.equal(leanVersion, pins.leanVersion);
  assert.match(leanVersion, /^Lean \(version 4\.28\.0(?:[, )])/);

  // Confirm the existing dependency checkout revisions; no fetch or Lake command.
  const manifest = JSON.parse(await readFile(path.join(root, 'lean/lake-manifest.json'), 'utf8'));
  const mathlibLibrary = checked.leanPath.find(p => path.basename(path.resolve(p, '../../../..')) === 'mathlib');
  assert.ok(mathlibLibrary, 'Missing configured mathlib cache. Run npm run setup:lean.');
  const packages = path.dirname(path.resolve(mathlibLibrary, '../../../..'));
  const dependencyRevisions: Record<string, string> = {};
  for (const item of manifest.packages) {
    const revision = (await exec('git', ['-C', path.join(packages, item.name), 'rev-parse', 'HEAD'], { timeout: 10_000 })).stdout.trim();
    assert.equal(revision, item.rev, `Configured dependency ${item.name} differs from the pinned manifest.`);
    dependencyRevisions[item.name] = revision;
  }

  const browserFiles: Record<string, string> = {};
  async function browserInventory(directory: string) {
    for (const entry of await readdir(directory, { withFileTypes: true })) {
      const file = path.join(directory, entry.name);
      assert.ok(!entry.isSymbolicLink(), 'Browser build must not contain symlinks.');
      if (entry.isDirectory()) await browserInventory(file);
      else if (entry.isFile()) browserFiles[path.relative(root, file)] = await fileSha256(file);
    }
  }
  await access(path.join(root, 'dist/index.html'));
  await browserInventory(path.join(root, 'dist'));
  const html = await readFile(path.join(root, 'dist/index.html'), 'utf8');
  const linkedAssets: string[] = [];
  const assetReference = (reference: string, base: string) => {
    const url = new URL(reference, base);
    assert.equal(url.origin, 'http://local', 'Browser entry assets must be local.');
    const file = path.resolve(root, 'dist', '.' + decodeURIComponent(url.pathname));
    assert.ok(file.startsWith(path.join(root, 'dist') + path.sep), 'Browser asset escapes dist.');
    const name = path.relative(root, file);
    assert.ok(browserFiles[name], `Missing browser asset ${name}. Run npm run build.`);
    linkedAssets.push(name);
    return file;
  };
  const entryReferences = [...html.matchAll(/<(script|link)\b[^>]*\b(?:src|href)\s*=\s*["']([^"']+)["'][^>]*>/gi)];
  assert.match(html, /<html\b/i, 'dist/index.html is not a built browser entry.');
  assert.ok(entryReferences.some(match => match[1]!.toLowerCase() === 'script'), 'Browser entry has no script. Run npm run build.');
  for (const match of entryReferences) {
    const file = assetReference(match[2]!, 'http://local/');
    if (file.endsWith('.css')) {
      const css = await readFile(file, 'utf8');
      for (const link of css.matchAll(/url\(\s*["']?([^\s"')]+)["']?\s*\)/g)) {
        if (!link[1]!.startsWith('data:')) assetReference(link[1]!, 'http://local/' + path.relative(path.join(root, 'dist'), file));
      }
    }
  }
  const fixture = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-setup-check-')));
  let capture;
  try {
    const fileName = path.join(fixture, 'Main.lean');
    const source = '#check ∀ (n : Nat), n = n\n';
    const selection = { start: { line: 0, character: 7 }, end: { line: 0, character: source.trimEnd().length } };
    await mkdir(path.join(fixture, '.lake/build/lib/lean'), { recursive: true });
    await writeFile(path.join(fixture, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
    await writeFile(fileName, source);
    const response = await analyzeEditorContext({ engineDirectory: root, fileName, source, selection,
      document: { uri: pathToFileURL(fileName).href, version: 1 }, workspaceTrusted: true });
    assert.equal(response.ok, true, JSON.stringify(response));
    validateSourceSnapshot(response.sourceSnapshot);
    assert.ok(isSourceSnapshotOrigin(response.sourceSnapshotOrigin));
    assert.deepEqual(response.sourceSnapshotOrigin.engine, engine);
    assert.deepEqual(response.sourceSnapshotOrigin.selection, selection);
    assert.equal(response.sourceSnapshotOrigin.sourceSha256, sha(source));
    capture = { source, selection, origin: response.sourceSnapshotOrigin };
  } finally { await rm(fixture, { recursive: true, force: true }); }
  assert.equal(await readFile(configFile, 'utf8'), configText, 'Configuration changed during verification; retry after builds finish.');
  for (const [file, digest] of Object.entries(verifiedFiles)) await matches(file, digest);
  for (const [file, digest] of Object.entries(browserFiles)) assert.equal(await fileSha256(path.join(root, file)), digest, 'Browser build changed during verification.');
  console.log(JSON.stringify({ status: 'local setup verified', node: process.version, leanVersion, configSha256: sha(configText),
    engine, verifiedFiles, dependencyRevisions, browserFiles, linkedAssets: [...new Set(linkedAssets)], smokeCapture: capture,
    boundary: 'Checks recorded build consistency, browser entry references and one native capture. Build browser assets from fixed sources first; this does not certify all dynamic browser behavior, imported cache contents or release-wide behavior.' }, null, 2));
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 1;
}
