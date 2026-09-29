/** Direct Lean state/retention controls, isolated from native runtime artifacts. */
import { mkdtemp, mkdir, readFile, readdir, copyFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { fileSha256 } from './source-capture-dependency.mjs';

const control = process.argv[2] ?? 'SourceSnapshotControls';
if (!['SourceSnapshotControls', 'SourceOccurrenceControls'].includes(control)) throw new Error('Unknown source control suite.');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(root, '.local/config.json'), 'utf8'));
const pins = config.sourceCapture;
if (!pins?.adapter) throw new Error('Run setup:lean with the source snapshot adapter first.');
if (await fileSha256(config.leanExecutable) !== pins.leanSha256
  || await fileSha256(path.join(root, 'lean/StatementLens/Context.lean')) !== pins.contextSourceSha256
  || await fileSha256(path.join(root, 'lean/StatementLens/SourceSnapshot.lean')) !== pins.adapter.sourceSha256) throw new Error('The native build is stale; run setup:lean first.');
const temporary = await mkdtemp(path.join(os.tmpdir(), 'definograph-snapshot-controls-'));
try {
  // Lean resolves a namespace from a single root. Copy its compiled siblings so
  // compiling a test Context module cannot shadow Export or alter the engine.
  const namespace = path.join(temporary, 'StatementLens');
  await mkdir(namespace);
  for (const file of await readdir(path.join(config.leanPath[0], 'StatementLens'))) {
    if (file.endsWith('.olean')) await copyFile(path.join(config.leanPath[0], 'StatementLens', file), path.join(namespace, file));
  }
  const run = args => {
    const result = spawnSync(config.leanExecutable, args, { cwd: path.join(root, 'lean'), encoding: 'utf8', timeout: 45_000, maxBuffer: 1024 * 1024,
      env: { ...process.env, LEAN_PATH: [temporary, config.leanPath[0], pins.libraryPath].join(path.delimiter) } });
    if (result.error || result.status !== 0) throw new Error(result.error?.message || result.stderr || result.stdout);
    if (result.stdout.trim()) console.log(result.stdout.trim());
  };
  run(['-o', path.join(namespace, 'Context.olean'), 'StatementLens/Context.lean']);
  run([`StatementLens/${control}.lean`]);
} finally { await rm(temporary, { recursive: true, force: true }); }
