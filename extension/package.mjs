import { spawnSync } from 'node:child_process';
import { constants } from 'node:fs';
import { chmod, copyFile, lstat, mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { listFiles, PackageManager } from '@vscode/vsce';

const root = path.dirname(fileURLToPath(import.meta.url));
const shippedFiles = ['LICENSE', 'README.md', 'dist/extension.cjs', 'package.json'];
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const run = (directory, args, env = process.env) => {
  const result = spawnSync(process.execPath, args, { cwd: directory, env, stdio: 'inherit', shell: false });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`Packaging command failed (${result.status ?? result.signal}).`);
};

/** Package only the bundled controller and its public documentation. */
export async function packageExtension({ directory = root, output, epoch = process.env.SOURCE_DATE_EPOCH ?? '946684800' } = {}) {
  if (!/^\d+$/.test(epoch) || !Number.isSafeInteger(Number(epoch)) || Number(epoch) < 315532800 || Number(epoch) > 4354819199) {
    throw new Error('SOURCE_DATE_EPOCH must be a whole second in the ZIP date range (1980–2107).');
  }
  const manifest = JSON.parse(await readFile(path.join(directory, 'package.json'), 'utf8'));
  const target = output ? path.resolve(output) : path.resolve(directory, `../.local/statement-lens-editor-${manifest.version}.vsix`);
  try {
    await lstat(target);
    throw new Error(`Refusing to overwrite ${target}. Choose a new --out path.`);
  } catch (error) { if (error.code !== 'ENOENT') throw error; }
  run(directory, ['build.mjs']);
  const inventory = (await listFiles({ cwd: directory, packageManager: PackageManager.None })).sort();
  if (JSON.stringify(inventory) !== JSON.stringify(shippedFiles)) {
    throw new Error(`Unexpected extension package inventory: ${inventory.join(', ')}`);
  }
  const pins = {};
  const contents = new Map();
  for (const name of shippedFiles) {
    const bytes = await readFile(path.join(directory, name));
    contents.set(name, bytes); pins[name] = sha(bytes);
  }
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'definograph-vsix-'));
  try {
    const staging = path.join(temporary, 'extension');
    for (const [name, bytes] of contents) {
      const file = path.join(staging, name);
      await mkdir(path.dirname(file), { recursive: true });
      await writeFile(file, bytes);
      await chmod(file, 0o644); // Normalize ZIP permissions independently of the caller's umask.
    }
    await writeFile(path.join(staging, '.vscodeignore'), ['**', ...shippedFiles.map(name => '!' + name)].join('\n') + '\n');
    const staged = path.join(temporary, 'extension.vsix');
    run(staging, [path.join(directory, 'node_modules/@vscode/vsce/vsce'), 'package', '--no-dependencies', '--out', staged],
      { ...process.env, SOURCE_DATE_EPOCH: epoch, TZ: 'UTC' });
    for (const name of shippedFiles) {
      if (sha(await readFile(path.join(directory, name))) !== pins[name]) throw new Error(`Package input changed during assembly: ${name}. Retry on fixed sources.`);
    }
    await mkdir(path.dirname(target), { recursive: true });
    // VSCE writes its private temporary file; exclusive copying preserves earlier packages.
    await copyFile(staged, target, constants.COPYFILE_EXCL);
    const result = { output: target, sha256: sha(await readFile(target)), sourceDateEpoch: Number(epoch), inputs: pins };
    console.log(JSON.stringify(result, null, 2));
    return result;
  } finally { await rm(temporary, { recursive: true, force: true }); }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const { values } = parseArgs({ options: { out: { type: 'string' }, help: { type: 'boolean' } } });
    if (values.help) console.log('node extension/package.mjs [--out /absolute/path/to/new.vsix]\nBuilds the controller only; requires separately built browser assets and Lean setup. Existing output is never overwritten. SOURCE_DATE_EPOCH defaults to 2000-01-01 UTC for reproducible archives.');
    else await packageExtension({ output: values.out });
  } catch (error) { console.error(error.message); process.exitCode = 1; }
}
