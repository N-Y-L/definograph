import assert from 'node:assert/strict';
import { chmod, mkdtemp, mkdir, readFile, rm, symlink, utimes, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
import test from 'node:test';
import { listFiles, PackageManager } from '@vscode/vsce';
import { packageExtension } from './package.mjs';

const root = path.dirname(fileURLToPath(import.meta.url));
// Use the ZIP reader already required by the pinned VSCE packaging dependency.
const { open } = createRequire(import.meta.resolve('@vscode/vsce'))('yauzl');
const entries = file => new Promise((resolve, reject) => open(file, { lazyEntries: true }, (error, zip) => {
  if (error) return reject(error);
  const names = [];
  zip.on('error', reject);
  zip.on('entry', entry => { names.push(entry.fileName); zip.readEntry(); });
  zip.on('end', () => resolve(names.sort()));
  zip.readEntry();
}));
test('package excludes development/private files, reproduces bytes, and preserves existing output', async () => {
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'definograph-package-test-'));
  const originalTimezone = process.env.TZ;
  try {
    const directory = path.join(temporary, 'extension');
    await mkdir(path.join(directory, 'test'), { recursive: true });
    await mkdir(path.join(directory, 'notes'));
    for (const name of ['package.json', '.vscodeignore', 'LICENSE']) await writeFile(path.join(directory, name), await readFile(path.join(root, name)));
    await writeFile(path.join(directory, 'README.md'), '# Package test\nA controller-only package fixture.\n');
    await writeFile(path.join(directory, 'test/host-journey.cjs'), 'do not ship');
    await writeFile(path.join(directory, 'notes/private.md'), 'do not ship');
    await writeFile(path.join(directory, '.env'), 'DO_NOT_SHIP=fixture');
    await writeFile(path.join(directory, 'build.mjs'), "import {mkdir,writeFile} from 'node:fs/promises'; await mkdir('dist',{recursive:true}); await writeFile('dist/extension.cjs','exports.activate = function () {};\\n');\n");
    await symlink(path.join(root, 'node_modules'), path.join(directory, 'node_modules'), 'dir');
    process.env.TZ = 'UTC';
    const first = await packageExtension({ directory, output: path.join(temporary, 'one.vsix'), epoch: '946684800' });
    assert.deepEqual((await listFiles({ cwd: directory, packageManager: PackageManager.None })).sort(), ['LICENSE', 'README.md', 'dist/extension.cjs', 'package.json']);
    assert.deepEqual(await entries(first.output), ['[Content_Types].xml', 'extension.vsixmanifest', 'extension/LICENSE.txt', 'extension/dist/extension.cjs', 'extension/package.json', 'extension/readme.md']);
    await utimes(path.join(directory, 'README.md'), new Date(), new Date());
    await chmod(path.join(directory, 'README.md'), 0o755);
    await chmod(path.join(directory, 'LICENSE'), 0o700);
    process.env.TZ = 'America/Chicago';
    const second = await packageExtension({ directory, output: path.join(temporary, 'two.vsix'), epoch: '946684800' });
    assert.equal(first.sha256, second.sha256, 'timestamps, timezone and source permissions must not change the archive');
    await assert.rejects(packageExtension({ directory, output: first.output }), /Refusing to overwrite/);
    assert.deepEqual(await readFile(first.output), await readFile(second.output));
    await assert.rejects(packageExtension({ directory, output: path.join(temporary, 'bad.vsix'), epoch: 'invalid' }), /SOURCE_DATE_EPOCH/);
  } finally {
    if (originalTimezone === undefined) delete process.env.TZ; else process.env.TZ = originalTimezone;
    await rm(temporary, { recursive: true, force: true });
  }
});
