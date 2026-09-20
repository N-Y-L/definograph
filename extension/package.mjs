import { spawnSync } from 'node:child_process';
import { mkdir, readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const root = path.dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(await readFile(path.join(root, 'package.json'), 'utf8'));
await mkdir(path.join(root, '../.local'), { recursive: true });
const output = path.resolve(root, `../.local/statement-lens-editor-${manifest.version}.vsix`);
for (const [command, args] of [[process.execPath, ['build.mjs']], [process.execPath, ['node_modules/@vscode/vsce/vsce', 'package', '--no-dependencies', '--allow-missing-repository', '--out', output]]]) {
  const result = spawnSync(command, args, { cwd: root, stdio: 'inherit', shell: false });
  if (result.error) throw result.error;
  if (result.status !== 0) process.exit(result.status ?? 1);
}
console.log(`Local extension package: ${output}`);
