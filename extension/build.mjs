import { build } from 'esbuild';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
const root = path.dirname(fileURLToPath(import.meta.url));
await build({ entryPoints: [path.join(root, 'src/extension.ts')], bundle: true, outfile: path.join(root, 'dist/extension.cjs'), platform: 'node', format: 'cjs', target: 'node20', external: ['vscode'], sourcemap: false });
