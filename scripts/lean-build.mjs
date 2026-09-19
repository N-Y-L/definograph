import { spawnSync } from 'node:child_process';
import { access, copyFile, mkdir, readFile, readdir, realpath, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const local = path.join(root, '.local');
const pin = '8f9d9cff6bd728b17a24e163c9402775d9e6a365';
const { values } = parseArgs({ options: { lean: { type: 'string' }, packages: { type: 'string' }, download: { type: 'boolean' }, help: { type: 'boolean' } } });
if (values.help) {
  console.log('node scripts/lean-build.mjs --lean /absolute/path/to/lean --packages /absolute/path/to/.lake/packages\nUses Lean 4.28.0 and the pinned mathlib cache read-only. Alternatively use --download to fetch a separate pinned cache into .local/mathlib-lean. Rebuild without arguments after initial configuration.');
  process.exit(0);
}
const run = (command, args, options = {}) => {
  const result = spawnSync(command, args, { cwd: root, encoding: 'utf8', timeout: 120_000, maxBuffer: 8 * 1024 * 1024, ...options });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`${path.basename(command)} failed:\n${result.stderr || result.stdout || `exit status ${result.status}; see the command output above.`}`);
  return (result.stdout || '').trim();
};
try {
  let previous = {};
  try { previous = JSON.parse(await readFile(path.join(local, 'config.json'), 'utf8')); } catch { /* first setup */ }
  const leanExecutable = values.lean ? path.resolve(values.lean) : previous.leanExecutable;
  if (!leanExecutable) throw new Error('Supply --lean and --packages on the first run. No existing Lean environment will be changed.');
  const version = run(leanExecutable, ['--version']);
  if (!/^Lean \(version 4\.28\.0(?:[, )])/.test(version)) throw new Error(`Expected Lean 4.28.0; received ${version}`);
  const leanSysroot = run(leanExecutable, ['--print-prefix']);
  let leanPath = previous.leanPath;
  let packagesPath = values.packages;
  if (values.download) {
    if (packagesPath) throw new Error('Choose --download or --packages, not both.');
    const isolated = path.join(local, 'mathlib-lean');
    await mkdir(isolated, { recursive: true });
    if (await realpath(isolated) !== isolated) throw new Error('The isolated dependency directory must not be a symlink.');
    packagesPath = path.join(isolated, '.lake', 'packages');
    try {
      if (!(await realpath(packagesPath)).startsWith(isolated + path.sep)) throw new Error('The isolated package directory must stay inside .local/mathlib-lean.');
    } catch (error) { if (error.code !== 'ENOENT') throw error; }
    for (const file of ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']) {
      await copyFile(path.join(root, 'lean', file), path.join(isolated, file));
    }
    const lake = path.join(leanSysroot, 'bin', process.platform === 'win32' ? 'lake.exe' : 'lake');
    console.log('Fetching pinned mathlib dependencies and the two required module caches into .local/mathlib-lean. This may take several minutes.');
    run(lake, ['exe', 'cache', 'get', 'Mathlib.Topology.MetricSpace.Basic', 'Mathlib.Analysis.InnerProductSpace.PiL2'], {
      cwd: isolated, timeout: 30 * 60_000, stdio: 'inherit',
      env: { ...process.env, LEAN_PATH: '', PATH: path.join(leanSysroot, 'bin') + path.delimiter + (process.env.PATH || ''), MATHLIB_CACHE_DIR: path.join(local, 'mathlib-download-cache'), MATHLIB_NO_CACHE_ON_UPDATE: '1' },
    });
  }
  if (packagesPath) {
    const packages = path.resolve(packagesPath);
    leanPath = [];
    for (const entry of await readdir(packages, { withFileTypes: true })) {
      const candidate = path.join(packages, entry.name, '.lake', 'build', 'lib', 'lean');
      try { await access(candidate); leanPath.push(candidate); } catch { /* packages without Lean libraries */ }
    }
    leanPath.sort();
  }
  if (!Array.isArray(leanPath) || !leanPath.length) throw new Error('Supply --packages pointing to a built mathlib .lake/packages directory.');
  const mathlibLibrary = leanPath.find(p => path.basename(path.resolve(p, '../../../..')) === 'mathlib');
  if (!mathlibLibrary) throw new Error('No built mathlib library was found in the package paths.');
  const mathlibRoot = path.resolve(mathlibLibrary, '../../../..');
  const revision = run('git', ['-C', mathlibRoot, 'rev-parse', 'HEAD']);
  if (revision !== pin) throw new Error(`Expected mathlib ${pin}; found ${revision}. Use a separate pinned cache, without updating your formal project.`);
  const manifest = JSON.parse(await readFile(path.join(root, 'lean', 'lake-manifest.json'), 'utf8'));
  const packageRoot = path.dirname(mathlibRoot);
  for (const dependency of manifest.packages) {
    const actual = run('git', ['-C', path.join(packageRoot, dependency.name), 'rev-parse', 'HEAD']);
    if (actual !== dependency.rev) throw new Error(`Dependency ${dependency.name} does not match the pinned manifest: expected ${dependency.rev}; found ${actual}.`);
  }
  await access(path.join(mathlibLibrary, 'Mathlib', 'Analysis', 'InnerProductSpace', 'PiL2.olean'));
  await mkdir(local, { recursive: true });
  const workerExecutable = path.join(local, process.platform === 'win32' ? 'statementlens-worker.exe' : 'statementlens-worker');
  const cFile = path.join(local, 'worker.c');
  run(leanExecutable, ['-c', cFile, path.join(root, 'lean', 'StatementLens', 'Worker.lean')], { env: { ...process.env, LEAN_PATH: '' } });
  const leanc = path.join(leanSysroot, 'bin', process.platform === 'win32' ? 'leanc.exe' : 'leanc');
  if (process.platform === 'win32') throw new Error('Native Windows linking is not yet supported. Use WSL with Lean 4.28.0.');
  run(leanc, ['-rdynamic', '-o', workerExecutable, cFile]);
  await writeFile(path.join(local, 'config.json'), JSON.stringify({ leanExecutable, workerExecutable, leanPath, leanSysroot }, null, 2) + '\n');
  console.log(`Built ${workerExecutable}\nLean 4.28.0; mathlib ${pin}. ${values.download ? "Dependencies were prepared only in the isolated repository cache." : "Existing project caches were only read."}`);
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
