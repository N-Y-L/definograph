import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { access, copyFile, mkdir, readFile, readdir, realpath, rename, writeFile } from 'node:fs/promises';
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
  // Preserve the vendored originals. Only these checksummed, bounded compatibility edits
  // are applied to copies in this repository's isolated build directory.
  const readableVendor = path.join(root, 'vendor', 'LeanTeX');
  const readableManifest = JSON.parse(await readFile(path.join(readableVendor, 'UPSTREAM.json'), 'utf8'));
  if (readableManifest.revision !== 'd66db4582b6cb4d9fa0b6309168103a248a5fd46') throw new Error('Unexpected LeanTeX source revision.');
  const readableRoot = path.join(local, 'leantex');
  const readableSource = path.join(readableRoot, 'src');
  const readableLibrary = path.join(readableRoot, 'lib', 'lean');
  const readableC = path.join(readableRoot, 'c');
  for (const directory of [readableRoot, readableSource, readableLibrary, readableC, path.join(readableSource, 'LeanTeX'), path.join(readableLibrary, 'LeanTeX'), path.join(readableLibrary, 'StatementLens')]) {
    await mkdir(directory, { recursive: true });
    if (await realpath(directory) !== directory) throw new Error('The isolated LeanTeX build directories must not be symlinks.');
  }
  const replacements = {
    RuleSyntax: [['                aux_def', '                public aux_def', 3]],
    Builtins: [[`match (s.split ('_' == ·)).map (fun part => part.foldl (λ s' t => s' ++ t.toLatex) "") with`, `match ((s.split ('_' == ·)).map (fun part => part.foldl (λ s' t => s' ++ t.toLatex) "")).toList with`, 1]],
  };
  const readableModules = ['Defs', 'LatexChar', 'MkAppN', 'Basic', 'RuleSyntax', 'Builtins'];
  for (const module of readableModules) {
    const relative = `LeanTeX/${module}.lean`;
    let source = await readFile(path.join(readableVendor, 'upstream', relative), 'utf8');
    const digest = createHash('sha256').update(source).digest('hex');
    if (digest !== readableManifest.files[relative]) throw new Error(`Vendored LeanTeX source checksum mismatch: ${relative}`);
    for (const [before, after, count] of replacements[module] ?? []) {
      if (source.split(before).length - 1 !== count) throw new Error(`LeanTeX compatibility patch no longer matches: ${relative}`);
      source = source.replaceAll(before, after);
    }
    await writeFile(path.join(readableSource, relative), source);
    run(leanExecutable, ['-o', path.join(readableLibrary, 'LeanTeX', `${module}.olean`), relative], {
      cwd: readableSource, env: { ...process.env, LEAN_PATH: readableLibrary },
    });
  }
  run(leanExecutable, ['-o', path.join(readableLibrary, 'StatementLens', 'ReadableMath.olean'), 'StatementLens/ReadableMath.lean'], {
    cwd: path.join(root, 'lean'), env: { ...process.env, LEAN_PATH: readableLibrary },
  });
  const responseC = path.join(readableC, 'Response.c');
  run(leanExecutable, ['-o', path.join(readableLibrary, 'StatementLens', 'Response.olean'), '-c', responseC, 'StatementLens/Response.lean'], {
    cwd: path.join(root, 'lean'), env: { ...process.env, LEAN_PATH: readableLibrary },
  });
  leanPath = [readableLibrary, ...leanPath.filter(candidate => candidate !== readableLibrary)];
  const workerExecutable = path.join(local, process.platform === 'win32' ? 'statementlens-worker.exe' : 'statementlens-worker');
  const cFile = path.join(local, 'worker.c');
  run(leanExecutable, ['-c', cFile, path.join(root, 'lean', 'StatementLens', 'Worker.lean')], { env: { ...process.env, LEAN_PATH: readableLibrary } });
  const leanc = path.join(leanSysroot, 'bin', process.platform === 'win32' ? 'leanc.exe' : 'leanc');
  if (process.platform === 'win32') throw new Error('Native Windows linking is not yet supported. Use WSL with Lean 4.28.0.');
  // Do not overwrite the inode mapped by a running persistent worker. A completed
  // same-directory rename lets existing requests finish and new sessions use this build.
  const nextWorkerExecutable = `${workerExecutable}.next`;
  run(leanc, ['-rdynamic', '-o', nextWorkerExecutable, cFile, responseC]);
  await rename(nextWorkerExecutable, workerExecutable);
  await writeFile(path.join(local, 'config.json'), JSON.stringify({ leanExecutable, workerExecutable, leanPath, leanSysroot }, null, 2) + '\n');
  console.log(`Built ${workerExecutable}\nLean 4.28.0; mathlib ${pin}; LeanTeX ${readableManifest.revision}. ${values.download ? "Dependencies were prepared only in the isolated repository cache." : "Existing project caches were only read."}`);
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
