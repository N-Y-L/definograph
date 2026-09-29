/** Verified build input for the separately maintained source-capture library. */
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, readFile, realpath, readdir, writeFile } from 'node:fs/promises';
import path from 'node:path';

export const SOURCE_CAPTURE_COMMIT = '747631072c57c118a409d4e16280d29a33e05a20';
const HASH = /^[0-9a-f]{64}$/;
const MODULE = /^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$/;
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const requireThat = (condition, message) => { if (!condition) throw new Error(`Source capture dependency: ${message}`); };

/** Read import headers without interpreting examples or comments as dependencies. */
export function sourceImports(bytes) {
  const source = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  let clean = '', depth = 0, quoted = false;
  for (let i = 0; i < source.length;) {
    const pair = source.slice(i, i + 2), char = source[i];
    if (depth) {
      if (pair === '/-') { depth++; i += 2; }
      else if (pair === '-/') { depth--; i += 2; }
      else { if (char === '\n') clean += char; i++; }
    } else if (quoted) {
      clean += char; i++;
      if (char === '\\' && i < source.length) clean += source[i++];
      else if (char === '"') quoted = false;
    } else if (pair === '/-') { clean += ' '; depth = 1; i += 2; }
    else if (pair === '--') { const end = source.indexOf('\n', i); i = end < 0 ? source.length : end; }
    else { clean += char; quoted = char === '"'; i++; }
  }
  requireThat(depth === 0, 'unterminated source comment');
  const imports = [];
  for (const raw of clean.split('\n')) {
    const line = raw.trim();
    if (!line || line === 'prelude') continue;
    const match = /^(?:public\s+)?import\s+(.+)$/.exec(line);
    if (!match) break;
    for (const name of match[1].split(/\s+/)) {
      requireThat(MODULE.test(name), 'unsupported import header'); imports.push(name);
    }
  }
  return imports;
}

function exactKeys(value, keys, label) {
  requireThat(value && typeof value === 'object' && !Array.isArray(value)
    && Object.keys(value).sort().join('\0') === [...keys].sort().join('\0'), `invalid ${label} fields`);
}

export async function loadSourceCaptureDependency(vendorDirectory) {
  const directory = await realpath(vendorDirectory);
  const manifestFile = path.join(directory, 'UPSTREAM.json');
  requireThat(await realpath(manifestFile) === manifestFile, 'manifest must not be a symlink');
  const bytes = await readFile(manifestFile);
  requireThat(bytes.length <= 1024 * 1024, 'manifest is too large');
  const manifest = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
  exactKeys(manifest, ['schema', 'sourceCommit', 'upstreamManifest', 'leanVersion', 'entryModule', 'modules'], 'manifest');
  requireThat(manifest.schema === 1 && manifest.sourceCommit === SOURCE_CAPTURE_COMMIT
    && manifest.leanVersion === '4.28.0' && manifest.entryModule === 'SourceCapture', 'unsupported snapshot identity');
  exactKeys(manifest.upstreamManifest, ['path', 'sha256'], 'upstream manifest');
  requireThat(manifest.upstreamManifest.path === 'deps.json' && HASH.test(manifest.upstreamManifest.sha256), 'invalid upstream manifest identity');
  requireThat(Array.isArray(manifest.modules) && manifest.modules.length === 26, 'expected the complete 26-module closure');
  const modules = new Map();
  for (const entry of manifest.modules) {
    exactKeys(entry, ['module', 'source', 'upstreamSource', 'sha256', 'imports'], 'module');
    requireThat(typeof entry.module === 'string' && MODULE.test(entry.module) && !modules.has(entry.module), 'unknown or duplicate module');
    requireThat(entry.source === `src/${entry.module.replaceAll('.', '/')}.lean`, 'source path must match its module');
    requireThat(typeof entry.upstreamSource === 'string' && /^lean\/(?:library\/|admission\/)?[A-Za-z_][A-Za-z_0-9]*\.lean$/.test(entry.upstreamSource), 'invalid upstream source path');
    requireThat(typeof entry.sha256 === 'string' && HASH.test(entry.sha256), 'invalid source hash');
    requireThat(Array.isArray(entry.imports) && entry.imports.every(name => typeof name === 'string' && MODULE.test(name)), 'invalid import list');
    modules.set(entry.module, entry);
  }
  const seen = new Set(), sources = [];
  for (const entry of manifest.modules) {
    const sourceFile = path.join(directory, entry.source);
    requireThat(await realpath(sourceFile) === sourceFile, `source path escapes its fixed location: ${entry.module}`);
    const sourceBytes = await readFile(sourceFile);
    requireThat(sha256(sourceBytes) === entry.sha256, `source checksum mismatch: ${entry.module}`);
    const imports = sourceImports(sourceBytes);
    requireThat(JSON.stringify(imports) === JSON.stringify(entry.imports), `import inventory differs: ${entry.module}`);
    for (const imported of imports) {
      if (modules.has(imported)) requireThat(seen.has(imported), `import order is invalid: ${entry.module} imports ${imported}`);
      else requireThat(['Lean', 'Init', 'Std'].includes(imported.split('.')[0]), `import is outside the closure: ${entry.module} imports ${imported}`);
    }
    seen.add(entry.module); sources.push({ ...entry, bytes: sourceBytes });
  }
  const reachable = new Set();
  const visit = name => {
    requireThat(modules.has(name), `missing entry module: ${name}`);
    if (reachable.has(name)) return;
    reachable.add(name);
    for (const dependency of modules.get(name).imports) if (modules.has(dependency)) visit(dependency);
  };
  visit(manifest.entryModule);
  requireThat(reachable.size === modules.size, 'snapshot contains modules outside the entry import closure');
  const actualFiles = [];
  async function inventory(directoryName, prefix = '') {
    for (const entry of await readdir(directoryName, { withFileTypes: true })) {
      const relative = prefix + entry.name;
      requireThat(!entry.isSymbolicLink(), `unexpected source symlink: ${relative}`);
      if (entry.isDirectory()) await inventory(path.join(directoryName, entry.name), relative + '/');
      else { requireThat(entry.isFile(), `unexpected source entry: ${relative}`); actualFiles.push('src/' + relative); }
    }
  }
  await inventory(path.join(directory, 'src'));
  requireThat(JSON.stringify(actualFiles.sort()) === JSON.stringify(sources.map(entry => entry.source).sort()), 'unlisted source files in snapshot');
  return { digest: sha256(bytes), manifest, sources };
}

/** Stage verified bytes before compiling; use only this fresh import directory.
 * run is the build script's bounded compiler runner, injectable for portable tests. */
export async function compileSourceCaptureDependency({ snapshot, buildDirectory, leanExecutable, run }) {
  await mkdir(buildDirectory, { recursive: true });
  const parent = path.resolve(buildDirectory);
  requireThat(await realpath(parent) === parent, 'build directory must not be a symlink');
  const directory = await mkdtemp(path.join(parent, 'source-capture-'));
  const sourceDirectory = path.join(directory, 'src');
  const libraryPath = path.join(directory, 'lib');
  const cDirectory = path.join(directory, 'c');
  for (const folder of [sourceDirectory, libraryPath, cDirectory]) await mkdir(folder);
  for (const source of snapshot.sources) {
    requireThat(sha256(source.bytes) === source.sha256, `source snapshot changed: ${source.module}`);
    const file = path.join(sourceDirectory, source.module.replaceAll('.', '/') + '.lean');
    await mkdir(path.dirname(file), { recursive: true }); await writeFile(file, source.bytes);
  }
  const cFiles = [], artifacts = [];
  for (const source of snapshot.sources) {
    const relative = source.module.replaceAll('.', '/');
    const olean = path.join(libraryPath, relative + '.olean'), c = path.join(cDirectory, relative + '.c');
    await mkdir(path.dirname(olean), { recursive: true }); await mkdir(path.dirname(c), { recursive: true });
    await run(leanExecutable, ['-o', olean, '-c', c, relative + '.lean'], {
      cwd: sourceDirectory, env: { ...process.env, LEAN_PATH: libraryPath },
    });
    artifacts.push({ module: source.module, sourceSha256: source.sha256,
      oleanSha256: sha256(await readFile(olean)), cSha256: sha256(await readFile(c)) });
    cFiles.push(c);
  }
  return { directory, sourceDirectory, libraryPath, cDirectory, cFiles, artifacts };
}

export async function fileSha256(file) { return sha256(await readFile(file)); }
/** SHA-256 of compact JSON with recursively sorted object keys; array order is
 * significant. The build identity contains only ordinary JSON scalar fields. */
export function buildFingerprint(identity) {
  const canonical = value => value === null || typeof value !== 'object' ? JSON.stringify(value)
    : Array.isArray(value) ? '[' + value.map(canonical).join(',') + ']'
    : '{' + Object.keys(value).sort().map(key => JSON.stringify(key) + ':' + canonical(value[key])).join(',') + '}';
  return sha256(canonical(identity));
}
