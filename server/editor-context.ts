import { spawn } from 'node:child_process';
import { constants } from 'node:fs';
import { access, mkdtemp, readFile, realpath, rm, stat } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { WorkerError, type WorkerResult } from './protocol.js';

export interface EditorPosition { line: number; character: number }
export interface EditorRange { start: EditorPosition; end: EditorPosition }
export interface EditorContextRequest {
  engineDirectory: string;
  fileName: string;
  source: string;
  selection: EditorRange;
  workspaceTrusted: boolean;
  /** Extra built library roots, in Lean's lookup order, for nonstandard Lake layouts. */
  libraryPaths?: string[];
  signal?: AbortSignal;
  timeoutMs?: number;
  expansion?: { constants: string[]; maxDepth: number };
}
export interface ProjectContext { root: string; libraries: string[]; toolchain: string }
const MAX_SOURCE_BYTES = 512 * 1024;
const MAX_RESULT_BYTES = 2 * 1024 * 1024;
const PIN = 'leanprover/lean4:v4.28.0';

async function boundedText(file: string, limit: number): Promise<string> {
  const info = await stat(file);
  if (!info.isFile() || info.size > limit) throw new WorkerError('EDITOR_CONFIG', `File is too large or unavailable: ${file}`);
  const content = await readFile(file, 'utf8');
  if (Buffer.byteLength(content) > limit) throw new WorkerError('EDITOR_CONFIG', `File exceeds the size limit: ${file}`);
  return content;
}
async function exists(file: string): Promise<boolean> {
  try { await access(file, constants.R_OK); return true; } catch { return false; }
}
function inside(root: string, file: string): boolean {
  const relative = path.relative(root, file);
  return relative !== '..' && !relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative);
}

/** No Lake config is evaluated, no package is fetched, and no build is invoked here. */
export async function resolveEditorProject(fileName: string, extraLibraries: string[] = []): Promise<ProjectContext> {
  if (!path.isAbsolute(fileName) || fileName.includes('\0')) throw new WorkerError('EDITOR_FILE', 'Open a saved Lean file in a project with lean-toolchain.');
  let root = path.dirname(fileName);
  while (!await exists(path.join(root, 'lean-toolchain'))) {
    const parent = path.dirname(root);
    if (parent === root) throw new WorkerError('EDITOR_PROJECT', 'No lean-toolchain was found above this file.');
    root = parent;
  }
  root = await realpath(root);
  const toolchain = (await boundedText(path.join(root, 'lean-toolchain'), 1024)).trim();
  if (toolchain !== PIN && toolchain !== 'v4.28.0') throw new WorkerError('EDITOR_VERSION', `This context adapter requires ${PIN}; the project uses ${toolchain || 'an empty toolchain file'}. Its toolchain has not been changed.`);
  if (extraLibraries.length > 32 || extraLibraries.some(value => typeof value !== 'string' || value.includes('\0'))) throw new WorkerError('EDITOR_CONFIG', 'At most 32 extra Lean library paths are supported.');
  const libraries: string[] = [];
  const add = async (directory: string, required = false) => {
    try {
      const resolved = await realpath(directory);
      if (!(await stat(resolved)).isDirectory()) throw new Error('not a directory');
      if (!libraries.includes(resolved)) libraries.push(resolved);
    } catch { if (required) throw new WorkerError('EDITOR_CONFIG', `Built Lean library directory is unavailable: ${directory}`); }
  };
  for (const directory of extraLibraries) await add(path.resolve(root, directory), true);
  await add(path.join(root, '.lake/build/lib/lean'));
  const manifestFile = path.join(root, 'lake-manifest.json');
  if (await exists(manifestFile)) {
    const manifest = JSON.parse(await boundedText(manifestFile, 512 * 1024)) as Record<string, unknown>;
    if (!Array.isArray(manifest.packages) || manifest.packages.length > 256) throw new WorkerError('EDITOR_CONFIG', 'The project package manifest is unsupported.');
    const packagesDirectory = typeof manifest.packagesDir === 'string' ? manifest.packagesDir : '.lake/packages';
    for (const value of manifest.packages) {
      if (!value || typeof value !== 'object') throw new WorkerError('EDITOR_CONFIG', 'Invalid package manifest entry.');
      const entry = value as Record<string, unknown>;
      let packageRoot: string;
      if (entry.type === 'path' && typeof entry.dir === 'string') packageRoot = path.resolve(root, entry.dir);
      else if (entry.type === 'git' && typeof entry.name === 'string' && !entry.name.includes('/') && !entry.name.includes('\\') && entry.name !== '..') {
        packageRoot = path.resolve(root, packagesDirectory, entry.name);
        if (typeof entry.subDir === 'string') packageRoot = path.resolve(packageRoot, entry.subDir);
      } else throw new WorkerError('EDITOR_CONFIG', 'Unsupported package manifest entry; configure statementLens.libraryPaths for the built libraries.');
      await add(path.join(packageRoot, '.lake/build/lib/lean'));
    }
  }
  if (libraries.length > 64) throw new WorkerError('EDITOR_CONFIG', 'The project has more than 64 Lean library roots.');
  return { root, libraries, toolchain };
}

export function positionOffset(source: string, position: EditorPosition): number {
  if (!Number.isSafeInteger(position.line) || !Number.isSafeInteger(position.character) || position.line < 0 || position.character < 0) throw new WorkerError('EDITOR_SELECTION', 'Invalid editor selection.');
  let offset = 0;
  for (let line = 0; line < position.line; line++) {
    const next = source.indexOf('\n', offset);
    if (next < 0) throw new WorkerError('EDITOR_SELECTION', 'Selection is outside the source buffer.');
    offset = next + 1;
  }
  const end = source.indexOf('\n', offset);
  const lineEnd = end < 0 ? source.length : end;
  const textEnd = lineEnd > offset && source[lineEnd - 1] === '\r' ? lineEnd - 1 : lineEnd;
  const result = offset + position.character;
  if (result > textEnd || result > 0 && result < source.length && /[\uD800-\uDBFF]/.test(source[result - 1]!) && /[\uDC00-\uDFFF]/.test(source[result]!)) throw new WorkerError('EDITOR_SELECTION', 'Selection is outside the line or splits a Unicode character.');
  return result;
}

/** Runs trusted Lean source in a separate process, not a security sandbox. */
async function runContext(executable: string, input: string, cwd: string, env: NodeJS.ProcessEnv, signal?: AbortSignal, timeoutMs = 45_000): Promise<void> {
  if (signal?.aborted) throw new WorkerError('CANCELLED', 'Editor analysis was cancelled.');
  await new Promise<void>((resolve, reject) => {
    const child = spawn(executable, [], { cwd, env, stdio: ['pipe', 'pipe', 'pipe'], shell: false, detached: process.platform !== 'win32', windowsHide: true });
    let failure: Error | undefined;
    let bytes = 0;
    let done = false;
    const stop = (error: Error) => {
      if (done || failure) return;
      failure = error;
      // Trusted elaborators may spawn subprocesses. Cancel the process group on POSIX.
      try { if (process.platform !== 'win32' && child.pid) process.kill(-child.pid, 'SIGKILL'); else child.kill('SIGKILL'); } catch { child.kill('SIGKILL'); }
    };
    const abort = () => stop(new WorkerError('CANCELLED', 'Editor analysis was cancelled.'));
    signal?.addEventListener('abort', abort, { once: true });
    const timer = setTimeout(() => stop(new WorkerError('EDITOR_TIMEOUT', 'Project context elaboration exceeded 45 seconds. Try a smaller file.')), Math.min(45_000, Math.max(1, timeoutMs)));
    timer.unref();
    const finish = (error?: Error) => {
      if (done) return; done = true;
      clearTimeout(timer); signal?.removeEventListener('abort', abort);
      if (failure || error) reject(failure ?? error); else resolve();
    };
    const onData = (chunk: Buffer) => { bytes += chunk.length; if (bytes > 128 * 1024) stop(new WorkerError('EDITOR_OUTPUT_LIMIT', 'Project elaboration produced too much console output.')); };
    child.stdout.on('data', onData); child.stderr.on('data', onData);
    child.on('error', () => finish(new WorkerError('EDITOR_UNAVAILABLE', 'The context worker could not start. Run npm run setup:lean.')));
    child.on('close', code => finish(code === 0 ? undefined : new WorkerError('EDITOR_FAILED', 'The project context process stopped unexpectedly.')));
    child.stdin.on('error', () => undefined);
    child.stdin.end(input);
    if (signal?.aborted) abort();
  });
}

export async function analyzeEditorContext(request: EditorContextRequest): Promise<WorkerResult> {
  if (!request.workspaceTrusted) throw new WorkerError('EDITOR_TRUST', 'Workspace Trust is required: Lean project elaboration can run project code.');
  if (!request.source.trim() || Buffer.byteLength(request.source) > MAX_SOURCE_BYTES) throw new WorkerError('EDITOR_SOURCE_LIMIT', 'The editor buffer must contain at most 512 KiB.');
  let start = positionOffset(request.source, request.selection.start);
  let end = positionOffset(request.source, request.selection.end);
  if (end < start) throw new WorkerError('EDITOR_SELECTION', 'Selection ends before it starts.');
  if (start !== end) {
    const selected = request.source.slice(start, end);
    const leading = selected.length - selected.trimStart().length;
    const trailing = selected.length - selected.trimEnd().length;
    start += leading; end = Math.max(start, end - trailing);
  }
  const sourceFile = await realpath(request.fileName);
  const project = await resolveEditorProject(sourceFile, request.libraryPaths);
  const engine = await realpath(request.engineDirectory);
  const config = JSON.parse(await boundedText(path.join(engine, '.local/config.json'), 32_768)) as Record<string, unknown>;
  const executable = path.join(engine, '.local/statementlens-context');
  if (typeof config.leanSysroot !== 'string' || !path.isAbsolute(config.leanSysroot)) throw new WorkerError('EDITOR_CONFIG', 'The engine Lean installation is not configured.');
  await access(executable, constants.R_OK | constants.X_OK);
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-context-'));
  try {
    const resultFile = path.join(temporary, 'result.json');
    const relative = path.relative(project.root, sourceFile);
    if (!inside(project.root, sourceFile)) throw new WorkerError('EDITOR_FILE', 'The selected file is outside its resolved Lean project.');
    const mainModule = relative.replace(/\.lean$/, '').split(path.sep).join('.');
    await runContext(executable, JSON.stringify({ source: request.source, fileName: sourceFile, mainModule, expansion: request.expansion,
      startByte: Buffer.byteLength(request.source.slice(0, start)), endByte: Buffer.byteLength(request.source.slice(0, end)) }) + '\n', temporary, {
      ...process.env, LEAN_PATH: project.libraries.join(path.delimiter),
      STATEMENTLENS_LEAN_SYSROOT: config.leanSysroot, STATEMENTLENS_CONTEXT_RESULT: resultFile,
    }, request.signal, request.timeoutMs);
    if (request.signal?.aborted) throw new WorkerError('CANCELLED', 'Editor analysis was cancelled.');
    const result: unknown = JSON.parse(await boundedText(resultFile, MAX_RESULT_BYTES));
    if (!result || typeof result !== 'object' || typeof (result as WorkerResult).ok !== 'boolean' || !Array.isArray((result as WorkerResult).diagnostics)) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned an invalid response.');
    return result as WorkerResult;
  } finally { await rm(temporary, { recursive: true, force: true }); }
}
