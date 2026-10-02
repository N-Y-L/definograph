import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { constants } from 'node:fs';
import { access, mkdtemp, readFile, realpath, rm, stat } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { WorkerError, type WorkerResult } from './protocol.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';
import { validateSourceSnapshot, sourceSnapshotValidation, type SourceSnapshot } from '../src/editor/source-snapshot.js';
import { isSourceSnapshotOrigin, type SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { isSourceOccurrencePath, validateSourceOccurrence, type SourceOccurrence, type SourceOccurrenceStep } from '../src/editor/source-occurrence.js';
import { hashContextExecutable, sourceCaptureEngine } from './source-capture-origin.js';
import { parseEditorResult } from './editor-result.js';
import { GUIDED_CONTEXT_CONTRACT, GUIDED_CONTEXT_MISMATCH } from '../src/editor/guided-context-contract.js';
import { validateSourceHeadExposure, type HeadExposureTarget, type SourceHeadExposure } from '../src/editor/source-head-exposure.js';
import { validateDecompositionHistory, decompositionPlan, validateSourceDecomposition,
  type DecompositionOperation, type SourceDecompositionBundle } from '../src/editor/source-decomposition.js';
import { sanitizeSourcePresentation } from '../src/editor/source-presentation.js';

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
  previewDefinitions?: boolean;
  document?: { uri: string; version: number };
  /** Supplied only from the host's retained, current source capture. */
  occurrence?: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; path: SourceOccurrenceStep[] };
  /** A separate operation on the host's retained original occurrence. */
  headExposure?: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence; target: HeadExposureTarget };
  /** Retained immutable attempts; the server resolves the selected prefix. */
  decomposition?: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence;
    seed: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; record: SourceHeadExposure } | null; version?: 1 | 2 | 3;
    attempts: SourceDecompositionBundle[]; previousCaptureId: string; parentStepIndex: number; operation: DecompositionOperation };
}
export interface ProjectContext { root: string; libraries: string[]; toolchain: string }
const MAX_SOURCE_BYTES = 512 * 1024;
// Legacy reading retains its 2 MiB allowance; the independently bounded source
// attachment must survive a reading failure or omission.
const MAX_RESULT_BYTES = 4 * 1024 * 1024;
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
  if (request.document && (typeof request.document.uri !== 'string' || !request.document.uri || !Number.isSafeInteger(request.document.version) || request.document.version < 0)) throw new WorkerError('EDITOR_SELECTION', 'Invalid editor document revision.');
  const { canonical, freeze } = createExactJsonTools();
  const same = (a: unknown, b: unknown) => canonical(a as JsonValue) === canonical(b as JsonValue);
  let parent: EditorContextRequest['occurrence'];
  let exposureParent: EditorContextRequest['headExposure'];
  let decompositionHistory: ReturnType<typeof validateDecompositionHistory> | undefined;
  let decomposition: Record<string, unknown> | undefined;
  if ([request.occurrence, request.headExposure, request.decomposition].filter(value => value !== undefined).length > 1) throw new WorkerError('EDITOR_HEAD_EXPOSURE', 'Occurrence, definition-head and decomposition requests are mutually exclusive.');
  if (request.occurrence !== undefined) {
    if (!request.occurrence || !isSourceSnapshotOrigin(request.occurrence.origin) || !isSourceOccurrencePath(request.occurrence.path)) throw new WorkerError('EDITOR_OCCURRENCE', 'Invalid source occurrence request.');
    parent = { snapshot: validateSourceSnapshot(request.occurrence.snapshot), origin: structuredClone(request.occurrence.origin), path: [...request.occurrence.path] };
    if (parent.snapshot.prepared.status !== 'available') throw new WorkerError('EDITOR_OCCURRENCE', 'The selected source capture has no prepared expression. Refresh the source first.');
  }
  if (request.headExposure !== undefined) {
    const requested = request.headExposure;
    if (!requested || !isSourceSnapshotOrigin(requested.origin) || !['term', 'type'].includes(requested.target)) throw new WorkerError('EDITOR_HEAD_EXPOSURE', 'Invalid definition-head request.');
    const snapshot = validateSourceSnapshot(requested.snapshot);
    const occurrence = validateSourceOccurrence(requested.occurrence, snapshot);
    if (snapshot.prepared.status !== 'available' || occurrence.captureId !== requested.origin.captureId
      || occurrence.checking.status !== 'captured' || occurrence.checking.action.status !== 'completed' || !occurrence.checking.selected) throw new WorkerError('EDITOR_HEAD_EXPOSURE', 'A definition-head request requires the retained current selected candidate.');
    exposureParent = { snapshot, origin: structuredClone(requested.origin), occurrence, target: requested.target };
    parent = { snapshot, origin: exposureParent.origin, path: [...occurrence.path] };
  }
  if (request.decomposition !== undefined) {
    const requested = request.decomposition;
    sourceSnapshotValidation.preflight(requested, 16 * 1024 * 1024, ['decomposition'], false, 128, 16 * 1024 * 1024);
    if (!requested || !isSourceSnapshotOrigin(requested.origin) || !Array.isArray(requested.attempts)
      || requested.attempts.length >= 8 || requested.version !== undefined && requested.version !== 1 && requested.version !== 2 && requested.version !== 3
      || (requested.version ?? 1) === 1 && !requested.seed) throw new WorkerError('EDITOR_DECOMPOSITION', 'Invalid or full retained decomposition history. Save and refresh to start another history.');
    const snapshot = validateSourceSnapshot(requested.snapshot);
    const occurrence = validateSourceOccurrence(requested.occurrence, snapshot);
    if (snapshot.prepared.status !== 'available' || occurrence.captureId !== requested.origin.captureId
      || occurrence.checking.status !== 'captured' || occurrence.checking.action.status !== 'completed' || !occurrence.checking.selected) throw new WorkerError('EDITOR_DECOMPOSITION', 'Decomposition requires the retained original selected candidate.');
    decompositionHistory = validateDecompositionHistory({ snapshot, occurrence,
      seed: requested.seed ? { snapshot: requested.seed.snapshot, record: requested.seed.record } : null,
      attempts: requested.attempts.map(bundle => ({ snapshot: bundle.snapshot, record: bundle.record })) });
    for (const bundle of [...(requested.seed ? [requested.seed] : []), ...requested.attempts]) {
      if (!isSourceSnapshotOrigin(bundle.origin) || bundle.origin.captureId !== bundle.record.captureId
        || !same(bundle.origin.sourceSha256, requested.origin.sourceSha256)
        || !same(bundle.origin.engine, requested.origin.engine) || !same(bundle.origin.project, requested.origin.project)
        || !same(bundle.origin.document, requested.origin.document) || !same(bundle.origin.selection, requested.origin.selection)) throw new WorkerError('EDITOR_STALE', 'A retained continuation belongs to another source, project, document or engine. Refresh before continuing.');
    }
    const version = requested.version ?? 1;
    const plan = decompositionPlan(decompositionHistory, requested.previousCaptureId, requested.parentStepIndex, requested.operation, version);
    decomposition = { schema: `definograph.source-decomposition-request.v${version}`, parentCaptureId: occurrence.captureId,
      previousCaptureId: requested.previousCaptureId, parentStepIndex: requested.parentStepIndex,
      selection: snapshot.selection, prepared: snapshot.prepared, path: occurrence.path,
      expectedSelected: occurrence.checking.selected, operations: plan.operations, expectedHistory: plan.expectedHistory };
    sourceSnapshotValidation.preflight(decomposition, 2 * 1024 * 1024, ['decompositionRequest'], false, 120);
    parent = { snapshot, origin: structuredClone(requested.origin), path: [...occurrence.path] };
  }
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
  const configPath = path.join(engine, '.local/config.json');
  const configText = await boundedText(configPath, 256 * 1024);
  const config = JSON.parse(configText) as Record<string, unknown>;
  const executable = path.join(engine, '.local/statementlens-context');
  if (typeof config.leanSysroot !== 'string' || !path.isAbsolute(config.leanSysroot)) throw new WorkerError('EDITOR_CONFIG', 'The engine Lean installation is not configured.');
  await access(executable, constants.R_OK | constants.X_OK);
  const contextSha256 = await hashContextExecutable(executable);
  const captureEngine = sourceCaptureEngine(config, contextSha256);
  const captureId = randomUUID();
  const startByte = Buffer.byteLength(request.source.slice(0, start));
  const endByte = Buffer.byteLength(request.source.slice(0, end));
  const sourceSha256 = createHash('sha256').update(request.source).digest('hex');
  const projectOrigin: SourceSnapshotOrigin['project'] = { root: project.root, toolchain: project.toolchain, libraryPaths: project.libraries, dependencyTracking: 'snapshot-paths-only' };
  if (parent && (!captureEngine || parent.origin.sourceSha256 !== sourceSha256
      || !same(parent.origin.engine, captureEngine) || !same(parent.origin.project, projectOrigin)
      || !same(parent.origin.document, request.document ?? null) || !same(parent.origin.selection, request.selection)
      || parent.snapshot.selection.requestedStartByte !== startByte || parent.snapshot.selection.requestedEndByte !== endByte
      || parent.snapshot.selection.startByte > startByte || parent.snapshot.selection.endByte < endByte
      || parent.snapshot.selection.endByte > Buffer.byteLength(request.source)
      || (startByte !== endByte && (parent.snapshot.selection.startByte !== startByte || parent.snapshot.selection.endByte !== endByte))
      || (parent.snapshot.checking.status === 'captured' && parent.snapshot.checking.binding.attempt !== parent.origin.captureId))) {
    throw new WorkerError('EDITOR_STALE', 'The source capture no longer matches this buffer, selection, project or engine. Refresh before checking an occurrence or exposing a definition.');
  }
  const occurrence = parent && !exposureParent && !decomposition ? { schema: 'definograph.source-occurrence-request.v1', parentCaptureId: parent.origin.captureId,
    selection: parent.snapshot.selection, prepared: parent.snapshot.prepared, path: parent.path } : undefined;
  const headExposure = exposureParent && exposureParent.occurrence.checking.status === 'captured' ? {
    schema: 'definograph.source-head-exposure-request.v1', parentCaptureId: exposureParent.origin.captureId,
    selection: exposureParent.snapshot.selection, prepared: exposureParent.snapshot.prepared,
    path: exposureParent.occurrence.path, target: exposureParent.target, expectedSelected: exposureParent.occurrence.checking.selected,
  } : undefined;
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-context-'));
  try {
    const resultFile = path.join(temporary, 'result.json');
    const relative = path.relative(project.root, sourceFile);
    if (!inside(project.root, sourceFile)) throw new WorkerError('EDITOR_FILE', 'The selected file is outside its resolved Lean project.');
    const mainModule = relative.replace(/\.lean$/, '').split(path.sep).join('.');
    await runContext(executable, JSON.stringify({ guidedContextContract: GUIDED_CONTEXT_CONTRACT, source: request.source, fileName: sourceFile, mainModule, captureId, expansion: request.expansion, previewDefinitions: request.previewDefinitions,
      startByte, endByte, occurrence, headExposure, decomposition }) + '\n', temporary, {
      ...process.env, LEAN_PATH: project.libraries.join(path.delimiter),
      STATEMENTLENS_LEAN_SYSROOT: config.leanSysroot, STATEMENTLENS_CONTEXT_RESULT: resultFile,
    }, request.signal, request.timeoutMs);
    if (request.signal?.aborted) throw new WorkerError('CANCELLED', 'Editor analysis was cancelled.');
    if (contextSha256 !== await hashContextExecutable(executable) || configText !== await boundedText(configPath, 256 * 1024)) throw new WorkerError('EDITOR_STALE', 'The Lean engine changed during analysis. Refresh after the build completes.');
    const response = parseEditorResult(await boundedText(resultFile, MAX_RESULT_BYTES));
    if (response.ok && response.guidedContextContract !== GUIDED_CONTEXT_CONTRACT) {
      // Refuse the incompatible guided reading; validate raw attachments below as usual.
      response.ok = false; response.error = GUIDED_CONTEXT_MISMATCH;
      response.code = 'EDITOR_COMPATIBILITY';
      delete response.tree; delete response.expression;
    }
    if (response.sourceSnapshotUnavailable !== undefined && (typeof response.sourceSnapshotUnavailable !== 'string' || [...response.sourceSnapshotUnavailable].length > 4096 || Object.hasOwn(response, 'sourceSnapshot'))) throw new WorkerError('EDITOR_PROTOCOL', 'Invalid source capture omission record.');
    if (response.sourceOccurrenceUnavailable !== undefined && (typeof response.sourceOccurrenceUnavailable !== 'string' || [...response.sourceOccurrenceUnavailable].length > 4096 || Object.hasOwn(response, 'sourceOccurrence'))) throw new WorkerError('EDITOR_PROTOCOL', 'Invalid source occurrence omission record.');
    if (!occurrence && (Object.hasOwn(response, 'sourceOccurrence') || Object.hasOwn(response, 'sourceOccurrenceUnavailable'))) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned an unrequested source occurrence.');
    if (occurrence && !Object.hasOwn(response, 'sourceOccurrence') && !Object.hasOwn(response, 'sourceOccurrenceUnavailable')) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker omitted the requested occurrence result.');
    if (response.sourceHeadExposureUnavailable !== undefined && (typeof response.sourceHeadExposureUnavailable !== 'string' || [...response.sourceHeadExposureUnavailable].length > 4096 || Object.hasOwn(response, 'sourceHeadExposure'))) throw new WorkerError('EDITOR_PROTOCOL', 'Invalid definition-head omission record.');
    if (!headExposure && (Object.hasOwn(response, 'sourceHeadExposure') || Object.hasOwn(response, 'sourceHeadExposureUnavailable'))) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned an unrequested definition-head result.');
    if (headExposure && !Object.hasOwn(response, 'sourceHeadExposure') && !Object.hasOwn(response, 'sourceHeadExposureUnavailable')) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker omitted the requested definition-head result.');
    if (response.sourceDecompositionUnavailable !== undefined && (typeof response.sourceDecompositionUnavailable !== 'string' || [...response.sourceDecompositionUnavailable].length > 4096 || Object.hasOwn(response, 'sourceDecomposition'))) throw new WorkerError('EDITOR_PROTOCOL', 'Invalid decomposition omission record.');
    if (!decomposition && (Object.hasOwn(response, 'sourceDecomposition') || Object.hasOwn(response, 'sourceDecompositionUnavailable'))) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned an unrequested decomposition result.');
    if (decomposition && !Object.hasOwn(response, 'sourceDecomposition') && !Object.hasOwn(response, 'sourceDecompositionUnavailable')) throw new WorkerError('EDITOR_PROTOCOL', 'The context worker omitted the requested decomposition result.');
    // Display-only data is meaningful only beside a requested exact record.
    if (!decomposition || !Object.hasOwn(response, 'sourceDecomposition')) delete response.sourceDecompositionPresentation;
    // The process cannot supply host provenance. Associate only the native
    // attachment we received during this request with the actual input/build.
    delete response.sourceSnapshotOrigin;
    if (Object.hasOwn(response, 'sourceSnapshot')) {
      if (!captureEngine) throw new WorkerError('EDITOR_PROTOCOL', 'Source capture requires a matching native build record. Rebuild the Lean engine.');
      const snapshot = validateSourceSnapshot(response.sourceSnapshot);
      if (snapshot.selection.requestedStartByte !== startByte || snapshot.selection.requestedEndByte !== endByte
        || snapshot.selection.startByte > startByte || snapshot.selection.endByte < endByte || snapshot.selection.endByte > Buffer.byteLength(request.source)
        || (startByte !== endByte && (snapshot.selection.startByte !== startByte || snapshot.selection.endByte !== endByte))
        || (snapshot.checking.status === 'captured' && snapshot.checking.binding.attempt !== captureId)) {
        throw new WorkerError('EDITOR_PROTOCOL', 'Source capture does not match this request and selection.');
      }
      const origin: SourceSnapshotOrigin = {
        kind: 'local-editor-process-snapshot', captureId,
        sourceSha256, engine: captureEngine, project: projectOrigin,
        document: structuredClone(request.document ?? null), selection: structuredClone(request.selection), policyId: 'named-source-v1',
      };
      response.sourceSnapshot = snapshot; response.sourceSnapshotOrigin = origin;
      if (Object.hasOwn(response, 'sourceOccurrence')) {
        const checked = validateSourceOccurrence(response.sourceOccurrence, snapshot);
        if (!parent || checked.captureId !== captureId || checked.parentCaptureId !== parent.origin.captureId || !same(checked.path, parent.path)) throw new WorkerError('EDITOR_PROTOCOL', 'Source occurrence does not match this request and parent capture.');
        const matchesParent = same(snapshot.selection, parent.snapshot.selection) && same(snapshot.prepared, parent.snapshot.prepared) && same(snapshot.policy, parent.snapshot.policy);
        if (!matchesParent && (checked.checking.status === 'captured' || checked.checking.attempted)) throw new WorkerError('EDITOR_PROTOCOL', 'Source occurrence checking ran against a changed prepared parent.');
        response.sourceOccurrence = checked;
      }
      if (Object.hasOwn(response, 'sourceHeadExposure')) {
        if (!exposureParent) throw new WorkerError('EDITOR_PROTOCOL', 'No retained parent for definition-head result.');
        const checked = validateSourceHeadExposure(response.sourceHeadExposure, snapshot, { snapshot: exposureParent.snapshot, occurrence: exposureParent.occurrence });
        if (checked.captureId !== captureId || checked.parentCaptureId !== exposureParent.origin.captureId
          || checked.target !== exposureParent.target || !same(checked.path, exposureParent.occurrence.path)) throw new WorkerError('EDITOR_PROTOCOL', 'Definition-head result does not match this request and retained occurrence.');
        const matchesParent = same(snapshot.selection, exposureParent.snapshot.selection) && same(snapshot.prepared, exposureParent.snapshot.prepared) && same(snapshot.policy, exposureParent.snapshot.policy);
        if (!matchesParent && (checked.checking.status === 'captured' || checked.checking.attempted)) throw new WorkerError('EDITOR_PROTOCOL', 'Definition-head checking ran against a changed prepared parent.');
        response.sourceHeadExposure = checked;
      }
      if (Object.hasOwn(response, 'sourceDecomposition')) {
        if (!decomposition || !decompositionHistory || !parent) throw new WorkerError('EDITOR_PROTOCOL', 'No retained history for decomposition result.');
        const checked = validateSourceDecomposition(response.sourceDecomposition, snapshot, decompositionHistory);
        if (checked.schema !== (decomposition.schema === 'definograph.source-decomposition-request.v3' ? 'definograph.source-decomposition.v3' : decomposition.schema === 'definograph.source-decomposition-request.v2' ? 'definograph.source-decomposition.v2' : 'definograph.source-decomposition.v1')
          || checked.captureId !== captureId || checked.parentCaptureId !== parent.origin.captureId
          || checked.previousCaptureId !== decomposition.previousCaptureId || checked.parentStepIndex !== decomposition.parentStepIndex
          || !same(checked.operations, decomposition.operations) || !same(checked.path, parent.path)) throw new WorkerError('EDITOR_PROTOCOL', 'Decomposition does not match this request and retained prefix.');
        const matchesParent = same(snapshot.selection, parent.snapshot.selection) && same(snapshot.prepared, parent.snapshot.prepared) && same(snapshot.policy, parent.snapshot.policy);
        if (!matchesParent && (checked.checking.status === 'captured' || checked.checking.attempted)) throw new WorkerError('EDITOR_PROTOCOL', 'Decomposition ran against a changed prepared parent.');
        response.sourceDecomposition = checked;
        if (Object.hasOwn(response, 'sourceDecompositionPresentation'))
          response.sourceDecompositionPresentation = sanitizeSourcePresentation(response.sourceDecompositionPresentation, checked);
      }
    }
    if (Object.hasOwn(response, 'sourceOccurrence') && !Object.hasOwn(response, 'sourceSnapshot')) throw new WorkerError('EDITOR_PROTOCOL', 'A source occurrence requires its fresh source snapshot.');
    if (Object.hasOwn(response, 'sourceHeadExposure') && !Object.hasOwn(response, 'sourceSnapshot')) throw new WorkerError('EDITOR_PROTOCOL', 'A definition-head result requires its fresh source snapshot.');
    if (Object.hasOwn(response, 'sourceDecomposition') && !Object.hasOwn(response, 'sourceSnapshot')) throw new WorkerError('EDITOR_PROTOCOL', 'Decomposition requires its fresh source snapshot.');
    if (request.signal?.aborted) throw new WorkerError('CANCELLED', 'Editor analysis was cancelled.');
    freeze(response);
    return response;
  } finally { await rm(temporary, { recursive: true, force: true }); }
}
