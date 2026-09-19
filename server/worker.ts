import { spawn } from 'node:child_process';
import { stat } from 'node:fs/promises';
import path from 'node:path';
import { ConfigError, loadWorkerConfig, type WorkerConfig } from './config.js';
import { LeanSession } from './session.js';
import { WorkerError, type WorkerResult } from './protocol.js';
export { WorkerError, type WorkerResult } from './protocol.js';

export const MAX_SOURCE_CHARACTERS = 32_768;
export const MAX_SOURCE_BYTES = 65_536;

export interface Health {
  ok: true;
  ready: boolean;
  leanVersion: string | null;
  issue: string | null;
}

export interface WorkerBackend {
  health(): Promise<Health>;
  analyze(source: string, signal?: AbortSignal): Promise<WorkerResult>;
  close?(): void;
}

interface ProcessOptions {
  args?: string[];
  input?: string;
  cwd: string;
  env?: NodeJS.ProcessEnv;
  timeoutMs?: number;
  maxOutputBytes?: number;
  maxErrorBytes?: number;
  signal?: AbortSignal;
}

/** Executes a fixed local program, never a shell, and never turns user text into arguments. */
export async function runBoundedProcess(executable: string, options: ProcessOptions): Promise<string> {
  if (options.signal?.aborted) throw new WorkerError('CANCELLED', 'Analysis was cancelled.', 499);
  return new Promise((resolve, reject) => {
    const child = spawn(executable, options.args ?? [], {
      cwd: options.cwd,
      env: options.env,
      stdio: ['pipe', 'pipe', 'pipe'],
      windowsHide: true,
      shell: false,
    });
    let outputBytes = 0;
    let errorBytes = 0;
    const output: Buffer[] = [];
    let failure: WorkerError | undefined;
    let settled = false;
    const stop = (error: WorkerError) => {
      if (failure || settled) return;
      failure = error;
      // A worker is one process, with no shell or child-command execution path.
      child.kill('SIGKILL');
    };
    const abort = () => stop(new WorkerError('CANCELLED', 'Analysis was cancelled.', 499));
    options.signal?.addEventListener('abort', abort, { once: true });
    const timer = setTimeout(() => {
      stop(new WorkerError('WORKER_TIMEOUT', 'Lean analysis exceeded the time limit. Try a smaller statement.', 504));
    }, options.timeoutMs ?? 30_000);
    timer.unref();
    const finish = (error?: WorkerError) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      options.signal?.removeEventListener('abort', abort);
      if (error) reject(error);
      else resolve(Buffer.concat(output).toString('utf8'));
    };
    child.stdout.on('data', (chunk: Buffer) => {
      outputBytes += chunk.length;
      if (outputBytes > (options.maxOutputBytes ?? 2 * 1024 * 1024)) {
        stop(new WorkerError('WORKER_OUTPUT_LIMIT', 'Lean analysis produced too much output. Try a smaller statement.'));
      } else {
        output.push(chunk);
      }
    });
    child.stderr.on('data', (chunk: Buffer) => {
      errorBytes += chunk.length;
      // Diagnostics belong in structured stdout. Do not return raw process stderr to the browser.
      if (errorBytes > (options.maxErrorBytes ?? 128 * 1024)) {
        stop(new WorkerError('WORKER_OUTPUT_LIMIT', 'Lean analysis produced too much diagnostic output.'));
      }
    });
    child.on('error', () => finish(new WorkerError('WORKER_UNAVAILABLE', 'The local Lean worker could not start. Run npm run setup:lean.', 503)));
    child.on('close', (code) => {
      if (failure) finish(failure);
      else if (code !== 0) finish(new WorkerError('WORKER_FAILED', 'The local Lean worker stopped unexpectedly.'));
      else finish();
    });
    // An early parser exit can close stdin before Node finishes writing; close/error decides the result.
    child.stdin.on('error', () => undefined);
    child.stdin.end(options.input ?? '');
    // The signal could have changed while spawn and listeners were installed.
    if (options.signal?.aborted) abort();
  });
}

function workerEnvironment(config: WorkerConfig): NodeJS.ProcessEnv {
  return {
    ...process.env,
    LEAN_PATH: config.leanPath.join(path.delimiter),
    STATEMENTLENS_LEAN_SYSROOT: config.leanSysroot,
  };
}

export function createWorkerBackend(options: {
  rootDir: string;
  configPath?: string;
  timeoutMs?: number;
}): WorkerBackend {
  const configPath = options.configPath ?? path.join(options.rootDir, '.local/config.json');
  let pendingHealth: Promise<Health> | undefined;
  let session: LeanSession | undefined;
  let sessionFingerprint: string | undefined;
  let analyzing = false;
  let closed = false;
  const readHealth = async (): Promise<Health> => {
    try {
      const config = await loadWorkerConfig(configPath);
      const version = (await runBoundedProcess(config.leanExecutable, {
        args: ['--version'], cwd: options.rootDir, env: workerEnvironment(config),
        timeoutMs: 5_000, maxOutputBytes: 8_192,
      })).trim();
      if (!/^Lean \(version [^\n]+\)/.test(version)) {
        return { ok: true, ready: false, leanVersion: null, issue: 'The configured executable did not report a Lean version.' };
      }
      return { ok: true, ready: true, leanVersion: version, issue: null };
    } catch (error) {
      return { ok: true, ready: false, leanVersion: null, issue: error instanceof Error ? error.message : 'The local Lean worker is unavailable.' };
    }
  };
  return {
    close() {
      closed = true;
      session?.close();
      session = undefined;
    },
    health() {
      // Simultaneous browser health checks share one subprocess.
      pendingHealth ??= readHealth().finally(() => { pendingHealth = undefined; });
      return pendingHealth;
    },
    async analyze(source, signal) {
      if (closed) throw new WorkerError('WORKER_CLOSED', 'The local Lean service has stopped.', 503);
      if (analyzing) throw new WorkerError('WORKER_BUSY', 'Lean is analyzing another statement.', 429);
      if (!source.trim() || source.length > MAX_SOURCE_CHARACTERS || Buffer.byteLength(source) > MAX_SOURCE_BYTES) {
        throw new WorkerError('INVALID_SOURCE', 'Provide a nonempty Lean statement of at most 32,768 characters and 65,536 bytes.', 400);
      }
      analyzing = true;
      try {
        let config: WorkerConfig;
        try {
          config = await loadWorkerConfig(configPath);
        } catch (error) {
          if (error instanceof ConfigError) throw new WorkerError('WORKER_UNAVAILABLE', error.message, 503);
          throw error;
        }
        const executableInfo = await stat(config.workerExecutable);
        const fingerprint = JSON.stringify([config, executableInfo.mtimeMs, executableInfo.size]);
        if (closed) throw new WorkerError('WORKER_CLOSED', 'The local Lean service has stopped.', 503);
        if (!session || sessionFingerprint !== fingerprint) {
          session?.close();
          session = new LeanSession({
            executable: config.workerExecutable,
            cwd: options.rootDir,
            env: workerEnvironment(config),
            timeoutMs: options.timeoutMs,
          });
          sessionFingerprint = fingerprint;
        }
        return await session.analyze(source, signal);
      } finally {
        analyzing = false;
      }
    },
  };
}
