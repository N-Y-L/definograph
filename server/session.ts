import type { AnalysisOptions } from '../src/protocol.js';
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { WorkerError, type WorkerResult } from './protocol.js';

interface PendingRequest {
  requestId: string;
  resolve: (result: WorkerResult) => void;
  reject: (error: WorkerError) => void;
  timer: ReturnType<typeof setTimeout>;
  signal?: AbortSignal;
  abort: () => void;
  outputBytes: number;
  errorBytes: number;
}

interface ProcessState {
  child: ChildProcessWithoutNullStreams;
  pending?: PendingRequest;
  chunks: Buffer[];
}

/** A single bounded JSON-lines connection. A protocol failure always discards its process. */
export class LeanSession {
  private state?: ProcessState;
  private closed = false;

  constructor(private readonly options: {
    executable: string;
    args?: string[];
    cwd: string;
    env?: NodeJS.ProcessEnv;
    timeoutMs?: number;
    maxOutputBytes?: number;
    maxErrorBytes?: number;
  }) {}

  analyze(source: string, signal?: AbortSignal, options?: AnalysisOptions): Promise<WorkerResult> {
    if (this.closed) return Promise.reject(new WorkerError('WORKER_CLOSED', 'The local Lean service has stopped.', 503));
    if (signal?.aborted) return Promise.reject(new WorkerError('CANCELLED', 'Analysis was cancelled.', 499));
    if (this.state?.pending) return Promise.reject(new WorkerError('WORKER_BUSY', 'Lean is analyzing another statement.', 429));
    const state = this.state ?? this.start();
    return new Promise((resolve, reject) => {
      const requestId = randomUUID();
      const abort = () => this.discard(state, new WorkerError('CANCELLED', 'Analysis was cancelled.', 499));
      const timer = setTimeout(() => this.discard(state, new WorkerError(
        'WORKER_TIMEOUT', 'Lean analysis exceeded the time limit. Try a smaller statement.', 504,
      )), this.options.timeoutMs ?? 30_000);
      timer.unref();
      state.pending = { requestId, resolve, reject, timer, signal, abort, outputBytes: 0, errorBytes: 0 };
      signal?.addEventListener('abort', abort, { once: true });
      // Only one bounded source can be in flight. The stream owns backpressure; no unbounded queue exists.
      state.child.stdin.write(`${JSON.stringify({ ...options, requestId, source })}\n`, (error) => {
        if (error) this.discard(state, new WorkerError('WORKER_FAILED', 'The local Lean worker stopped unexpectedly.'));
      });
      if (signal?.aborted) abort();
    });
  }

  close(): void {
    this.closed = true;
    if (this.state) this.discard(this.state, new WorkerError('WORKER_CLOSED', 'The local Lean service has stopped.', 503));
  }

  private start(): ProcessState {
    const child = spawn(this.options.executable, this.options.args ?? [], {
      cwd: this.options.cwd, env: this.options.env, stdio: ['pipe', 'pipe', 'pipe'],
      windowsHide: true, shell: false,
    });
    const state: ProcessState = { child, chunks: [] };
    this.state = state;
    child.stdout.on('data', (chunk: Buffer) => this.onOutput(state, chunk));
    child.stderr.on('data', (chunk: Buffer) => {
      if (this.state !== state) return;
      if (!state.pending) {
        this.discard(state, new WorkerError('INVALID_WORKER_RESPONSE', 'The Lean worker emitted unexpected diagnostics.'));
        return;
      }
      state.pending.errorBytes += chunk.length;
      if (state.pending.errorBytes > (this.options.maxErrorBytes ?? 128 * 1024)) {
        this.discard(state, new WorkerError('WORKER_OUTPUT_LIMIT', 'Lean analysis produced too much diagnostic output.'));
      }
    });
    child.on('error', () => this.discard(state, new WorkerError(
      'WORKER_UNAVAILABLE', 'The local Lean worker could not start. Run npm run setup:lean.', 503,
    )));
    child.on('close', () => this.discard(state, new WorkerError('WORKER_FAILED', 'The local Lean worker stopped unexpectedly.')));
    child.stdin.on('error', () => this.discard(state, new WorkerError('WORKER_FAILED', 'The local Lean worker stopped unexpectedly.')));
    return state;
  }

  private onOutput(state: ProcessState, chunk: Buffer): void {
    if (this.state !== state) return;
    const pending = state.pending;
    if (!pending) {
      this.discard(state, new WorkerError('INVALID_WORKER_RESPONSE', 'The Lean worker emitted an unsolicited response.'));
      return;
    }
    pending.outputBytes += chunk.length;
    if (pending.outputBytes > (this.options.maxOutputBytes ?? 2 * 1024 * 1024)) {
      this.discard(state, new WorkerError('WORKER_OUTPUT_LIMIT', 'Lean analysis produced too much output. Try a smaller statement.'));
      return;
    }
    const newline = chunk.indexOf(10);
    state.chunks.push(chunk);
    if (newline === -1) return;
    const output = Buffer.concat(state.chunks);
    // A single request must produce exactly one complete line, with no unassigned trailing bytes.
    if (newline !== chunk.length - 1 || output.indexOf(10) !== output.length - 1) {
      this.discard(state, new WorkerError('INVALID_WORKER_RESPONSE', 'The Lean worker returned extra response data.'));
      return;
    }
    let result: unknown;
    try { result = JSON.parse(output.toString('utf8')); } catch {
      this.discard(state, new WorkerError('INVALID_WORKER_RESPONSE', 'The Lean worker returned an invalid response.'));
      return;
    }
    if (!result || typeof result !== 'object' || Array.isArray(result) ||
      typeof (result as WorkerResult).ok !== 'boolean' || !Array.isArray((result as WorkerResult).diagnostics) ||
      (result as WorkerResult).requestId !== pending.requestId) {
      this.discard(state, new WorkerError('INVALID_WORKER_RESPONSE', 'The Lean worker returned an incomplete or mismatched response.'));
      return;
    }
    state.chunks = [];
    state.pending = undefined;
    this.cleanup(pending);
    pending.resolve(result as WorkerResult);
  }

  private cleanup(pending: PendingRequest): void {
    clearTimeout(pending.timer);
    pending.signal?.removeEventListener('abort', pending.abort);
  }

  private discard(state: ProcessState, error: WorkerError): void {
    if (this.state !== state) return;
    this.state = undefined;
    const pending = state.pending;
    state.pending = undefined;
    state.chunks = [];
    state.child.kill('SIGKILL');
    if (pending) {
      this.cleanup(pending);
      pending.reject(error);
    }
  }
}
