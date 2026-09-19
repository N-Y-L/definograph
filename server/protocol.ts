export class WorkerError extends Error {
  constructor(readonly code: string, message: string, readonly status = 502) {
    super(message);
    this.name = 'WorkerError';
  }
}

export interface WorkerResult {
  ok: boolean;
  diagnostics: unknown[];
  [key: string]: unknown;
}
