import type { Analysis } from '../core';
import { analysisShapeIssue } from '../core/analysis-shape';
import type { AnalysisRequest } from '../protocol';

/** Why a reading did not arrive. Only `rejected` and `too-large` point at the statement, and `rejected` may be
 * one of Definograph's own limits rather than an error in it. */
export type FailureKind = 'rejected' | 'busy' | 'timeout' | 'too-large' | 'answer-too-large' | 'refused' | 'unavailable' | 'unreachable' | 'failed' | 'unreadable';
export interface ServiceFailure { kind: FailureKind; title: string; advice: string; detail: string }

const MESSAGES: Record<FailureKind, { title: string; advice: string }> = {
  // An HTTP 200 refusal comes from Lean, or from one of Definograph's own limits (its syntax allowlist, the
  // proposition and sorry rules, the export depth, definition expansion, Lean's heartbeat limit).
  rejected: { title: 'Lean or Definograph refused this statement.', advice: "The reason is in the Lean source panel. It may be an error that Lean found in the statement, or one of Definograph's own limits on what it reads; in that case the statement can still be valid Lean." },
  busy: { title: 'Lean is busy with another statement.', advice: 'Lean reads one statement at a time. Wait until it finishes, then interpret this statement again.' },
  timeout: { title: 'Lean was stopped at its time limit.', advice: "Its time limit includes loading Lean's libraries, which happens again after every stop. Try once more; if Lean is stopped again, try a shorter statement or expand fewer definitions." },
  'too-large': { title: 'This statement is too long.', advice: 'A statement may have at most 32,768 characters and at most 65,536 bytes; a symbol such as ∀ or ℝ takes 3 bytes.' },
  'answer-too-large': { title: "Lean's answer was larger than the local Lean service accepts.", advice: 'Expand fewer definitions, or try a shorter statement.' },
  refused: { title: 'The local Lean service refused the request from this page.', advice: 'This is not a fault in the statement. Reload the page. If it happens again, stop the local Lean service, start it again with npm run dev, and open http://127.0.0.1:5173.' },
  unavailable: { title: 'Lean is not available.', advice: 'The local Lean service answered, but could not use Lean. Its reason is in the Lean source panel.' },
  unreachable: { title: 'The local Lean service is not reachable.', advice: 'Start it with npm run dev in the Definograph folder, then interpret the statement again.' },
  failed: { title: 'The local Lean service failed on this request.', advice: 'Interpret the statement again. If this happens again, stop the local Lean service and start it again with npm run dev.' },
  unreadable: { title: "Definograph could not read Lean's answer.", advice: 'Lean answered, but Definograph could not use the answer, so nothing is drawn. This is a fault in Definograph, not in the statement. The details are in the Lean source panel.' },
};
/** Advice for one code where the advice of its kind would not help. */
const CODE_ADVICE: Record<string, string> = {
  // npm start with the Vite page (npm run dev:web) open: reloading cannot help, starting the service with --dev does.
  FORBIDDEN_ORIGIN: 'The service accepts the page on port 5173 only when it was started with npm run dev. Stop the local Lean service, start it again with npm run dev, and open http://127.0.0.1:5173.',
};

export function serviceFailure(kind: FailureKind, detail: string, code?: string): ServiceFailure {
  return { kind, ...MESSAGES[kind], ...(code && CODE_ADVICE[code] ? { advice: CODE_ADVICE[code] } : {}), detail };
}

/** Error codes sent by server/http.ts, server/worker.ts and server/session.ts. WORKER_FAILED,
 * INVALID_WORKER_RESPONSE, INTERNAL_ERROR, CANCELLED and any unknown code count as `failed`. */
const CODE_KINDS: Record<string, FailureKind> = {
  WORKER_BUSY: 'busy',
  WORKER_TIMEOUT: 'timeout',
  // This page never sends an empty statement (App checks first), so INVALID_SOURCE means one that is too long.
  BODY_TOO_LARGE: 'too-large', INVALID_SOURCE: 'too-large',
  WORKER_OUTPUT_LIMIT: 'answer-too-large',
  INVALID_JSON: 'refused', INVALID_OPTIONS: 'refused', INVALID_CONTENT_TYPE: 'refused', UNSUPPORTED_ENCODING: 'refused',
  NOT_FOUND: 'refused', FORBIDDEN_HOST: 'refused', FORBIDDEN_ORIGIN: 'refused',
  WORKER_UNAVAILABLE: 'unavailable', WORKER_CLOSED: 'unavailable',
};
const STATUS_KINDS: Record<number, FailureKind> = { 413: 'too-large', 429: 'busy', 503: 'unavailable', 504: 'timeout' };

export type AnalysisOutcome =
  | { ok: true; analysis: Analysis }
  | { ok: false; failure: ServiceFailure; retryAfterMs?: number };

const record = (value: unknown): value is Record<string, unknown> => !!value && typeof value === 'object' && !Array.isArray(value);

function leanMessage(body: Record<string, unknown>): string {
  if (typeof body.error === 'string' && body.error) return body.error;
  const messages = Array.isArray(body.diagnostics) ? body.diagnostics.flatMap(item => record(item) && typeof item.message === 'string' ? [item.message] : []) : [];
  return messages.join('\n') || 'No reason was given.';
}

/** Retry-After as this server sends it (whole seconds), or as an HTTP date. Otherwise one second. */
export function retryAfterMs(header: string | null, now = Date.now()): number {
  const value = header?.trim() ?? '';
  if (/^\d{1,6}$/.test(value)) return Number(value) * 1000;
  const date = Date.parse(value);
  return Number.isNaN(date) ? 1000 : Math.max(0, date - now);
}

/** Read one reply of POST /api/analyze. Only an HTTP 200 reply can carry a reading or a refusal (`rejected`). */
export function readAnalysisReply(status: number, retryAfter: string | null, text: string): AnalysisOutcome {
  let body: unknown;
  try { body = JSON.parse(text); } catch {
    // Every /api answer of the local service is JSON; a truncated one fails here too.
    return { ok: false, failure: serviceFailure('unreachable', `The answer was not in the local Lean service's format, so something in between, such as the development server, probably sent it. (HTTP ${status})`) };
  }
  if (status === 200) {
    if (record(body) && body.ok === false) return { ok: false, failure: serviceFailure('rejected', leanMessage(body)) };
    const issue = analysisShapeIssue(body);
    return issue ? { ok: false, failure: serviceFailure('unreadable', `The answer has an unexpected shape: ${issue}.`) } : { ok: true, analysis: body as Analysis };
  }
  const code = record(body) && typeof body.code === 'string' ? body.code : undefined;
  const message = record(body) && typeof body.error === 'string' ? body.error : undefined;
  const kind = (code ? CODE_KINDS[code] : undefined) ?? STATUS_KINDS[status] ?? 'failed';
  // The plain sentence first; the code is for whoever reports the problem.
  const detail = message ? `${message} (${code ?? `HTTP ${status}`})` : (code ?? `HTTP ${status}`);
  return { ok: false, failure: serviceFailure(kind, detail, code), ...(kind === 'busy' ? { retryAfterMs: retryAfterMs(retryAfter) } : {}) };
}

/** Resolves after `ms`, or rejects with the signal's reason as soon as it aborts. */
export function abortableDelay(ms: number, signal: AbortSignal): Promise<void> {
  return new Promise((resolve, reject) => {
    if (signal.aborted) { reject(signal.reason); return; }
    const stop = () => { clearTimeout(timer); reject(signal.reason); };
    const timer = setTimeout(() => { signal.removeEventListener('abort', stop); resolve(); }, ms);
    signal.addEventListener('abort', stop, { once: true });
  });
}

/** A busy reply is retried this many times, waiting as long as Retry-After asks, but never longer than the cap. */
export const BUSY_RETRIES = 3;
export const MAX_BUSY_WAIT_MS = 5_000;

export interface AnalysisRequestOptions {
  signal: AbortSignal;
  /** Called when a busy reply will be retried after a wait, with the retry's number. */
  onBusyRetry?: (retry: number, of: number) => void;
  /** Called when that wait is over and the retry is sent; Lean may now be reading this statement. */
  onBusyRetrySent?: () => void;
  fetch?: typeof fetch;
  wait?: (ms: number, signal: AbortSignal) => Promise<void>;
}

/** Ask the local Lean service for a reading. Aborting the signal (a newer request does) cancels a pending retry:
 * the promise then rejects with the abort reason. Every other failure resolves as an outcome. */
export async function requestAnalysis(payload: AnalysisRequest, options: AnalysisRequestOptions): Promise<AnalysisOutcome> {
  const { signal, fetch: send = fetch, wait = abortableDelay } = options;
  for (let retry = 1; ; retry++) {
    let outcome: AnalysisOutcome;
    try {
      const response = await send('/api/analyze', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(payload), signal });
      outcome = readAnalysisReply(response.status, response.headers.get('retry-after'), await response.text());
    } catch (cause) {
      if (signal.aborted) throw cause;
      return { ok: false, failure: serviceFailure('unreachable', 'No answer came from the local Lean service.') };
    }
    if (outcome.ok || outcome.failure.kind !== 'busy' || retry > BUSY_RETRIES || (outcome.retryAfterMs ?? 0) > MAX_BUSY_WAIT_MS) return outcome;
    options.onBusyRetry?.(retry, BUSY_RETRIES);
    await wait(outcome.retryAfterMs ?? 1000, signal);
    options.onBusyRetrySent?.();
  }
}

export type HealthState =
  | { phase: 'checking' }
  | { phase: 'connected'; leanVersion: string }
  | { phase: 'unavailable'; issue: string }
  | { phase: 'unreachable'; issue: string };

/** One GET /api/health. Never throws; an aborted check reports `unreachable`, which the caller discards. */
export async function checkHealth(send: typeof fetch = fetch, signal?: AbortSignal): Promise<HealthState> {
  let body: unknown;
  try {
    const response = await send('/api/health', { signal });
    body = JSON.parse(await response.text());
  } catch {
    return { phase: 'unreachable', issue: 'The local Lean service did not answer.' };
  }
  if (!record(body) || typeof body.ready !== 'boolean') return { phase: 'unavailable', issue: 'The local Lean service sent an unexpected health answer.' };
  if (body.ready) return { phase: 'connected', leanVersion: typeof body.leanVersion === 'string' ? body.leanVersion : '' };
  return { phase: 'unavailable', issue: typeof body.issue === 'string' && body.issue ? body.issue : 'Lean is not ready.' };
}

export const HEALTH_RETRY_MS = 5_000;

/** Check health now, then again every HEALTH_RETRY_MS until Lean is connected or the signal aborts. */
export async function watchHealth(options: { onState: (state: HealthState) => void; signal: AbortSignal; fetch?: typeof fetch; wait?: (ms: number, signal: AbortSignal) => Promise<void> }): Promise<void> {
  const { onState, signal, wait = abortableDelay } = options;
  while (!signal.aborted) {
    const state = await checkHealth(options.fetch, signal);
    if (signal.aborted) return;
    onState(state);
    if (state.phase === 'connected') return;
    try { await wait(HEALTH_RETRY_MS, signal); } catch { return; }
  }
}

export function healthLabel(state: HealthState): { text: string; tone: 'ready' | 'pending' | 'down'; detail: string } {
  switch (state.phase) {
    case 'checking': return { text: 'Checking Lean…', tone: 'pending', detail: 'Checking the local Lean service…' };
    case 'connected': return { text: 'Lean connected', tone: 'ready', detail: `Lean ${state.leanVersion.match(/\d+\.\d+\.\d+/)?.[0] ?? '4'} · read-only environment` };
    case 'unavailable': return { text: 'Lean unavailable', tone: 'down', detail: `${state.issue} Checking again every ${HEALTH_RETRY_MS / 1000} seconds.` };
    case 'unreachable': return { text: 'Lean service not reachable', tone: 'down', detail: `${state.issue} Start it with npm run dev. Checking again every ${HEALTH_RETRY_MS / 1000} seconds.` };
  }
}
