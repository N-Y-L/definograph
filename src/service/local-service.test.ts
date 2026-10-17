import { afterEach, describe, expect, it, vi } from 'vitest';
import type { StatementNode } from '../core';
import { BUSY_RETRIES, checkHealth, HEALTH_RETRY_MS, healthLabel, readAnalysisReply, requestAnalysis, retryAfterMs, watchHealth, type HealthState } from './local-service';

const tree: StatementNode = { id: 'n', kind: 'predicate', label: 'True', lean: 'True', children: [], expression: { kind: 'const', name: 'True' } };
const reading = { ok: true, source: 'True', pretty: 'True', type: 'Prop', tree, expression: tree.expression, metrics: [], diagnostics: [] };
const serverError = (status: number, code: string, error = 'Server text.') => ({ status, body: { ok: false, error, code, diagnostics: [{ severity: 'error', message: error }] } });
/** A minimal stand-in for a fetch Response: status, headers and a text body. */
const reply = (status: number, body: unknown, headers: Record<string, string> = {}) =>
  ({ status, headers: new Headers(headers), text: async () => typeof body === 'string' ? body : JSON.stringify(body) }) as unknown as Response;
const busy = () => reply(429, serverError(429, 'WORKER_BUSY', 'Lean is analyzing another statement. Try again when it finishes.').body, { 'Retry-After': '1' });

/** A fake fetch that answers each call from the list, repeating the last answer. */
function fakeFetch(...answers: (() => Response | Promise<Response>)[]) {
  const calls: string[] = [];
  const send = vi.fn(async (input: RequestInfo | URL) => { calls.push(String(input)); return answers[Math.min(calls.length, answers.length) - 1]!(); });
  return { send: send as unknown as typeof fetch, calls };
}
const payload = { source: 'True', inputMode: 'term' as const, previewDefinitions: true };

afterEach(() => { vi.useRealTimers(); });

describe('reading a reply of the local service', () => {
  it('gives each server error code its own cause, and points at the statement only for a refusal or its length', () => {
    const cases: [number, string, string][] = [
      [429, 'WORKER_BUSY', 'busy'], [504, 'WORKER_TIMEOUT', 'timeout'],
      [413, 'BODY_TOO_LARGE', 'too-large'], [400, 'INVALID_SOURCE', 'too-large'],
      [502, 'WORKER_OUTPUT_LIMIT', 'answer-too-large'],
      [400, 'INVALID_JSON', 'refused'], [400, 'INVALID_OPTIONS', 'refused'], [415, 'INVALID_CONTENT_TYPE', 'refused'], [415, 'UNSUPPORTED_ENCODING', 'refused'],
      [404, 'NOT_FOUND', 'refused'], [403, 'FORBIDDEN_HOST', 'refused'], [403, 'FORBIDDEN_ORIGIN', 'refused'],
      [503, 'WORKER_UNAVAILABLE', 'unavailable'], [503, 'WORKER_CLOSED', 'unavailable'],
      [502, 'WORKER_FAILED', 'failed'], [502, 'INVALID_WORKER_RESPONSE', 'failed'], [500, 'INTERNAL_ERROR', 'failed'], [502, 'SOMETHING_NEW', 'failed'],
    ];
    const titles = new Set<string>();
    for (const [status, code, kind] of cases) {
      const outcome = readAnalysisReply(status, null, JSON.stringify(serverError(status, code).body));
      expect(outcome.ok, code).toBe(false);
      if (outcome.ok) continue;
      expect(outcome.failure.kind, code).toBe(kind);
      // The plain sentence comes first; the code is last.
      expect(outcome.failure.detail, code).toBe(`Server text. (${code})`);
      if (kind !== 'too-large') expect(`${outcome.failure.title} ${outcome.failure.advice}`, code).not.toMatch(/correct the statement|could not be read|did not accept/i);
      titles.add(outcome.failure.title);
    }
    expect(titles.size).toBe(7);
  });

  it('falls back on the HTTP status when a reply has no code', () => {
    for (const [status, kind] of [[429, 'busy'], [504, 'timeout'], [413, 'too-large'], [503, 'unavailable'], [500, 'failed']] as const) {
      const outcome = readAnalysisReply(status, null, '{"ok":false}');
      expect(!outcome.ok && outcome.failure.kind, String(status)).toBe(kind);
    }
  });

  it('reads a refusal, a valid reading, an invalid reading and a reply that is not JSON', () => {
    const rejected = readAnalysisReply(200, null, JSON.stringify({ ok: false, error: "unknown identifier 'foo'\nmore", diagnostics: [] }));
    expect(rejected).toMatchObject({ ok: false, failure: { kind: 'rejected', title: 'Lean or Definograph refused this statement.', detail: "unknown identifier 'foo'\nmore" } });
    // A refusal may be one of Definograph's own limits, which Lean never saw; the message must not say that Lean refused.
    const limit = readAnalysisReply(200, null, JSON.stringify({ ok: false, error: 'Logical structure exceeds export depth (80).', diagnostics: [] }));
    expect(!limit.ok && `${limit.failure.title} ${limit.failure.advice}`).toMatch(/Definograph's own limits/);
    expect(!limit.ok && limit.failure.title).not.toMatch(/^Lean (did not|refused)/);
    expect(readAnalysisReply(200, null, '{"ok":false}')).toMatchObject({ ok: false, failure: { detail: 'No reason was given.' } });
    const fromDiagnostics = readAnalysisReply(200, null, JSON.stringify({ ok: false, diagnostics: [{ severity: 'error', message: 'type mismatch' }] }));
    expect(!fromDiagnostics.ok && fromDiagnostics.failure.detail).toBe('type mismatch');
    expect(readAnalysisReply(200, null, JSON.stringify(reading))).toEqual({ ok: true, analysis: reading });
    const invalid = readAnalysisReply(200, null, JSON.stringify({ ...reading, tree: { ...tree, children: [{ id: 'c' }] } }));
    expect(invalid).toMatchObject({ ok: false, failure: { kind: 'unreadable', title: "Definograph could not read Lean's answer.", detail: 'The answer has an unexpected shape: tree.children[0].kind is not text.' } });
    const proxy = readAnalysisReply(500, null, '');
    expect(proxy).toMatchObject({ ok: false, failure: { kind: 'unreachable', detail: "The answer was not in the local Lean service's format, so something in between, such as the development server, probably sent it. (HTTP 500)" } });
  });

  it('reads Retry-After in seconds or as a date, and otherwise waits one second', () => {
    expect(retryAfterMs('1')).toBe(1000);
    expect(retryAfterMs(' 3 ')).toBe(3000);
    expect(retryAfterMs(null)).toBe(1000);
    expect(retryAfterMs('soon')).toBe(1000);
    const now = Date.parse('2026-10-17T12:00:00Z');
    expect(retryAfterMs('Sat, 17 Oct 2026 12:00:02 GMT', now)).toBe(2000);
    expect(retryAfterMs('Sat, 17 Oct 2026 11:00:00 GMT', now)).toBe(0);
  });
});

describe('asking the local service for a reading', () => {
  it('retries a busy reply after Retry-After and shows each retry', async () => {
    const { send, calls } = fakeFetch(busy, busy, () => reply(200, reading));
    const waits: number[] = [], retries: [number, number][] = [];
    const outcome = await requestAnalysis(payload, { signal: new AbortController().signal, fetch: send, wait: async ms => { waits.push(ms); }, onBusyRetry: (retry, of) => retries.push([retry, of]) });
    expect(outcome).toEqual({ ok: true, analysis: reading });
    expect(calls).toEqual(['/api/analyze', '/api/analyze', '/api/analyze']);
    expect(waits).toEqual([1000, 1000]);
    expect(retries).toEqual([[1, BUSY_RETRIES], [2, BUSY_RETRIES]]);
  });

  it('says a retry is sent once its wait is over, so the page stops saying Lean is busy while Lean reads this statement', async () => {
    const events: string[] = [];
    const { send } = fakeFetch(() => { events.push('request'); return busy(); }, () => { events.push('request'); return reply(200, reading); });
    const outcome = await requestAnalysis(payload, { signal: new AbortController().signal, fetch: send,
      onBusyRetry: retry => events.push(`retry ${retry} announced`), wait: async () => { events.push('wait'); }, onBusyRetrySent: () => events.push('retry sent') });
    expect(outcome).toEqual({ ok: true, analysis: reading });
    expect(events).toEqual(['request', 'retry 1 announced', 'wait', 'retry sent', 'request']);
  });

  it('gives the advice that helps for a refused origin, which reloading cannot fix', () => {
    const origin = readAnalysisReply(403, null, JSON.stringify(serverError(403, 'FORBIDDEN_ORIGIN').body));
    const other = readAnalysisReply(400, null, JSON.stringify(serverError(400, 'INVALID_JSON').body));
    expect(origin.ok || other.ok).toBe(false);
    if (origin.ok || other.ok) return;
    expect(origin.failure.kind).toBe(other.failure.kind);
    expect(origin.failure.advice).toMatch(/npm run dev/);
    expect(origin.failure.advice).not.toMatch(/Reload/);
    expect(other.failure.advice).toMatch(/Reload the page/);
  });

  it('gives up with the busy message after a bounded number of retries', async () => {
    const { send, calls } = fakeFetch(busy);
    const retries: number[] = [];
    const outcome = await requestAnalysis(payload, { signal: new AbortController().signal, fetch: send, wait: async () => undefined, onBusyRetry: retry => retries.push(retry) });
    expect(outcome).toMatchObject({ ok: false, failure: { kind: 'busy', title: 'Lean is busy with another statement.' } });
    expect(calls).toHaveLength(BUSY_RETRIES + 1);
    expect(retries).toEqual([1, 2, 3]);
  });

  it('does not wait longer than the cap when Retry-After asks for more', async () => {
    const { send, calls } = fakeFetch(() => reply(429, serverError(429, 'WORKER_BUSY').body, { 'Retry-After': '30' }));
    const outcome = await requestAnalysis(payload, { signal: new AbortController().signal, fetch: send, wait: async () => { throw new Error('must not wait'); } });
    expect(outcome).toMatchObject({ ok: false, failure: { kind: 'busy' } });
    expect(calls).toHaveLength(1);
  });

  it('a newer request (choosing another example) cancels a pending retry', async () => {
    vi.useFakeTimers();
    const { send, calls } = fakeFetch(busy, () => reply(200, reading));
    const controller = new AbortController();
    let scheduled!: () => void;
    const retryScheduled = new Promise<void>(resolve => { scheduled = resolve; });
    const pending = requestAnalysis(payload, { signal: controller.signal, fetch: send, onBusyRetry: () => scheduled() });
    await retryScheduled;
    controller.abort();
    await expect(pending).rejects.toMatchObject({ name: 'AbortError' });
    await vi.advanceTimersByTimeAsync(10_000);
    expect(calls).toHaveLength(1);
  });

  it('reports an unreachable service, and passes a cancellation through', async () => {
    const offline = fakeFetch(() => Promise.reject(new TypeError('fetch failed')));
    await expect(requestAnalysis(payload, { signal: new AbortController().signal, fetch: offline.send }))
      .resolves.toMatchObject({ ok: false, failure: { kind: 'unreachable', title: 'The local Lean service is not reachable.' } });
    const controller = new AbortController();
    controller.abort();
    const cancelled = fakeFetch(() => Promise.reject(controller.signal.reason));
    await expect(requestAnalysis(payload, { signal: controller.signal, fetch: cancelled.send })).rejects.toMatchObject({ name: 'AbortError' });
  });
});

describe('the Lean connection label', () => {
  it('shows the real state of the service', async () => {
    const ready = { ok: true, ready: true, leanVersion: 'Lean (version 4.28.0, arm64)', issue: null };
    expect(await checkHealth(fakeFetch(() => reply(200, ready)).send)).toEqual({ phase: 'connected', leanVersion: ready.leanVersion });
    expect(await checkHealth(fakeFetch(() => reply(200, { ok: true, ready: false, leanVersion: null, issue: 'Run npm run setup:lean.' })).send))
      .toEqual({ phase: 'unavailable', issue: 'Run npm run setup:lean.' });
    expect(await checkHealth(fakeFetch(() => Promise.reject(new TypeError('fetch failed'))).send)).toMatchObject({ phase: 'unreachable' });
    expect(await checkHealth(fakeFetch(() => reply(500, '')).send)).toMatchObject({ phase: 'unreachable' });
    expect(await checkHealth(fakeFetch(() => reply(200, { ok: true })).send)).toMatchObject({ phase: 'unavailable' });
    const label = (state: HealthState) => healthLabel(state).text;
    expect(label({ phase: 'checking' })).toBe('Checking Lean…');
    expect(label({ phase: 'connected', leanVersion: ready.leanVersion })).toBe('Lean connected');
    expect(healthLabel({ phase: 'connected', leanVersion: ready.leanVersion }).detail).toBe('Lean 4.28.0 · read-only environment');
    expect(label({ phase: 'unavailable', issue: 'x' })).toBe('Lean unavailable');
    expect(label({ phase: 'unreachable', issue: 'x' })).toBe('Lean service not reachable');
  });

  it('keeps checking after a failed check and recovers when the service comes back', async () => {
    const offline = () => Promise.reject(new TypeError('fetch failed'));
    const { send, calls } = fakeFetch(offline, offline, () => reply(200, { ok: true, ready: true, leanVersion: 'Lean (version 4.28.0)', issue: null }));
    const states: string[] = [], waits: number[] = [];
    await watchHealth({ signal: new AbortController().signal, fetch: send, wait: async ms => { waits.push(ms); }, onState: state => states.push(state.phase) });
    expect(states).toEqual(['unreachable', 'unreachable', 'connected']);
    expect(waits).toEqual([HEALTH_RETRY_MS, HEALTH_RETRY_MS]);
    expect(calls).toEqual(['/api/health', '/api/health', '/api/health']);
  });

  it('stops checking when the page no longer needs it', async () => {
    vi.useFakeTimers();
    const { send, calls } = fakeFetch(() => Promise.reject(new TypeError('fetch failed')));
    const controller = new AbortController();
    const watching = watchHealth({ signal: controller.signal, fetch: send, onState: () => controller.abort() });
    await watching;
    await vi.advanceTimersByTimeAsync(HEALTH_RETRY_MS * 3);
    expect(calls).toHaveLength(1);
  });
});
