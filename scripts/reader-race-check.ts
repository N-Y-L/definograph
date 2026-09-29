/** RC5 webview-side race control: the production build runs in headless Chrome
 * over the DevTools protocol with an injected host spy and a save interceptor.
 * Two editor requests are announced on the same buffer version, then the
 * superseded request's result arrives late carrying a longer retained history
 * from the same real corpus input. This replays saved captures, not fresh native
 * refreshes. The displayed history, the panel (compared with the accepted module)
 * and the saved source snapshot must all carry only the accepted result; late
 * duplicates and a late obsolete status must change nothing and post nothing.
 * Writes a report and a screenshot to DEFINOGRAPH_RACE_EVIDENCE_OUT. */
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createServer } from 'node:http';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { registerHooks } from 'node:module';
import { validateDecompositionHistory, validateSourceDecomposition } from '../src/editor/source-decomposition.js';
import { occurrenceProvenance, type OccurrenceProvenance } from '../src/editor/source-provenance.js';
import { parseEditorMessage } from '../src/editor/host.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

// The Node serialization oracle imports a React module that also imports CSS.
// Ignore styles only for this import; Chrome still loads the production assets.
const styles = registerHooks({ load(url, context, next) {
  return url.endsWith('.css') ? { format: 'module', source: 'export {};', shortCircuit: true } : next(url, context);
} });
const { savedSourceSnapshot } = await import('../src/editor/SourceSnapshotReading.js');
styles.deregister();

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const dist = path.join(root, 'dist');
const chrome = process.env.DEFINOGRAPH_CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const corpusPath = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES ?? '/private/tmp/definograph-logical-editor-captures.json';
const out = process.env.DEFINOGRAPH_RACE_EVIDENCE_OUT;
assert.ok(out, 'Set DEFINOGRAPH_RACE_EVIDENCE_OUT to a directory outside the repository.');
await mkdir(out); // A run must never overwrite an earlier evidence directory.
const { canonical } = createExactJsonTools();
const sha = (text: string) => createHash('sha256').update(text).digest('hex');
const report: Record<string, unknown> = { startedAt: new Date().toISOString(), corpus: corpusPath, corpusSha256: sha(await readFile(corpusPath, 'utf8')), distIndexSha256: sha(await readFile(path.join(dist, 'index.html'), 'utf8')), scenarios: [], consoleErrors: [] };

const types: Record<string, string> = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.svg': 'image/svg+xml', '.json': 'application/json', '.woff2': 'font/woff2', '.woff': 'font/woff', '.png': 'image/png' };
const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? '/', 'http://127.0.0.1');
  const file = path.join(dist, url.pathname === '/' ? 'index.html' : url.pathname);
  try { const body = await readFile(file); response.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream' }); response.end(body); }
  catch { response.writeHead(404); response.end(); }
});
let browserProcess: ReturnType<typeof spawn> | undefined;
let browserProfile: string | undefined;
let closeSocket: (() => void) | undefined;
let captureFailure: (() => Promise<void>) | undefined;
try {
await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
const address = server.address(); assert.ok(address && typeof address === 'object');
const pageUrl = `http://127.0.0.1:${address.port}/`;
const profile = await mkdtemp(path.join(os.tmpdir(), 'definograph-chrome-race-'));
browserProfile = profile;
const browser = spawn(chrome, ['--headless=new', '--disable-gpu', '--no-first-run', '--no-default-browser-check', `--user-data-dir=${profile}`, '--remote-debugging-port=0', '--window-size=1280,900', 'about:blank'], { stdio: ['ignore', 'pipe', 'pipe'] });
browserProcess = browser;
const wsUrl = await new Promise<string>((resolve, reject) => {
  let text = ''; const timer = setTimeout(() => reject(new Error('Chrome did not expose DevTools')), 20000);
  browser.stderr.on('data', chunk => { text += String(chunk); const match = text.match(/DevTools listening on (ws:\/\/\S+)/); if (match) { clearTimeout(timer); resolve(match[1]); } });
  browser.on('error', error => { clearTimeout(timer); reject(error); });
  browser.on('exit', code => { clearTimeout(timer); reject(new Error(`Chrome exited ${code}`)); });
});
const socket = new WebSocket(wsUrl);
closeSocket = () => socket.close();
await new Promise<void>((resolve, reject) => {
  const timer = setTimeout(() => reject(new Error('DevTools connection timed out')), 15000);
  socket.addEventListener('open', () => { clearTimeout(timer); resolve(); });
  socket.addEventListener('error', () => { clearTimeout(timer); reject(new Error('DevTools socket failed')); });
});
let nextId = 1;
const pending = new Map<number, { resolve: (value: unknown) => void; reject: (error: Error) => void; timer: ReturnType<typeof setTimeout> }>();
const listeners: ((method: string, params: Record<string, unknown>, sessionId?: string) => void)[] = [];
socket.addEventListener('message', event => {
  const message = JSON.parse(String(event.data)) as { id?: number; method?: string; params?: Record<string, unknown>; sessionId?: string; result?: unknown; error?: { message: string } };
  if (message.id !== undefined) { const waiter = pending.get(message.id); pending.delete(message.id); if (!waiter) return; clearTimeout(waiter.timer); message.error ? waiter.reject(new Error(message.error.message)) : waiter.resolve(message.result); }
  else if (message.method) for (const listener of listeners) listener(message.method, message.params ?? {}, message.sessionId);
});
socket.addEventListener('close', () => {
  for (const waiter of pending.values()) { clearTimeout(waiter.timer); waiter.reject(new Error('DevTools connection closed')); }
  pending.clear();
});
function send<T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}, sessionId?: string): Promise<T> {
  const id = nextId++;
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => { pending.delete(id); reject(new Error(`DevTools timeout: ${method}`)); }, 15000);
    pending.set(id, { resolve: value => resolve(value as T), reject, timer });
    socket.send(JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) }));
  });
}
const waitFor = (predicate: (method: string, params: Record<string, unknown>) => boolean, timeoutMs = 15000) => new Promise<void>((resolve, reject) => {
  const timer = setTimeout(() => reject(new Error('timed out waiting for browser event')), timeoutMs);
  listeners.push((method, params) => { if (predicate(method, params)) { clearTimeout(timer); resolve(); } });
});
const { targetId } = await send<{ targetId: string }>('Target.createTarget', { url: 'about:blank' });
const { sessionId } = await send<{ sessionId: string }>('Target.attachToTarget', { targetId, flatten: true });
const page = <T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}) => send<T>(method, params, sessionId);
await page('Page.enable'); await page('Runtime.enable'); await page('Log.enable');
const consoleErrors = report.consoleErrors as string[];
listeners.push((method, params) => {
  if (method === 'Runtime.exceptionThrown') consoleErrors.push(`exception: ${JSON.stringify(params.exceptionDetails).slice(0, 300)}`);
  if (method === 'Runtime.consoleAPICalled' && (params.type === 'error' || params.type === 'warning')) consoleErrors.push(`${params.type}: ${JSON.stringify((params.args as unknown[]).map(a => (a as { value?: unknown; description?: string }).value ?? (a as { description?: string }).description)).slice(0, 300)}`);
  if (method === 'Log.entryAdded' && ((params.entry as { level: string }).level === 'error' || (params.entry as { level: string }).level === 'warning')) consoleErrors.push(`log: ${JSON.stringify(params.entry).slice(0, 300)}`);
});
// Host spy plus save interceptor: the saved snapshot's bytes are captured from the Blob the page creates; the download click is swallowed.
await page('Page.addScriptToEvaluateOnNewDocument', { source: `window.__hostMessages = []; window.acquireVsCodeApi = () => ({ postMessage: message => { window.__hostMessages.push(JSON.parse(JSON.stringify(message))); } });
window.__saved = []; const realCreate = URL.createObjectURL.bind(URL); URL.createObjectURL = blob => { if (blob instanceof Blob) blob.text().then(text => window.__saved.push(text)); return realCreate(blob); }; HTMLAnchorElement.prototype.click = function () {};` });
async function evaluate<T>(expression: string): Promise<T> {
  const result = await page<{ result: { value: T }; exceptionDetails?: unknown }>('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
  if (result.exceptionDetails) throw new Error(`page evaluation failed: ${JSON.stringify(result.exceptionDetails).slice(0, 400)}`);
  return result.result.value;
}
captureFailure = async () => {
  const snapshot = await evaluate<string>('document.body.innerText');
  await writeFile(path.join(out, 'failure-state.txt'), snapshot);
  const shot = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
  await writeFile(path.join(out, 'failure-state.png'), Buffer.from(shot.data, 'base64'));
};
const settle = (ms = 250) => new Promise(resolve => setTimeout(resolve, ms));
const hostMessages = () => evaluate<{ type: string }[]>('window.__hostMessages');
const post = async (message: unknown, ms = 300) => { await evaluate(`window.postMessage(${JSON.stringify(message)}, '*'); true`); await settle(ms); };
await page('Emulation.setDeviceMetricsOverride', { width: 1272, height: 900, deviceScaleFactor: 1, mobile: false });
const loaded = waitFor(method => method === 'Page.loadEventFired');
await page('Page.navigate', { url: pageUrl }); await loaded; await settle(600);
assert.deepEqual((await hostMessages()).map(message => message.type), ['statementlens.ready'], 'the page announces itself once');

// Two unmodified records on exactly the same input: A has one additional old
// attempt, B is the accepted shorter history. Shared ancestors are legitimate;
// only A's exclusive tail must disappear. Validate both envelopes before testing
// ordering, so an invalid message cannot make stale rejection pass vacuously.
const rows = JSON.parse(await readFile(corpusPath, 'utf8')) as any[];
const bundle = (row: any) => {
  const decompositions = [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }];
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null, attempts: row.priorAttempts.map((item: any) => ({ snapshot: item.snapshot, record: item.record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  const ids = new Set<string>([row.parent.origin.captureId, row.parent.occurrence?.captureId, ...decompositions.map((item: any) => item.origin.captureId), ...decompositions.map((item: any) => item.record.captureId)].filter(Boolean));
  return { label: row.label as string, snapshot: row.parent.snapshot, origin: row.parent.origin, occurrence: row.parent.occurrence, decompositions, history, ids: [...ids] };
};
const candidates = rows.filter(row => row.label === 'literal Rotor law');
assert.ok(candidates.length >= 2, 'two retained histories from one native input');
const A = bundle(candidates.at(-1));
const B = bundle(candidates.at(-2));
const supersededOnlyIds = A.ids.filter(id => !B.ids.includes(id));
assert.ok(supersededOnlyIds.length > 0, 'the superseded history has an exclusive tail');
assert.deepEqual(A.origin.document, B.origin.document);
assert.deepEqual(A.origin.selection, B.origin.selection);
assert.equal(A.origin.sourceSha256, B.origin.sourceSha256);
report.superseded = { label: A.label, attempts: A.decompositions.length, ids: A.ids }; report.accepted = { label: B.label, attempts: B.decompositions.length, ids: B.ids };
report.fixtureBoundary = { kind: 'unchanged native captures replayed into a simulated host', sharedInput: true, supersededOnlyIds, freshNativeRefreshes: false };
const document = { ...B.origin.document, fileName: new URL(B.origin.document.uri).pathname, selection: B.origin.selection };
const result = (requestId: string, item: typeof A) => ({ type: 'statementlens.error', requestId, document, message: 'Independent guided export unavailable.', sourceSnapshot: item.snapshot, sourceSnapshotOrigin: item.origin, sourceOccurrence: item.occurrence, decompositions: item.decompositions });
const status = (requestId: string, phase = 'analyzing') => ({ type: 'statementlens.status', requestId, phase, document });
assert.ok(parseEditorMessage(result('12', A)), 'superseded envelope is independently admissible');
assert.ok(parseEditorMessage(result('13', B)), 'accepted envelope is independently admissible');

const expectedAttributes = (provenance: OccurrenceProvenance) => {
  const origin = (item: { origin: any; receipts: any }) => ({ originKind: item.origin.kind, originCapture: item.origin.captureId, originStep: item.origin.kind === 'step' ? String(item.origin.stepIndex) : null, receiptCapture: item.receipts.captureId, receiptStart: String(item.receipts.start), receiptCount: String(item.receipts.count) });
  return { occurrences: provenance.occurrences.map(occurrence => ({ index: String(occurrence.index), ...origin(occurrence) })), edges: provenance.edges.map(edge => ({ edge: `${edge.from}-${edge.to}`, kind: edge.relation.kind, ...origin(edge) })), excluded: provenance.excluded ? provenance.excluded.stepIndices.join(',') : null, step: String(provenance.prefix.parentStepIndex) };
};
const renderedAttributes = () => evaluate<Record<string, unknown> | null>(`(() => { const section = document.querySelector('section.source-provenance[data-provenance-route]'); if (!section) return null;
  const pick = el => ({ originKind: el.getAttribute('data-origin-kind'), originCapture: el.getAttribute('data-origin-capture'), originStep: el.getAttribute('data-origin-step'), receiptCapture: el.getAttribute('data-receipt-capture'), receiptStart: el.getAttribute('data-receipt-start'), receiptCount: el.getAttribute('data-receipt-count') });
  return { occurrences: [...section.querySelectorAll('li[data-provenance-occurrence]')].map(el => ({ index: el.getAttribute('data-provenance-occurrence'), ...pick(el) })),
    edges: [...section.querySelectorAll('li[data-provenance-edge]')].map(el => ({ edge: el.getAttribute('data-provenance-edge'), kind: el.getAttribute('data-relation-kind'), ...pick(el) })),
    excluded: (section.parentElement?.querySelector('[data-provenance-excluded]') ?? section.querySelector('[data-provenance-excluded]'))?.getAttribute('data-provenance-excluded') ?? null, step: section.getAttribute('data-provenance-step') }; })()`);
const displayed = () => evaluate<{ attempts: number; html: string; text: string }>(`(() => ({ attempts: document.querySelectorAll('.continuation-attempts button').length, html: document.body.innerHTML, text: document.body.textContent || '' }))()`);
const mentions = (html: string, ids: string[]) => ids.filter(id => html.includes(id) || html.includes(id.slice(0, 8)));

async function selectChainEnd(item: typeof B) {
  await evaluate(`(() => { const all = document.querySelectorAll('.continuation-attempts button'); const b = all[all.length - 1]; if (b) b.click(); return true; })()`); await settle(300);
  await evaluate(`(() => { const all = document.querySelectorAll('ol.continuation-steps button'); const b = all[all.length - 1]; if (b) b.click(); return true; })()`); await settle(400);
}
async function inspectPrefix(item: typeof B, selectedStep?: number) {
  const attempt = item.history.attempts.at(-1)!.record;
  const steps = attempt.checking.status === 'captured' ? attempt.checking.steps.length : 0;
  const step = selectedStep ?? steps - 1;
  const expected = expectedAttributes(occurrenceProvenance(item.history, attempt.captureId, step));
  const rendered = await renderedAttributes();
  return { match: canonical(rendered as unknown as JsonValue) === canonical(expected as unknown as JsonValue), attempt: item.history.attempts.length, step: step + 1 };
}
async function assertOnlyAccepted(label: string, accepted: typeof B, superseded: typeof A, selectedStep?: number) {
  const view = await displayed();
  const acceptedMentions = mentions(view.html, accepted.ids), supersededMentions = mentions(view.html, superseded.ids.filter(id => !accepted.ids.includes(id)));
  const panel = await inspectPrefix(accepted, selectedStep);
  const entry = { label, attempts: view.attempts, acceptedAttempts: accepted.decompositions.length, acceptedIdsShown: acceptedMentions.length, supersededIdsShown: supersededMentions.length, panelMatchesModule: panel.match, panelAttempt: panel.attempt, panelStep: panel.step, hostMessages: (await hostMessages()).length, bodySha256: sha((await displayed()).html) };
  (report.scenarios as unknown[]).push(entry);
  assert.equal(view.attempts, accepted.decompositions.length, `${label}: displayed attempts`);
  assert.equal(supersededMentions.length, 0, `${label}: superseded identities visible ${JSON.stringify(supersededMentions)}`);
  assert.ok(acceptedMentions.length > 0, `${label}: accepted identities visible`);
  assert.ok(panel.match, `${label}: panel differs from the module`);
  return entry;
}

// Scenario 1, overlapping: both requests announced before any result; the superseded result arrives first, then late again, then an obsolete status.
await post(status('12')); await post(status('13'));
await post(result('12', A), 800);
const afterLateA = await displayed();
assert.equal(afterLateA.attempts, 0, 'the superseded result fills nothing while the accepted request is pending');
assert.ok(await evaluate<boolean>(`[...document.querySelectorAll('button.toolbar-button')].find(b => b.textContent === 'Source data')?.disabled === true`), 'superseded result cannot enable the unopened source drawer');
await post(result('13', B), 800);
assert.ok(await evaluate<boolean>(`(() => { const b = [...document.querySelectorAll('button.toolbar-button')].find(b => b.textContent === 'Source data'); if (!b || b.disabled) return false; b.click(); return true; })()`), 'accepted result enables Source data');
await settle(400);
await selectChainEnd(B);
const overlap = await assertOnlyAccepted('overlapping: status 12, status 13, result 12 (superseded), result 13 (accepted)', B, A);
// Leave the reader on an earlier step. The late-message assertion must observe
// the untouched selection; selecting the chain end inside it would conceal a reset.
await evaluate(`document.querySelectorAll('ol.continuation-steps button')[2].click(); true`); await settle(400);
const earlier = await assertOnlyAccepted('accepted history, earlier step selected', B, A, 2);
await post(result('12', A), 800);
await post(status('12'), 800);
const afterNoise = await assertOnlyAccepted('overlapping: late duplicate of result 12 and an obsolete analyzing status 12 afterwards', B, A, 2);
assert.equal(afterNoise.bodySha256, earlier.bodySha256, 'late noise changed the displayed document or selection');
// Saved snapshot: the page's own Save button; the Blob bytes equal the accepted history's saved record and name nothing superseded.
await evaluate(`(() => { const b = [...document.querySelectorAll('button')].find(b => b.textContent === 'Save source snapshot'); if (!b) return false; b.click(); return true; })()`); await settle(800);
const saved = await evaluate<string[]>('window.__saved');
assert.equal(saved.length, 1, 'exactly one snapshot was saved');
const expectedSaved = savedSourceSnapshot(B.snapshot, B.origin, B.occurrence, undefined, undefined, B.decompositions, undefined);
const savedMatches = canonical(JSON.parse(saved[0]) as JsonValue) === canonical(expectedSaved as unknown as JsonValue);
report.saved = { bytes: saved[0].length, sha256: sha(saved[0]), matchesAcceptedRecord: savedMatches, supersededIdsInSaved: mentions(saved[0], supersededOnlyIds).length, acceptedIdsInSaved: mentions(saved[0], B.ids).length, version: JSON.parse(saved[0]).version };
assert.ok(savedMatches, 'saved snapshot differs from the accepted history');
assert.equal(mentions(saved[0], supersededOnlyIds).length, 0, 'saved snapshot names superseded-only identities');
// Scenario 2, sequential: the first result was displayed, then superseded on the same buffer version; a late duplicate of the first is discarded.
await post(status('14')); await post(result('14', A), 800);
const shownA = await displayed(); assert.equal(shownA.attempts, A.decompositions.length, 'the first result of the sequential pair is displayed before it is superseded');
await post(status('15')); await post(result('15', B), 800); await selectChainEnd(B);
const beforeSequentialNoise = (await displayed()).html;
await post(result('14', A), 800);
assert.equal((await displayed()).html, beforeSequentialNoise, 'sequential late result changed the untouched reader');
await assertOnlyAccepted('sequential: status 14, result 14 (displayed), status 15, result 15 (accepted), late duplicate of result 14', B, A);
assert.deepEqual((await hostMessages()).map(message => message.type), ['statementlens.ready'], 'no host message beyond the initial ready');
await mkdir(out, { recursive: true });
const shot = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
await writeFile(path.join(out, 'final-state.png'), Buffer.from(shot.data, 'base64'));
await writeFile(path.join(out, 'saved-snapshot.json'), saved[0]);
report.finishedAt = new Date().toISOString();
assert.equal(consoleErrors.length, 0, 'browser console remains clean');
report.status = consoleErrors.length === 0 ? 'webview race control passed: only the accepted result is displayed, compared with the module, and saved; late duplicates and obsolete statuses change nothing and post nothing' : 'webview race control passed with console output recorded';
console.log(JSON.stringify({ status: report.status, scenarios: (report.scenarios as unknown[]).length, saved: report.saved, consoleErrors: consoleErrors.length }));
} catch (error) {
  report.status = 'failed'; report.error = error instanceof Error ? error.stack : String(error);
  process.exitCode = 1;
  console.error(report.error);
  await captureFailure?.().catch(error => { report.failureCaptureError = String(error); });
} finally {
  report.finishedAt = new Date().toISOString();
  await mkdir(out, { recursive: true });
  await writeFile(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  closeSocket?.();
  if (browserProcess && browserProcess.exitCode === null && browserProcess.signalCode === null) {
    const stopped = new Promise<void>(resolve => { browserProcess!.once('exit', () => resolve()); setTimeout(resolve, 3000); });
    browserProcess.kill(); await stopped;
  }
  server.close();
  if (browserProfile) await rm(browserProfile, { recursive: true, force: true }).catch(() => undefined);
}
