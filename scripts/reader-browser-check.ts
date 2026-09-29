/** RC4 browser evidence: drive the production build in headless Chrome over
 * the DevTools protocol with no extra dependency. An injected host spy records
 * every outgoing host message; a real corpus chain is posted as the editor
 * would; attempt, step, term/type and disclosure interactions run by click and
 * by keyboard; the panel's data attributes are compared with the accepted
 * module in Node; layouts are checked at three widths with screenshots.
 * Writes a report and screenshots to DEFINOGRAPH_BROWSER_EVIDENCE_OUT.
 * DEFINOGRAPH_BROWSER_ONLY=M2 runs only the short-name visibility controls;
 * DEFINOGRAPH_DIST can select a retained production build. */
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { validateDecompositionHistory, validateSourceDecomposition } from '../src/editor/source-decomposition.js';
import { occurrenceProvenance, type OccurrenceProvenance } from '../src/editor/source-provenance.js';
import { supplierReading, type SupplierReading } from '../src/editor/source-supplier.js';
import { GUIDED_CONTEXT_CONTRACT } from '../src/editor/guided-context-contract.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const dist = process.env.DEFINOGRAPH_DIST ?? path.join(root, 'dist');
const only = process.env.DEFINOGRAPH_BROWSER_ONLY;
assert.ok(only === undefined || only === 'M2', 'DEFINOGRAPH_BROWSER_ONLY supports only M2.');
const m2Only = only === 'M2';
const chrome = process.env.DEFINOGRAPH_CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const corpusPath = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES ?? '/private/tmp/definograph-logical-editor-captures.json';
const out = process.env.DEFINOGRAPH_BROWSER_EVIDENCE_OUT;
assert.ok(out, 'Set DEFINOGRAPH_BROWSER_EVIDENCE_OUT to a directory outside the repository.');
const { canonical } = createExactJsonTools();
const report: Record<string, unknown> = { startedAt: new Date().toISOString(), scope: m2Only ? 'M2 only' : 'full', dist, chrome: null, corpus: corpusPath, interactions: [], layouts: [], consoleErrors: [], differential: [] };

const types: Record<string, string> = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.svg': 'image/svg+xml', '.json': 'application/json', '.woff2': 'font/woff2', '.woff': 'font/woff', '.png': 'image/png' };
const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? '/', 'http://127.0.0.1');
  const file = path.join(dist, url.pathname === '/' ? 'index.html' : url.pathname);
  try { const body = await readFile(file); response.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream' }); response.end(body); }
  catch { response.writeHead(404); response.end(); }
});
await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
const address = server.address(); assert.ok(address && typeof address === 'object');
const pageUrl = `http://127.0.0.1:${address.port}/`;
const profile = await mkdtemp(path.join(os.tmpdir(), 'definograph-chrome-'));
const browser = spawn(chrome, ['--headless=new', '--disable-gpu', '--no-first-run', '--no-default-browser-check', `--user-data-dir=${profile}`, '--remote-debugging-port=0', '--window-size=1280,900', 'about:blank'], { stdio: ['ignore', 'pipe', 'pipe'] });
const wsUrl = await new Promise<string>((resolve, reject) => {
  let text = ''; const timer = setTimeout(() => reject(new Error('Chrome did not expose DevTools')), 20000);
  browser.stderr.on('data', chunk => { text += String(chunk); const match = text.match(/DevTools listening on (ws:\/\/\S+)/); if (match) { clearTimeout(timer); resolve(match[1]); } });
  browser.on('exit', code => reject(new Error(`Chrome exited ${code}`)));
});
report.chrome = wsUrl.replace(/ws:\/\/[^/]+/, 'ws://…');

// Minimal DevTools protocol client on Node's built-in WebSocket.
const socket = new WebSocket(wsUrl);
await new Promise<void>((resolve, reject) => { socket.addEventListener('open', () => resolve()); socket.addEventListener('error', () => reject(new Error('DevTools socket failed'))); });
let nextId = 1;
const pending = new Map<number, { resolve: (value: unknown) => void; reject: (error: Error) => void }>();
const listeners: ((method: string, params: Record<string, unknown>, sessionId?: string) => void)[] = [];
socket.addEventListener('message', event => {
  const message = JSON.parse(String(event.data)) as { id?: number; method?: string; params?: Record<string, unknown>; sessionId?: string; result?: unknown; error?: { message: string } };
  if (message.id !== undefined) { const waiter = pending.get(message.id); pending.delete(message.id); if (!waiter) return; message.error ? waiter.reject(new Error(message.error.message)) : waiter.resolve(message.result); }
  else if (message.method) for (const listener of listeners) listener(message.method, message.params ?? {}, message.sessionId);
});
function send<T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}, sessionId?: string): Promise<T> {
  const id = nextId++;
  socket.send(JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) }));
  return new Promise((resolve, reject) => pending.set(id, { resolve: value => resolve(value as T), reject }));
}
const waitFor = (predicate: (method: string, params: Record<string, unknown>) => boolean, timeoutMs = 15000) => new Promise<void>((resolve, reject) => {
  const timer = setTimeout(() => reject(new Error('timed out waiting for browser event')), timeoutMs);
  listeners.push((method, params) => { if (predicate(method, params)) { clearTimeout(timer); resolve(); } });
});
const { targetId } = await send<{ targetId: string }>('Target.createTarget', { url: 'about:blank' });
const { sessionId } = await send<{ sessionId: string }>('Target.attachToTarget', { targetId, flatten: true });
const page = <T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}) => send<T>(method, params, sessionId);
await page('Page.enable'); await page('Runtime.enable'); await page('Log.enable');
const consoleErrors: string[] = [];
listeners.push((method, params) => {
  if (method === 'Runtime.exceptionThrown') consoleErrors.push(`exception: ${JSON.stringify(params.exceptionDetails).slice(0, 300)}`);
  if (method === 'Runtime.consoleAPICalled' && (params.type === 'error' || params.type === 'warning')) consoleErrors.push(`${params.type}: ${JSON.stringify((params.args as unknown[]).map(a => (a as { value?: unknown; description?: string }).value ?? (a as { description?: string }).description)).slice(0, 300)}`);
  if (method === 'Log.entryAdded' && ((params.entry as { level: string }).level === 'error' || (params.entry as { level: string }).level === 'warning')) consoleErrors.push(`log: ${JSON.stringify(params.entry).slice(0, 300)}`);
});
// Host spy: the page believes it runs inside the editor webview; every outgoing message is recorded.
await page('Page.addScriptToEvaluateOnNewDocument', { source: `window.__hostMessages = []; window.acquireVsCodeApi = () => ({ postMessage: message => { window.__hostMessages.push(JSON.parse(JSON.stringify(message))); } });` });
async function evaluate<T>(expression: string): Promise<T> {
  const result = await page<{ result: { value: T }; exceptionDetails?: unknown }>('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
  if (result.exceptionDetails) throw new Error(`page evaluation failed: ${JSON.stringify(result.exceptionDetails).slice(0, 400)}`);
  return result.result.value;
}
const settle = (ms = 250) => new Promise(resolve => setTimeout(resolve, ms));
const hostMessages = () => evaluate<{ type: string }[]>('window.__hostMessages');

async function setWidth(width: number) { await page('Emulation.setDeviceMetricsOverride', { width, height: 900, deviceScaleFactor: 1, mobile: width < 700 }); await settle(300); }
await setWidth(1272);
const loaded = waitFor(method => method === 'Page.loadEventFired');
await page('Page.navigate', { url: pageUrl }); await loaded; await settle(600);
assert.deepEqual((await hostMessages()).map(message => message.type), ['statementlens.ready'], 'the page announces itself once');

// A real corpus chain, posted as the editor would: status analyzing, then the result carrying the source attachment.
const rows = JSON.parse(await readFile(corpusPath, 'utf8')) as any[];
const row = rows.filter(row => row.label === 'literal Rotor law').at(-1);
assert.ok(row, 'corpus row');
const origin = row.parent.origin;
const document = { ...origin.document, fileName: new URL(origin.document.uri).pathname, selection: origin.selection };
const decompositions = [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }];
const result = { type: 'statementlens.error', guidedContextContract: GUIDED_CONTEXT_CONTRACT, requestId: '4', document, message: 'Independent guided export unavailable.', sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: row.parent.occurrence, decompositions };
await evaluate(`window.postMessage(${JSON.stringify({ type: 'statementlens.status', requestId: '4', phase: 'analyzing', document })}, '*'); true`);
await settle(200);
await evaluate(`window.postMessage(${JSON.stringify(result)}, '*'); true`);
await settle(800);
// Expected chains from the accepted module for every (attempt, step) the page can select.
const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null, attempts: row.priorAttempts.map((bundle: any) => ({ snapshot: bundle.snapshot, record: bundle.record })) });
const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, prior);
const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
const expectedAttributes = (provenance: OccurrenceProvenance) => {
  const origin = (item: { origin: any; receipts: any }) => ({ originKind: item.origin.kind, originCapture: item.origin.captureId, originStep: item.origin.kind === 'step' ? String(item.origin.stepIndex) : null, receiptCapture: item.receipts.captureId, receiptStart: String(item.receipts.start), receiptCount: String(item.receipts.count) });
  return { occurrences: provenance.occurrences.map(occurrence => ({ index: String(occurrence.index), ...origin(occurrence) })), edges: provenance.edges.map(edge => ({ edge: `${edge.from}-${edge.to}`, kind: edge.relation.kind, ...origin(edge) })), excluded: provenance.excluded ? provenance.excluded.stepIndices.join(',') : null, step: String(provenance.prefix.parentStepIndex) };
};
const renderedAttributes = () => evaluate<Record<string, unknown>>(`(() => { const section = document.querySelector('section.source-provenance[data-provenance-route]'); if (!section) return null;
  const pick = el => ({ originKind: el.getAttribute('data-origin-kind'), originCapture: el.getAttribute('data-origin-capture'), originStep: el.getAttribute('data-origin-step'), receiptCapture: el.getAttribute('data-receipt-capture'), receiptStart: el.getAttribute('data-receipt-start'), receiptCount: el.getAttribute('data-receipt-count') });
  return { occurrences: [...section.querySelectorAll('li[data-provenance-occurrence]')].map(el => ({ index: el.getAttribute('data-provenance-occurrence'), ...pick(el) })),
    edges: [...section.querySelectorAll('li[data-provenance-edge]')].map(el => ({ edge: el.getAttribute('data-provenance-edge'), kind: el.getAttribute('data-relation-kind'), ...pick(el) })),
    excluded: (section.parentElement?.querySelector('[data-provenance-excluded]') ?? section.querySelector('[data-provenance-excluded]'))?.getAttribute('data-provenance-excluded') ?? null, step: section.getAttribute('data-provenance-step') }; })()`);
const expectedSupply = (reading: SupplierReading) => ({
  links: reading.links.map(link => ({ edge: link.edge, status: link.status, from: link.from, to: link.to,
    restsOn: link.status === 'supplier' ? link.formation.judgements.filter(group => group.established).flatMap(group => group.receipts.filter(receipt => receipt.outcome === 'accepted').map(receipt => `${receipt.captureId}#${receipt.index}`)).join(',') : '',
    typing: [link.typing.captureId, link.typing.index, link.typing.outcome],
    home: link.conditions.home.map(entry => ({ position: entry.position, kind: entry.kind, origin: entry.origin.kind })),
    groups: link.formation.judgements.map((group, index) => ({ index, established: group.established,
      receipts: group.receipts.map(receipt => [receipt.captureId, receipt.index, receipt.outcome, receipt.alsoTyping]) })) })),
  parts: reading.parts.map(part => ({ occurrence: part.occurrence, root: part.root, tier: part.tier, path: JSON.stringify(part.path) })),
  sentences: reading.links.filter(link => link.status === 'supplier').length,
});
const renderedSupply = () => evaluate<Record<string, unknown>>(`(() => {
  const section = document.querySelector('section.source-supplier[data-supplier-route]'); if (!section) return null;
  const a = (el, key) => el.getAttribute('data-' + key), n = (el, key) => Number(a(el,key));
  return { links: [...section.querySelectorAll('[data-supplier-link]')].map(el => ({
    edge: n(el,'supplier-link'), status: a(el,'supplier-status'), from: n(el,'link-from'), to: n(el,'link-to'), restsOn: a(el,'supplier-rests-on'),
    typing: [a(el,'typing-capture'),n(el,'typing-index'),a(el,'typing-outcome')],
    home: [...el.querySelectorAll('[data-home-position]')].map(h => ({ position:n(h,'home-position'),kind:a(h,'home-kind'),origin:a(h,'home-origin') })),
    groups: [...el.querySelectorAll('[data-judgement]')].map(g => ({ index:n(g,'judgement'),established:a(g,'established')==='true',
      receipts:[...g.querySelectorAll('[data-formation-index]')].map(r => [a(r,'formation-capture'),n(r,'formation-index'),a(r,'formation-outcome'),a(r,'formation-also-typing')==='true']) })) })),
    parts: [...section.querySelectorAll('[data-supplier-part]')].map(p => ({ occurrence:n(p,'supplier-part'),root:n(p,'part-root'),tier:a(p,'part-tier'),path:a(p,'part-path') })),
    sentences: (document.body.innerText.match(/is read as supplying a proof of/g)||[]).length }; })()`);
async function checkSupply(selectedHistory: typeof history, capture: string, index: number) {
  const reading = supplierReading(selectedHistory, capture, index);
  assert.deepEqual(await renderedSupply(), expectedSupply(reading), 'supply panel agrees with the accepted module');
  const referencesResolve = await evaluate<{ outcomes: boolean; occurrences: boolean; axiomAdjacency: boolean }>(`(() => {
    const section = document.querySelector('section.source-supplier'); if (!section) return false;
    const cited = [...section.innerText.matchAll(/Outcome (\\d+)/g)].map(m => Number(m[1]));
    const links = [...section.querySelectorAll('[data-supplier-link]')];
    return {
      outcomes: cited.every(n => { const line = document.querySelector('[data-numbered-outcome="'+n+'"]'); return line && line.getClientRects().length > 0; }),
      occurrences: links.every(link => {
        const refs = [...link.querySelectorAll('[data-supplier-occurrence-reference]')];
        return refs.length === 2 && refs.every((ref, i) => {
          const index = link.getAttribute(i === 0 ? 'data-link-from' : 'data-link-to'), anchor = ref.querySelector('a');
          const target = anchor && document.getElementById(anchor.getAttribute('href').slice(1)), panel = target?.closest('section.source-provenance');
          return ref.getAttribute('data-supplier-occurrence-reference') === index && target?.getAttribute('data-provenance-occurrence') === index
            && panel?.getAttribute('data-provenance-prefix') === section.getAttribute('data-supplier-prefix')
            && panel?.getAttribute('data-provenance-step') === section.getAttribute('data-supplier-step')
            && [...document.querySelectorAll('[id]')].filter(el => el.id === target.id).length === 1;
        });
      }),
      axiomAdjacency: links.every(link => link.querySelector('[data-supplier-sentence]')?.nextElementSibling?.hasAttribute('data-supplier-axioms'))
    };
  })()`);
  assert.deepEqual(referencesResolve, { outcomes: true, occurrences: true, axiomAdjacency: true }, 'outcomes and same-prefix occurrence references resolve; axiom disclosure immediately follows each sentence');
}
/** Clip the whole provenance panel: the drawer is its own scroll container, so it is expanded only for the capture and restored afterwards. */
async function clipPanel(selector = 'section.source-provenance[data-provenance-route]'): Promise<string> {
  // The drawer is 100dvh tall; a tall emulated viewport lets the whole panel paint for the clip, then the viewport is restored.
  const width = await evaluate<number>('window.innerWidth');
  await page('Emulation.setDeviceMetricsOverride', { width, height: 6000, deviceScaleFactor: 1, mobile: width < 700 }); await settle(300);
  const box = await evaluate<{ x: number; y: number; width: number; height: number } | null>(`(() => { const d = document.querySelector('.atlas-drawer'); const s = document.querySelector(${JSON.stringify(selector)}); if (!d || !s) return null;
    d.setAttribute('data-capture-height', d.style.height); d.setAttribute('data-capture-overflow', d.style.overflow); d.style.height = 'auto'; d.style.overflow = 'visible'; document.body.style.overflow = 'visible';
    const r = s.getBoundingClientRect(); return { x: r.left + window.scrollX, y: r.top + window.scrollY, width: r.width, height: r.height }; })()`);
  if (!box) return '';
  const clip = await page<{ data: string }>('Page.captureScreenshot', { format: 'png', captureBeyondViewport: true, clip: { x: box.x, y: box.y, width: Math.ceil(box.width), height: Math.min(Math.ceil(box.height), 6000), scale: 1 } });
  await evaluate(`(() => { const d = document.querySelector('.atlas-drawer'); if (d) { d.style.height = d.getAttribute('data-capture-height') || ''; d.style.overflow = d.getAttribute('data-capture-overflow') || ''; } document.body.style.overflow = ''; return true; })()`);
  await page('Emulation.setDeviceMetricsOverride', { width, height: 900, deviceScaleFactor: 1, mobile: width < 700 }); await settle(200);
  return clip.data;
}
const clickText = (selector: string, text: string) => evaluate<boolean>(`(() => { const el = [...document.querySelectorAll(${JSON.stringify(selector)})].find(el => el.textContent && el.textContent.includes(${JSON.stringify(text)})); if (!el) return false; el.click(); return true; })()`);
const interactions = report.interactions as { action: string; hostMessagesAfter: number; ok: boolean; detail?: string }[];
async function act(action: string, fn: () => Promise<boolean>) {
  const ok = await fn(); await settle(300);
  const messages = await hostMessages();
  interactions.push({ action, ok, hostMessagesAfter: messages.length });
  assert.ok(ok, `interaction failed: ${action}`);
  assert.equal(messages.length, 1, `no host message may follow: ${action}`);
}
await act('open Source data drawer', () => clickText('button.toolbar-button', 'Source data'));
assert.ok(await evaluate<boolean>(`!!document.querySelector('section.source-decomposition')`), 'continuation history rendered');
await act('open attempts disclosure', () => evaluate<boolean>(`(() => { const s = [...document.querySelectorAll('details.snapshot-exact > summary')].find(s => s.textContent.includes('Earlier continuations')); if (!s) return false; s.click(); return true; })()`));
const differential = report.differential as { attempt: number; step: number; match: boolean }[];
async function checkCurrent(attemptIndex: number, stepIndex: number) {
  const rendered = await renderedAttributes();
  const attempt = history.attempts[attemptIndex].record;
  const expected = expectedAttributes(occurrenceProvenance(history, attempt.captureId, stepIndex));
  await checkSupply(history, attempt.captureId, stepIndex);
  const match = canonical(rendered as unknown as JsonValue) === canonical(expected as unknown as JsonValue);
  differential.push({ attempt: attemptIndex, step: stepIndex, match });
  assert.ok(match, `panel differs from the module at attempt ${attemptIndex + 1} step ${stepIndex + 1}`);
}
// Walk every attempt and every step by click; compare the panel against the module each time.
for (let attemptIndex = 0; !m2Only && attemptIndex < history.attempts.length; attemptIndex++) {
  await act(`select attempt ${attemptIndex + 1}`, () => evaluate<boolean>(`(() => { const b = document.querySelectorAll('.continuation-attempts button')[${attemptIndex}]; if (!b) return false; b.click(); return true; })()`));
  const attempt = history.attempts[attemptIndex].record;
  const steps = attempt.checking.status === 'captured' ? attempt.checking.steps.length : 0;
  for (let stepIndex = 0; stepIndex < steps; stepIndex++) {
    await act(`attempt ${attemptIndex + 1} step ${stepIndex + 1}`, () => evaluate<boolean>(`(() => { const b = document.querySelectorAll('ol.continuation-steps button')[${stepIndex}]; if (!b) return false; b.click(); return true; })()`));
    await checkCurrent(attemptIndex, stepIndex);
    if (stepIndex === steps - 1) {
      await act(`attempt ${attemptIndex + 1} type view`, () => clickText('div[role="tablist"][aria-label="Checked part target"] button', 'type'));
      assert.ok(await evaluate<boolean>(`(() => { const panel = document.querySelector('section.continuation-step div[role="tabpanel"]'); return !!panel && !panel.querySelector('[data-provenance-route]') && !/For every|Candidate|Role:/.test(panel.textContent || ''); })()`), 'type view carries no provenance chain');
      await act(`attempt ${attemptIndex + 1} term view`, () => evaluate<boolean>(`(() => { const b = document.querySelector('div[role="tablist"][aria-label="Checked part target"] button'); if (!b) return false; b.click(); return true; })()`));
      await act(`attempt ${attemptIndex + 1} open every disclosure`, () => evaluate<boolean>(`(() => { const all = [...document.querySelectorAll('section.source-provenance details')]; all.forEach(d => { d.open = true; d.dispatchEvent(new Event('toggle')); }); return all.length > 0; })()`));
    }
  }
}
await mkdir(out, { recursive: true });
const layouts = report.layouts as { width: number; innerWidth: number; scrollWidth: number; overflow: boolean; panelVisible: boolean; screenshot: string }[];
if (!m2Only) {
// Keyboard: focus the first step button by Tab traversal and press Enter to select it; no host message follows.
await evaluate(`(() => { const b = document.querySelectorAll('ol.continuation-steps button')[0]; b.focus(); return true; })()`);
await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Enter', code: 'Enter', text: '\r', unmodifiedText: '\r', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 }); await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
await settle(300);
const keyboardSelected = await evaluate<boolean>(`document.querySelectorAll('ol.continuation-steps button')[0].getAttribute('aria-pressed') === 'true'`);
interactions.push({ action: 'keyboard Enter selects step 1', ok: keyboardSelected, hostMessagesAfter: (await hostMessages()).length });
assert.ok(keyboardSelected, 'keyboard selection');
await checkCurrent(history.attempts.length - 1, 0);
await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9, nativeVirtualKeyCode: 9 }); await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9, nativeVirtualKeyCode: 9 }); await settle(200);
const tabbed = await evaluate<string>(`document.activeElement ? document.activeElement.tagName + ':' + (document.activeElement.textContent || '').slice(0, 40) : ''`);
interactions.push({ action: 'keyboard Tab moves focus', ok: tabbed.startsWith('BUTTON'), hostMessagesAfter: (await hostMessages()).length, detail: tabbed });
// Layouts: no horizontal document overflow at desktop, medium and narrow widths, with screenshots of the chain end (the informative view).
await act('reselect the chain end for the screenshots', () => evaluate<boolean>(`(() => { const all = document.querySelectorAll('ol.continuation-steps button'); const b = all[all.length - 1]; if (!b) return false; b.click(); return true; })()`));
const lastChecking = history.attempts.at(-1)!.record.checking;
await checkCurrent(history.attempts.length - 1, (lastChecking.status === 'captured' ? lastChecking.steps.length : 1) - 1);
for (const width of [1272, 600, 400]) {
  await setWidth(width);
  const metrics = await evaluate<{ innerWidth: number; scrollWidth: number; panel: boolean }>(`({ innerWidth: window.innerWidth, scrollWidth: document.documentElement.scrollWidth, panel: !!document.querySelector('section.source-provenance[data-provenance-route]') })`);
  // Bring the provenance panel into view for the viewport screenshot, then clip the panel itself for the reading review.
  await evaluate(`(() => { const s = document.querySelector('section.source-provenance[data-provenance-route]'); if (s) s.scrollIntoView({ block: 'start' }); return true; })()`); await settle(300);
  const shot = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
  const file = `reader-${width}.png`; await writeFile(path.join(out, file), Buffer.from(shot.data, 'base64'));
  const box = await evaluate<{ x: number; y: number; width: number; height: number } | null>(`(() => { const s = document.querySelector('section.source-provenance[data-provenance-route]'); if (!s) return null; const r = s.getBoundingClientRect(); return { x: r.left + window.scrollX, y: r.top + window.scrollY, width: r.width, height: r.height }; })()`);
  if (box) await writeFile(path.join(out, `panel-${width}.png`), Buffer.from(await clipPanel(), 'base64'));
  await writeFile(path.join(out, `supply-${width}.png`), Buffer.from(await clipPanel('section.source-supplier[data-supplier-route]'), 'base64'));
  layouts.push({ width, innerWidth: metrics.innerWidth, scrollWidth: metrics.scrollWidth, overflow: metrics.scrollWidth > metrics.innerWidth, panelVisible: metrics.panel, screenshot: file });
}
}
// Reading phase: every chain end of the corpus, posted as a fresh editor session; panel and step text plus a panel screenshot retained for the reading review.
await setWidth(1272);
await mkdir(path.join(out, 'reading'), { recursive: true });
const readings = report.readings = [] as { label: string; requestId: string; differentialMatch: boolean; hostMessagesAfter: number; text: string; screenshot: string }[];
const chainEnds = rows.filter((candidate, index) => rows[index + 1]?.label !== candidate.label);
let requestId = 5;
for (const end of m2Only ? [] : chainEnds) {
  const id = String(requestId++);
  const endOrigin = end.parent.origin, endDocument = { ...endOrigin.document, fileName: new URL(endOrigin.document.uri).pathname, selection: endOrigin.selection };
  const endDecompositions = [...end.priorAttempts, { snapshot: end.response.sourceSnapshot, origin: end.response.sourceSnapshotOrigin, record: end.response.sourceDecomposition }];
  await evaluate(`window.postMessage(${JSON.stringify({ type: 'statementlens.status', requestId: id, phase: 'analyzing', document: endDocument })}, '*'); true`); await settle(200);
  await evaluate(`window.postMessage(${JSON.stringify({ type: 'statementlens.error', guidedContextContract: GUIDED_CONTEXT_CONTRACT, requestId: id, document: endDocument, message: 'Independent guided export unavailable.', sourceSnapshot: end.parent.snapshot, sourceSnapshotOrigin: endOrigin, sourceOccurrence: end.parent.occurrence, decompositions: endDecompositions })}, '*'); true`); await settle(800);
  const opened = await evaluate<boolean>(`(() => { if (document.querySelector('section.source-provenance[data-provenance-route]')) return true; const b = [...document.querySelectorAll('button.toolbar-button')].find(el => el.textContent && el.textContent.includes('Source data')); if (!b) return false; b.click(); return true; })()`);
  await settle(500);
  const endPrior = validateDecompositionHistory({ snapshot: end.parent.snapshot, occurrence: end.parent.occurrence, seed: null, attempts: end.priorAttempts.map((bundle: any) => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const endRecord = validateSourceDecomposition(end.response.sourceDecomposition, end.response.sourceSnapshot, endPrior);
  const endHistory = validateDecompositionHistory({ ...endPrior, attempts: [...endPrior.attempts, { snapshot: end.response.sourceSnapshot, record: endRecord }] });
  const rendered = await renderedAttributes();
  const match = opened && canonical(rendered as unknown as JsonValue) === canonical(expectedAttributes(occurrenceProvenance(endHistory, endRecord.captureId, endRecord.operations.length - 1)) as unknown as JsonValue);
  await checkSupply(endHistory, endRecord.captureId, endRecord.operations.length - 1);
  const text = await evaluate<string>(`(() => { const step = document.querySelector('section.continuation-step'); const panel = document.querySelector('section.source-provenance[data-provenance-route]'); const supply = document.querySelector('section.source-supplier'); return [step ? step.innerText : '(no step)', '', '----- ordered provenance -----', '', panel ? panel.innerText : '(no panel)', '', '----- supply reading -----', '', supply ? supply.innerText : '(no supply panel)'].join('\\n'); })()`);
  const slug = end.label.replace(/[^a-z0-9]+/gi, '-').toLowerCase();
  await writeFile(path.join(out, 'reading', `${slug}.txt`), text + '\n');
  await evaluate(`(() => { const s = document.querySelector('section.source-provenance[data-provenance-route]'); if (s) s.scrollIntoView({ block: 'start' }); return true; })()`); await settle(200);
  const shot = await clipPanel(); if (shot) await writeFile(path.join(out, 'reading', `${slug}.png`), Buffer.from(shot, 'base64'));
  const supplyShot = await clipPanel('section.source-supplier[data-supplier-route]'); if (supplyShot) await writeFile(path.join(out, 'reading', `${slug}-supply.png`), Buffer.from(supplyShot, 'base64'));
  readings.push({ label: end.label, requestId: id, differentialMatch: match, hostMessagesAfter: (await hostMessages()).length, text: `reading/${slug}.txt`, screenshot: `reading/${slug}.png` });
  assert.ok(match, `reading phase panel differs from the module for ${end.label}`);
}
// Real DOM clicks exercise the four-key transport on original, derived and seed
// pairs. These clicks use the host spy, so they make no native-process claim.
const actionClicks = report.actionClicks = [] as { label: string; message: unknown }[];
async function postCapture(capture: any, seedOnly = false) {
  const id = String(requestId++), capturedOrigin = capture.parent.origin;
  const capturedDocument = { ...capturedOrigin.document, fileName: new URL(capturedOrigin.document.uri).pathname, selection: capturedOrigin.selection };
  const payload = { type: 'statementlens.error', guidedContextContract: GUIDED_CONTEXT_CONTRACT, requestId: id, document: capturedDocument,
    message: 'Independent guided export unavailable.', sourceSnapshot: capture.parent.snapshot, sourceSnapshotOrigin: capturedOrigin,
    sourceOccurrence: capture.parent.occurrence, ...(capture.seed ? { headExposure: capture.seed } : {}),
    ...(!seedOnly ? { decompositions: [...capture.priorAttempts, { snapshot: capture.response.sourceSnapshot, origin: capture.response.sourceSnapshotOrigin, record: capture.response.sourceDecomposition }] } : {}) };
  await evaluate(`window.postMessage(${JSON.stringify({ type: 'statementlens.status', requestId: id, phase: 'analyzing', document: capturedDocument })}, '*'); true`); await settle(100);
  await evaluate(`window.postMessage(${JSON.stringify(payload)}, '*'); true`); await settle(600);
  if (!await evaluate<boolean>(`!!document.querySelector('section.source-snapshot')`)) { assert.ok(await clickText('button.toolbar-button', 'Source data')); await settle(300); }
  return { payload, capturedDocument };
}
async function clickAction(label: string, expected: Record<string, unknown>, selector = 'section.source-snapshot button') {
  const before = (await hostMessages()).length;
  assert.ok(await clickText(selector, label), `action button exists: ${label}`); await settle(250);
  const sent = (await hostMessages()).slice(before);
  assert.equal(sent.length, 1, `one message for ${label}`);
  assert.deepEqual(Object.keys(sent[0]).sort(), ['parentCaptureId', 'parentStepIndex', 'previousCaptureId', 'type']);
  assert.deepEqual(sent[0], expected, `exact request for ${label}`);
  actionClicks.push({ label, message: sent[0] });
}
// Both real corpora, every eligible step of every fresh record, on a narrow
// whole page. No derived fixture truncation stands in for selecting a prefix.
const allPrefixChecks = report.allPrefixChecks = [] as { corpus: string; label: string; step: number; links: number; supplySentences: number }[];
const acceptancePath = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
assert.ok(acceptancePath, 'Set DEFINOGRAPH_ACCEPTANCE_FIXTURES for the whole-page acceptance controls.');
const acceptanceRows = JSON.parse(await readFile(acceptancePath, 'utf8'));
await setWidth(400);
if (!m2Only) for (const [corpus, corpusRows] of [['logical', rows], ['acceptance', acceptanceRows]] as const) for (const captured of corpusRows) {
  const capturedPrior = validateDecompositionHistory({ snapshot: captured.parent.snapshot, occurrence: captured.parent.occurrence, seed: captured.seed ?? null,
    attempts: captured.priorAttempts.map((bundle: any) => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const capturedRecord = validateSourceDecomposition(captured.response.sourceDecomposition, captured.response.sourceSnapshot, capturedPrior);
  const capturedHistory = validateDecompositionHistory({ ...capturedPrior, attempts: [...capturedPrior.attempts, { snapshot: captured.response.sourceSnapshot, record: capturedRecord }] });
  if (capturedRecord.checking.status !== 'captured') continue;
  await postCapture(captured);
  for (const step of capturedRecord.checking.steps) {
    if (step.output.status !== 'candidate' || step.output.checking.status !== 'completed' || (step.replay !== 'new' && step.replay !== 'matched')) continue;
    assert.ok(await evaluate<boolean>(`(() => { const button = document.querySelectorAll('ol.continuation-steps button')[${step.index}]; if (!button) return false; button.click(); return true; })()`));
    await settle(35);
    await checkSupply(capturedHistory, capturedRecord.captureId, step.index);
    const reading = supplierReading(capturedHistory, capturedRecord.captureId, step.index);
    const pageLimits = await evaluate<{ stray: number; overflow: boolean }>(`(() => ({
      stray: [...document.querySelectorAll('section.source-provenance,.occurrence-guided-target,[data-supplier-part]')].reduce((n,el) => n + (el.innerText.match(/is read as supplying a proof of/g)||[]).length,0),
      overflow: document.documentElement.scrollWidth > window.innerWidth
    }))()`);
    assert.equal(pageLimits.stray, 0, 'the supply phrase belongs only to supply link blocks');
    assert.equal(pageLimits.overflow, false, 'the whole page fits the narrow viewport');
    allPrefixChecks.push({ corpus, label: captured.label, step: step.index, links: reading.links.length, supplySentences: reading.links.filter(link => link.status === 'supplier').length });
  }
}
assert.equal((await hostMessages()).length, 1, 'all-prefix navigation sends no host request');
// F1/F3/M2: retained real captures in ordinary 900px drawer viewports. These
// presentation checks neither manufacture source data nor request host work.
const presentationChecks = report.presentationChecks = [] as Record<string, unknown>[];
const presentationState = () => evaluate(`(() => ({
  capture: document.querySelector('[data-decomposition-capture]')?.getAttribute('data-decomposition-capture'),
  step: document.querySelector('section.continuation-step')?.getAttribute('data-decomposition-step'),
  attempts: [...document.querySelectorAll('.continuation-attempts button')].map(el => el.getAttribute('aria-pressed')),
  steps: [...document.querySelectorAll('ol.continuation-steps button')].map(el => el.getAttribute('aria-pressed')),
  targets: [...document.querySelectorAll('[aria-label="Checked part target"] button')].map(el => el.getAttribute('aria-selected')),
  prefixes: ['provenance','supplier'].map(kind => { const section = document.querySelector('section.source-' + kind + '[data-' + kind + '-route]'); return ['route','prefix','step'].map(key => section?.getAttribute('data-' + kind + '-' + key)); }),
  hash: location.hash, messages: window.__hostMessages
}))()`);
async function presentationShot(name: string) {
  const shot = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
  await writeFile(path.join(out!, name), Buffer.from(shot.data, 'base64'));
  return name;
}
async function presentationEnd(captured: any) {
  const prior = validateDecompositionHistory({ snapshot: captured.parent.snapshot, occurrence: captured.parent.occurrence, seed: captured.seed ?? null,
    attempts: captured.priorAttempts.map((bundle: any) => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const record = validateSourceDecomposition(captured.response.sourceDecomposition, captured.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: captured.response.sourceSnapshot, record }] });
  const step = record.operations.length - 1;
  await postCapture(captured);
  assert.deepEqual(await evaluate(`({ capture: document.querySelector('[data-decomposition-capture]')?.getAttribute('data-decomposition-capture'), step: document.querySelector('section.continuation-step')?.getAttribute('data-decomposition-step') })`),
    { capture: record.captureId, step: String(step) }, 'presentation fixture selects its exact final capture and step');
  await checkSupply(history, record.captureId, step);
  const reading = supplierReading(history, record.captureId, step);
  assert.deepEqual(await renderedAttributes(), expectedAttributes(reading.provenance));
  return reading;
}
const sorriedPresentation = acceptanceRows.filter((candidate: any) => candidate.label === 'term using a lemma proved with a placeholder').at(-1);
const negatedPresentation = rows.filter(candidate => candidate.label === 'negated owner').at(-1);
assert.ok(sorriedPresentation && negatedPresentation, 'real sorried-lemma and negated-owner final rows are required');
for (const width of [1272, 400]) {
  await setWidth(width);
  for (const [fixture, captured, axiom] of [['sorried', sorriedPresentation, 'sorryAx'], ['negated', negatedPresentation, 'none recorded']] as const) {
    if (m2Only && fixture !== 'sorried') continue;
    const reading = await presentationEnd(captured), before = await presentationState();
    if (!m2Only) {
    const link = reading.links.find(item => item.status === 'supplier');
    assert.ok(link, `${fixture}: nonvacuous supply link`);
    assert.deepEqual(link.typing.audit, { tag: 'available', axioms: axiom === 'sorryAx' ? [['str', ['anonymous'], 'sorryAx']] : [] }, 'fixture retains the actual typing audit');
    const linkSelector = `section.source-supplier[data-supplier-route] [data-supplier-link="${link.edge}"]`;
    assert.ok(await evaluate(`(() => { const sentence = document.querySelector(${JSON.stringify(linkSelector)})?.querySelector('[data-supplier-sentence]'); if (!sentence) return false; sentence.scrollIntoView({ block: 'center' }); return true; })()`));
    await settle();
    const axiomLayout = await evaluate<any>(`(() => {
      const link = document.querySelector(${JSON.stringify(linkSelector)}), sentence = link.querySelector('[data-supplier-sentence]'), axiom = link.querySelector('[data-supplier-axioms]');
      const drawer = document.querySelector('dialog.atlas-drawer[open]'), header = drawer.querySelector('.drawer-heading');
      const s = sentence.getBoundingClientRect(), a = axiom.getBoundingClientRect(), d = drawer.getBoundingClientRect(), h = header.getBoundingClientRect();
      const normal = getComputedStyle(document.querySelector('[data-supplier-environment]')), ss = getComputedStyle(sentence), as = getComputedStyle(axiom);
      const visible = rect => rect.width > 0 && rect.height > 0 && rect.top >= Math.max(d.top, h.bottom) - 1 && rect.bottom <= Math.min(d.bottom, innerHeight) + 1 && rect.left >= d.left - 1 && rect.right <= d.right + 1;
      return { adjacent: sentence.nextElementSibling === axiom, sentenceVisible: visible(s), axiomVisible: visible(a), text: axiom.textContent,
        codes: [...axiom.querySelectorAll('code')].map(el => el.textContent), gap: a.top - s.bottom, maxGap: Math.max(24, parseFloat(ss.lineHeight)),
        neutral: as.color === normal.color && ss.color === normal.color && as.fontWeight === normal.fontWeight && as.backgroundColor === ss.backgroundColor && !axiom.closest('[role="alert"],.snapshot-unavailable'),
        color: as.color, background: as.backgroundColor, headerBottom: h.bottom, sentenceTop: s.top, axiomBottom: a.bottom, viewportBottom: Math.min(d.bottom, innerHeight) };
    })()`);
    assert.ok(axiomLayout.adjacent && axiomLayout.sentenceVisible && axiomLayout.axiomVisible, 'supply sentence and immediately following axiom disclosure are both visible below the sticky header');
    assert.ok(axiomLayout.gap >= -1 && axiomLayout.gap <= axiomLayout.maxGap && axiomLayout.neutral, 'axiom disclosure has ordinary neutral styling and close spacing');
    assert.equal(axiomLayout.text, `Recorded axioms of the typing declaration: ${axiom}.`);
    assert.deepEqual(axiomLayout.codes, axiom === 'sorryAx' ? ['sorryAx'] : []);
    assert.deepEqual(await presentationState(), before, 'axiom layout inspection changes no selection or host message');
    presentationChecks.push({ check: 'F1', fixture, width, source: 'retained real corpus', ...axiomLayout, screenshot: await presentationShot(`f1-${fixture}-${width}.png`) });
    }
    if (fixture === 'sorried') {
      // The guided stage and full reading are distinct routes. Closed details can still return positive geometry.
      const surface = 'section.continuation-step .occurrence-guided-target[data-occurrence-target="term"] > .statement-reading-view > .sr-atlas-layout > .sr-atlas-main > .sr-reading-surface';
      const disclosure = `${surface} > details.sr-complete-reading`, summary = `${disclosure} > summary`;
      const routes = { guided: `${surface} > .reading-guide > .rg-stage`, full: `${disclosure} > .sr-reading-content` };
      const nameIn = (route: keyof typeof routes) => `[...document.querySelectorAll(${JSON.stringify(routes[route] + ' .sr-binder-auxiliary > .sr-binder-name > strong')})].filter(el => el.textContent === '_example')`;
      const initialVisibility = await evaluate<any>(`(() => { const guided = ${nameIn('guided')}, full = ${nameIn('full')};
        return { guidedCount: guided.length, fullCount: full.length, disclosureOpen: document.querySelector(${JSON.stringify(disclosure)})?.open,
          guidedVisible: guided[0]?.checkVisibility({ contentVisibilityAuto: true, visibilityProperty: true, opacityProperty: true }),
          fullVisible: full[0]?.checkVisibility({ contentVisibilityAuto: true, visibilityProperty: true, opacityProperty: true }) }; })()`);
      assert.deepEqual(initialVisibility, { guidedCount: 1, fullCount: 1, disclosureOpen: false, guidedVisible: true, fullVisible: false }, 'the full-reading name is hidden until its disclosure opens, regardless of geometry');
      async function toggleFullReading(open: boolean) {
        assert.ok(await evaluate(`(() => { const summary = document.querySelector(${JSON.stringify(summary)}); if (!summary || summary.textContent !== 'Full visual reading') return false; summary.scrollIntoView({ block: 'center' }); return true; })()`));
        await settle();
        const pointer = await evaluate<any>(`(() => { const summary = document.querySelector(${JSON.stringify(summary)}), rect = summary.getBoundingClientRect();
          const drawer = summary.closest('dialog'), header = drawer.querySelector('.drawer-heading').getBoundingClientRect();
          const x = (rect.left + rect.right) / 2, y = (rect.top + rect.bottom) / 2;
          return { x, y, hit: summary.contains(document.elementFromPoint(x, y)), visible: summary.checkVisibility({ visibilityProperty: true, opacityProperty: true }) && y >= header.bottom && y <= Math.min(drawer.getBoundingClientRect().bottom, innerHeight) }; })()`);
        assert.ok(pointer.hit && pointer.visible, 'the full-reading summary receives normal pointer input below the sticky header');
        await page('Input.dispatchMouseEvent', { type: 'mousePressed', x: pointer.x, y: pointer.y, button: 'left', buttons: 1, clickCount: 1 });
        await page('Input.dispatchMouseEvent', { type: 'mouseReleased', x: pointer.x, y: pointer.y, button: 'left', clickCount: 1 });
        await settle();
        assert.equal(await evaluate(`document.querySelector(${JSON.stringify(disclosure)}).open`), open, 'normal disclosure click takes effect');
      }
      for (const route of ['guided', 'full'] as const) {
        if (route === 'full') await toggleFullReading(true);
        const selectedName = `(${nameIn(route)})[0]`;
        await evaluate(`${selectedName}.closest('.sr-binder-name').scrollIntoView({ block: 'center' }); true`);
        await settle();
        const nameLayout = await evaluate<any>(`(() => {
          const name = ${selectedName}, button = name.closest('.sr-binder-name'), drawer = name.closest('dialog');
          const ancestors = []; for (let el = name.parentElement; el; el = el.parentElement) if (el.tagName === 'DETAILS') ancestors.push({ className: el.className, open: el.open });
          const range = document.createRange(); range.selectNodeContents(name);
          const rects = [...range.getClientRects()].filter(rect => rect.width > 0 && rect.height > 0), n = name.getBoundingClientRect(), b = button.getBoundingClientRect(), d = drawer.getBoundingClientRect(), h = drawer.querySelector('.drawer-heading').getBoundingClientRect();
          const hit = document.elementFromPoint((n.left + n.right) / 2, (n.top + n.bottom) / 2);
          return { text: name.textContent, lines: new Set(rects.map(rect => Math.round(rect.top))).size, nameWidth: n.width, buttonWidth: b.width,
            ancestors, noClosedAncestor: ancestors.every(item => item.open), checkVisibility: name.checkVisibility({ contentVisibilityAuto: true, visibilityProperty: true, opacityProperty: true }),
            hitName: name.contains(hit), hitButton: button.contains(hit), nameInsideButton: n.left >= b.left - 1 && n.right <= b.right + 1,
            visible: n.width > 0 && n.height > 0 && n.top >= h.bottom - 1 && n.bottom <= Math.min(d.bottom, innerHeight) + 1 && n.left >= d.left - 1 && n.right <= d.right + 1,
            buttonOverflow: button.scrollWidth - button.clientWidth, drawerOverflow: drawer.scrollWidth - drawer.clientWidth, pageOverflow: document.documentElement.scrollWidth - innerWidth };
        })()`);
        assert.equal(nameLayout.text, '_example'); assert.equal(nameLayout.lines, 1, 'real short binder name fits on one line');
        assert.ok(nameLayout.noClosedAncestor && nameLayout.checkVisibility && nameLayout.hitName && nameLayout.hitButton, 'the measured binder is visible and receives pointer input');
        assert.ok(nameLayout.nameInsideButton && nameLayout.visible && nameLayout.buttonOverflow <= 1 && nameLayout.drawerOverflow <= 1 && nameLayout.pageOverflow <= 1, 'name, button, drawer and page fit without horizontal overflow');
        assert.deepEqual(await presentationState(), before, 'name layout inspection changes no selection or host message');
        presentationChecks.push({ check: 'M2', fixture, width, route, initialVisibility, source: 'retained real corpus', ...nameLayout, screenshot: await presentationShot(`m2-sorried-${width}-${route}.png`) });
      }
      await toggleFullReading(false);
      assert.deepEqual(await presentationState(), before, 'restoring the disclosure changes no selection or host message');
    } else {
      for (const endpoint of reading.links.flatMap(item => [item.from, item.to].map(index => ({ edge: item.edge, index })))) for (const input of ['mouse', 'Enter'] as const) {
        const selector = `section.source-supplier[data-supplier-route] [data-supplier-link="${endpoint.edge}"] [data-supplier-occurrence-reference="${endpoint.index}"] > a[href^="#"]`;
        assert.ok(await evaluate(`(() => { const anchor = document.querySelector(${JSON.stringify(selector)}); if (!anchor) return false; anchor.scrollIntoView({ block: 'center' }); return true; })()`));
        await settle();
        const anchor = await evaluate<any>(`(() => {
          const anchor = document.querySelector(${JSON.stringify(selector)}), drawer = document.querySelector('dialog.atlas-drawer[open]');
          const header = drawer.querySelector('.drawer-heading').getBoundingClientRect(), bottom = Math.min(drawer.getBoundingClientRect().bottom, innerHeight);
          const rect = [...anchor.getClientRects()].find(rect => rect.width > 0 && rect.top >= header.bottom && rect.bottom <= bottom);
          if (!rect) return null;
          const x = (rect.left + rect.right) / 2, y = (rect.top + rect.bottom) / 2;
          return { id: anchor.getAttribute('href').slice(1), x, y, hit: anchor.contains(document.elementFromPoint(x, y)) };
        })()`);
        assert.ok(anchor?.hit, 'reference receives actual pointer input below the header');
        if (input === 'mouse') {
          await page('Input.dispatchMouseEvent', { type: 'mousePressed', x: anchor.x, y: anchor.y, button: 'left', buttons: 1, clickCount: 1 });
          await page('Input.dispatchMouseEvent', { type: 'mouseReleased', x: anchor.x, y: anchor.y, button: 'left', clickCount: 1 });
        } else {
          assert.ok(await evaluate(`(() => { const anchor = document.querySelector(${JSON.stringify(selector)}); anchor.focus({ preventScroll: true }); return document.activeElement === anchor; })()`));
          await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Enter', code: 'Enter', text: '\r', unmodifiedText: '\r', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
          await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
        }
        await settle(300);
        const destination = await evaluate<any>(`(() => {
          const target = document.getElementById(${JSON.stringify(anchor.id)}), panel = target?.closest('section.source-provenance'), supply = document.querySelector('section.source-supplier[data-supplier-route]');
          const drawer = document.querySelector('dialog.atlas-drawer[open]'), header = drawer.querySelector('.drawer-heading').getBoundingClientRect(), heading = target?.querySelector(':scope > strong'), rect = heading?.getBoundingClientRect();
          const ids = [...document.querySelectorAll('[id]')].map(el => el.id), occurrences = [...panel.querySelectorAll('[data-provenance-occurrence]')];
          return { focused: document.activeElement === target, tabindex: target?.tabIndex, index: target?.getAttribute('data-provenance-occurrence'),
            samePrefix: ['route','prefix','step'].every(key => panel.getAttribute('data-provenance-' + key) === supply.getAttribute('data-supplier-' + key)),
            prefix: ['route','prefix','step'].map(key => panel.getAttribute('data-provenance-' + key)),
            uniqueIds: occurrences.every(el => el.id && ids.filter(id => id === el.id).length === 1),
            belowHeader: rect && target.getBoundingClientRect().top >= header.bottom - 1 && rect.top >= header.bottom - 1, visibleBottom: rect && rect.bottom <= Math.min(drawer.getBoundingClientRect().bottom, innerHeight) + 1,
            hit: rect && target.contains(document.elementFromPoint((rect.left + rect.right) / 2, (rect.top + rect.bottom) / 2)),
            headerBottom: header.bottom, targetTop: target?.getBoundingClientRect().top, headingTop: rect?.top, headingBottom: rect?.bottom, drawerScrollTop: drawer.scrollTop };
        })()`);
        assert.ok(destination.focused && destination.tabindex === -1 && destination.samePrefix && destination.uniqueIds, 'reference focuses its unique exact occurrence in the same prefix');
        assert.equal(destination.index, String(endpoint.index));
        assert.deepEqual(destination.prefix, [reading.provenance.prefix.route, reading.provenance.prefix.previousCaptureId, String(reading.provenance.prefix.parentStepIndex)], 'destination belongs to the exact accepted selected prefix');
        assert.ok(destination.belowHeader && destination.visibleBottom && destination.hit, 'referenced occurrence heading is visible below the sticky header');
        assert.deepEqual(await renderedAttributes(), expectedAttributes(reading.provenance), 'navigation retains the exact accepted occurrences and receipt identities');
        assert.deepEqual(await presentationState(), before, 'reference navigation changes neither selected capture/step nor host messages');
        presentationChecks.push({ check: 'F3', fixture, width, input, edge: endpoint.edge, occurrence: endpoint.index, ...destination,
          screenshot: await presentationShot(`f3-negated-${width}-${endpoint.edge}-${endpoint.index}-${input.toLowerCase()}.png`) });
      }
    }
  }
}
assert.equal((await hostMessages()).length, 1, 'F1/F3/M2 browser presentation checks send no host request');
report.presentationSummary = { F1: presentationChecks.filter(item => item.check === 'F1').length, F3: presentationChecks.filter(item => item.check === 'F3').length, M2: presentationChecks.filter(item => item.check === 'M2').length, widths: [1272, 400], source: 'retained real corpora; no synthetic controls' };
if (!m2Only) {
const actionRow = rows.find(candidate => candidate.label === 'literal Rotor law' && candidate.operation.kind === 'logical');
assert.ok(actionRow);
const actionSession = await postCapture(actionRow);
const originalBase = { parentCaptureId: actionRow.parent.origin.captureId, previousCaptureId: actionRow.parent.occurrence.captureId, parentStepIndex: 0 };
for (const tab of ['Selected term', 'Inferred type']) {
  assert.ok(await clickText('[aria-label="Occurrence reading target"] button', tab)); await settle();
  await clickAction('Inspect type of original selected term', { type: 'statementlens.inspectTypeComponent', ...originalBase });
  await clickAction('Read logical structure of original selected term (one layer)', { type: 'statementlens.inspectLogicalStructure', ...originalBase });
}
const currentRecord = actionRow.response.sourceDecomposition;
const derivedBase = { parentCaptureId: actionRow.parent.origin.captureId, previousCaptureId: currentRecord.captureId, parentStepIndex: currentRecord.operations.length - 1 };
await clickAction('Inspect type of this term', { type: 'statementlens.inspectTypeComponent', ...derivedBase }, 'section.continuation-step button');
await clickAction('Read logical structure of this term (one layer)', { type: 'statementlens.inspectLogicalStructure', ...derivedBase }, 'section.continuation-step button');
assert.ok(await clickText('[aria-label="Checked part target"] button', 'type')); await settle();
assert.ok(await evaluate<boolean>(`!Array.from(document.querySelectorAll('section.continuation-step button')).some(el => el.textContent.includes('Read logical structure'))`), 'logical action hidden on derived type tab');
await clickAction('Inspect type of this term', { type: 'statementlens.inspectTypeComponent', ...derivedBase }, 'section.continuation-step button');
const beforeBusy = (await hostMessages()).length;
await evaluate(`window.postMessage(${JSON.stringify({ type: 'statementlens.status', requestId: String(requestId++), phase: 'analyzing', document: actionSession.capturedDocument })}, '*'); true`); await settle(300);
assert.ok(await evaluate<boolean>(`!Array.from(document.querySelectorAll('section.source-snapshot button')).some(el => /Inspect type|Read logical structure/.test(el.textContent))`), 'inspection actions absent while busy');
assert.equal((await hostMessages()).length, beforeBusy, 'busy status causes no request');
const seedRows = JSON.parse(await readFile(process.env.DEFINOGRAPH_DECOMPOSITION_FIXTURES ?? '/private/tmp/definograph-decomposition-captures.json', 'utf8'));
const seedRow = seedRows.find((candidate: any) => candidate.seed?.record.checking.exposure?.status === 'candidate');
assert.ok(seedRow, 'a real seed-route capture is required');
await postCapture(seedRow, true);
const seedBase = { parentCaptureId: seedRow.parent.origin.captureId, previousCaptureId: seedRow.seed.record.captureId, parentStepIndex: 0 };
await clickAction('Inspect type of exposed term', { type: 'statementlens.inspectTypeComponent', ...seedBase });
await clickAction('Read logical structure of exposed term (one layer)', { type: 'statementlens.inspectLogicalStructure', ...seedBase });
const beforeSwitch = (await hostMessages()).length;
assert.ok(await clickText('[aria-label="Exposure comparison side"] button', 'Before exposure')); await settle();
assert.ok(await evaluate<boolean>(`!Array.from(document.querySelectorAll('section.source-head-exposure button')).some(el => /Inspect type|Read logical structure/.test(el.textContent))`), 'seed actions belong to after exposure');
assert.equal((await hostMessages()).length, beforeSwitch, 'comparison selection causes no request');
}
const finalMessages = await hostMessages();
report.hostMessages = finalMessages; report.consoleErrors = consoleErrors; report.finishedAt = new Date().toISOString();
report.summary = { scope: m2Only ? 'M2 only; prefix, reading, F1/F3 and action phases skipped' : 'full', M2: presentationChecks.filter(item => item.check === 'M2').length, interactions: interactions.length, allInteractionsOk: interactions.every(item => item.ok), hostMessagesTotal: finalMessages.length, differentialChecks: differential.length + readings.length, differentialAllMatch: differential.every(item => item.match) && readings.every(item => item.differentialMatch), overflowAtAnyWidth: layouts.some(item => item.overflow), consoleErrors: consoleErrors.length, chainEndsRead: readings.length };
await writeFile(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report.summary));
const exited = new Promise<void>(resolve => { browser.once('exit', () => resolve()); setTimeout(resolve, 10000); });
socket.close(); browser.kill('SIGTERM'); server.close(); await exited;
await rm(profile, { recursive: true, force: true }).catch(() => undefined);
assert.equal(finalMessages.length, 1 + actionClicks.length, 'only ready and the deliberately clicked actions left the page');
assert.equal(presentationChecks.filter(item => item.check === 'M2').length, 4, 'guided and full names are measured at both widths');
assert.ok(!layouts.some(item => item.overflow), 'no horizontal overflow');
assert.ok(differential.every(item => item.match), 'panel matched the module everywhere');
assert.ok(interactions.every(item => item.ok), 'every interaction succeeded');
