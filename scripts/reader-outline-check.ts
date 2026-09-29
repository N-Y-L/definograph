/** Selected-attempt section outline: drive a production build in headless Chrome over the DevTools
 * protocol with no extra dependency, as the other reader checks do. A host spy records outgoing
 * messages; retained real corpus rows arrive through the page's host message path. Real pointer and
 * keyboard input moves between the outline, its potential destinations and their return links. Each
 * check reads painted visibility below the sticky drawer heading (never the geometry of a closed
 * disclosure), keyboard focus with its visible ring, and that navigation changes no attempt, step, tab,
 * disclosure, URL, history, saved snapshot bytes or host request.
 * - Two constructed controls, derived from one real row and admitted by the page's own parser, cover
 *   unavailable checking and a captured attempt with no step; no retained capture has either shape.
 * - Two mounted readers run in a page compiled with Vite from this checkout's src, each reader in its
 *   own drawer-styled scroll container.
 * - With DEFINOGRAPH_BASELINE_DIST, every attempt and step of each fixture also renders in that build:
 *   the source-data markup with the outline removed and the saved snapshot bytes must be identical.
 * Writes report.json and screenshots to DEFINOGRAPH_OUTLINE_EVIDENCE_OUT; exits nonzero on failure. */
import { spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createServer } from 'node:http';
import { mkdir, mkdtemp, readFile, readdir, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { GUIDED_CONTEXT_CONTRACT } from '../src/editor/guided-context-contract.js';
import { validateDecompositionHistory, validateSourceDecomposition } from '../src/editor/source-decomposition.js';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const dist = process.env.DEFINOGRAPH_DIST ?? path.join(root, 'dist'), baselineDist = process.env.DEFINOGRAPH_BASELINE_DIST;
const chrome = process.env.DEFINOGRAPH_CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const logicalPath = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES, acceptancePath = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
const out = process.env.DEFINOGRAPH_OUTLINE_EVIDENCE_OUT;
if (!out || !logicalPath || !acceptancePath) throw new Error('Set DEFINOGRAPH_OUTLINE_EVIDENCE_OUT, DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES and DEFINOGRAPH_ACCEPTANCE_FIXTURES.');
const DRAWER = 'dialog.atlas-drawer-left';
const SECTIONS = ['step', 'provenance', 'supply', 'outcomes'] as const;
type Section = typeof SECTIONS[number];
type Row = any;
type Check = { name: string; ok: boolean; detail?: unknown };
type Scenario = { name: string; fixture: string; source: string; viewport: string; checks: Check[]; observations: Record<string, unknown>; screenshots: string[] };
const report = { startedAt: new Date().toISOString(), dist, baselineDist: baselineDist ?? null, scenarios: [] as Scenario[], comparison: null as unknown, consoleErrors: [] as string[], summary: {} as Record<string, unknown> };
const sha256 = (text: string) => createHash('sha256').update(text).digest('hex');

// Page instrumentation, identical for every build: host spy, saved-snapshot capture without a download, and read-only probes.
const INSTRUMENT = String.raw`
window.__hostMessages = [];
window.acquireVsCodeApi = () => ({ postMessage: message => { window.__hostMessages.push(JSON.parse(JSON.stringify(message))); } });
window.__saved = [];
URL.createObjectURL = blob => { window.__saved.push(blob); return 'blob:outline-check/' + window.__saved.length; };
URL.revokeObjectURL = () => {};
{ const click = HTMLAnchorElement.prototype.click; HTMLAnchorElement.prototype.click = function () { if (this.hasAttribute('download')) return; return click.call(this); }; }
window.__probe = (() => {
  const frameOf = el => { const d = el && el.closest('.atlas-drawer'); if (!d) return null; const box = d.getBoundingClientRect(), top = box.top + d.clientTop, heading = d.querySelector('.drawer-heading');
    return { d, top, headerBottom: heading ? heading.getBoundingClientRect().bottom : top, bottom: Math.min(top + d.clientHeight, innerHeight), left: box.left + d.clientLeft, right: box.left + d.clientLeft + d.clientWidth }; };
  const closed = el => { for (let d = el.closest('details'); d; d = d.parentElement && d.parentElement.closest('details')) if (!d.open && !(d.querySelector(':scope > summary') || { contains: () => false }).contains(el)) return true; return false; };
  // Painted, outside any closed disclosure, wholly inside its drawer below the sticky heading, and the element hit at its centre.
  const shown = el => { if (!el || !el.isConnected) return false; const f = frameOf(el), r = el.getBoundingClientRect();
    if (!f || !(r.width > 0 && r.height > 0) || closed(el) || !el.checkVisibility({ contentVisibilityAuto: true, visibilityProperty: true, opacityProperty: true })) return false;
    if (r.top < f.headerBottom - 1 || r.bottom > f.bottom + 1 || r.left < f.left - 1 || r.right > f.right + 1) return false;
    const hit = document.elementFromPoint((r.left + r.right) / 2, (r.top + r.bottom) / 2); return !!hit && el.contains(hit); };
  // The keyboard ring: :focus-visible with a painted outline whose whole box stays inside the drawer below its heading.
  const ring = el => { const s = getComputedStyle(el), width = parseFloat(s.outlineWidth) || 0, offset = Math.max(0, parseFloat(s.outlineOffset) || 0), r = el.getBoundingClientRect(), f = frameOf(el), e = width + offset;
    return { focusVisible: el.matches(':focus-visible'), style: s.outlineStyle, width, painted: el.matches(':focus-visible') && s.outlineStyle !== 'none' && width >= 2,
      inside: !!f && r.top - e >= f.headerBottom - 1 && r.bottom + e <= f.bottom + 1 && r.left - e >= f.left - 1 && r.right + e <= f.right + 1 }; };
  const expected = { step: 'section.continuation-step', provenance: 'section.source-provenance', supply: 'section.source-supplier', outcomes: 'details.snapshot-exact' };
  const headingOf = el => el ? (el.matches('details') ? el.querySelector(':scope > summary') : el.querySelector(':scope > h4')) : null;
  const text = el => (el && el.textContent || '').replace(/\s+/g, ' ').trim();
  const describe = el => !el || el === document.body ? { tag: el ? el.tagName : null } : ({ tag: el.tagName, id: el.id || null, text: text(el).slice(0, 160),
    outlineLink: el.getAttribute('data-reader-outline-link'), landing: el.parentElement && el.parentElement.getAttribute('data-reader-outline-landing'),
    namespace: el.closest('[data-reader-outline]') ? el.closest('[data-reader-outline]').getAttribute('data-reader-outline') : null,
    instance: el.closest('[data-harness-instance]') ? el.closest('[data-harness-instance]').getAttribute('data-harness-instance') : null,
    result: el.getAttribute('data-source-result'), stepButton: el.matches('ol.continuation-steps button') ? [...el.closest('ol').querySelectorAll('button')].indexOf(el) : null,
    inAttempt: !!el.closest('[data-decomposition-capture]'), within: el.closest('section.continuation-step') ? 'step' : el.closest('section.source-provenance') ? 'provenance' : el.closest('section.source-supplier') ? 'supply' : el.closest('nav.reader-outline') ? 'outline' : null,
    inDrawer: !!el.closest('.atlas-drawer'), shown: shown(el), ring: ring(el) });
  const scope = instance => instance ? document.querySelector('[data-harness-instance="' + instance + '"]') : document.querySelector('dialog.atlas-drawer-left[open]');
  function state(instance) {
    const s = scope(instance), attempt = s && s.querySelector('[data-decomposition-capture]'), step = attempt && attempt.querySelector('section.continuation-step[data-decomposition-step]');
    const nav = attempt && attempt.querySelector('nav.reader-outline'), title = nav && nav.querySelector('.reader-outline-title'), f = s && frameOf(s.matches('.atlas-drawer') ? s.firstElementChild : s);
    const ids = [...document.querySelectorAll('[id]')].map(el => el.id);
    return { open: !!s, scrollTop: f ? Math.round(f.d.scrollTop) : null, scrollHeight: f ? f.d.scrollHeight : null, headerBottom: f ? Math.round(f.headerBottom - f.top) : null,
      capture: attempt ? attempt.getAttribute('data-decomposition-capture') : null, step: step ? step.getAttribute('data-decomposition-step') : null,
      heading: s && s.querySelector('section.source-decomposition > h3') ? text(s.querySelector('section.source-decomposition > h3')) : null,
      stepHeading: step ? text(step.querySelector(':scope > h4')) : null,
      attempts: [...(s ? s.querySelectorAll('.continuation-attempts button') : [])].map(b => b.getAttribute('aria-pressed')),
      steps: [...(s ? s.querySelectorAll('ol.continuation-steps button') : [])].map(b => b.getAttribute('aria-pressed')),
      tabs: [...(s ? s.querySelectorAll('[role="tab"]') : [])].map(b => b.getAttribute('aria-selected')),
      disclosures: [...(attempt ? attempt.querySelectorAll('details') : [])].map(d => d.open),
      outline: nav ? { namespace: nav.getAttribute('data-reader-outline'), title: text(title), titleShown: shown(title),
        links: [...nav.querySelectorAll('a[data-reader-outline-link]')].map(a => ({ section: a.getAttribute('data-reader-outline-link'), id: a.id, href: a.getAttribute('href'), text: text(a), shown: shown(a) })) } : null,
      landings: [...(attempt ? attempt.querySelectorAll('[data-reader-outline-landing]') : [])].map(l => { const a = l.querySelector(':scope > a'), next = l.nextElementSibling, key = l.getAttribute('data-reader-outline-landing'), heading = headingOf(next);
        return { section: key, namespace: l.getAttribute('data-reader-outline'), id: a && a.id, href: a && a.getAttribute('href'), text: text(a), scope: l.querySelector('[data-reader-outline-scope]') ? text(l.querySelector('[data-reader-outline-scope]')) : null,
          adjacent: !!next && next.matches(expected[key]), heading: text(heading).slice(0, 120), linkShown: shown(a), headingShown: shown(heading), scopeShown: shown(l.querySelector('[data-reader-outline-scope]')) }; }),
      outcomeItems: [...(attempt ? attempt.querySelectorAll('[data-numbered-outcome]') : [])].map(li => ({ n: Number(li.getAttribute('data-numbered-outcome')), step: (text(li.querySelector('strong')).match(/· Step (\d+) ·/) || [])[1] || null, shown: shown(li.querySelector('strong')) })),
      provenanceHeading: attempt && attempt.querySelector('section.source-provenance > h4') ? text(attempt.querySelector('section.source-provenance > h4')) : null,
      excluded: attempt && attempt.querySelector('[data-provenance-excluded]') ? text(attempt.querySelector('[data-provenance-excluded]')) : null,
      unavailable: attempt ? [...attempt.querySelectorAll(':scope > .snapshot-unavailable')].map(text) : [],
      active: describe(document.activeElement), duplicateIds: ids.length - new Set(ids).size,
      hash: location.hash, historyLength: history.length, messages: window.__hostMessages.length,
      sourceTab: document.querySelector('dialog.atlas-drawer-left .source-tabs > button.active') ? text(document.querySelector('dialog.atlas-drawer-left .source-tabs > button.active')) : null,
      overflow: { page: document.documentElement.scrollWidth - innerWidth, drawer: f ? f.d.scrollWidth - f.d.clientWidth : null, outline: nav ? nav.scrollWidth - nav.clientWidth : null } };
  }
  // Source-data markup with the outline removed; the comparison normalizes nothing else.
  async function markup() {
    const view = document.querySelector('dialog.atlas-drawer-left[open] section.source-snapshot'); if (!view) return null;
    const copy = view.cloneNode(true); copy.querySelectorAll('nav.reader-outline, .reader-outline-landing').forEach(el => el.remove());
    const html = copy.outerHTML, digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(html));
    return { bytes: html.length, sha256: [...new Uint8Array(digest)].map(b => b.toString(16).padStart(2, '0')).join('') };
  }
  // The first sequentially focusable, rendered element after el in document order, with whether it lies in el's following section.
  const TABBABLE = 'a[href], button:not([disabled]), summary, input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])';
  function nextTabbable(el) {
    if (!el) return null;
    const all = [...document.querySelectorAll(TABBABLE)].filter(item => item.tabIndex >= 0 && !closed(item) && item.checkVisibility({ visibilityProperty: true }));
    const next = all.find(item => el.compareDocumentPosition(item) & Node.DOCUMENT_POSITION_FOLLOWING && !el.contains(item));
    const section = el.closest('[data-reader-outline-landing]') && el.closest('[data-reader-outline-landing]').nextElementSibling;
    return { next: describe(next), isActive: next === document.activeElement, inSection: !!section && !!next && section.contains(next), sectionHasControl: !!section && all.some(item => section.contains(item)) };
  }
  return { shown, ring, describe, state, markup, nextTabbable };
})();
`;

let served = dist;
const harnessDir = path.join(out, 'two-reader-harness');
const types: Record<string, string> = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.svg': 'image/svg+xml', '.json': 'application/json', '.woff2': 'font/woff2', '.woff': 'font/woff', '.ttf': 'font/ttf', '.png': 'image/png' };
const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? '/', 'http://127.0.0.1'), harness = url.pathname.startsWith('/harness/');
  const file = path.join(harness ? harnessDir : served, harness ? url.pathname.slice('/harness/'.length) : url.pathname === '/' ? 'index.html' : url.pathname);
  try { const body = await readFile(file); response.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream' }); response.end(body); }
  catch { response.writeHead(404); response.end(); }
});
await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
const address = server.address();
if (!address || typeof address !== 'object') throw new Error('no server address');
const origin = `http://127.0.0.1:${address.port}/`;
const profile = await mkdtemp(path.join(os.tmpdir(), 'definograph-outline-'));
const browser = spawn(chrome, ['--headless=new', '--disable-gpu', '--no-first-run', '--no-default-browser-check', `--user-data-dir=${profile}`, '--remote-debugging-port=0', '--window-size=1280,900', 'about:blank'], { stdio: ['ignore', 'pipe', 'pipe'] });
let socket: WebSocket | undefined;
async function shutdown() {
  const exited = new Promise<void>(resolve => { if (browser.exitCode !== null) resolve(); else { browser.once('exit', () => resolve()); setTimeout(resolve, 8000); } });
  socket?.close(); browser.kill('SIGTERM'); server.close(); await exited;
  if (browser.exitCode === null) browser.kill('SIGKILL');
  await rm(profile, { recursive: true, force: true }).catch(() => undefined);
}
try {
  const wsUrl = await new Promise<string>((resolve, reject) => {
    let text = ''; const timer = setTimeout(() => reject(new Error('Chrome did not expose DevTools')), 20000);
    browser.stderr.on('data', chunk => { text += String(chunk); const match = text.match(/DevTools listening on (ws:\/\/\S+)/); if (match) { clearTimeout(timer); resolve(match[1]); } });
    browser.on('exit', code => reject(new Error(`Chrome exited ${code}`)));
  });
  socket = new WebSocket(wsUrl);
  const ws = socket;
  await new Promise<void>((resolve, reject) => { ws.addEventListener('open', () => resolve()); ws.addEventListener('error', () => reject(new Error('DevTools socket failed'))); });
  let nextId = 1;
  const pending = new Map<number, { resolve: (value: unknown) => void; reject: (error: Error) => void }>();
  const listeners: ((method: string, params: Record<string, unknown>) => void)[] = [];
  ws.addEventListener('message', event => {
    const message = JSON.parse(String(event.data)) as { id?: number; method?: string; params?: Record<string, unknown>; result?: unknown; error?: { message: string } };
    if (message.id !== undefined) { const waiter = pending.get(message.id); pending.delete(message.id); if (!waiter) return; message.error ? waiter.reject(new Error(message.error.message)) : waiter.resolve(message.result); }
    else if (message.method) for (const listener of listeners) listener(message.method, message.params ?? {});
  });
  const send = <T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}, sessionId?: string): Promise<T> => {
    const id = nextId++; ws.send(JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) }));
    return new Promise((resolve, reject) => pending.set(id, { resolve: value => resolve(value as T), reject }));
  };
  const { targetId } = await send<{ targetId: string }>('Target.createTarget', { url: 'about:blank' });
  const { sessionId } = await send<{ sessionId: string }>('Target.attachToTarget', { targetId, flatten: true });
  const page = <T = Record<string, unknown>>(method: string, params: Record<string, unknown> = {}) => send<T>(method, params, sessionId);
  await page('Page.enable'); await page('Runtime.enable');
  listeners.push((method, params) => {
    if (method === 'Runtime.exceptionThrown') report.consoleErrors.push(`exception: ${JSON.stringify(params.exceptionDetails).slice(0, 300)}`);
    if (method === 'Runtime.consoleAPICalled' && (params.type === 'error' || params.type === 'warning')) report.consoleErrors.push(`${params.type}: ${JSON.stringify(params.args).slice(0, 300)}`);
  });
  await page('Page.addScriptToEvaluateOnNewDocument', { source: INSTRUMENT });
  const evaluate = async <T>(expression: string): Promise<T> => {
    const result = await page<{ result: { value: T }; exceptionDetails?: unknown }>('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
    if (result.exceptionDetails) throw new Error(`page evaluation failed: ${JSON.stringify(result.exceptionDetails).slice(0, 400)}`);
    return result.result.value;
  };
  const settle = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));
  const frames = () => evaluate<boolean>('new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve(true))))');
  const state = (instance?: string) => evaluate<Record<string, any>>(`window.__probe.state(${JSON.stringify(instance ?? null)})`);

  const logical = JSON.parse(await readFile(logicalPath, 'utf8')) as Row[], acceptance = JSON.parse(await readFile(acceptancePath, 'utf8')) as Row[];
  const last = (rows: Row[], label: string) => { const found = rows.filter(row => row.label === label); if (!found.length) throw new Error(`no corpus rows for ${label}`); return found.at(-1); };
  const rowsOf = (rows: Row[], label: string) => rows.filter(row => row.label === label);
  const documentOf = (row: Row) => ({ ...row.parent.origin.document, fileName: new URL(row.parent.origin.document.uri).pathname, selection: row.parent.origin.selection });
  const historyOf = (row: Row) => [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }];
  const post = (message: unknown) => evaluate(`window.postMessage(${JSON.stringify(message)}, '*'); true`);
  let requestId = 0;
  const status = (id: number, row: Row) => post({ type: 'statementlens.status', requestId: String(id), phase: 'analyzing', document: documentOf(row) });
  const result = (id: number, row: Row, decompositions = historyOf(row)) => post({ type: 'statementlens.error', guidedContextContract: GUIDED_CONTEXT_CONTRACT, requestId: String(id),
    document: documentOf(row), message: 'Independent guided export unavailable.', sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: row.parent.origin, sourceOccurrence: row.parent.occurrence,
    ...(row.seed ? { headExposure: row.seed } : {}), decompositions });

  /** Constructed controls: one real row's final record with its checking replaced, validated here by the product validator before the page parses it. */
  function constructed(row: Row, kind: 'unavailable' | 'no-step'): Row {
    const record = structuredClone(row.response.sourceDecomposition), checking = record.checking;
    if (kind === 'unavailable') record.checking = { status: 'unavailable', kind: 'error', phase: 'constructed-control', reason: 'Constructed control: checking unavailable for this attempt.', attempted: true };
    else {
      Object.assign(checking, { action: { status: 'error', reason: 'Constructed control: the source extraction reported an error before any step.' }, steps: [], selected: null, stop: null,
        checks: checking.checks.slice(0, 6), audits: checking.audits.slice(0, 6) });
      checking.environmentSnapshotCount = checking.checks.at(-1).envAfter + 1;
    }
    const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
      attempts: row.priorAttempts.map((bundle: Row) => ({ snapshot: bundle.snapshot, record: bundle.record })) });
    validateSourceDecomposition(structuredClone(record), row.response.sourceSnapshot, prior);
    return { ...row, label: `${row.label} (constructed: ${kind})`, response: { ...row.response, sourceDecomposition: record } };
  }

  async function load(width: number, height = 900, scale = 1, mobile = width < 700, url = origin) {
    await page('Emulation.setDeviceMetricsOverride', { width, height, deviceScaleFactor: scale, mobile });
    const loaded = new Promise<void>(resolve => { const listener = (method: string) => { if (method === 'Page.loadEventFired') { listeners.splice(listeners.indexOf(listener), 1); resolve(); } }; listeners.push(listener); });
    await page('Page.navigate', { url }); await loaded; await settle(500);
  }
  /** A reader brings an off-screen control into view before pressing it; a control already shown is pressed where it is. */
  async function pointer(expression: string): Promise<boolean> {
    const box = await evaluate<{ x: number; y: number } | null>(`(() => { const el = ${expression}; if (!el) return null; if (!window.__probe.shown(el)) el.scrollIntoView({ block: 'center' });
      const r = el.getBoundingClientRect(), x = r.left + r.width / 2, y = r.top + r.height / 2, hit = document.elementFromPoint(x, y); return hit && el.contains(hit) ? { x, y } : null; })()`);
    if (!box) return false;
    await settle(120);
    for (const type of ['mouseMoved', 'mousePressed', 'mouseReleased']) await page('Input.dispatchMouseEvent', { type, x: box.x, y: box.y, button: 'left', buttons: type === 'mousePressed' ? 1 : 0, clickCount: type === 'mouseMoved' ? 0 : 1 });
    await frames(); await settle(150);
    return true;
  }
  const keys = { Enter: { key: 'Enter', code: 'Enter', text: '\r', unmodifiedText: '\r', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 }, Tab: { key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9, nativeVirtualKeyCode: 9 },
    Escape: { key: 'Escape', code: 'Escape', windowsVirtualKeyCode: 27, nativeVirtualKeyCode: 27 } } as const;
  async function press(name: keyof typeof keys, shift = false) {
    const { text: _text, unmodifiedText: _unmodified, ...up } = keys[name] as Record<string, unknown>; void _text; void _unmodified;
    await page('Input.dispatchKeyEvent', { type: 'keyDown', ...keys[name], modifiers: shift ? 8 : 0 });
    await page('Input.dispatchKeyEvent', { type: 'keyUp', ...up, modifiers: shift ? 8 : 0 });
    await frames(); await settle(120);
  }
  async function shot(scenario: Scenario, name: string) {
    const image = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
    const file = `${scenario.name}-${name}.png`; await writeFile(path.join(out!, file), Buffer.from(image.data, 'base64')); scenario.screenshots.push(file);
  }
  const check = (scenario: Scenario, name: string, ok: boolean, detail?: unknown) => { scenario.checks.push({ name, ok, ...(ok || detail === undefined ? {} : { detail }) }); return ok; };
  function begin(name: string, fixture: string, source: string, viewport: string): Scenario {
    const scenario: Scenario = { name, fixture, source, viewport, checks: [], observations: {}, screenshots: [] }; report.scenarios.push(scenario); return scenario;
  }
  const button = (scope: string, text: string) => `[...document.querySelectorAll(${JSON.stringify(`${scope} button`)})].find(el => (el.textContent || '').trim() === ${JSON.stringify(text)})`;
  const scopeOf = (instance?: string) => instance ? `document.querySelector('[data-harness-instance="${instance}"]')` : `document.querySelector(${JSON.stringify(`${DRAWER}[open]`)})`;
  const outlineLink = (section: Section, instance?: string) => `(${scopeOf(instance)}?.querySelector('nav.reader-outline a[data-reader-outline-link="${section}"]') ?? null)`;
  const returnLink = (section: Section, instance?: string) => `(${scopeOf(instance)}?.querySelector('[data-reader-outline-landing="${section}"] > a') ?? null)`;
  async function open(scenario: Scenario, row: Row, via: 'pointer' | 'keyboard' = 'pointer', decompositions = historyOf(row)) {
    const id = ++requestId; await status(id, row); await settle(150); await result(id, row, decompositions); await settle(600);
    if (via === 'pointer') check(scenario, 'Source data opens by pointer', await pointer(button('.statement-actions', 'Source data')));
    else { await evaluate(`(${button('.statement-actions', 'Source data')}).focus(); true`); await press('Enter'); }
    await settle(350);
    const opened = await state();
    check(scenario, 'the source drawer shows the posted capture', opened.open === true && opened.sourceTab === 'Source data', { open: opened.open, sourceTab: opened.sourceTab });
    return opened;
  }
  /** What a passive jump may not change. */
  const passive = (before: Record<string, any>, after: Record<string, any>) => ['capture', 'step', 'heading', 'attempts', 'steps', 'tabs', 'disclosures', 'hash', 'historyLength', 'messages', 'sourceTab']
    .filter(key => JSON.stringify(before[key]) !== JSON.stringify(after[key]));
  const expectedIdentity = (s: Record<string, any>) => s.stepHeading ? `Section navigation · ${s.heading} · step ${s.stepHeading.match(/^Step (\d+)/)[1]} · ${s.stepHeading.replace(/^Step \d+ · /, '')}` : `Section navigation · ${s.heading} · no recorded step`;
  const returnText = (s: Record<string, any>) => `${s.heading} · ${s.stepHeading ? `step ${s.stepHeading.match(/^Step (\d+)/)[1]}` : 'no recorded step'} · section navigation`;

  function outlineChecks(scenario: Scenario, s: Record<string, any>, expected: Section[]) {
    check(scenario, 'outline names the displayed attempt and selected step', s.outline?.title === expectedIdentity(s), { title: s.outline?.title, expected: expectedIdentity(s) });
    check(scenario, `destinations are exactly ${expected.join(', ')}`, JSON.stringify(s.outline?.links.map((link: any) => link.section)) === JSON.stringify(expected), s.outline?.links);
    check(scenario, 'each rendered destination has one landing immediately before its section, in the same namespace',
      JSON.stringify(s.landings.map((l: any) => l.section)) === JSON.stringify(expected) && s.landings.every((l: any) => l.adjacent && l.namespace === s.outline?.namespace && l.text === returnText(s)
        && s.outline?.links.find((link: any) => link.section === l.section)?.href === `#${l.id}` && l.href === `#${s.outline?.links.find((link: any) => link.section === l.section)?.id}`), s.landings);
    check(scenario, 'no duplicate element ids', s.duplicateIds === 0, s.duplicateIds);
  }
  /** One deliberate activation from the outline and one back; returns the landing observation. */
  async function jump(scenario: Scenario, section: Section, input: 'pointer' | 'keyboard', label: string, instance?: string) {
    const before = await state(instance);
    if (input === 'pointer') check(scenario, `${label}: pointer on ${section} outline link`, await pointer(outlineLink(section, instance)));
    else { const focused = await evaluate<boolean>(`document.activeElement === ${outlineLink(section, instance)}`); check(scenario, `${label}: keyboard focus is on the ${section} outline link`, focused); await press('Enter'); }
    const at = await state(instance), landing = at.landings.find((item: any) => item.section === section);
    check(scenario, `${label}: focus lands on the ${section} return link of this attempt and step`, at.active?.landing === section && at.active?.namespace === before.outline?.namespace && (!instance || at.active?.instance === instance), at.active);
    check(scenario, `${label}: the landing and the existing ${section} heading are painted below the sticky heading`, !!landing?.linkShown && !!landing?.headingShown, landing);
    if (input === 'keyboard') check(scenario, `${label}: visible keyboard focus ring inside the drawer`, !!at.active?.ring?.painted && !!at.active?.ring?.inside, at.active?.ring);
    check(scenario, `${label}: selection, tabs, disclosures, URL, history and host messages unchanged`, passive(before, at).length === 0, passive(before, at));
    return { before, at, landing };
  }
  async function back(scenario: Scenario, section: Section, input: 'pointer' | 'keyboard', label: string, instance?: string) {
    const before = await state(instance);
    if (input === 'pointer') check(scenario, `${label}: pointer on the ${section} return link`, await pointer(returnLink(section, instance)));
    else { check(scenario, `${label}: keyboard focus is on the ${section} return link`, await evaluate<boolean>(`document.activeElement === ${returnLink(section, instance)}`)); await press('Enter'); }
    const at = await state(instance);
    check(scenario, `${label}: focus returns to the ${section} outline link`, at.active?.outlineLink === section && at.active?.namespace === before.outline?.namespace && (!instance || at.active?.instance === instance), at.active);
    check(scenario, `${label}: the outline identity and the focused link are painted below the sticky heading`, !!at.outline?.titleShown && !!at.active?.shown, { title: at.outline?.titleShown, active: at.active });
    if (input === 'keyboard') check(scenario, `${label}: visible keyboard focus ring inside the drawer`, !!at.active?.ring?.painted && !!at.active?.ring?.inside, at.active?.ring);
    check(scenario, `${label}: selection, tabs, disclosures, URL, history and host messages unchanged`, passive(before, at).length === 0, passive(before, at));
    return at;
  }
  /** Round trip through every destination: outline → landing → outline → next link, at most two activations per section change. */
  async function cycle(scenario: Scenario, input: 'pointer' | 'keyboard', sections: readonly Section[], shots: boolean, instance?: string) {
    let activations = 0; const landings: Record<string, unknown>[] = [];
    for (const [index, section] of sections.entries()) {
      if (input === 'keyboard' && index > 0) { await press('Tab'); check(scenario, `Tab moves from the ${sections[index - 1]} link to the ${section} link`, (await state(instance)).active?.outlineLink === section); }
      const { at, landing } = await jump(scenario, section, input, `${section} jump`, instance); activations++;
      landings.push({ section, scrollTop: at.scrollTop, landing: landing ?? null });
      if (shots) await shot(scenario, `${section}-landing`);
      if (input === 'keyboard') {
        const expected = await evaluate<Record<string, any> | null>(`window.__probe.nextTabbable(${returnLink(section, instance)})`);
        await press('Tab'); const next = await state(instance), moved = await evaluate<boolean>(`(() => { const el = document.activeElement, landing = ${returnLink(section, instance)}; return !!landing && (landing.compareDocumentPosition(el) & Node.DOCUMENT_POSITION_FOLLOWING) > 0; })()`);
        const exactNext = await evaluate<boolean>(`window.__probe.nextTabbable(${returnLink(section, instance)})?.isActive === true`);
        check(scenario, `Tab from the ${section} landing moves forward to the first control of that section, or past it when it has none`,
          !!expected && moved && exactNext && next.active?.shown === true && expected.inSection === expected.sectionHasControl, { expected, active: next.active, exactNext });
        ((scenario.observations.tabAfterLanding ??= []) as unknown[]).push({ section, next: next.active?.text?.slice(0, 60), inSection: expected?.inSection, sectionHasControl: expected?.sectionHasControl });
        await press('Tab', true); check(scenario, `Shift+Tab returns to the ${section} landing`, (await state(instance)).active?.landing === section);
      }
      await back(scenario, section, input, `${section} return`, instance); activations++;
    }
    scenario.observations.landings = landings;
    check(scenario, 'each section change takes at most two deliberate activations (return, then the next link)', activations === sections.length * 2, activations);
  }
  async function saved(): Promise<{ count: number; sha256: string | null; bytes: number }> {
    const before = await evaluate<number>('window.__saved.length');
    await evaluate(`(${button('section.source-snapshot > header', 'Save source snapshot')}).click(); true`); await settle(150);
    const text = await evaluate<string | null>(`window.__saved.length > ${before} ? window.__saved.at(-1).text() : null`);
    return { count: await evaluate<number>('window.__saved.length'), sha256: text === null ? null : sha256(text), bytes: text?.length ?? 0 };
  }

  await mkdir(out, { recursive: true });
  const rotor = last(logical, 'literal Rotor law'), negated = rowsOf(logical, 'negated owner');
  const forallExists = last(logical, 'universal then existential'), existsForall = last(logical, 'existential then universal'), ordinaryFunction = last(logical, 'ordinary function type');
  const sorried = last(acceptance, 'term using a lemma proved with a placeholder'), falseExistential = last(acceptance, 'unproved false existential'), ordinaryValue = last(acceptance, 'ordinary value inspected');
  const stoppedHead = last(acceptance, 'inductive predicate head'), constructorRefusal = last(acceptance, 'constructor head refusal');
  const unavailable = constructed(ordinaryFunction, 'unavailable'), noStep = constructed(ordinaryFunction, 'no-step');

  // 1. Rotor at 1272: pointer round trip through the four destinations; saved bytes and geometry.
  {
    const scenario = begin('rotor-pointer-1272', rotor.label, 'retained real corpus', '1272×900');
    await load(1272); const opened = await open(scenario, rotor);
    outlineChecks(scenario, opened, [...SECTIONS]);
    check(scenario, 'identity is the current attempt 7 at its final step 5', opened.heading === 'Current continuation · attempt 7' && opened.step === '4', { heading: opened.heading, step: opened.step });
    check(scenario, 'opening does not scroll to or focus the outline', opened.scrollTop === 0 && opened.active?.within !== 'outline' && !opened.active?.landing, opened.active);
    const savedBefore = await saved();
    scenario.observations.geometry = await evaluate(`(() => { const d = document.querySelector(${JSON.stringify(`${DRAWER}[open]`)}), top = el => el ? Math.round(el.getBoundingClientRect().top - d.getBoundingClientRect().top + d.scrollTop) : null;
      return { scrollHeight: d.scrollHeight, attempt: top(d.querySelector('section.source-decomposition > h3')), outline: top(d.querySelector('nav.reader-outline')), step: top(d.querySelector('section.continuation-step')),
        provenance: top(d.querySelector('section.source-provenance')), supply: top(d.querySelector('section.source-supplier')), outcomes: top(d.querySelector('[data-reader-outline-landing="outcomes"]')) }; })()`);
    await evaluate(`${outlineLink('step')}?.scrollIntoView({ block: 'center' }); true`); await settle(150); await shot(scenario, 'outline');
    await cycle(scenario, 'pointer', SECTIONS, true);
    const savedAfter = await saved();
    check(scenario, 'saved snapshot bytes are identical before and after navigation', !!savedBefore.sha256 && savedBefore.sha256 === savedAfter.sha256, { savedBefore, savedAfter });
    scenario.observations.saved = savedBefore;
    check(scenario, 'only the ready message reached the host', (await evaluate<number>('window.__hostMessages.length')) === 1);
  }

  // 2. Negated owner at 400 by keyboard only: arrive at an explicit action's answer, Tab to the outline, round trip, then Escape.
  {
    const scenario = begin('negated-keyboard-400', 'negated owner', 'retained real corpus', '400×900');
    const before = negated[4], next = negated[5];
    await load(400); await open(scenario, before, 'keyboard');
    const sent = await evaluate<number>('window.__hostMessages.length');
    const action = button('section.continuation-step', 'Read logical structure of this term (one layer)');
    check(scenario, 'explicit action by keyboard', await evaluate<boolean>(`(() => { const el = ${action}; if (!el) return false; el.scrollIntoView({ block: 'center' }); el.focus(); return document.activeElement === el; })()`));
    await press('Enter');
    check(scenario, 'the action posts exactly one host request', (await evaluate<number>('window.__hostMessages.length')) === sent + 1);
    const id = ++requestId; await status(id, before); await settle(800); await result(id, before, historyOf(next)); await frames(); await settle(400);
    const answered = await state();
    check(scenario, 'the existing explicit-result navigation focuses the new attempt heading, not the outline', answered.active?.result === 'attempt' && answered.heading === 'Current continuation · attempt 6', answered.active);
    outlineChecks(scenario, answered, [...SECTIONS]);
    await shot(scenario, 'answer');
    const path: unknown[] = [];
    for (let i = 0; i < 30 && (await state()).active?.outlineLink !== 'step'; i++) { await press('Tab'); path.push((await state()).active); }
    const reached = await state();
    check(scenario, 'Tab from the answer passes the attempt list and step controls and reaches the outline', reached.active?.outlineLink === 'step'
      && (path.at(-2) as any)?.stepButton === reached.steps.length - 1, path.map((item: any) => item?.text?.slice(0, 50)));
    scenario.observations.tabPathToOutline = path.map((item: any) => item?.text?.slice(0, 60));
    await cycle(scenario, 'keyboard', SECTIONS, true);
    check(scenario, 'no request after the answer', (await evaluate<number>('window.__hostMessages.length')) === sent + 1);
    await press('Escape');
    const closed = await evaluate<Record<string, unknown>>(`({ open: !!document.querySelector(${JSON.stringify(`${DRAWER}[open]`)}), active: (document.activeElement && document.activeElement.textContent || '').trim() })`);
    check(scenario, 'Escape closes the drawer and returns focus to Source data', closed.open === false && closed.active === 'Source data', closed);
    await press('Enter'); await settle(300);
    const reopened = await state();
    scenario.observations.reopened = { scrollTop: reopened.scrollTop, active: reopened.active };
    await settle(600); const later = await state();
    check(scenario, 'reopening replays neither a landing nor the outline focus, and nothing scrolls afterwards', reopened.open && !reopened.active?.landing && reopened.active?.within !== 'outline'
      && later.scrollTop === reopened.scrollTop && later.active?.text === reopened.active?.text, { reopened: { scrollTop: reopened.scrollTop, active: reopened.active }, later: { scrollTop: later.scrollTop, active: later.active } });
    check(scenario, 'closing and reopening post no request', reopened.messages === sent + 1);
  }

  // 3. Rotor at 200% zoom (a 1272×900 window at 200%: 636×450 CSS px, scale 2) by keyboard, and 4. at 320 by pointer.
  for (const [name, width, height, scale, input] of [['rotor-keyboard-zoom200', 636, 450, 2, 'keyboard'], ['rotor-pointer-320', 320, 900, 1, 'pointer']] as const) {
    const scenario = begin(name, rotor.label, 'retained real corpus', `${width}×${height} CSS px at scale ${scale}`);
    await load(width, height, scale, width < 400); const opened = await open(scenario, rotor, input);
    outlineChecks(scenario, opened, [...SECTIONS]);
    check(scenario, 'no horizontal overflow of page, drawer or outline', opened.overflow.page <= 0 && opened.overflow.drawer <= 0 && opened.overflow.outline <= 0, opened.overflow);
    await evaluate(`document.querySelector(${JSON.stringify(`${DRAWER}[open] nav.reader-outline`)})?.scrollIntoView({ block: 'center' }); true`); await settle(150);
    const inView = await state();
    check(scenario, 'every outline link is painted inside the drawer when the outline is in view', inView.outline?.links.every((link: any) => link.shown) ?? false, inView.outline?.links);
    await shot(scenario, 'outline');
    if (input === 'keyboard') await evaluate(`${outlineLink('step')}?.focus({ preventScroll: true }); true`);
    await cycle(scenario, input, SECTIONS, true);
    const after = await state();
    check(scenario, 'still no horizontal overflow after navigation', after.overflow.page <= 0 && after.overflow.drawer <= 0 && after.overflow.outline <= 0, after.overflow);
    check(scenario, 'only the ready message reached the host', after.messages === 1);
  }

  // 5. Rotor at 1272: an earlier prefix of the current attempt keeps later outcomes in the whole-attempt list.
  {
    const scenario = begin('rotor-earlier-prefix-1272', rotor.label, 'retained real corpus', '1272×900');
    await load(1272); const opened = await open(scenario, rotor);
    const oldIds = [...(opened.outline?.links ?? []).map((link: any) => link.id), ...opened.landings.map((l: any) => l.id)];
    check(scenario, 'reader selects step 2 by pointer', await pointer(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] ol.continuation-steps button`)})[1]`));
    const selected = await state();
    check(scenario, 'selecting a step moves no focus to the outline or a landing', selected.active?.stepButton === 1, selected.active);
    check(scenario, 'selecting a step posts no request', selected.messages === 1);
    check(scenario, 'the displayed prefix is step 2 of attempt 7', selected.step === '1' && selected.provenanceHeading === 'Ordered provenance · through step 2 of this attempt', { step: selected.step, provenance: selected.provenanceHeading });
    outlineChecks(scenario, selected, [...SECTIONS]);
    check(scenario, 'targets of the previous step no longer exist', await evaluate<boolean>(`${JSON.stringify(oldIds)}.every(id => !document.getElementById(id))`) && !!selected.outline && selected.outline.namespace !== opened.outline?.namespace);
    check(scenario, 'reader chooses the inferred type and the Structure view of step 2', await pointer(`[...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] [aria-label="Checked part target"] button`)})][1]`)
      && await pointer(`[...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] [aria-label="Continuation presentation"] button`)})][1]`));
    const chosen = await state();
    await jump(scenario, 'step', 'pointer', 'step jump keeps the chosen subject and view'); await back(scenario, 'step', 'pointer', 'step return keeps the chosen subject and view');
    const kept = await evaluate<string[]>(`[...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] section.continuation-step [role="tab"][aria-selected="true"]`)})].map(el => el.textContent.trim())`);
    check(scenario, 'the step reading keeps its inferred-type subject and Structure view', JSON.stringify(kept) === JSON.stringify(['Inferred type', 'Structure']) && JSON.stringify((await state()).tabs) === JSON.stringify(chosen.tabs), kept);
    const { landing } = await jump(scenario, 'outcomes', 'pointer', 'outcomes jump');
    check(scenario, 'the outcome landing states the whole attempt including later steps outside the prefix', landing?.scope === 'All recorded outcomes of attempt 7, including outcomes of steps after step 2, which are outside the selected prefix.' && landing?.scopeShown === true, landing);
    const listed = (await state()).outcomeItems;
    check(scenario, 'the whole-attempt list retains outcomes of steps after the selected prefix', listed.length === 17 && listed.some((item: any) => Number(item.step) > 2), listed.map((item: any) => item.step));
    check(scenario, 'the excluded-suffix notice stays in the prefix reading', /^Steps 3, 4, 5 of attempt 7 \([0-9a-f]{8}\) are outside this prefix and not read\.$/.test(selected.excluded ?? ''), selected.excluded);
    await shot(scenario, 'outcomes-landing');
    await back(scenario, 'outcomes', 'pointer', 'outcomes return');
  }

  // 6. Rotor at 400: an earlier attempt, then attempt 1 whose only step retains no outcome of its own.
  {
    const scenario = begin('rotor-earlier-attempt-400', rotor.label, 'retained real corpus', '400×900');
    await load(400); await open(scenario, rotor);
    check(scenario, 'reader opens the attempt list', await pointer(`[...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] details.snapshot-exact > summary`)})].find(el => el.textContent.startsWith('Earlier continuations'))`));
    check(scenario, 'reader selects attempt 3', await pointer(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] .continuation-attempts button`)})[2]`));
    const third = await state();
    check(scenario, 'the earlier attempt keeps its existing qualification', third.heading === 'Earlier continuation · attempt 3' && third.active?.outlineLink === null && !third.active?.landing, { heading: third.heading, active: third.active });
    outlineChecks(scenario, third, [...SECTIONS]);
    await jump(scenario, 'supply', 'pointer', 'attempt 3 supply jump'); await shot(scenario, 'attempt3-supply');
    await back(scenario, 'supply', 'pointer', 'attempt 3 supply return');
    check(scenario, 'reader selects attempt 1', await pointer(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] .continuation-attempts button`)})[0]`));
    const first = await state();
    check(scenario, 'attempt 1 has one step that retained no outcome of its own', first.steps.length === 1 && first.outcomeItems.length === 6, { steps: first.steps, outcomes: first.outcomeItems.length });
    outlineChecks(scenario, first, [...SECTIONS]);
    const { landing } = await jump(scenario, 'outcomes', 'pointer', 'attempt 1 outcomes jump');
    check(scenario, 'the outcome destination follows the rendered list, not the step receipt count', landing?.scope === 'All recorded outcomes of attempt 1, not only those of step 1.', landing);
    check(scenario, 'only the ready message reached the host', (await state()).messages === 1);
  }

  // 7. Rotor at 320: the user-collapsed outcome list stays collapsed; its descendants are not counted as shown.
  {
    const scenario = begin('rotor-closed-outcomes-320', rotor.label, 'retained real corpus', '320×900');
    await load(320); await open(scenario, rotor);
    const summary = `[...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] details.snapshot-exact > summary`)})].find(el => el.textContent.startsWith('Recorded outcomes in this attempt'))`;
    check(scenario, 'reader collapses the outcome list by pointer', await pointer(summary) && await evaluate<boolean>(`!(${summary}).parentElement.open`));
    const { at, landing } = await jump(scenario, 'outcomes', 'pointer', 'closed outcomes jump');
    check(scenario, 'the list stays collapsed; the landing, whole-attempt statement and summary are painted', await evaluate<boolean>(`!(${summary}).parentElement.open`) && !!landing?.linkShown && !!landing?.scopeShown && !!landing?.headingShown, landing);
    check(scenario, 'no descendant of the closed list is counted as shown', at.outcomeItems.length === 17 && at.outcomeItems.every((item: any) => item.shown === false), at.outcomeItems.filter((item: any) => item.shown));
    await shot(scenario, 'closed-outcomes-landing');
    await back(scenario, 'outcomes', 'pointer', 'closed outcomes return');
    check(scenario, 'returning leaves the list collapsed', await evaluate<boolean>(`!(${summary}).parentElement.open`));
  }

  // 8. Required semantic fixtures, stopped and refused prefixes: each rendered destination, there and back.
  const fixtures: [string, Row, number, 'pointer' | 'keyboard', string][] = [
    ['forall-exists-1272', forallExists, 1272, 'pointer', 'retained real corpus'], ['exists-forall-400', existsForall, 400, 'keyboard', 'retained real corpus'],
    ['sorried-lemma-1272', sorried, 1272, 'pointer', 'retained real corpus'], ['false-existential-400', falseExistential, 400, 'pointer', 'retained real corpus'],
    ['ordinary-value-1272', ordinaryValue, 1272, 'keyboard', 'retained real corpus'], ['stopped-head-400', stoppedHead, 400, 'pointer', 'retained real corpus'],
    ['constructor-refusal-1272', constructorRefusal, 1272, 'pointer', 'retained real corpus'], ['constructed-no-step-400', noStep, 400, 'keyboard', 'constructed control derived from a real row'],
  ];
  for (const [name, row, width, input, source] of fixtures) {
    const scenario = begin(name, row.label, source, `${width}×900`);
    await load(width); const opened = await open(scenario, row, input);
    const rendered = await evaluate<Record<Section, boolean>>(`(() => { const a = document.querySelector(${JSON.stringify(`${DRAWER}[open] [data-decomposition-capture]`)});
      return { step: !!a.querySelector('section.continuation-step'), provenance: !!a.querySelector('section.source-provenance'), supply: !!a.querySelector('section.source-supplier'),
        outcomes: [...a.querySelectorAll('details > summary')].some(s => s.textContent.startsWith('Recorded outcomes in this attempt')) }; })()`);
    const expected = SECTIONS.filter(section => rendered[section]);
    scenario.observations.rendered = rendered; scenario.observations.unavailable = opened.unavailable;
    outlineChecks(scenario, opened, expected);
    if (row === noStep) check(scenario, 'a captured attempt without steps has no step reading and says so', !rendered.step && opened.outline?.title.endsWith('· no recorded step') && opened.landings.every((l: any) => !/step \d/.test(l.text)), opened.outline);
    if (input === 'keyboard') await evaluate(`${outlineLink(expected[0])}?.focus(); true`);
    await cycle(scenario, input, expected, true);
    if (rendered.supply) {
      await jump(scenario, 'supply', 'pointer', 'supply check');
      const f1 = await evaluate<Record<string, unknown>>(`(() => { const s = document.querySelector(${JSON.stringify(`${DRAWER}[open] section.source-supplier`)}); if (!s) return { adjacent: null }; const links = [...s.querySelectorAll('[data-supplier-link]')];
        return { state: s.getAttribute('data-supplier-state'), links: links.length, adjacent: links.every(link => link.querySelector('[data-supplier-sentence]')?.nextElementSibling?.hasAttribute('data-supplier-axioms')), refused: s.getAttribute('data-supplier-state') === 'refused' ? s.textContent.replace(/\\s+/g, ' ').trim() : null }; })()`);
      scenario.observations.supply = f1;
      check(scenario, 'the axiom line still directly follows each supply sentence', f1.adjacent === true, f1);
      await back(scenario, 'supply', 'pointer', 'supply check return');
    }
    check(scenario, 'only the ready message reached the host', (await state()).messages === 1);
  }

  // 9. Stopped prefix: selecting the earlier completed step of the stopped attempt gives a provenance reading where the stopped step is refused.
  {
    const scenario = begin('stopped-head-earlier-prefix-1272', stoppedHead.label, 'retained real corpus', '1272×900');
    await load(1272); const opened = await open(scenario, stoppedHead);
    check(scenario, 'the stopped final step keeps its stop reason above the outline', opened.unavailable.some((text: string) => text.startsWith('Stopped during head:')) && opened.step === '1', opened.unavailable);
    const refused = await evaluate<boolean>(`!!document.querySelector(${JSON.stringify(`${DRAWER}[open] section.source-provenance[data-provenance-refused]`)})`);
    check(scenario, 'reader selects step 1', await pointer(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] ol.continuation-steps button`)})[0]`));
    const earlier = await state();
    outlineChecks(scenario, earlier, [...SECTIONS]);
    check(scenario, 'the refused stopped step and the read earlier prefix both have a provenance destination', refused && earlier.provenanceHeading === 'Ordered provenance · through step 1 of this attempt', { refused, provenance: earlier.provenanceHeading });
    const { landing } = await jump(scenario, 'outcomes', 'pointer', 'stopped attempt outcomes jump');
    check(scenario, 'no outcome follows step 1, so the list is described as not only step 1', landing?.scope === 'All recorded outcomes of attempt 2, not only those of step 1.', landing);
  }

  // 10. Unavailable checking: no section exists, so no outline is shown.
  {
    const scenario = begin('constructed-unavailable-1272', unavailable.label, 'constructed control derived from a real row', '1272×900');
    await load(1272); const opened = await open(scenario, unavailable);
    check(scenario, 'the page parser admitted the control and shows the unavailable attempt', opened.capture === unavailable.response.sourceDecomposition.captureId
      && opened.unavailable.includes('Continuation unavailable during constructed-control: Constructed control: checking unavailable for this attempt.'), opened.unavailable);
    check(scenario, 'no outline, landing or navigation label is invented', opened.outline === null && opened.landings.length === 0
      && await evaluate<boolean>(`!document.querySelector(${JSON.stringify(`${DRAWER}[open]`)}).textContent.includes('Section navigation')`));
    await evaluate(`document.querySelector(${JSON.stringify(`${DRAWER}[open] section.source-decomposition`)})?.scrollIntoView({ block: 'start' }); true`); await settle(150);
    await shot(scenario, 'unavailable');
  }

  // 11. Passive refresh and source-tab change after a jump: no stale return, no automatic focus or scroll.
  {
    const scenario = begin('refresh-and-tab-1272', rotor.label, 'retained real corpus', '1272×900');
    await load(1272); await open(scenario, rotor);
    await jump(scenario, 'provenance', 'pointer', 'before refresh');
    check(scenario, 'reader chooses the Source tab', await pointer(button(`${DRAWER} .source-tabs`, 'Source')));
    check(scenario, 'reader returns to Source data', await pointer(button(`${DRAWER} .source-tabs`, 'Source data')));
    const returned = await state();
    check(scenario, 'the reader remounts at the top with no replayed landing', returned.scrollTop === 0 && !returned.active?.landing && returned.active?.within !== 'outline', { scrollTop: returned.scrollTop, active: returned.active });
    const { at } = await jump(scenario, 'supply', 'pointer', 'before passive capture');
    const stale = [...(at.outline?.links ?? []).map((link: any) => link.id), ...at.landings.map((l: any) => l.id)];
    check(scenario, 'the replacement check starts with this mounted capture’s live targets', stale.length > 0
      && await evaluate<boolean>(`${JSON.stringify(stale)}.every(id => !!document.getElementById(id))`));
    const id = ++requestId; await status(id, ordinaryFunction); await settle(300); await result(id, ordinaryFunction); await frames(); await settle(500);
    const refreshed = await state();
    check(scenario, 'a passive capture shows its own attempt without moving focus to its outline or a landing', refreshed.capture === ordinaryFunction.response.sourceDecomposition.captureId
      && !refreshed.active?.landing && refreshed.active?.within !== 'outline', refreshed.active);
    check(scenario, 'targets of the replaced capture no longer exist', await evaluate<boolean>(`${JSON.stringify(stale)}.every(id => !document.getElementById(id))`));
    check(scenario, 'navigation and refreshes post no request', refreshed.messages === 1);
  }

  // 12. Two mounted readers of one history, compiled from this checkout's src, each in its own drawer-styled container.
  {
    const scenario = begin('two-readers-1272', `${negated.at(-1).label} (two mounted readers)`, 'two-reader page compiled from this checkout src', '1272×900');
    const { build } = await import('vite');
    const entry = `import { createElement } from 'react';
import { createRoot } from 'react-dom/client';
import ${JSON.stringify(path.join(root, 'src/styles.css'))};
import { parseEditorMessage, retainedDecompositionHistory } from ${JSON.stringify(path.join(root, 'src/editor/host.ts'))};
import { SourceDecompositionReading } from ${JSON.stringify(path.join(root, 'src/editor/SourceDecompositionReading.tsx'))};
import ${JSON.stringify(path.join(root, 'src/editor/source-snapshot.css'))};
window.__harnessActions = 0;
window.__mountReaders = message => {
  const parsed = parseEditorMessage(message), attempts = parsed && parsed.decompositions, history = attempts && retainedDecompositionHistory(attempts);
  if (!attempts || !history) return false;
  const reader = instance => createElement('div', { className: 'atlas-drawer', 'data-harness-instance': instance, style: { position: 'static', margin: 0, height: '860px', width: '520px', flex: '0 0 520px' } },
    createElement('div', { className: 'drawer-surface' }, createElement('header', { className: 'drawer-heading' }, createElement('h2', null, 'Reader ' + instance)),
      createElement('section', { className: 'source-snapshot' }, createElement(SourceDecompositionReading, { attempts, history, currentOrigin: true, onContinue: () => { window.__harnessActions++; } }))));
  createRoot(document.getElementById('harness')).render(createElement('div', { style: { display: 'flex', gap: '24px', padding: '8px' } }, reader('one'), reader('two')));
  return true;
};`;
    await build({ configFile: false, root, logLevel: 'error', define: { 'process.env.NODE_ENV': JSON.stringify('production') },
      plugins: [{ name: 'reader-outline-harness', resolveId: (id: string) => id.endsWith('virtual:reader-outline-harness') ? '\0reader-outline-harness' : undefined, load: (id: string) => id === '\0reader-outline-harness' ? entry : undefined }],
      build: { outDir: harnessDir, emptyOutDir: true, minify: false, target: 'es2022', lib: { entry: 'virtual:reader-outline-harness', formats: ['es'], fileName: () => 'harness.js' } } });
    const styles = (await readdir(harnessDir)).filter(file => file.endsWith('.css'));
    await writeFile(path.join(harnessDir, 'index.html'), `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">${styles.map(file => `<link rel="stylesheet" href="./${file}">`).join('')}<title>Two mounted readers</title></head><body><div id="harness"></div><script type="module" src="./harness.js"></script></body></html>`);
    await load(1272, 900, 1, false, `${origin}harness/index.html`); await settle(300);
    const row = negated.at(-1);
    check(scenario, 'both readers mount from one host-validated history', await evaluate<boolean>(`window.__mountReaders(${JSON.stringify({ type: 'statementlens.error', requestId: '1', document: documentOf(row), message: 'Independent guided export unavailable.',
      sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: row.parent.origin, sourceOccurrence: row.parent.occurrence, decompositions: historyOf(row) })})`));
    await settle(600);
    const [one, two] = [await state('one'), await state('two')];
    check(scenario, 'distinct namespaces and no duplicate ids across both readers', !!one.outline && !!two.outline && one.outline.namespace !== two.outline.namespace && one.duplicateIds === 0, { one: one.outline?.namespace, two: two.outline?.namespace, duplicates: one.duplicateIds });
    for (const [instance, other] of [['one', 'two'], ['two', 'one']] as const) {
      const otherBefore = await state(other);
      for (const section of ['provenance', 'outcomes'] as const) { await jump(scenario, section, 'pointer', `reader ${instance} ${section}`, instance); await back(scenario, section, 'pointer', `reader ${instance} ${section} return`, instance); }
      const otherAfter = await state(other);
      check(scenario, `reader ${instance} navigation leaves reader ${other} unscrolled and unchanged`, otherAfter.scrollTop === otherBefore.scrollTop && passive(otherBefore, otherAfter).length === 0 && otherAfter.outline?.namespace === otherBefore.outline?.namespace, { before: otherBefore.scrollTop, after: otherAfter.scrollTop, changed: passive(otherBefore, otherAfter) });
    }
    check(scenario, 'reader one selects step 3 without changing reader two', await pointer(`document.querySelector('[data-harness-instance="one"]').querySelectorAll('ol.continuation-steps button')[2]`)
      && (await state('one')).step === '2' && (await state('two')).step === '7');
    await evaluate(`${outlineLink('supply', 'one')}?.focus(); true`); await press('Tab', true); await press('Tab');
    await jump(scenario, 'supply', 'keyboard', 'reader one step 3 supply', 'one'); await back(scenario, 'supply', 'keyboard', 'reader one step 3 supply return', 'one');
    await shot(scenario, 'two-readers');
    check(scenario, 'no host message or continuation action from either reader', (await evaluate<number>('window.__hostMessages.length')) === 0 && (await evaluate<number>('window.__harnessActions')) === 0);
  }

  // 13. Baseline comparison: the source-data markup without the outline and the saved bytes, for every attempt and step.
  if (baselineDist) {
    const rows: [string, Row][] = [['rotor', rotor], ['forall-exists', forallExists], ['exists-forall', existsForall], ['negated', negated.at(-1)], ['sorried', sorried], ['false-existential', falseExistential],
      ['ordinary-value', ordinaryValue], ['stopped-head', stoppedHead], ['constructor-refusal', constructorRefusal], ['constructed-no-step', noStep], ['constructed-unavailable', unavailable]];
    async function capture(build: string) {
      served = build; const results: Record<string, unknown> = {};
      for (const [name, row] of rows) {
        const scenario: Scenario = { name: `capture-${name}`, fixture: row.label, source: '', viewport: '1272×900', checks: [], observations: {}, screenshots: [] };
        await load(1272); await open(scenario, row);
        const savedRecord = await saved();
        check(scenario, 'the fixture produces nonempty saved snapshot bytes', savedRecord.sha256 !== null && savedRecord.bytes > 0, savedRecord);
        const entries: Record<string, unknown> = { saved: savedRecord };
        const attempts = await evaluate<number>(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] .continuation-attempts button`)}).length`);
        for (let attempt = 0; attempt < attempts; attempt++) {
          await evaluate(`(() => { const d = [...document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] details.snapshot-exact`)})].find(el => el.querySelector(':scope > summary').textContent.startsWith('Earlier continuations')); d.open = true;
            document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] .continuation-attempts button`)})[${attempt}].click(); return true; })()`); await frames(); await settle(60);
          const steps = await evaluate<number>(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] ol.continuation-steps button`)}).length`);
          entries[`attempt ${attempt + 1} default`] = await evaluate('window.__probe.markup()');
          for (let step = 0; step < steps; step++) {
            await evaluate(`document.querySelectorAll(${JSON.stringify(`${DRAWER}[open] ol.continuation-steps button`)})[${step}].click(); true`); await frames(); await settle(40);
            entries[`attempt ${attempt + 1} step ${step + 1}`] = await evaluate('window.__probe.markup()');
          }
        }
        entries.checks = scenario.checks;
        results[name] = entries;
      }
      served = dist; return results;
    }
    const baseline = await capture(baselineDist), draft = await capture(dist);
    // Compare both key sets: a removed fixture or attempt/step state is a difference too.
    const names = [...new Set([...Object.keys(baseline), ...Object.keys(draft)])];
    const differences = names.flatMap(name => [...new Set([...Object.keys(baseline[name] as object ?? {}), ...Object.keys(draft[name] as object ?? {})])]
      .filter(key => key !== 'checks' && JSON.stringify((draft[name] as any)?.[key]) !== JSON.stringify((baseline[name] as any)?.[key])).map(key => `${name}: ${key}`));
    const openedEverywhere = [...Object.values(baseline), ...Object.values(draft)].every((entries: any) => entries.checks.length > 0 && entries.checks.every((item: Check) => item.ok));
    const compared = Object.values(draft).reduce((n: number, entries: any) => n + Object.keys(entries).filter(key => key.startsWith('attempt')).length, 0);
    report.comparison = { fixtures: rows.map(([name]) => name), comparedStates: compared, differences, openedEverywhere, baseline, draft };
    const scenario = begin('baseline-markup-and-saved-bytes', rows.map(([, row]) => row.label).join('; '), 'retained real corpus and two constructed controls', '1272×900');
    check(scenario, 'every fixture opened in both builds', openedEverywhere);
    check(scenario, `${compared} attempt/step states: source-data markup without the outline and saved bytes equal the baseline build`, differences.length === 0 && compared > 0, differences);
  }
} catch (error) {
  report.summary.error = error instanceof Error ? error.stack ?? error.message : String(error);
} finally {
  await shutdown();
}
const failed = report.scenarios.flatMap(scenario => scenario.checks.filter(item => !item.ok).map(item => `${scenario.name}: ${item.name}`));
Object.assign(report.summary, { finishedAt: new Date().toISOString(), scenarios: report.scenarios.length, checks: report.scenarios.reduce((n, s) => n + s.checks.length, 0), failed,
  baselineComparison: baselineDist ? 'run' : 'skipped: DEFINOGRAPH_BASELINE_DIST not set', consoleErrors: report.consoleErrors.length });
await mkdir(out, { recursive: true });
await writeFile(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report.summary, null, 1));
if (failed.length || report.summary.error || report.consoleErrors.length) process.exitCode = 1;
