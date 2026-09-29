/** Explicit-action result landing: drive a production build in headless Chrome over the DevTools
 * protocol with no extra dependency. A host spy records outgoing messages; the harness answers as the
 * extension does (status `analyzing`, then the recorded result after a delay). Actions are real pointer
 * or keyboard activations of drawer buttons after the reader has scrolled to them. After an answer the
 * harness never scrolls: it reads the drawer position, the answer's visibility below the sticky heading
 * and keyboard focus, and keeps viewport screenshots. Passive results, stale statuses, superseded
 * requests and requests refused before they start must not navigate or move focus.
 * Writes report.json and screenshots to DEFINOGRAPH_NAVIGATION_EVIDENCE_OUT; exits nonzero on failure. */
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { GUIDED_CONTEXT_CONTRACT } from '../src/editor/guided-context-contract.js';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const dist = process.env.DEFINOGRAPH_DIST ?? path.join(root, 'dist');
const chrome = process.env.DEFINOGRAPH_CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const logicalPath = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES, acceptancePath = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
const out = process.env.DEFINOGRAPH_NAVIGATION_EVIDENCE_OUT;
const hostDelay = Number(process.env.DEFINOGRAPH_HOST_DELAY_MS ?? 800);
if (!out || !logicalPath || !acceptancePath) throw new Error('Set DEFINOGRAPH_NAVIGATION_EVIDENCE_OUT, DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES and DEFINOGRAPH_ACCEPTANCE_FIXTURES.');
// The host's own refusal text for a result beyond the retained-history limit (extension/src/extension.ts).
const HISTORY_LIMIT = 'This result exceeds the retained-history limits (16 MiB total). Earlier history is unchanged. Save it and Refresh to start another.';
const DRAWER = 'dialog.atlas-drawer-left';

type Row = any;
type Check = { name: string; ok: boolean; detail?: unknown };
type ScenarioReport = { name: string; kind: 'navigation' | 'guard'; width: number; checks: Check[]; observations: Record<string, unknown>; screenshots: string[] };
const report = { startedAt: new Date().toISOString(), dist, hostDelayMs: hostDelay, scenarios: [] as ScenarioReport[], consoleErrors: [] as string[], summary: {} as Record<string, unknown> };

const types: Record<string, string> = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.svg': 'image/svg+xml', '.json': 'application/json', '.woff2': 'font/woff2', '.woff': 'font/woff', '.ttf': 'font/ttf', '.png': 'image/png' };
const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? '/', 'http://127.0.0.1');
  const file = path.join(dist, url.pathname === '/' ? 'index.html' : url.pathname);
  try { const body = await readFile(file); response.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream' }); response.end(body); }
  catch { response.writeHead(404); response.end(); }
});
await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
const address = server.address();
if (!address || typeof address !== 'object') throw new Error('no server address');
const pageUrl = `http://127.0.0.1:${address.port}/`;
const profile = await mkdtemp(path.join(os.tmpdir(), 'definograph-navigation-'));
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
  await page('Page.addScriptToEvaluateOnNewDocument', { source: `window.__hostMessages = []; window.acquireVsCodeApi = () => ({ postMessage: message => { window.__hostMessages.push(JSON.parse(JSON.stringify(message))); } });` });
  const evaluate = async <T>(expression: string): Promise<T> => {
    const result = await page<{ result: { value: T }; exceptionDetails?: unknown }>('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
    if (result.exceptionDetails) throw new Error(`page evaluation failed: ${JSON.stringify(result.exceptionDetails).slice(0, 400)}`);
    return result.result.value;
  };
  const settle = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));
  const frames = () => evaluate<boolean>('new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve(true))))');
  const hostMessages = () => evaluate<Record<string, unknown>[]>('window.__hostMessages');

  const logical = JSON.parse(await readFile(logicalPath, 'utf8')) as Row[], acceptance = JSON.parse(await readFile(acceptancePath, 'utf8')) as Row[];
  const rowsOf = (rows: Row[], label: string) => { const found = rows.filter(row => row.label === label); if (!found.length) throw new Error(`no corpus rows for ${label}`); return found; };
  const documentOf = (row: Row) => ({ ...row.parent.origin.document, fileName: new URL(row.parent.origin.document.uri).pathname, selection: row.parent.origin.selection });
  const historyOf = (row: Row) => [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }];
  const post = (message: unknown) => evaluate(`window.postMessage(${JSON.stringify(message)}, '*'); true`);
  let requestId = 0;
  const status = (id: number, row: Row, phase: 'analyzing' | 'stale' = 'analyzing') => post({ type: 'statementlens.status', requestId: String(id), phase, document: documentOf(row) });
  // The extension's continuation answer: the parent capture with the retained history (extension.ts refresh).
  const result = (id: number, row: Row, decompositions: unknown[], extra: Record<string, unknown> = {}) => post({ type: 'statementlens.error', guidedContextContract: GUIDED_CONTEXT_CONTRACT, requestId: String(id),
    document: documentOf(row), message: 'Independent guided export unavailable.', sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: row.parent.origin, sourceOccurrence: row.parent.occurrence, decompositions, ...extra });

  async function load(width: number) {
    await page('Emulation.setDeviceMetricsOverride', { width, height: 900, deviceScaleFactor: 1, mobile: width < 700 });
    const loaded = new Promise<void>(resolve => { const listener = (method: string) => { if (method === 'Page.loadEventFired') { listeners.splice(listeners.indexOf(listener), 1); resolve(); } }; listeners.push(listener); });
    await page('Page.navigate', { url: pageUrl }); await loaded; await settle(500);
  }
  async function pointerClick(expression: string, label: string): Promise<boolean> {
    // A reader scrolls the button into view before activating it; this is the only harness scroll.
    const box = await evaluate<{ x: number; y: number } | null>(`(() => { const el = ${expression}; if (!el) return null; el.scrollIntoView({ block: 'center' }); const r = el.getBoundingClientRect(); return { x: r.left + r.width / 2, y: r.top + r.height / 2 }; })()`);
    if (!box) return false;
    await settle(150);
    for (const type of ['mouseMoved', 'mousePressed', 'mouseReleased']) await page('Input.dispatchMouseEvent', { type, x: box.x, y: box.y, button: 'left', clickCount: type === 'mouseMoved' ? 0 : 1 });
    await settle(150);
    return label.length > 0; // the label documents which control a reader activates
  }
  async function keyboardActivate(expression: string): Promise<boolean> {
    const found = await evaluate<boolean>(`(() => { const el = ${expression}; if (!el) return false; el.scrollIntoView({ block: 'center' }); el.focus(); return document.activeElement === el; })()`);
    if (!found) return false;
    await settle(100);
    await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Enter', code: 'Enter', text: '\r', unmodifiedText: '\r', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
    await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
    await settle(150);
    return true;
  }
  const button = (scope: string, text: string) => `[...document.querySelectorAll(${JSON.stringify(`${scope} button`)})].find(el => (el.textContent || '').trim() === ${JSON.stringify(text)})`;
  const state = () => evaluate<Record<string, any>>(`(() => {
    const drawer = document.querySelector(${JSON.stringify(DRAWER)});
    if (!drawer) return { drawerOpen: false };
    const box = drawer.getBoundingClientRect(), heading = drawer.querySelector('.drawer-heading')?.getBoundingClientRect();
    // Answers are found by existing structure and wording, so the unmodified baseline is measured the same way.
    const answers = { attempt: drawer.querySelector('section.source-decomposition > h3'),
      'continuation-unavailable': [...drawer.querySelectorAll('p.snapshot-unavailable')].find(p => (p.textContent || '').startsWith('Continuation data unavailable:')) };
    const answerOf = el => Object.entries(answers).find(([, candidate]) => candidate && candidate === el)?.[0] ?? null;
    const describe = el => el ? { tag: el.tagName, answer: answerOf(el), text: (el.textContent || '').trim().slice(0, 80), insideDrawer: drawer.contains(el), insideAttempt: !!el.closest('section.source-decomposition') } : null;
    if (!drawer.open) return { drawerOpen: false, active: describe(document.activeElement) };
    const attempt = drawer.querySelector('section.source-decomposition [data-decomposition-capture]');
    const selectedStep = attempt?.querySelector('section.continuation-step[data-decomposition-step]');
    const anchors = Object.fromEntries(Object.entries(answers).filter(([, el]) => el).map(([key, el]) => { const r = el.getBoundingClientRect();
      return [key, { top: Math.round(r.top - box.top), bottom: Math.round(r.bottom - box.top), text: (el.textContent || '').trim().slice(0, 80),
        visibleBelowHeading: r.top >= (heading ? heading.bottom : box.top) - 1 && r.bottom <= box.bottom }]; }));
    const headings = [...drawer.querySelectorAll('h3,h4')].map(h => ({ text: h.textContent.trim().slice(0, 60), top: Math.round(h.getBoundingClientRect().top - box.top) }))
      .filter(h => h.top > -40 && h.top < box.height);
    return { drawerOpen: true, scrollTop: Math.round(drawer.scrollTop), clientHeight: drawer.clientHeight, scrollHeight: drawer.scrollHeight,
      captureId: attempt?.getAttribute('data-decomposition-capture') ?? null, stepIndex: selectedStep?.getAttribute('data-decomposition-step') ?? null,
      sourceTab: drawer.querySelector('.source-tabs > button.active')?.textContent?.trim() ?? null,
      headingBottom: heading ? Math.round(heading.bottom - box.top) : null, active: describe(document.activeElement), anchors, headingsInView: headings };
  })()`);
  async function shot(name: string, scenario: ScenarioReport) {
    const image = await page<{ data: string }>('Page.captureScreenshot', { format: 'png' });
    const file = `${scenario.name}-${name}.png`; await writeFile(path.join(out!, file), Buffer.from(image.data, 'base64')); scenario.screenshots.push(file);
  }
  const check = (scenario: ScenarioReport, name: string, ok: boolean, detail?: unknown) => { scenario.checks.push({ name, ok, ...(detail === undefined ? {} : { detail }) }); };
  async function openWith(scenario: ScenarioReport, row: Row) {
    const id = ++requestId; await status(id, row); await settle(150); await result(id, row, historyOf(row)); await settle(700);
    check(scenario, 'passive capture does not open or move the drawer', !(await state()).drawerOpen);
    check(scenario, 'Source data opens by pointer', await pointerClick(button('.statement-actions', 'Source data'), 'Source data'));
    await settle(400);
  }
  const keys = (message: Record<string, unknown>) => Object.keys(message).sort().join(',');
  // Expected commands come from the chosen control and the displayed recorded step, not the emitted message.
  async function checkRequest(scenario: ScenarioReport, sent: number, before: Row, action: 'logical' | 'expose-term' = 'logical') {
    const record = before.response.sourceDecomposition, step = record.checking.steps.at(-1);
    if (!step) throw new Error('Navigation fixture has no executed step');
    const expected: Record<string, unknown> = { type: action === 'logical' ? 'statementlens.inspectLogicalStructure' : 'statementlens.exposeFocusedHead',
      parentCaptureId: before.parent.origin.captureId, previousCaptureId: record.captureId, parentStepIndex: step.index,
      ...(action === 'expose-term' ? { target: 'term' } : {}) };
    const posted = (await hostMessages()).slice(sent);
    check(scenario, 'exactly one command with the expected type, payload and parent step', posted.length === 1 && keys(posted[0]) === keys(expected)
      && Object.entries(expected).every(([key, value]) => posted[0][key] === value), { posted, expected });
  }
  function checkSelected(scenario: ScenarioReport, observed: Record<string, any>, row: Row) {
    const record = row.response.sourceDecomposition, step = record.checking.steps.at(-1);
    if (!step) throw new Error('Navigation fixture has no executed step');
    check(scenario, 'selected capture and executed step equal the returned record', observed.captureId === record.captureId && observed.stepIndex === String(step.index),
      { actual: { captureId: observed.captureId, stepIndex: observed.stepIndex }, expected: { captureId: record.captureId, stepIndex: step.index } });
  }

  /** One explicit action answered by the host; the answer must be shown and focused without harness scrolling. */
  async function navigation(name: string, width: number, rows: Row[], beforeIndex: number, buttonText: string, activation: 'pointer' | 'keyboard',
    expectedAnchor: string, answer: 'recorded' | 'history-limit', action: 'logical' | 'expose-term' = 'logical') {
    const scenario: ScenarioReport = { name, kind: 'navigation', width, checks: [], observations: {}, screenshots: [] };
    report.scenarios.push(scenario);
    const before = rows[beforeIndex], next = rows[beforeIndex + 1];
    await load(width); await openWith(scenario, before);
    const sent = (await hostMessages()).length;
    const target = button('section.continuation-step', buttonText);
    const activated = activation === 'pointer' ? await pointerClick(target, buttonText) : await keyboardActivate(target);
    check(scenario, `activates "${buttonText}" by ${activation}`, activated);
    await checkRequest(scenario, sent, before, action);
    scenario.observations.beforeAnswer = await state(); await shot('before-answer', scenario);
    const id = ++requestId; await status(id, before); await frames();
    scenario.observations.analyzing = await state(); await shot('analyzing', scenario);
    await settle(hostDelay);
    if (answer === 'recorded') await result(id, before, historyOf(next));
    else await result(id, before, historyOf(before), { decompositionUnavailable: HISTORY_LIMIT });
    await frames(); await settle(300);
    const after = scenario.observations.afterAnswer = await state();
    await shot('after-answer', scenario);
    checkSelected(scenario, after, answer === 'recorded' ? next : before);
    const anchor = after.anchors?.[expectedAnchor];
    check(scenario, `answer "${expectedAnchor}" is present`, !!anchor, anchor);
    check(scenario, 'answer is visible below the sticky drawer heading without harness scrolling', !!anchor?.visibleBelowHeading, { anchor, scrollTop: after.scrollTop, headingBottom: after.headingBottom });
    check(scenario, 'keyboard focus is on the answer inside the drawer', after.active?.answer === expectedAnchor && after.active?.insideDrawer === true, after.active);
    check(scenario, 'no request follows the answer', (await hostMessages()).length === sent + 1);
    // Keyboard continuity: the next Tab stop follows the answer inside the drawer.
    await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9, nativeVirtualKeyCode: 9 });
    await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9, nativeVirtualKeyCode: 9 }); await settle(150);
    const afterTab = scenario.observations.afterTab = (await state()).active;
    check(scenario, 'Tab moves to a control inside the drawer after the answer', afterTab?.insideDrawer === true && afterTab.answer === null
      && ['BUTTON', 'A', 'INPUT', 'SELECT', 'TEXTAREA', 'SUMMARY'].includes(afterTab.tag)
      && (expectedAnchor !== 'attempt' || afterTab.insideAttempt === true), afterTab);
    check(scenario, 'Tab posts no host request', (await hostMessages()).length === sent + 1);
  }

  /** A result that is not the answer to a pending action must neither navigate nor take focus. */
  async function guard(name: string, width: number, rows: Row[], beforeIndex: number, flow: 'passive' | 'stale' | 'superseded' | 'refused-before-start', other: Row) {
    const scenario: ScenarioReport = { name, kind: 'guard', width, checks: [], observations: { flow }, screenshots: [] };
    report.scenarios.push(scenario);
    const before = rows[beforeIndex], next = rows[beforeIndex + 1];
    await load(width); await openWith(scenario, before);
    const sent = (await hostMessages()).length;
    if (flow === 'passive') {
      // An inspection-only click: selecting an earlier step posts nothing.
      check(scenario, 'reader selects step 1', await pointerClick(`document.querySelectorAll('ol.continuation-steps button')[0]`, 'step 1'));
      check(scenario, 'selecting a step posts no request', (await hostMessages()).length === sent);
      const selected = await state();
      check(scenario, 'passive control selected the first step of the displayed capture', selected.captureId === before.response.sourceDecomposition.captureId && selected.stepIndex === '0', selected);
      const id = ++requestId; await status(id, other); await settle(hostDelay); await result(id, other, historyOf(other));
    } else {
      check(scenario, 'activates Read logical structure', await pointerClick(button('section.continuation-step', 'Read logical structure of this term (one layer)'), 'logical'));
      await checkRequest(scenario, sent, before);
      if (flow === 'stale') {
        const id = ++requestId; await status(id, before); await settle(200); await status(id, before, 'stale'); await settle(hostDelay);
        const afterStale = await state();
        await result(id, before, historyOf(next)); // late answer after the capture became stale: rejected by the view
        await frames(); await settle(300);
        const afterLate = scenario.observations.afterLate = await state(); await shot('after-late-answer', scenario);
        check(scenario, 'late stale answer remains absent before any unrelated capture', afterLate.captureId === null && !afterLate.anchors?.attempt, afterLate);
        check(scenario, 'late stale answer takes no focus or scroll position', !afterLate.active?.answer && afterLate.scrollTop === afterStale.scrollTop, { afterStale, afterLate });
        const later = ++requestId; await status(later, other); await settle(200); await result(later, other, historyOf(other));
      } else if (flow === 'superseded') {
        const id = ++requestId; await status(id, before); await settle(200);
        const newer = ++requestId; await status(newer, before); await settle(hostDelay);
        await result(newer, before, historyOf(next)); // content that would answer the action, under a newer request
      } else {
        // The host refused before starting (no message reaches the view), then an unrelated capture arrives.
        await settle(hostDelay); const id = ++requestId; await status(id, other); await settle(hostDelay); await result(id, other, historyOf(other));
      }
    }
    await frames(); await settle(300);
    const after = scenario.observations.after = await state(); await shot('after', scenario);
    check(scenario, 'focus is not moved to a result', !after.active?.answer, after.active);
    check(scenario, 'drawer is not navigated to a result', after.scrollTop === 0, { scrollTop: after.scrollTop });
    checkSelected(scenario, after, flow === 'superseded' ? next : other);
    check(scenario, 'guard delivery posts no additional request', (await hostMessages()).length === sent + (flow === 'passive' ? 0 : 1));
  }

  /** A reader can dismiss the drawer or choose another source tab while the requested work is pending. */
  async function dismissal(name: string, width: number, rows: Row[], beforeIndex: number, control: 'escape' | 'source-tab') {
    const scenario: ScenarioReport = { name, kind: 'guard', width, checks: [], observations: { control }, screenshots: [] };
    report.scenarios.push(scenario);
    const before = rows[beforeIndex], next = rows[beforeIndex + 1];
    await load(width); await openWith(scenario, before);
    const sent = (await hostMessages()).length;
    check(scenario, 'activates the pending logical action', await pointerClick(button('section.continuation-step', 'Read logical structure of this term (one layer)'), 'logical'));
    await checkRequest(scenario, sent, before);
    const id = ++requestId; await status(id, before); await frames(); await settle(200);
    if (control === 'escape') {
      await page('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Escape', code: 'Escape', windowsVirtualKeyCode: 27, nativeVirtualKeyCode: 27 });
      await page('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Escape', code: 'Escape', windowsVirtualKeyCode: 27, nativeVirtualKeyCode: 27 });
    } else check(scenario, 'activates the Source tab', await pointerClick(button(`${DRAWER} .source-tabs`, 'Source'), 'Source tab'));
    await frames(); await settle(150);
    const dismissed = scenario.observations.dismissed = await state();
    check(scenario, 'the dismissal control took effect', control === 'escape' ? dismissed.drawerOpen === false : dismissed.drawerOpen === true && dismissed.sourceTab === 'Source', dismissed);
    await evaluate('window.__navigationGuardFocus = document.activeElement; true');
    await settle(hostDelay); await result(id, before, historyOf(next)); await frames(); await settle(300);
    const after = scenario.observations.afterAnswer = await state(); await shot('after-answer', scenario);
    check(scenario, 'answer preserves the closed drawer or selected Source tab', control === 'escape' ? after.drawerOpen === false : after.drawerOpen === true && after.sourceTab === 'Source', after);
    check(scenario, 'answer preserves focus after dismissal', await evaluate<boolean>('document.activeElement === window.__navigationGuardFocus') && !after.active?.answer, after.active);
    check(scenario, 'dismissal and answer post no additional request', (await hostMessages()).length === sent + 1);
    check(scenario, 'reader reopens Source data', await pointerClick(button(control === 'escape' ? '.statement-actions' : `${DRAWER} .source-tabs`, 'Source data'), 'Source data'));
    await frames(); await settle(250);
    const reopened = scenario.observations.reopened = await state(); await shot('reopened', scenario);
    checkSelected(scenario, reopened, next);
    check(scenario, 'reopening does not replay the old focus landing', reopened.drawerOpen === true && reopened.sourceTab === 'Source data' && !reopened.active?.answer, reopened.active);
    check(scenario, 'reopening posts no host request', (await hostMessages()).length === sent + 1);
    await evaluate('delete window.__navigationGuardFocus; true');
  }

  /** An accepted request can fail before any record exists; show the real host error in the open drawer. */
  async function inFlightError(before: Row, other: Row) {
    const scenario: ScenarioReport = { name: 'in-flight-error-400', kind: 'guard', width: 400, checks: [], observations: {}, screenshots: [] };
    report.scenarios.push(scenario);
    // Exact extension/src/extension.ts engine-change refusal; no fabricated source record accompanies it.
    const message = 'The configured engine changed. Run Definograph: Visualize Selection again to load its matching interface.';
    await load(scenario.width); await openWith(scenario, before);
    const sent = (await hostMessages()).length;
    check(scenario, 'activates the action that will fail in flight', await pointerClick(button('section.continuation-step', 'Read logical structure of this term (one layer)'), 'logical'));
    await checkRequest(scenario, sent, before);
    const id = ++requestId; await status(id, before); await settle(hostDelay);
    await post({ type: 'statementlens.error', requestId: String(id), document: documentOf(before), message });
    await frames(); await settle(300);
    const failure = await evaluate<Record<string, any>>(`(() => { const drawer = document.querySelector(${JSON.stringify(DRAWER)});
      const alert = drawer?.querySelector('.error-box[role="alert"]'), rect = alert?.getBoundingClientRect(), box = drawer?.getBoundingClientRect();
      const heading = drawer?.querySelector('.drawer-heading')?.getBoundingClientRect();
      return { open: drawer?.open, text: alert?.textContent?.trim() ?? null,
        visible: !!rect && !!box && rect.height > 0 && rect.top >= (heading?.bottom ?? box.top) - 1 && rect.bottom <= box.bottom }; })()`);
    scenario.observations.failure = failure; await shot('host-error', scenario);
    check(scenario, 'exact host error is visible inside the open source drawer', failure.open === true && failure.text === message && failure.visible === true, failure);
    check(scenario, 'an error without a record does not focus a result', !(await state()).active?.answer);
    const fresh = ++requestId; await status(fresh, other); await frames(); await settle(150);
    const noOldAlert = () => evaluate<boolean>(`${JSON.stringify(message)} !== document.querySelector(${JSON.stringify(`${DRAWER} .error-box[role="alert"]`)})?.textContent?.trim()`);
    check(scenario, 'the next analyzing status clears the old alert', await noOldAlert());
    await result(fresh, other, historyOf(other)); await frames(); await settle(300);
    check(scenario, 'the fresh capture does not retain the old alert', await noOldAlert());
    checkSelected(scenario, await state(), other);
    check(scenario, 'error and fresh capture post no additional host request', (await hostMessages()).length === sent + 1);
  }

  await mkdir(out, { recursive: true });
  const rotor = rowsOf(logical, 'literal Rotor law'), negated = rowsOf(logical, 'negated owner'), stopped = rowsOf(acceptance, 'inductive predicate head');
  const unrelated = rowsOf(logical, 'ordinary function type').at(-1);
  await navigation('success-pointer-1272', 1272, rotor, 2, 'Read logical structure of this term (one layer)', 'pointer', 'attempt', 'recorded');
  await navigation('success-keyboard-400', 400, negated, 4, 'Read logical structure of this term (one layer)', 'keyboard', 'attempt', 'recorded');
  await navigation('stopped-pointer-1272', 1272, stopped, 0, 'Expose definition head of term', 'pointer', 'attempt', 'recorded', 'expose-term');
  await navigation('history-limit-pointer-1272', 1272, rotor, 2, 'Read logical structure of this term (one layer)', 'pointer', 'continuation-unavailable', 'history-limit');
  await guard('passive-1272', 1272, rotor, 2, 'passive', unrelated);
  await guard('stale-1272', 1272, rotor, 2, 'stale', unrelated);
  await guard('superseded-1272', 1272, rotor, 2, 'superseded', unrelated);
  await guard('refused-before-start-400', 400, negated, 4, 'refused-before-start', unrelated);
  await dismissal('pending-escape-400', 400, negated, 4, 'escape');
  await dismissal('pending-source-tab-1272', 1272, rotor, 2, 'source-tab');
  await inFlightError(negated[4], unrelated);
} catch (error) {
  report.summary.error = error instanceof Error ? error.stack ?? error.message : String(error);
} finally {
  await shutdown();
}
const failed = report.scenarios.flatMap(scenario => scenario.checks.filter(check => !check.ok).map(check => `${scenario.name}: ${check.name}`));
Object.assign(report.summary, { finishedAt: new Date().toISOString(), scenarios: report.scenarios.length, checks: report.scenarios.reduce((n, s) => n + s.checks.length, 0), failed, consoleErrors: report.consoleErrors.length });
await mkdir(out, { recursive: true });
await writeFile(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report.summary, null, 1));
if (failed.length || report.summary.error || report.consoleErrors.length) process.exitCode = 1;
