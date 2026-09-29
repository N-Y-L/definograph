/* RC5 Extension Development Host journey. Runs inside a real VS Code extension
 * host (--extensionTestsPath). It opens the private Lean project, selects the
 * expression, runs the real command, and observes the real extension: the
 * webview panel it creates is wrapped so every message the extension posts to
 * the webview is recorded. Inspection requests are actual DOM clicks through
 * the live React UI and webview bridge, observed at the registered listener.
 * Setup, refusal, cancellation and refresh controls retain handler injection.
 * The real engine runs Lean for each accepted native request. Neither the
 * application callbacks nor its VS Code bridge are replaced. */
'use strict';
const vscode = require('vscode');
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const childProcess = require('node:child_process');

const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
async function waitFor(predicate, timeoutMs, label) {
  const started = Date.now();
  while (Date.now() - started < timeoutMs) { const value = predicate(); if (value) return value; await sleep(100); }
  throw new Error(`timed out waiting for ${label}`);
}

// Connect only to this launcher's isolated Electron debugger. Find the actual
// app document through its DOM; neither the React callbacks nor the VS Code
// bridge are replaced. Same-process frames and OOPIFs both have to be inspected.
async function connectJourneyWebview(port, record) {
  assert.ok(Number.isInteger(port) && port > 0 && port < 65536, 'isolated debugger port');
  assert.equal(typeof fetch, 'function', 'extension host needs global fetch');
  assert.equal(typeof WebSocket, 'function', 'extension host needs global WebSocket');
  const response = await fetch(`http://127.0.0.1:${port}/json/version`, { signal: AbortSignal.timeout(5000) });
  assert.ok(response.ok, 'isolated debugger responds');
  const endpoint = new URL((await response.json()).webSocketDebuggerUrl);
  assert.ok(['127.0.0.1', 'localhost', '[::1]'].includes(endpoint.hostname) && Number(endpoint.port) === port,
    'debugger websocket stays on the reserved localhost port');
  const socket = new WebSocket(endpoint.href), pending = new Map(), sessions = new Map(), contexts = new Map();
  let nextId = 0, stopped = false;
  const rejectPending = error => {
    for (const waiter of pending.values()) { clearTimeout(waiter.timer); waiter.reject(error); }
    pending.clear();
  };
  socket.addEventListener('close', () => { stopped = true; rejectPending(new Error('isolated debugger closed')); });
  socket.addEventListener('error', () => rejectPending(new Error('isolated debugger socket failed')));
  socket.addEventListener('message', event => {
    const message = JSON.parse(String(event.data));
    if (message.id !== undefined) {
      const waiter = pending.get(message.id);
      if (!waiter) return;
      pending.delete(message.id); clearTimeout(waiter.timer);
      message.error ? waiter.reject(new Error(`${waiter.method}: ${message.error.message}`)) : waiter.resolve(message.result);
    } else if (message.method === 'Runtime.executionContextCreated') {
      const context = message.params.context;
      if (context.auxData?.isDefault !== false) contexts.set(`${message.sessionId}:${context.id}`, { sessionId: message.sessionId, ...context });
    } else if (message.method === 'Runtime.executionContextDestroyed') {
      contexts.delete(`${message.sessionId}:${message.params.executionContextId}`);
    } else if (message.method === 'Runtime.executionContextsCleared' || message.method === 'Target.detachedFromTarget') {
      const sessionId = message.method === 'Target.detachedFromTarget' ? message.params.sessionId : message.sessionId;
      for (const [key, context] of contexts) if (context.sessionId === sessionId) contexts.delete(key);
      if (message.method === 'Target.detachedFromTarget') for (const [targetId, attached] of sessions) if (attached.sessionId === sessionId) sessions.delete(targetId);
    }
  });
  function send(method, params = {}, sessionId, timeoutMs = 10000) {
    if (stopped) return Promise.reject(new Error('isolated debugger is closed'));
    return new Promise((resolve, reject) => {
      const id = ++nextId;
      const timer = setTimeout(() => { pending.delete(id); reject(new Error(`CDP deadline: ${method}`)); }, timeoutMs);
      pending.set(id, { resolve, reject, timer, method });
      try { socket.send(JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) })); }
      catch (error) { pending.delete(id); clearTimeout(timer); reject(error); }
    });
  }
  async function close() {
    if (!stopped) await Promise.allSettled([...sessions.values()].map(session => send('Target.detachFromTarget', { sessionId: session.sessionId }, undefined, 1000)));
    stopped = true; rejectPending(new Error('journey debugger cleanup')); sessions.clear(); contexts.clear();
    if (socket.readyState !== WebSocket.CLOSED) await new Promise(resolve => {
      const timer = setTimeout(resolve, 1000);
      socket.addEventListener('close', () => { clearTimeout(timer); resolve(); }, { once: true });
      socket.close();
    });
  }
  try {
    await new Promise((resolve, reject) => {
      const finish = error => {
        clearTimeout(timer); socket.removeEventListener('open', opened); socket.removeEventListener('close', closed); socket.removeEventListener('error', failed);
        error ? reject(error) : resolve();
      };
      const opened = () => finish(), closed = () => finish(new Error('isolated debugger closed before opening')), failed = () => finish(new Error('isolated debugger connection failed'));
      const timer = setTimeout(() => finish(new Error('isolated debugger connection deadline')), 10000);
      socket.addEventListener('open', opened); socket.addEventListener('close', closed); socket.addEventListener('error', failed);
    });
    await send('Target.setDiscoverTargets', { discover: true });
    const transient = error => /Cannot find context|Execution context was destroyed|Cannot find default execution context|No target with given id|No session with given id|Session with given id not found|Target closed/i.test(String(error));
    const remaining = deadline => { const value = deadline - Date.now(); if (value <= 0) throw new Error('webview discovery deadline'); return Math.min(value, 10000); };
    async function discover(deadline) {
      const { targetInfos } = await send('Target.getTargets', {}, undefined, remaining(deadline));
      for (const target of targetInfos) {
        if (!['page', 'iframe', 'webview'].includes(target.type) || sessions.has(target.targetId)) continue;
        let attached;
        try {
          attached = (await send('Target.attachToTarget', { targetId: target.targetId, flatten: true }, undefined, remaining(deadline))).sessionId;
          await send('Runtime.enable', {}, attached, remaining(deadline));
          sessions.set(target.targetId, { sessionId: attached, target });
        } catch (error) {
          if (attached) {
            for (const [key, context] of contexts) if (context.sessionId === attached) contexts.delete(key);
            await send('Target.detachFromTarget', { sessionId: attached }, undefined, Math.max(1, Math.min(1000, deadline - Date.now()))).catch(() => undefined);
          }
          if (!transient(error)) throw error;
        }
      }
    }
    async function evaluate(context, expression, deadline) {
      const identity = context.uniqueId ? { uniqueContextId: context.uniqueId } : { contextId: context.id };
      const result = await send('Runtime.evaluate', { expression, ...identity, returnByValue: true, awaitPromise: true }, context.sessionId, remaining(deadline));
      if (result.exceptionDetails) throw new Error(`webview DOM evaluation: ${JSON.stringify(result.exceptionDetails)}`);
      return result.result.value;
    }
    const productProbe = `(() => typeof document !== 'undefined' && !!document.querySelector('.brand[aria-label="Definograph home"]') && [...document.querySelectorAll('.statement-actions button.toolbar-button')].some(button => button.textContent.trim() === 'Source data'))()`;
    async function inProduct(expression, label, action = false) {
      const deadline = Date.now() + 30000;
      while (Date.now() < deadline) {
        await discover(deadline);
        const found = [];
        for (const context of contexts.values()) {
          try { if (await evaluate(context, productProbe, deadline)) found.push(context); }
          catch (error) { if (!transient(error)) throw error; }
        }
        assert.ok(found.length <= 1, `${label}: one Definograph app document in the isolated host`);
        if (found.length === 1) {
          try { const value = await evaluate(found[0], expression, deadline); if (value) return value; }
          // A failed reply may follow a click that already ran. Fail this test
          // rather than retrying a possibly executed native request.
          catch (error) { if (action || !transient(error)) throw error; }
        }
        await sleep(100);
      }
      throw new Error(`timed out locating ${label}; targets=${JSON.stringify([...sessions.values()].map(item => ({ type: item.target.type, url: item.target.url })))}; contexts=${contexts.size}`);
    }
    async function openSourceData() {
      return inProduct(`(() => {
        if (document.querySelector('section.source-snapshot')) return true;
        const buttons = [...document.querySelectorAll('.statement-actions button.toolbar-button')].filter(button => button.textContent.trim() === 'Source data' && !button.disabled);
        if (buttons.length !== 1) return false;
        buttons[0].click(); return true;
      })()`, 'Source data drawer');
    }
    async function click(label, selector, guard) {
      await openSourceData();
      return inProduct(`(() => {
        if (!(${productProbe})) return false;
        if (${JSON.stringify(guard ?? '')} && !document.querySelector(${JSON.stringify(guard ?? '')})) return false;
        const accessibleName = button => button.getAttribute('aria-label') || (button.getAttribute('aria-labelledby') || '').split(/\\s+/).filter(Boolean).map(id => document.getElementById(id)?.textContent || '').join(' ') || button.textContent;
        const buttons = [...document.querySelectorAll(${JSON.stringify(selector)})].filter(button => accessibleName(button).replace(/\\s+/g, ' ').trim() === ${JSON.stringify(label)} && !button.disabled && button.getClientRects().length && getComputedStyle(button).visibility !== 'hidden');
        if (buttons.length !== 1) return false;
        buttons[0].click(); return { label: ${JSON.stringify(label)}, selector: ${JSON.stringify(selector)}, location: location.href };
      })()`, `enabled button ${label}`, true);
    }
    record('attached isolated webview debugger', { port, runtime: process.versions });
    return { click, openSourceData, close };
  } catch (error) { await close(); throw error; }
}

exports.run = async function run() {
  const out = process.env.DEFINOGRAPH_JOURNEY_OUT;
  const journal = { startedAt: new Date().toISOString(), vscode: vscode.version, steps: [], outgoing: [], incoming: [], blockers: [], nativeProcesses: [] };
  const record = (step, data = {}) => journal.steps.push({ at: new Date().toISOString(), step, ...data });
  const finish = async () => { journal.finishedAt = new Date().toISOString(); fs.writeFileSync(out, JSON.stringify(journal, null, 2) + '\n'); };
  let webviewDriver;
  const originalSpawn = childProcess.spawn, originalCreate = vscode.window.createWebviewPanel, originalError = vscode.window.showErrorMessage;
  try {
    // Observe actual engine starts without replacing execution or changing its input.
    childProcess.spawn = function (executable, ...args) {
      const child = originalSpawn.call(childProcess, executable, ...args);
      if (executable === process.env.DEFINOGRAPH_JOURNEY_ENGINE_EXECUTABLE) {
        const status = [...journal.outgoing].reverse().find(item => item.message.type === 'statementlens.status' && item.message.phase === 'analyzing');
        const entry = { requestId: status?.message.requestId, pid: child.pid, executable, startedAt: new Date().toISOString() };
        journal.nativeProcesses.push(entry);
        child.on('exit', (code, signal) => Object.assign(entry, { exitCode: code, exitSignal: signal, finishedAt: new Date().toISOString() }));
        child.on('error', error => Object.assign(entry, { error: String(error), finishedAt: new Date().toISOString() }));
      }
      return child;
    };
    // Observe the real panel: record what the extension posts and capture the handler it registers for webview messages.
    let panel, handler;
    const outgoing = journal.outgoing, incoming = journal.incoming;
    vscode.window.createWebviewPanel = function (...args) {
      panel = originalCreate.apply(vscode.window, args);
      const originalPost = panel.webview.postMessage.bind(panel.webview);
      panel.webview.postMessage = message => { outgoing.push({ at: new Date().toISOString(), message: JSON.parse(JSON.stringify(message)) }); return originalPost(message); };
      const originalOn = panel.webview.onDidReceiveMessage.bind(panel.webview);
      panel.webview.onDidReceiveMessage = (listener, ...rest) => {
        handler = listener; // Existing injected controls remain distinguishable from bridge traffic.
        return originalOn(function (message) {
          incoming.push({ at: new Date().toISOString(), message: JSON.parse(JSON.stringify(message)) });
          return listener.call(this, message);
        }, ...rest);
      };
      return panel;
    };
    const refusals = journal.refusals = [];
    vscode.window.showErrorMessage = (message, ...rest) => { refusals.push({ at: new Date().toISOString(), message: String(message) }); return originalError.call(vscode.window, message, ...rest); };
    const patched = vscode.window.createWebviewPanel !== originalCreate;
    record('patch panel factory', { patched });
    const folder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    if (!folder) throw new Error('no workspace folder');
    const file = path.join(folder, 'Main.lean');
    const document = await vscode.workspace.openTextDocument(file);
    let editor = await vscode.window.showTextDocument(document, { viewColumn: vscode.ViewColumn.One, preserveFocus: false });
    const target = process.env.DEFINOGRAPH_JOURNEY_SELECT || 'owner';
    const text = document.getText(), index = text.lastIndexOf(target);
    if (index < 0) throw new Error('selection target missing');
    editor.selection = new vscode.Selection(document.positionAt(index), document.positionAt(index + target.length));
    if (!vscode.workspace.isTrusted) {
      record('awaiting workspace trust', { folder, trusted: false });
      fs.writeFileSync(out, JSON.stringify(journal, null, 2) + '\n');
      const commands = await vscode.commands.getCommands(true);
      if (commands.includes('workbench.trust.manage')) await vscode.commands.executeCommand('workbench.trust.manage');
    }
    await waitFor(() => vscode.workspace.isTrusted, Number(process.env.DEFINOGRAPH_JOURNEY_TRUST_TIMEOUT_MS || 120000), 'normal Workspace Trust approval for the private fixture');
    const rangeData = selection => ({ start: { line: selection.start.line, character: selection.start.character }, end: { line: selection.end.line, character: selection.end.character } });
    const selectText = async textToSelect => {
      const offset = document.getText().lastIndexOf(textToSelect);
      assert.ok(offset >= 0, 'requested source text exists');
      const selection = new vscode.Selection(document.positionAt(offset), document.positionAt(offset + textToSelect.length));
      // A preceding editor switch can still be reaching the extension host.
      // Always request the source editor and selection together, then reacquire
      // the active handle instead of waiting on a previously returned object.
      await vscode.window.showTextDocument(document, { viewColumn: vscode.ViewColumn.One, preserveFocus: false, selection });
      try {
        editor = await waitFor(() => {
          const active = vscode.window.activeTextEditor;
          return active?.document === document && active.selection.isEqual(selection) ? active : undefined;
        }, 10000, 'the restored editor and exact selection');
      } catch (error) {
        const describeEditor = candidate => candidate ? { file: candidate.document.fileName, viewColumn: candidate.viewColumn, selection: rangeData(candidate.selection) } : null;
        record('source selection restoration failed', { requested: rangeData(selection), sourceFile: document.fileName,
          active: describeEditor(vscode.window.activeTextEditor), visible: vscode.window.visibleTextEditors.map(describeEditor) });
        throw error;
      }
      assert.equal(document.getText(editor.selection), textToSelect);
      return rangeData(selection);
    };
    // The trust page may have focus; restore this test editor and exact selection.
    const expectedSelection = await selectText(target);
    const selectedText = document.getText(editor.selection);
    record('open and select', { languageId: document.languageId, trusted: vscode.workspace.isTrusted, version: document.version, selection: selectedText, range: { start: editor.selection.start, end: editor.selection.end } });
    assert.equal(selectedText, target, 'the active editor must select the requested source text');
    assert.equal(document.languageId, 'lean4', 'Lean 4 language must be active');
    assert.ok(vscode.workspace.isTrusted, 'normal Workspace Trust must admit this fixture');
    await vscode.commands.executeCommand('statementLens.visualizeSelection');
    await waitFor(() => panel && handler, 30000, 'the extension to create its webview panel');
    record('command ran', { panelCreated: !!panel, handlerCaptured: !!handler, extensionUsedWrappedPanel: outgoing.length > 0 });
    const posted = () => outgoing.map(item => item.message);
    const latestOf = (type, requestId) => [...posted()].reverse().find(m => m.type === type && (requestId === undefined || m.requestId === requestId));
    const awaitResult = async (requestId, label, timeoutMs = 180000) => waitFor(() => latestOf('statementlens.analysis', requestId) || latestOf('statementlens.error', requestId), timeoutMs, label);
    // The real webview loads dist/index.html and sends ready itself; wait for the first result it triggers.
    const first = await waitFor(() => posted().find(m => m.type === 'statementlens.analysis' || m.type === 'statementlens.error'), 240000, 'the first analysis from the real webview handshake');
    record('first result', { type: first.type, requestId: first.requestId, hasSnapshot: !!first.sourceSnapshot, hasOrigin: !!first.sourceSnapshotOrigin, message: first.message, code: first.code });
    assert.deepEqual(first.document.selection, expectedSelection, 'initial native analysis uses the selected source range');
    if (!first.sourceSnapshot || !first.sourceSnapshotOrigin) { journal.blockers.push(`first result carried no source capture: ${first.message || first.type}`); await finish(); return; }
    assert.ok(incoming.some(item => item.message.type === 'statementlens.ready'), 'ready was observed through the real webview bridge');
    webviewDriver = await connectJourneyWebview(Number(process.env.DEFINOGRAPH_JOURNEY_CDP_PORT), record);
    const parentCaptureId = first.sourceSnapshotOrigin.captureId;
    const requestIdOf = () => String(Math.max(...posted().filter(m => m.type === 'statementlens.status' && m.phase === 'analyzing').map(m => Number(m.requestId))));
    const send = async (message, label, expectedNative = 1) => {
      const before = posted().length;
      await handler(message);
      await waitFor(() => posted().length > before, 30000, `status for ${label}`);
      const starts = posted().slice(before).filter(m => m.type === 'statementlens.status' && m.phase === 'analyzing');
      assert.equal(starts.length, 1, `${label}: exactly one analysis request`);
      const requestId = starts[0].requestId;
      const result = await awaitResult(requestId, label);
      assert.equal(journal.nativeProcesses.filter(p => p.requestId === requestId).length, expectedNative, `${label}: native process count`);
      return { requestId, result };
    };
    // These inspection requests originate only from actual React button clicks.
    // The observer below is the extension's registered bridge listener, not an
    // injected postMessage implementation or a replacement application callback.
    const clickInspection = async (message, label, buttonLabel, selector, guard) => {
      panel.reveal(panel.viewColumn, true);
      const beforeSetup = journal.nativeProcesses.length;
      await webviewDriver.openSourceData();
      assert.equal(journal.nativeProcesses.length, beforeSetup, `${label}: opening Source data starts no process`);
      const before = posted().length, beforeIncoming = incoming.length, beforeNative = journal.nativeProcesses.length;
      const click = await webviewDriver.click(buttonLabel, selector, guard);
      await waitFor(() => incoming.length > beforeIncoming, 30000, `actual webview message for ${label}`);
      assert.deepEqual(incoming.slice(beforeIncoming).map(item => item.message), [message], `${label}: one actual message with the expected capture fields`);
      assert.deepEqual(Object.keys(incoming[beforeIncoming].message).sort(), ['parentCaptureId', 'parentStepIndex', 'previousCaptureId', 'type'], `${label}: exactly four command keys`);
      await waitFor(() => posted().slice(before).some(m => m.type === 'statementlens.status' && m.phase === 'analyzing'), 30000, `status for clicked ${label}`);
      const starts = posted().slice(before).filter(m => m.type === 'statementlens.status' && m.phase === 'analyzing');
      assert.equal(starts.length, 1, `${label}: exactly one analysis request`);
      const requestId = starts[0].requestId, result = await awaitResult(requestId, label);
      await sleep(250);
      assert.equal(journal.nativeProcesses.filter(process => process.requestId === requestId).length, 1, `${label}: one native process for this request`);
      assert.equal(journal.nativeProcesses.length, beforeNative + 1, `${label}: no extra native process`);
      assert.deepEqual(incoming.slice(beforeIncoming).map(item => item.message), [message], `${label}: no extra bridge command`);
      assert.equal(posted().slice(before).filter(m => m.type === 'statementlens.status' && m.phase === 'analyzing').length, 1, `${label}: no extra analysis request`);
      record('inspection DOM click', { label, click, message, requestId, nativeProcessesStarted: 1 });
      return { requestId, result };
    };
    const summarize = (result) => ({ type: result.type, requestId: result.requestId, message: result.message, code: result.code,
      occurrence: result.sourceOccurrence ? { captureId: result.sourceOccurrence.captureId, status: result.sourceOccurrence.checking?.status, action: result.sourceOccurrence.checking?.action?.status, checks: result.sourceOccurrence.checking?.checks?.length } : undefined,
      occurrenceUnavailable: result.sourceOccurrenceUnavailable,
      decompositions: result.decompositions ? result.decompositions.map(b => ({ captureId: b.record.captureId, previousCaptureId: b.record.previousCaptureId, parentStepIndex: b.record.parentStepIndex, operations: b.record.operations.map(o => o.kind + (o.path ? ':' + o.path.join('/') : o.index !== undefined ? ':' + o.index : '')), steps: b.record.checking?.steps?.map(s => `${s.replay}:${s.output?.status}`), stop: b.record.checking?.stop })) : undefined,
      decompositionUnavailable: result.decompositionUnavailable });
    // 1. Check the selected occurrence (whole selected term).
    let step = await send({ type: 'statementlens.checkOccurrence', parentCaptureId, path: [] }, 'check occurrence');
    record('check occurrence', summarize(step.result));
    const occurrence = step.result.sourceOccurrence; if (!occurrence) { journal.blockers.push('no source occurrence'); await finish(); return; }
    assert.equal(occurrence.checking.action.status, 'completed');
    const continuationParent = occurrence.captureId;
    // 2. Continuations: fields, project law, type component, logical structure, focus body, backtrack to domain.
    let previous = occurrence.captureId, stepIndex = 0, attemptCount = 0;
    const continuation = async (operation, label) => {
      const base = { parentCaptureId: continuationParent, previousCaptureId: previous, parentStepIndex: stepIndex };
      const message = operation.kind === 'fields' ? { type: 'statementlens.inspectFields', ...base } : operation.kind === 'project' ? { type: 'statementlens.projectField', ...base, index: operation.index }
        : operation.kind === 'typeComponent' ? { type: 'statementlens.inspectTypeComponent', ...base } : operation.kind === 'logical' ? { type: 'statementlens.inspectLogicalStructure', ...base }
          : { type: 'statementlens.focusExposedPart', ...base, path: operation.path };
      const outcome = operation.kind === 'typeComponent' || operation.kind === 'logical'
        ? await clickInspection(message, label, operation.kind === 'typeComponent' ? 'Inspect type of this term' : 'Read logical structure of this term (one layer)',
          'section.continuation-step button', `[data-decomposition-capture="${previous}"] [data-decomposition-step="${stepIndex}"]`)
        : await send(message, label);
      record(label, summarize(outcome.result));
      const last = outcome.result.decompositions?.at(-1);
      assert.equal(outcome.result.decompositions?.length, ++attemptCount, `${label}: exactly one appended attempt`);
      assert.ok(last, `${label}: a continuation record is required`);
      assert.notEqual(last.record.captureId, previous, `${label}: fresh capture identity`);
      assert.equal(last.record.parentCaptureId, base.parentCaptureId, `${label}: expected original capture`);
      assert.equal(last.record.previousCaptureId, base.previousCaptureId, `${label}: expected previous capture`);
      assert.equal(last.record.parentStepIndex, base.parentStepIndex, `${label}: expected selected prefix`);
      assert.equal(new Set(outcome.result.decompositions.map(b => b.record.captureId)).size, attemptCount, `${label}: unique attempt identities`);
      assert.equal(last.record.checking.status, 'captured', `${label}: captured checking`);
      assert.equal(last.record.checking.action.status, 'completed', `${label}: completed action`);
      assert.equal(last.record.checking.steps.at(-1).output.status, 'candidate', `${label}: completed candidate`);
      assert.equal(last.record.operations.at(-1).kind, operation.kind, `${label}: requested operation`);
      if (last) { previous = last.record.captureId; stepIndex = last.record.operations.length - 1; }
      return outcome.result;
    };
    await continuation({ kind: 'fields' }, 'inspect fields');
    await continuation({ kind: 'project', index: 2 }, 'project law field');
    await continuation({ kind: 'typeComponent' }, 'inspect type component');
    await continuation({ kind: 'logical' }, 'read logical structure');
    const body = await continuation({ kind: 'focus', path: ['piBody'] }, 'focus body');
    // Backtrack: continue from the earlier prefix (before the body focus) with a different focus.
    const bodyRecord = body.decompositions?.at(-1)?.record;
    if (bodyRecord) { previous = bodyRecord.captureId; stepIndex = bodyRecord.operations.length - 2; }
    const domain = await continuation({ kind: 'focus', path: ['piDomain'] }, 'backtrack to domain');
    record('backtracking retained', { attempts: domain.decompositions?.length, earlierBodyStillRetained: !!domain.decompositions?.some(b => b.record.operations.some(o => o.kind === 'focus' && o.path?.join('/') === 'piBody')) });
    assert.ok(domain.decompositions.some(b => b.record.captureId === bodyRecord.captureId), 'backtracking preserves the body attempt');
    assert.equal(domain.decompositions.at(-1).record.previousCaptureId, bodyRecord.captureId);
    assert.equal(domain.decompositions.at(-1).record.parentStepIndex, bodyRecord.operations.length - 2);
    // 3. Recoverable refusal: a projection index outside the catalogue must refuse explicitly, then a valid request recovers.
    const beforeRefusal = posted().length, refusalsBefore = refusals.length, processesBeforeRefusal = journal.nativeProcesses.length;
    await handler({ type: 'statementlens.projectField', parentCaptureId: continuationParent, previousCaptureId: domain.decompositions[0].record.captureId, parentStepIndex: 0, index: 15 });
    await waitFor(() => refusals.length > refusalsBefore, 30000, 'refusal notification');
    record('refusal control', { refusal: refusals.at(-1).message, requestPosted: posted().length > beforeRefusal });
    assert.equal(posted().length, beforeRefusal, 'invalid projection starts no analysis');
    assert.equal(journal.nativeProcesses.length, processesBeforeRefusal, 'invalid projection starts no native process');
    // The focused domain is a type, not a structure value. Recover from the
    // retained original owner, rather than expecting fields on owner.Carrier.
    previous = occurrence.captureId; stepIndex = 0;
    const recovered = await continuation({ kind: 'fields' }, 'recovery after refusal');
    record('recovery', { attempts: recovered.decompositions?.length });
    // 4. Edit the buffer: stale status must follow and the old results must not be replaced by anything for the old version.
    const before = posted().length;
    const editRace = handler({ type: 'statementlens.refresh' });
    await waitFor(() => posted().slice(before).some(m => m.type === 'statementlens.status' && m.phase === 'analyzing'), 30000, 'analysis before edit');
    const editRequestId = requestIdOf();
    await waitFor(() => journal.nativeProcesses.some(p => p.requestId === editRequestId), 30000, 'native process before edit');
    assert.ok(!posted().slice(before).some(m => (m.type === 'statementlens.analysis' || m.type === 'statementlens.error') && m.requestId === editRequestId), 'edit overlaps the native request');
    const versionBeforeEdit = document.version;
    assert.equal(await editor.edit(edit => edit.insert(new vscode.Position(0, 0), '-- edited during the journey\n')), true, 'source edit succeeds');
    assert.ok(document.version > versionBeforeEdit, 'source edit advances the document version');
    const stale = await waitFor(() => posted().slice(before).find(m => m.type === 'statementlens.status' && m.phase === 'stale'), 30000, 'stale status after edit');
    record('edit', { version: document.version, stale: !!stale, staleVersion: stale?.document?.version });
    await editRace;
    await waitFor(() => journal.nativeProcesses.find(p => p.requestId === editRequestId)?.finishedAt, 30000, 'edited request process to exit');
    assert.ok(!posted().slice(before).some(m => (m.type === 'statementlens.analysis' || m.type === 'statementlens.error') && m.requestId === editRequestId), 'edited request cannot post a result');
    record('edit cancellation', { requestId: editRequestId, native: journal.nativeProcesses.find(p => p.requestId === editRequestId), obsoleteResultPosted: false });
    // 5. Refresh from the webview: a new analysis for the new version; then two refreshes back to back: only the last request's result may arrive.
    let refreshed = await send({ type: 'statementlens.refresh' }, 'refresh after edit');
    record('refresh after edit', { ...summarize(refreshed.result), documentVersion: refreshed.result.document?.version });
    assert.equal(refreshed.result.document.version, document.version);
    assert.ok(refreshed.result.sourceSnapshotOrigin, 'refresh recovers a source capture');
    // Change only the selection while a real native request is pending.
    await selectText(target);
    const beforeSelection = posted().length, selectionVersion = document.version;
    const selectionRace = handler({ type: 'statementlens.refresh' });
    await waitFor(() => posted().slice(beforeSelection).some(m => m.type === 'statementlens.status' && m.phase === 'analyzing'), 30000, 'analysis before selection change');
    const selectionRequestId = requestIdOf();
    await waitFor(() => journal.nativeProcesses.some(p => p.requestId === selectionRequestId), 30000, 'native process before selection change');
    assert.ok(!posted().slice(beforeSelection).some(m => (m.type === 'statementlens.analysis' || m.type === 'statementlens.error') && m.requestId === selectionRequestId), 'selection change overlaps the native request');
    const changedSelection = await selectText('Rotor');
    const selectionStale = await waitFor(() => posted().slice(beforeSelection).find(m => m.type === 'statementlens.status' && m.phase === 'stale' && m.requestId === selectionRequestId && JSON.stringify(m.document.selection) === JSON.stringify(changedSelection)), 30000, 'stale status for the changed selection and in-flight request');
    await selectionRace;
    await waitFor(() => journal.nativeProcesses.find(p => p.requestId === selectionRequestId)?.finishedAt, 30000, 'selection request process to exit');
    assert.equal(document.version, selectionVersion, 'selection alone does not change the source version');
    assert.ok(!posted().slice(beforeSelection).some(m => (m.type === 'statementlens.analysis' || m.type === 'statementlens.error') && m.requestId === selectionRequestId), 'old selection cannot post a result');
    const selected = await send({ type: 'statementlens.refresh' }, 'refresh changed selection');
    assert.ok(selected.result.sourceSnapshotOrigin, 'changed selection yields a real source capture');
    assert.deepEqual(selected.result.document.selection, changedSelection);
    record('selection cancellation and recovery', { requestId: selectionRequestId, native: journal.nativeProcesses.find(p => p.requestId === selectionRequestId), obsoleteResultPosted: false, version: document.version, selection: changedSelection, stale: selectionStale, acceptedRequestId: selected.requestId, captureId: selected.result.sourceSnapshotOrigin.captureId });
    const beforeRestore = posted().length;
    const restoredSelection = await selectText(target);
    await waitFor(() => posted().slice(beforeRestore).some(m => m.type === 'statementlens.status' && m.phase === 'stale' && JSON.stringify(m.document.selection) === JSON.stringify(restoredSelection)), 30000, 'stale status after restoring the original selection');
    refreshed = await send({ type: 'statementlens.refresh' }, 'restore original selection');
    assert.ok(refreshed.result.sourceSnapshotOrigin, 'restoring the original selection yields a capture');
    assert.deepEqual(refreshed.result.document.selection, restoredSelection);
    // 5b. Overlapping refreshes. The first handler call is deliberately not awaited: the second refresh is sent as soon as the
    //     first request's analyzing status is visible, while its analysis is still in flight. (The earlier journey awaited the
    //     first handler, so its two requests ran one after the other and both results were legitimately posted.)
    const previousOrigin = refreshed.result.sourceSnapshotOrigin ? refreshed.result.sourceSnapshotOrigin.captureId : null;
    const beforeRace = posted().length;
    const isResult = m => m.type === 'statementlens.analysis' || m.type === 'statementlens.error';
    const firstRace = handler({ type: 'statementlens.refresh' });
    await waitFor(() => posted().slice(beforeRace).some(m => m.type === 'statementlens.status' && m.phase === 'analyzing'), 30000, 'the first racing request to start');
    const firstId = requestIdOf();
    await waitFor(() => journal.nativeProcesses.some(p => p.requestId === firstId), 30000, 'first racing native process');
    const firstResultBeforeSecondRequest = posted().slice(beforeRace).some(m => isResult(m) && m.requestId === firstId);
    const secondRace = handler({ type: 'statementlens.refresh' });
    await Promise.all([firstRace, secondRace]);
    const raceIds = posted().slice(beforeRace).filter(m => m.type === 'statementlens.status' && m.phase === 'analyzing').map(m => m.requestId);
    const last = raceIds[raceIds.length - 1];
    await awaitResult(last, 'result of the last racing request');
    await sleep(3000);
    const results = posted().slice(beforeRace).filter(isResult).map(m => m.requestId);
    const accepted = latestOf('statementlens.analysis', last) || latestOf('statementlens.error', last);
    record('overlapping refresh race', { requestIds: raceIds, discardedRequestId: firstId, firstResultBeforeSecondRequest, resultRequestIds: results,
      onlyLastArrived: results.length === 1 && results[0] === last, discardedResultPosted: results.includes(firstId), acceptedResult: summarize(accepted) });
    assert.equal(firstResultBeforeSecondRequest, false, 'refreshes actually overlap');
    assert.equal(raceIds.length, 2, 'exactly two refreshes began');
    assert.deepEqual(results, [last], 'only the final refresh posts a result');
    // 5c. Retained history after the race: only the accepted result's capture is current. The capture of the result before the
    //     race is refused without any request, and the accepted capture is the parent of a fresh occurrence check.
    const acceptedOrigin = accepted && accepted.sourceSnapshotOrigin ? accepted.sourceSnapshotOrigin.captureId : null;
    if (previousOrigin && acceptedOrigin && previousOrigin !== acceptedOrigin) {
      const refusalsBeforeRetained = refusals.length, beforeSuperseded = posted().length;
      await handler({ type: 'statementlens.checkOccurrence', parentCaptureId: previousOrigin, path: [] });
      await waitFor(() => refusals.length > refusalsBeforeRetained, 30000, 'refusal for the superseded capture');
      const supersededRefusal = refusals.at(-1).message, supersededRequestPosted = posted().length > beforeSuperseded;
      const kept = await send({ type: 'statementlens.checkOccurrence', parentCaptureId: acceptedOrigin, path: [] }, 'check occurrence on the accepted capture');
      record('retained history after the race', { supersededCapture: previousOrigin, supersededRefusal, supersededRequestPosted, acceptedCapture: acceptedOrigin, acceptedCheck: summarize(kept.result),
        acceptedCheckParentCapture: kept.result.sourceOccurrence?.parentCaptureId, freshOccurrenceCapture: kept.result.sourceSnapshotOrigin?.captureId });
      assert.equal(supersededRequestPosted, false, 'superseded capture starts no request');
      assert.equal(kept.result.sourceOccurrence.parentCaptureId, acceptedOrigin, 'fresh occurrence names the accepted capture as its parent');
      assert.notEqual(kept.result.sourceSnapshotOrigin.captureId, acceptedOrigin, 'new native check has a fresh capture identity');
      assert.equal(kept.result.sourceSnapshotOrigin.captureId, kept.result.sourceOccurrence.captureId);
      assert.equal(kept.result.sourceOccurrence.checking.action.status, 'completed');
    } else throw new Error('race must produce a distinct accepted capture');

    // A second dirty Lean buffer gives a real error response without starting Lean; reverting it recovers.
    const helper = await vscode.workspace.openTextDocument(path.join(folder, 'Helper.lean'));
    const helperEditor = await vscode.window.showTextDocument(helper);
    assert.equal(await helperEditor.edit(edit => edit.insert(new vscode.Position(0, 0), '-- unsaved control\n')), true, 'dependency edit succeeds');
    assert.ok(helper.isDirty, 'dependency buffer is dirty');
    const dirtySelection = await selectText(target);
    const processesBeforeError = journal.nativeProcesses.length;
    const dirty = await send({ type: 'statementlens.refresh' }, 'dirty dependency refusal', 0);
    assert.equal(dirty.result.type, 'statementlens.error');
    assert.deepEqual(dirty.result.document.selection, dirtySelection);
    assert.match(dirty.result.message, /Save and build imported Lean dependencies/);
    assert.equal(journal.nativeProcesses.length, processesBeforeError, 'dirty dependency refusal starts no native process');
    record('dirty dependency error', summarize(dirty.result));
    await vscode.window.showTextDocument(helper);
    await vscode.commands.executeCommand('workbench.action.files.revert');
    assert.equal(helper.isDirty, false);
    const recoverySelection = await selectText(target);
    const afterError = await send({ type: 'statementlens.refresh' }, 'recovery after error');
    assert.ok(afterError.result.sourceSnapshotOrigin, 'valid refresh recovers after the error');
    assert.equal(afterError.result.document.version, document.version);
    assert.deepEqual(afterError.result.document.selection, recoverySelection);
    record('recovery after error', summarize(afterError.result));
    // 6. Fresh original-root controls: both buttons branch from one original
    // occurrence, not from the result of the preceding inspection.
    const originalNativeBefore = journal.nativeProcesses.length;
    await selectText(target);
    const originalRefresh = await send({ type: 'statementlens.refresh' }, 'fresh original-root capture');
    assert.equal(originalRefresh.result.decompositions, undefined, 'refresh resets continuation history');
    assert.equal(originalRefresh.result.headExposure, undefined, 'refresh resets exposure history');
    const originalCheck = await send({ type: 'statementlens.checkOccurrence', parentCaptureId: originalRefresh.result.sourceSnapshotOrigin.captureId, path: [] }, 'fresh original-root occurrence');
    const originalOccurrence = originalCheck.result.sourceOccurrence;
    assert.equal(originalOccurrence.checking.action.status, 'completed');
    const originalBase = { parentCaptureId: originalOccurrence.captureId, previousCaptureId: originalOccurrence.captureId, parentStepIndex: 0 };
    const inspectOriginal = async (kind, buttonLabel, count) => {
      const message = { type: kind === 'typeComponent' ? 'statementlens.inspectTypeComponent' : 'statementlens.inspectLogicalStructure', ...originalBase };
      const result = (await clickInspection(message, `original ${kind}`, buttonLabel, 'section.source-snapshot button')).result;
      const last = result.decompositions?.at(-1)?.record;
      assert.equal(result.decompositions?.length, count, 'one appended original-root attempt');
      assert.deepEqual(result.sourceOccurrence, originalOccurrence, 'original occurrence remains retained');
      assert.equal(result.sourceSnapshotOrigin.captureId, originalBase.parentCaptureId);
      assert.equal(last.parentCaptureId, originalBase.parentCaptureId);
      assert.equal(last.previousCaptureId, originalBase.previousCaptureId);
      assert.equal(last.parentStepIndex, 0);
      assert.deepEqual(last.operations, [{ kind }], 'both original actions start at the original pair');
      assert.equal(last.checking.status, 'captured');
      assert.equal(last.checking.action.status, 'completed');
      assert.equal(last.checking.steps.at(-1).output.status, 'candidate');
      assert.equal(last.checking.steps.at(-1).output.checking.status, 'completed');
      assert.equal(new Set(result.decompositions.map(bundle => bundle.record.captureId)).size, count);
      record(`original-root ${kind}`, summarize(result));
      return result;
    };
    const originalType = await inspectOriginal('typeComponent', 'Inspect type of original selected term', 1);
    const originalLogical = await inspectOriginal('logical', 'Read logical structure of original selected term (one layer)', 2);
    assert.equal(originalLogical.decompositions[0].record.captureId, originalType.decompositions[0].record.captureId, 'original type attempt remains retained');
    assert.equal(journal.nativeProcesses.length, originalNativeBefore + 4, 'original scenario: refresh, occurrence, and exactly two clicked inspections');

    // 7. Fresh seed controls: a transparent identity definition supplies a small
    // real exposure; both inspection buttons continue from that same seed.
    const seedNativeBefore = journal.nativeProcesses.length;
    await selectText('journeySeed 0');
    const seedRefresh = await send({ type: 'statementlens.refresh' }, 'fresh seed capture');
    assert.equal(seedRefresh.result.decompositions, undefined, 'seed refresh resets continuation history');
    const seedCheck = await send({ type: 'statementlens.checkOccurrence', parentCaptureId: seedRefresh.result.sourceSnapshotOrigin.captureId, path: [] }, 'fresh seed occurrence');
    const seedOccurrence = seedCheck.result.sourceOccurrence;
    assert.equal(seedOccurrence.checking.action.status, 'completed');
    const exposure = await send({ type: 'statementlens.exposeDefinitionHead', parentCaptureId: seedOccurrence.captureId, target: 'term' }, 'fresh definition-head seed');
    const seed = exposure.result.headExposure;
    assert.ok(seed, 'a real definition-head seed is retained');
    assert.equal(seed.record.checking.status, 'captured');
    assert.equal(seed.record.checking.action.status, 'completed');
    assert.equal(seed.record.checking.exposure.status, 'candidate');
    assert.equal(seed.record.checking.exposure.checking.status, 'completed');
    const seedBase = { parentCaptureId: seedOccurrence.captureId, previousCaptureId: seed.record.captureId, parentStepIndex: 0 };
    const inspectSeed = async (kind, buttonLabel, count) => {
      const message = { type: kind === 'typeComponent' ? 'statementlens.inspectTypeComponent' : 'statementlens.inspectLogicalStructure', ...seedBase };
      const result = (await clickInspection(message, `seed ${kind}`, buttonLabel, 'section.source-head-exposure button')).result;
      const last = result.decompositions?.at(-1)?.record;
      assert.equal(result.decompositions?.length, count, 'one appended seed attempt');
      assert.deepEqual(result.headExposure, seed, 'the same seed remains retained');
      assert.deepEqual(result.sourceOccurrence, seedOccurrence, 'seed original occurrence remains retained');
      assert.equal(result.sourceSnapshotOrigin.captureId, seedBase.parentCaptureId);
      assert.equal(last.parentCaptureId, seedBase.parentCaptureId);
      assert.equal(last.previousCaptureId, seedBase.previousCaptureId);
      assert.equal(last.parentStepIndex, 0);
      assert.deepEqual(last.operations, [{ kind: 'expose', target: 'term' }, { kind }], 'both seed actions replay only the seed prefix');
      assert.equal(last.checking.status, 'captured');
      assert.equal(last.checking.action.status, 'completed');
      assert.equal(last.checking.steps.at(-1).output.status, 'candidate');
      assert.equal(last.checking.steps.at(-1).output.checking.status, 'completed');
      assert.equal(new Set(result.decompositions.map(bundle => bundle.record.captureId)).size, count);
      record(`seed ${kind}`, summarize(result));
      return result;
    };
    const seedType = await inspectSeed('typeComponent', 'Inspect type of exposed term', 1);
    const seedLogical = await inspectSeed('logical', 'Read logical structure of exposed term (one layer)', 2);
    assert.equal(seedLogical.decompositions[0].record.captureId, seedType.decompositions[0].record.captureId, 'seed type attempt remains retained');
    assert.equal(journal.nativeProcesses.length, seedNativeBefore + 5, 'seed scenario: refresh, occurrence, exposure, and exactly two clicked inspections');
    const finalSelection = await selectText(target);
    const finalRefresh = await send({ type: 'statementlens.refresh' }, 'restore original source for reveal');
    assert.deepEqual(finalRefresh.result.document.selection, finalSelection);
    assert.ok(finalRefresh.result.sourceSnapshotOrigin, 'original source is current for Reveal');
    // 8. Reveal returns to the original selection.
    await vscode.window.showTextDocument(helper, { viewColumn: vscode.ViewColumn.One, preserveFocus: false });
    assert.equal(vscode.window.activeTextEditor?.document, helper, 'Reveal begins from a different file');
    await handler({ type: 'statementlens.reveal' }); await sleep(500);
    record('reveal', { activeFile: vscode.window.activeTextEditor?.document.fileName, selection: vscode.window.activeTextEditor?.document.getText(vscode.window.activeTextEditor.selection) });
    assert.equal(vscode.window.activeTextEditor.document.fileName, file);
    assert.equal(vscode.window.activeTextEditor.document.getText(vscode.window.activeTextEditor.selection), target);
    journal.ok = true;
  } catch (error) {
    journal.error = error && error.stack ? error.stack : String(error);
  } finally {
    if (webviewDriver) try { await webviewDriver.close(); } catch (error) { journal.error ||= `CDP cleanup: ${error}`; }
    childProcess.spawn = originalSpawn;
    vscode.window.createWebviewPanel = originalCreate;
    vscode.window.showErrorMessage = originalError;
  }
  await finish();
  if (journal.error) throw new Error(journal.error);
};
