import * as vscode from 'vscode';
import { randomBytes } from 'node:crypto';
import { readFile, realpath } from 'node:fs/promises';
import path from 'node:path';
import { analyzeEditorContext, type EditorRange } from '../../server/editor-context.js';
import { EditorAnalysisLifecycle, type EditorDocument, type Ticket } from './lifecycle.js';

interface Expansion { constants: string[]; maxDepth: number }
function expansionValue(value: unknown): Expansion | undefined {
  if (value === undefined) return undefined;
  if (!value || typeof value !== 'object') throw new Error('Invalid definition expansion request.');
  const v = value as Record<string, unknown>;
  if (!Array.isArray(v.constants) || v.constants.length > 12 || v.constants.some(x => typeof x !== 'string' || !x || Buffer.byteLength(x) > 512) || !Number.isInteger(v.maxDepth) || Number(v.maxDepth) < 1 || Number(v.maxDepth) > 3) throw new Error('Definition expansion supports at most 12 names and depth 1–3.');
  return { constants: v.constants as string[], maxDepth: v.maxDepth as number };
}
function rangeValue(selection: vscode.Range): EditorRange {
  return { start: { line: selection.start.line, character: selection.start.character }, end: { line: selection.end.line, character: selection.end.character } };
}
function escapeAttribute(value: string): string { return value.replaceAll('&', '&amp;').replaceAll('"', '&quot;').replaceAll('<', '&lt;'); }
async function webviewHtml(webview: vscode.Webview, engine: string): Promise<string> {
  const dist = path.join(engine, 'dist');
  let html = await readFile(path.join(dist, 'index.html'), 'utf8');
  const nonce = randomBytes(24).toString('base64');
  html = html.replace(/\b(src|href)="([^"#][^"]*)"/g, (match, attribute: string, target: string) => {
    if (!target.startsWith('/assets/') && !target.startsWith('./assets/') && !target.startsWith('assets/') && !['/favicon.svg', './favicon.svg', 'favicon.svg'].includes(target)) return match;
    const relative = target.replace(/^\.\//, '').replace(/^\//, '');
    const resolved = path.resolve(dist, relative);
    if (!resolved.startsWith(dist + path.sep)) throw new Error('Invalid built asset path.');
    return `${attribute}="${escapeAttribute(webview.asWebviewUri(vscode.Uri.file(resolved)).toString())}"`;
  });
  html = html.replace(/<script\b/g, `<script nonce="${nonce}"`);
  const policy = `default-src 'none'; img-src ${webview.cspSource} data:; style-src ${webview.cspSource} 'unsafe-inline'; font-src ${webview.cspSource}; script-src 'nonce-${nonce}' ${webview.cspSource}; connect-src 'none';`;
  return html.replace('<head>', `<head><meta http-equiv="Content-Security-Policy" content="${escapeAttribute(policy)}">`);
}

export function activate(context: vscode.ExtensionContext): void {
  let panel: vscode.WebviewPanel | undefined;
  let ready = false;
  let activeDocument: vscode.TextDocument | undefined;
  let activeSelection: vscode.Range | undefined;
  let policy: Expansion | undefined;
  let engine = '';
  const lifecycle = new EditorAnalysisLifecycle();
  const post = (message: object) => { if (panel && ready) void panel.webview.postMessage(message); };
  const documentInfo = (doc: vscode.TextDocument, selection: vscode.Range): EditorDocument => ({ uri: doc.uri.toString(), version: doc.version, fileName: doc.fileName, selection: rangeValue(selection) });
  const sameWorkspace = (first: vscode.TextDocument, second: vscode.TextDocument) => {
    const a = vscode.workspace.getWorkspaceFolder(first.uri)?.uri.toString();
    const b = vscode.workspace.getWorkspaceFolder(second.uri)?.uri.toString();
    return a !== undefined ? a === b : b === undefined && path.dirname(first.fileName) === path.dirname(second.fileName);
  };
  const dirtyDependency = (doc: vscode.TextDocument) => vscode.workspace.textDocuments.find(other =>
    other !== doc && other.languageId === 'lean4' && other.isDirty && sameWorkspace(other, doc));
  const refresh = async () => {
    if (!panel || !ready || !activeDocument || !activeSelection) return;
    const doc = activeDocument;
    const visibleEditor = vscode.window.visibleTextEditors.find(editor => editor.document === doc);
    const selected = doc.validateRange(visibleEditor?.selection ?? activeSelection);
    activeSelection = selected;
    const metadata = documentInfo(doc, selected);
    const ticket = lifecycle.begin(metadata);
    post({ type: 'statementlens.status', phase: 'analyzing', requestId: ticket.requestId, document: metadata });
    try {
      if (!vscode.workspace.isTrusted) throw new Error('Workspace Trust is required because Lean elaboration can execute project code.');
      const dirtyImport = dirtyDependency(doc);
      if (dirtyImport) throw new Error(`Save and build imported Lean dependencies before analysis. Another Lean buffer has unsaved changes: ${path.basename(dirtyImport.fileName)}.`);
      const configuration = vscode.workspace.getConfiguration('statementLens', doc.uri);
      const analysis = await analyzeEditorContext({ engineDirectory: engine, fileName: doc.fileName, source: doc.getText(), selection: metadata.selection,
        workspaceTrusted: vscode.workspace.isTrusted, libraryPaths: configuration.get<string[]>('libraryPaths', []), signal: ticket.signal, expansion: policy });
      if (!lifecycle.accepts(ticket) || doc.version !== metadata.version) return;
      if (dirtyDependency(doc)) throw new Error("Another Lean buffer changed during analysis. Save and build imported dependencies, then refresh.");
      if (!analysis.ok) throw new Error(typeof analysis.error === 'string' ? analysis.error : 'The selected proposition could not be elaborated.');
      post({ type: 'statementlens.analysis', requestId: ticket.requestId, document: metadata, analysis });
    } catch (error) {
      if (!lifecycle.accepts(ticket)) return;
      post({ type: 'statementlens.error', requestId: ticket.requestId, document: metadata, message: error instanceof Error ? error.message : 'Editor analysis failed.', code: error && typeof error === 'object' && 'code' in error ? error.code : undefined });
    }
  };
  context.subscriptions.push(vscode.commands.registerCommand('statementLens.visualizeSelection', async () => {
    let opening: Ticket | undefined;
    try {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== 'lean4' || editor.document.uri.scheme !== 'file') throw new Error('Open a saved Lean file and select a proposition first.');
      if (!vscode.workspace.isTrusted) throw new Error('Trust this workspace before running Lean project elaboration.');
      activeDocument = editor.document; activeSelection = editor.selection; policy = undefined;
      opening = lifecycle.begin(documentInfo(activeDocument, activeSelection));
      post({ type: 'statementlens.status', phase: 'analyzing', requestId: opening.requestId, document: opening.document });
      const configured = vscode.workspace.getConfiguration('statementLens', editor.document.uri).get<string>('engineDirectory', '');
      const resolvedEngine = await realpath(configured || path.resolve(context.extensionPath, '..'));
      if (!lifecycle.accepts(opening)) return;
      if (panel && engine !== resolvedEngine) panel.dispose();
      engine = resolvedEngine;
      if (!panel) {
        panel = vscode.window.createWebviewPanel('statementLens', 'Statement Lens', { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true }, {
          enableScripts: true, retainContextWhenHidden: true, localResourceRoots: [vscode.Uri.file(path.join(engine, 'dist'))],
        });
        const createdPanel = panel;
        createdPanel.onDidDispose(() => { if (panel === createdPanel) { panel = undefined; ready = false; lifecycle.dispose(); } }, undefined, context.subscriptions);
        createdPanel.webview.onDidReceiveMessage(async (message: unknown) => {
          if (panel !== createdPanel) return;
          if (!message || typeof message !== 'object' || !('type' in message)) return;
          const incoming = message as Record<string, unknown>;
          if (incoming.type === 'statementlens.ready') { ready = true; await refresh(); }
          else if (incoming.type === 'statementlens.refresh') {
            try { policy = expansionValue(incoming.expansion); await refresh(); }
            catch (error) { void vscode.window.showErrorMessage(error instanceof Error ? error.message : 'Invalid request.'); }
          } else if (incoming.type === 'statementlens.reveal' && activeDocument && activeSelection) {
            const revealDocument = activeDocument;
            const revealSelection = activeSelection;
            const revealTicket = lifecycle.current();
            const revealVersion = revealDocument.version;
            const editor = await vscode.window.showTextDocument(revealDocument, { viewColumn: vscode.ViewColumn.One, preserveFocus: false });
            if (activeDocument !== revealDocument || activeSelection !== revealSelection || lifecycle.current() !== revealTicket || revealDocument.version !== revealVersion || panel !== createdPanel) return;
            // The webview cannot choose another file. Until a matching-version range
            // is explicitly supplied, reveal the original analyzed selection.
            let selected = revealSelection;
            const candidate = incoming.range as EditorRange | undefined;
            if (candidate && revealTicket?.document.version === revealVersion && [candidate.start?.line, candidate.start?.character, candidate.end?.line, candidate.end?.character].every(n => Number.isSafeInteger(n) && n >= 0)) {
              const proposed = new vscode.Range(candidate.start.line, candidate.start.character, candidate.end.line, candidate.end.character);
              if (revealDocument.validateRange(proposed).isEqual(proposed)) selected = proposed;
            }
            editor.selection = new vscode.Selection(selected.start, selected.end); editor.revealRange(selected, vscode.TextEditorRevealType.InCenterIfOutsideViewport);
          }
        }, undefined, context.subscriptions);
        try {
          const html = await webviewHtml(createdPanel.webview, resolvedEngine);
          if (panel === createdPanel && engine === resolvedEngine) createdPanel.webview.html = html;
        } catch (error) {
          if (panel === createdPanel) createdPanel.dispose();
          throw error;
        }
      } else { panel.reveal(vscode.ViewColumn.Beside, true); await refresh(); }
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Statement Lens could not open.';
      if (opening && lifecycle.accepts(opening)) post({ type: 'statementlens.error', requestId: opening.requestId, document: opening.document, message });
      void vscode.window.showErrorMessage(message);
    }
  }));
  context.subscriptions.push(vscode.workspace.onDidChangeTextDocument(event => {
    if (!activeDocument || event.contentChanges.length === 0) return;
    if (event.document !== activeDocument && (event.document.languageId !== 'lean4' || !sameWorkspace(event.document, activeDocument))) return;
    const ticket = lifecycle.invalidate(activeDocument.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId,
      document: documentInfo(activeDocument, activeSelection ?? new vscode.Range(0, 0, 0, 0)) });
  }));
  context.subscriptions.push(vscode.workspace.onDidCloseTextDocument(doc => {
    if (doc !== activeDocument) return;
    const ticket = lifecycle.invalidate(doc.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId, document: ticket.document });
    activeDocument = undefined;
  }));
  context.subscriptions.push({ dispose() { lifecycle.dispose(); panel?.dispose(); } });
}
export function deactivate(): void { /* subscription disposal cancels active analysis */ }
