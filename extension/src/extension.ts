import * as vscode from 'vscode';
import { randomBytes } from 'node:crypto';
import { readFile, realpath } from 'node:fs/promises';
import path from 'node:path';
import { analyzeEditorContext, type EditorRange } from '../../server/editor-context.js';
import { EditorAnalysisLifecycle, type EditorDocument, type Ticket } from './lifecycle.js';
import { isSourceOccurrencePath, type SourceOccurrence, type SourceOccurrenceStep } from '../../src/editor/source-occurrence.js';
import type { HeadExposureTarget } from '../../src/editor/source-head-exposure.js';
import { isSourceSnapshotOrigin, type SourceSnapshotOrigin } from '../../src/editor/source-origin.js';
import { SourceSnapshotError, type SourceSnapshot } from '../../src/editor/source-snapshot.js';
import type { HeadExposureBundle } from '../../src/editor/source-history.js';
import { assertSourceHistoryLimit } from '../../src/editor/source-history.js';
import type { SourceDecompositionBundle } from '../../src/editor/source-decomposition.js';
import { sanitizeSourcePresentation, fitSourcePresentationHistory } from '../../src/editor/source-presentation.js';
import { createExactJsonTools } from '../../src/packets/packet.js';
import { continuationCommand, requireContinuationParent, type ContinuationAction } from './continuation.js';
import { GUIDED_CONTEXT_CONTRACT, GUIDED_CONTEXT_MISMATCH } from '../../src/editor/guided-context-contract.js';

interface Expansion { constants: string[]; maxDepth: number }
type SourceAction = { kind: 'occurrence'; parentCaptureId: string; path: SourceOccurrenceStep[] }
  | { kind: 'head-exposure'; parentCaptureId: string; target: HeadExposureTarget } | ContinuationAction;
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
  let retained: { ticket: Ticket; snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence?: SourceOccurrence; headExposure?: HeadExposureBundle; decompositions?: SourceDecompositionBundle[] } | undefined;
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
  const refresh = async (action?: SourceAction) => {
    if (!panel || !ready || !activeDocument || !activeSelection) return;
    const doc = activeDocument;
    const visibleEditor = vscode.window.visibleTextEditors.find(editor => editor.document === doc);
    const selected = doc.validateRange(visibleEditor?.selection ?? activeSelection);
    activeSelection = selected;
    const metadata = documentInfo(doc, selected);
    const parent = retained;
    if (action && (!parent || !lifecycle.accepts(parent.ticket)
      || parent.origin.captureId !== action.parentCaptureId
      || parent.ticket.document.uri !== metadata.uri || parent.ticket.document.fileName !== metadata.fileName
      || parent.ticket.document.version !== metadata.version
      || parent.ticket.document.selection.start.line !== metadata.selection.start.line
      || parent.ticket.document.selection.start.character !== metadata.selection.start.character
      || parent.ticket.document.selection.end.line !== metadata.selection.end.line
      || parent.ticket.document.selection.end.character !== metadata.selection.end.character)) {
      throw new Error('This source capture is no longer current. Refresh before requesting another source operation.');
    }
    if (action && action.kind !== 'decomposition' && (parent?.headExposure || parent?.decompositions !== undefined)) throw new Error('This history retains its original occurrence and earlier attempts. Save it and Refresh to start another source history.');
    if (action?.kind === 'decomposition') {
      if (!parent?.occurrence) throw new Error('No checked occurrence is retained in this session.');
      try {
        requireContinuationParent(parent.headExposure ?? null, parent.decompositions ?? [], action, parent.occurrence.path, parent.occurrence);
      } catch (error) {
        // A retained, current parent exists only after native work has finished.
        // Associate this refusal with a new request without losing that history;
        // stale captures, in-flight duplicates and malformed commands fail earlier.
        const ticket = lifecycle.begin(metadata);
        const message = error instanceof Error ? error.message : 'This continuation is unavailable.';
        retained = { ...parent, ticket };
        post({ type: 'statementlens.status', phase: 'analyzing', requestId: ticket.requestId, document: metadata });
        post({ type: 'statementlens.error', requestId: ticket.requestId, document: metadata, message,
          sourceSnapshot: parent.snapshot, sourceSnapshotOrigin: parent.origin, sourceOccurrence: parent.occurrence,
          ...(parent.headExposure ? { headExposure: parent.headExposure } : {}),
          decompositions: parent.decompositions ?? [], decompositionUnavailable: message });
        return;
      }
    }
    if (action?.kind === 'head-exposure' && (!parent?.occurrence || parent.occurrence.checking.status !== 'captured'
      || parent.occurrence.checking.action.status !== 'completed' || !parent.occurrence.checking.selected || parent.occurrence.captureId !== parent.origin.captureId))
      throw new Error('Check a source occurrence before exposing its definition head.');
    const occurrence = action?.kind === 'occurrence' && parent ? { snapshot: parent.snapshot, origin: parent.origin, path: [...action.path] } : undefined;
    const headExposure = action?.kind === 'head-exposure' && parent?.occurrence
      ? { snapshot: parent.snapshot, origin: parent.origin, occurrence: parent.occurrence, target: action.target } : undefined;
    const decomposition = action?.kind === 'decomposition' && parent?.occurrence
      ? { snapshot: parent.snapshot, origin: parent.origin, occurrence: parent.occurrence, seed: parent.headExposure ?? null, version: 3 as const, attempts: parent.decompositions ?? [],
        previousCaptureId: action.previousCaptureId, parentStepIndex: action.parentStepIndex, operation: action.operation } : undefined;
    retained = undefined;
    const ticket = lifecycle.begin(metadata);
    post({ type: 'statementlens.status', phase: 'analyzing', requestId: ticket.requestId, document: metadata });
    try {
      if (!vscode.workspace.isTrusted) throw new Error('Workspace Trust is required because Lean elaboration can execute project code.');
      const dirtyImport = dirtyDependency(doc);
      if (dirtyImport) throw new Error(`Save and build imported Lean dependencies before analysis. Another Lean buffer has unsaved changes: ${path.basename(dirtyImport.fileName)}.`);
      const configuration = vscode.workspace.getConfiguration('statementLens', doc.uri);
      const configuredEngine = configuration.get<string>('engineDirectory', '');
      if (await realpath(configuredEngine || path.resolve(context.extensionPath, '..')) !== engine) throw new Error('The configured engine changed. Run Definograph: Visualize Selection again to load its matching interface.');
      const analysis = await analyzeEditorContext({ engineDirectory: engine, fileName: doc.fileName, source: doc.getText(), selection: metadata.selection,
        document: { uri: metadata.uri, version: metadata.version }, workspaceTrusted: vscode.workspace.isTrusted, libraryPaths: configuration.get<string[]>('libraryPaths', []), signal: ticket.signal, expansion: policy, previewDefinitions: !policy?.constants.length, occurrence, headExposure, decomposition });
      if (!lifecycle.accepts(ticket) || doc.version !== metadata.version) return;
      if (dirtyDependency(doc)) throw new Error("Another Lean buffer changed during analysis. Save and build imported dependencies, then refresh.");
      const { sourceSnapshot, sourceSnapshotOrigin, sourceSnapshotUnavailable, sourceOccurrence, sourceOccurrenceUnavailable,
        sourceHeadExposure, sourceHeadExposureUnavailable, sourceDecomposition, sourceDecompositionUnavailable, sourceDecompositionPresentation, ...guided } = analysis;
      let attachments: object;
      if (decomposition && parent) {
        if (sourceDecomposition !== undefined && (sourceSnapshot === undefined || !isSourceSnapshotOrigin(sourceSnapshotOrigin))
          || sourceDecomposition === undefined && typeof sourceDecompositionUnavailable !== 'string')
          throw new Error('The context worker omitted the requested continuation record.');
        let attempts = parent.decompositions ?? [], unavailable = sourceDecompositionUnavailable;
        if (sourceDecomposition !== undefined) {
          const next: SourceDecompositionBundle = { snapshot: sourceSnapshot as SourceSnapshot, origin: sourceSnapshotOrigin as SourceSnapshotOrigin, record: sourceDecomposition as SourceDecompositionBundle['record'] };
          const presentation = sanitizeSourcePresentation(sourceDecompositionPresentation, next.record);
          if (presentation) next.presentation = presentation;
          try {
            const proposed = fitSourcePresentationHistory([...attempts, next], decompositions => assertSourceHistoryLimit({
              sourceSnapshot: parent.snapshot, sourceSnapshotOrigin: parent.origin, sourceOccurrence: parent.occurrence,
              ...(parent.headExposure ? { headExposure: parent.headExposure } : {}), decompositions }, 20 * 1024));
            createExactJsonTools().freeze(proposed); attempts = proposed;
          } catch (error) {
            if (!(error instanceof SourceSnapshotError) || error.code !== 'limit') throw error;
            unavailable = 'This result exceeds the retained-history limits (16 MiB total). Earlier history is unchanged. Save it and Refresh to start another.';
          }
        }
        retained = { ...parent, ticket, decompositions: attempts };
        attachments = { sourceSnapshot: parent.snapshot, sourceSnapshotOrigin: parent.origin, sourceOccurrence: parent.occurrence,
          ...(parent.headExposure ? { headExposure: parent.headExposure } : {}), decompositions: attempts, ...(unavailable !== undefined ? { decompositionUnavailable: unavailable } : {}) };
      } else if (headExposure && parent) {
        if (sourceHeadExposure !== undefined && (sourceSnapshot === undefined || !isSourceSnapshotOrigin(sourceSnapshotOrigin))
          || sourceHeadExposure === undefined && typeof sourceHeadExposureUnavailable !== 'string')
          throw new Error('The context worker omitted the requested head-exposure record.');
        // Keep the original capture identity and receipts. Only the lifecycle
        // ticket moves forward so another explicit action can use this parent.
        const seed = sourceHeadExposure !== undefined ? { snapshot: sourceSnapshot as SourceSnapshot, origin: sourceSnapshotOrigin as SourceSnapshotOrigin, record: sourceHeadExposure as HeadExposureBundle['record'] } : undefined;
        if (seed) createExactJsonTools().freeze(seed);
        retained = { ...parent, ticket, ...(seed ? { headExposure: seed, decompositions: [] } : {}) };
        attachments = { sourceSnapshot: parent.snapshot, sourceSnapshotOrigin: parent.origin, sourceOccurrence: parent.occurrence,
          ...(sourceHeadExposure !== undefined ? { headExposure: seed }
            : { headExposureUnavailable: sourceHeadExposureUnavailable }) };
      } else {
        if (sourceSnapshot !== undefined && isSourceSnapshotOrigin(sourceSnapshotOrigin)) {
          createExactJsonTools().freeze(sourceSnapshot); createExactJsonTools().freeze(sourceSnapshotOrigin);
          if (sourceOccurrence !== undefined) createExactJsonTools().freeze(sourceOccurrence);
          retained = {
          ticket, snapshot: sourceSnapshot as SourceSnapshot, origin: sourceSnapshotOrigin, occurrence: sourceOccurrence as SourceOccurrence | undefined };
        }
        attachments = { sourceSnapshot, sourceSnapshotOrigin, sourceSnapshotUnavailable, sourceOccurrence, sourceOccurrenceUnavailable };
      }
      if (!analysis.ok) {
        post({ type: 'statementlens.error', requestId: ticket.requestId, document: metadata,
          message: typeof analysis.error === 'string' ? analysis.error : 'The selected proposition could not be elaborated.',
          source: doc.getText(), ...attachments });
      } else post({ type: 'statementlens.analysis', requestId: ticket.requestId, document: metadata, analysis: guided, ...attachments });
    } catch (error) {
      if (!lifecycle.accepts(ticket)) return;
      retained = undefined;
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
      retained = undefined;
      opening = lifecycle.begin(documentInfo(activeDocument, activeSelection));
      post({ type: 'statementlens.status', phase: 'analyzing', requestId: opening.requestId, document: opening.document });
      const configured = vscode.workspace.getConfiguration('statementLens', editor.document.uri).get<string>('engineDirectory', '');
      const resolvedEngine = await realpath(configured || path.resolve(context.extensionPath, '..'));
      if (!lifecycle.accepts(opening)) return;
      if (panel && engine !== resolvedEngine) panel.dispose();
      engine = resolvedEngine;
      if (!panel) {
        panel = vscode.window.createWebviewPanel('statementLens', 'Definograph', { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true }, {
          enableScripts: true, retainContextWhenHidden: true, localResourceRoots: [vscode.Uri.file(path.join(engine, 'dist'))],
        });
        const createdPanel = panel;
        createdPanel.onDidDispose(() => { if (panel === createdPanel) { panel = undefined; ready = false; retained = undefined; lifecycle.dispose(); } }, undefined, context.subscriptions);
        createdPanel.webview.onDidReceiveMessage(async (message: unknown) => {
          if (panel !== createdPanel) return;
          if (!message || typeof message !== 'object' || !('type' in message)) return;
          const incoming = message as Record<string, unknown>;
          if (incoming.type === 'statementlens.ready') {
            if (incoming.guidedContextContract !== GUIDED_CONTEXT_CONTRACT) {
              ready = false; retained = undefined; lifecycle.invalidate();
              createdPanel.dispose();
              void vscode.window.showErrorMessage(GUIDED_CONTEXT_MISMATCH);
              return;
            }
            ready = true; await refresh();
          }
          else if (incoming.type === 'statementlens.refresh') {
            try { policy = expansionValue(incoming.expansion); await refresh(); }
            catch (error) { void vscode.window.showErrorMessage(error instanceof Error ? error.message : 'Invalid request.'); }
          } else if (incoming.type === 'statementlens.checkOccurrence') {
            try {
              if (Object.keys(incoming).sort().join(',') !== 'parentCaptureId,path,type'
                || typeof incoming.parentCaptureId !== 'string' || !isSourceOccurrencePath(incoming.path)) throw new Error('Invalid source occurrence request.');
              await refresh({ kind: 'occurrence', parentCaptureId: incoming.parentCaptureId, path: incoming.path });
            } catch (error) { void vscode.window.showErrorMessage(error instanceof Error ? error.message : 'Invalid source occurrence request.'); }
          } else if (incoming.type === 'statementlens.exposeDefinitionHead') {
            try {
              if (Object.keys(incoming).sort().join(',') !== 'parentCaptureId,target,type'
                || typeof incoming.parentCaptureId !== 'string' || incoming.target !== 'term' && incoming.target !== 'type')
                throw new Error('Invalid definition-head exposure request.');
              await refresh({ kind: 'head-exposure', parentCaptureId: incoming.parentCaptureId, target: incoming.target as HeadExposureTarget });
            } catch (error) { void vscode.window.showErrorMessage(error instanceof Error ? error.message : 'Invalid definition-head exposure request.'); }
          } else if (incoming.type === 'statementlens.focusExposedPart' || incoming.type === 'statementlens.exposeFocusedHead' || incoming.type === 'statementlens.inspectFields' || incoming.type === 'statementlens.projectField' || incoming.type === 'statementlens.inspectTypeComponent' || incoming.type === 'statementlens.inspectLogicalStructure') {
            try { await refresh(continuationCommand(message)); }
            catch (error) { void vscode.window.showErrorMessage(error instanceof Error ? error.message : 'Invalid continuation request.'); }
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
      const message = error instanceof Error ? error.message : 'Definograph could not open.';
      if (opening && lifecycle.accepts(opening)) post({ type: 'statementlens.error', requestId: opening.requestId, document: opening.document, message });
      void vscode.window.showErrorMessage(message);
    }
  }));
  context.subscriptions.push(vscode.workspace.onDidChangeTextDocument(event => {
    if (!activeDocument || event.contentChanges.length === 0) return;
    if (event.document !== activeDocument && (event.document.languageId !== 'lean4' || !sameWorkspace(event.document, activeDocument))) return;
    retained = undefined;
    const ticket = lifecycle.invalidate(activeDocument.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId,
      document: documentInfo(activeDocument, activeSelection ?? new vscode.Range(0, 0, 0, 0)) });
  }));
  context.subscriptions.push(vscode.workspace.onDidCloseTextDocument(doc => {
    if (doc !== activeDocument) return;
    retained = undefined;
    const ticket = lifecycle.invalidate(doc.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId, document: ticket.document });
    activeDocument = undefined;
  }));
  context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection(event => {
    if (!activeDocument || event.textEditor.document !== activeDocument) return;
    const selected = event.textEditor.selection;
    if (activeSelection?.isEqual(selected)) return;
    retained = undefined;
    activeSelection = selected;
    const ticket = lifecycle.invalidate(activeDocument.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId, document: documentInfo(activeDocument, selected) });
  }));
  context.subscriptions.push(vscode.workspace.onDidChangeConfiguration(event => {
    if (!activeDocument || !event.affectsConfiguration('statementLens', activeDocument.uri)) return;
    retained = undefined;
    const ticket = lifecycle.invalidate(activeDocument.uri.toString());
    if (ticket) post({ type: 'statementlens.status', phase: 'stale', requestId: ticket.requestId, document: ticket.document });
  }));
  context.subscriptions.push({ dispose() { retained = undefined; lifecycle.dispose(); panel?.dispose(); } });
}
export function deactivate(): void { /* subscription disposal cancels active analysis */ }
