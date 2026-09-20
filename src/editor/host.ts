import type { Analysis } from '../core';

export interface EditorPosition { line: number; character: number }
export interface EditorRange { start: EditorPosition; end: EditorPosition }
export interface EditorDocument {
  uri: string;
  version: number;
  fileName: string;
  selection: EditorRange;
}
export type EditorMessage =
  | { type: 'statementlens.status'; requestId: string; phase: 'analyzing' | 'idle' | 'stale'; document: EditorDocument }
  | { type: 'statementlens.analysis'; requestId: string; document: EditorDocument; analysis: Analysis }
  | { type: 'statementlens.error'; requestId: string; document: EditorDocument; message: string; code?: string };
export type EditorCommand = { type: 'statementlens.ready' } | { type: 'statementlens.refresh'; expansion?: { constants: string[]; maxDepth: number } } | { type: 'statementlens.reveal'; range?: EditorRange };
export interface EditorHost { postMessage(message: EditorCommand): void }
declare global { interface Window { acquireVsCodeApi?: () => EditorHost } }
let acquiredHost: EditorHost | undefined;
export function getEditorHost(): EditorHost | undefined {
  if (typeof window === 'undefined' || !window.acquireVsCodeApi) return undefined;
  return acquiredHost ??= window.acquireVsCodeApi();
}

const record = (value: unknown): value is Record<string, unknown> => !!value && typeof value === 'object' && !Array.isArray(value);
const position = (value: unknown): value is EditorPosition => record(value) && Number.isSafeInteger(value.line) && Number(value.line) >= 0 && Number.isSafeInteger(value.character) && Number(value.character) >= 0;
/** The host already validates Lean's response; this rejects unrelated window messages. */
export function parseEditorMessage(value: unknown): EditorMessage | undefined {
  if (!record(value) || typeof value.requestId !== 'string' || !/^(0|[1-9][0-9]{0,19})$/.test(value.requestId) || !record(value.document)) return undefined;
  const doc = value.document;
  if (typeof doc.uri !== 'string' || typeof doc.fileName !== 'string' || !Number.isSafeInteger(doc.version) || Number(doc.version) < 0 || !record(doc.selection) || !position(doc.selection.start) || !position(doc.selection.end)) return undefined;
  if (value.type === 'statementlens.status' && ['analyzing', 'idle', 'stale'].includes(String(value.phase))) return value as unknown as EditorMessage;
  if (value.type === 'statementlens.error' && typeof value.message === 'string') return value as unknown as EditorMessage;
  if (value.type === 'statementlens.analysis' && record(value.analysis) && typeof value.analysis.source === 'string' && record(value.analysis.tree) && typeof value.analysis.tree.id === 'string' && Array.isArray(value.analysis.tree.children) && record(value.analysis.expression)) return value as unknown as EditorMessage;
  return undefined;
}

export interface EditorSession { requestId: string; document: EditorDocument; phase: 'analyzing' | 'idle' | 'stale' | 'error' }
/** The extension numbers requests monotonically within a webview lifetime. */
export function acceptsEditorStatus(session: EditorSession | null, message: Extract<EditorMessage, { type: 'statementlens.status' }>): boolean {
  if (!session) return true;
  if (BigInt(message.requestId) < BigInt(session.requestId)) return false;
  if (message.requestId !== session.requestId) return true;
  if (message.document.uri !== session.document.uri || message.document.version < session.document.version) return false;
  return message.phase !== 'analyzing' || session.phase === 'analyzing';
}
/** A result can only fill the exact document/version requested by the current host session. */
export function acceptsEditorResult(session: EditorSession | null, message: EditorMessage): boolean {
  return !!session && session.phase === 'analyzing' && message.requestId === session.requestId && message.document.uri === session.document.uri && message.document.version === session.document.version && message.document.selection.start.line === session.document.selection.start.line && message.document.selection.start.character === session.document.selection.start.character && message.document.selection.end.line === session.document.selection.end.line && message.document.selection.end.character === session.document.selection.end.character;
}
