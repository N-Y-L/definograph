import { describe, expect, it } from 'vitest';
import { acceptsEditorResult, acceptsEditorStatus, parseEditorMessage, type EditorDocument, type EditorMessage, type EditorSession } from './host';
const document: EditorDocument = { uri: 'file:///fixture.lean', fileName: 'fixture.lean', version: 4, selection: { start: { line: 1, character: 0 }, end: { line: 1, character: 8 } } };
const session: EditorSession = { requestId: '2', document, phase: 'analyzing' };
const message: EditorMessage = { type: 'statementlens.error', requestId: '2', document, message: 'Selected term is not a proposition' };
describe('editor host boundary', () => {
  it('accepts the exact request and rejects stale request, file, version, and selection results', () => {
    expect(acceptsEditorResult(session, message)).toBe(true);
    expect(acceptsEditorResult(session, { ...message, document: { ...document, selection: { end: { character: 8, line: 1 }, start: { character: 0, line: 1 } } } })).toBe(true);
    expect(acceptsEditorResult(null, message)).toBe(false);
    expect(acceptsEditorResult({ ...session, phase: 'stale' }, message)).toBe(false);
    for (const change of [{ requestId: 'old' }, { document: { ...document, version: 3 } }, { document: { ...document, uri: 'file:///other.lean' } }, { document: { ...document, selection: { ...document.selection, end: { line: 2, character: 0 } } } }]) expect(acceptsEditorResult(session, { ...message, ...change })).toBe(false);
  });
  it('rejects unrelated or malformed messages instead of admitting untracked analyses', () => {
    expect(parseEditorMessage(message)).toEqual(message);
    for (const value of [null, 'analysis', {}, { ...message, requestId: undefined }, { ...message, type: 'random' }, { ...message, document: { ...document, version: -1 } }, { ...message, document: { ...document, selection: { start: { line: 1, character: -1 }, end: document.selection.end } } }, { ...message, type: 'statementlens.analysis', analysis: {} }]) expect(parseEditorMessage(value)).toBeUndefined();
  });
  it('does not let an obsolete status clear a newer result, and accepts a real buffer edit', () => {
    const status = { type: 'statementlens.status' as const, requestId: '1', document, phase: 'analyzing' as const };
    expect(acceptsEditorStatus(session, status)).toBe(false);
    expect(acceptsEditorStatus({ ...session, phase: 'idle' }, { ...status, requestId: '2' })).toBe(false);
    expect(acceptsEditorStatus({ ...session, phase: 'idle' }, { ...status, requestId: '2', phase: 'stale', document: { ...document, version: 5 } })).toBe(true);
    expect(acceptsEditorStatus(session, { ...status, requestId: '3' })).toBe(true);
  });
});
