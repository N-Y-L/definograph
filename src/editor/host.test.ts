import { describe, expect, it } from 'vitest';
import { acceptsEditorResult, acceptsEditorStatus, parseEditorMessage, type EditorDocument, type EditorMessage, type EditorSession } from './host';
const document: EditorDocument = { uri: 'file:///fixture.lean', fileName: 'fixture.lean', version: 4, selection: { start: { line: 1, character: 0 }, end: { line: 1, character: 8 } } };
const session: EditorSession = { requestId: '2', document, phase: 'analyzing' };
const message: EditorMessage = { type: 'statementlens.error', requestId: '2', document, message: 'Selected term is not a proposition' };
describe('editor host boundary', () => {
  it('refuses absent and unsupported guided context contracts explicitly', () => {
    const analysis = { source: 'True', tree: { id: 'root', children: [] }, expression: {} };
    for (const guidedContextContract of [undefined, 'unsupported']) {
      const result = parseEditorMessage({ ...message, type: 'statementlens.analysis', analysis: { ...analysis, guidedContextContract } });
      expect(result?.type).toBe('statementlens.error');
      expect(result && 'code' in result && result.code).toBe('EDITOR_COMPATIBILITY');
    }
    expect(parseEditorMessage({ ...message, type: 'statementlens.analysis', analysis: { ...analysis, guidedContextContract: 'definograph.guided-context.v1' } })?.type).toBe('statementlens.analysis');
    expect(parseEditorMessage({ ...message, type: 'statementlens.analysis', analysis: { source: 'True', guidedContextContract: 'unsupported' } })?.type).toBe('statementlens.error');
  });
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
  it('discards the superseded result of two back-to-back refreshes in either arrival order and keeps the accepted one', () => {
    // The same reducer App.tsx runs: a status replaces the session when accepted; a result fills the session only when accepted.
    const run = (messages: EditorMessage[]) => {
      let current: EditorSession | null = null; const filled: string[] = [];
      for (const incoming of messages) {
        if (incoming.type === 'statementlens.status') { if (incoming.phase !== 'idle' && acceptsEditorStatus(current, incoming)) current = { requestId: incoming.requestId, document: incoming.document, phase: incoming.phase }; continue; }
        if (!acceptsEditorResult(current, incoming)) continue;
        filled.push(incoming.requestId); current = { requestId: incoming.requestId, document: incoming.document, phase: 'idle' };
      }
      return { filled, current };
    };
    const status = (requestId: string): EditorMessage => ({ type: 'statementlens.status', requestId, document, phase: 'analyzing' });
    const result = (requestId: string): EditorMessage => ({ ...message, requestId });
    // Overlapping: the second request starts before the first result; the first result arrives late and is discarded.
    expect(run([status('12'), status('13'), result('12'), result('13'), result('12'), status('12')])).toEqual({ filled: ['13'], current: { requestId: '13', document, phase: 'idle' } });
    // Sequential: the first result was displayed, then superseded by the second; a duplicate of the first is discarded afterwards.
    expect(run([status('12'), result('12'), status('13'), result('13'), result('12')])).toEqual({ filled: ['12', '13'], current: { requestId: '13', document, phase: 'idle' } });
    // A result for a request never announced by a status is discarded.
    expect(run([status('12'), result('13')])).toEqual({ filled: [], current: { requestId: '12', document, phase: 'analyzing' } });
  });
  it('keeps an occurrence on guided errors only with the exact fresh origin and snapshot', () => {
    const captureId = '550e8400-e29b-41d4-a716-446655440000';
    const unavailable = { status: 'unavailable', kind: 'prerequisite', phase: 'preparation', reason: 'No checking was performed.' };
    const sourceSnapshot = { schema: 'definograph.source-snapshot.v1',
      selection: { startByte: 0, endByte: 8, requestedStartByte: 0, requestedEndByte: 8, parentDeclaration: null },
      policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
      expectedType: { status: 'absent' }, original: unavailable, prepared: unavailable, checking: { ...unavailable, attempted: false } };
    const sourceSnapshotOrigin = { kind: 'local-editor-process-snapshot', captureId, sourceSha256: '0'.repeat(64),
      engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
      project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
      document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' };
    const sourceOccurrence = { schema: 'definograph.source-occurrence.v1', captureId,
      parentCaptureId: '660e8400-e29b-41d4-a716-446655440000', path: ['lamBody'],
      policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
      checking: { ...unavailable, attempted: false } };
    const response = { ...message, sourceSnapshot, sourceSnapshotOrigin, sourceOccurrence };
    const parsed = parseEditorMessage(response);
    expect(parsed?.type).toBe('statementlens.error');
    expect(parsed && 'sourceOccurrence' in parsed && parsed.sourceOccurrence).toEqual(sourceOccurrence);
    expect(Object.isFrozen(parsed && 'sourceOccurrence' in parsed && parsed.sourceOccurrence)).toBe(true);
    const incompatible = parseEditorMessage({ ...response, type: 'statementlens.analysis',
      analysis: { source: 'True', tree: { id: 'root', children: [] }, expression: {} } });
    expect(incompatible?.type).toBe('statementlens.error');
    expect(incompatible && 'sourceOccurrence' in incompatible && incompatible.sourceOccurrence).toEqual(sourceOccurrence);
    expect(parseEditorMessage({ ...response, type: 'statementlens.analysis', sourceSnapshotOrigin: undefined,
      analysis: { source: 'True', tree: { id: 'root', children: [] }, expression: {} } })).toBeUndefined();
    for (const altered of [
      { ...response, sourceSnapshot: undefined },
      { ...response, sourceSnapshotOrigin: undefined },
      { ...response, sourceOccurrence: { ...sourceOccurrence, captureId: sourceOccurrence.parentCaptureId } },
      { ...response, sourceOccurrence: { ...sourceOccurrence, path: ['metadata'] } },
      { ...response, sourceOccurrenceUnavailable: 'also omitted' },
      { ...response, sourceSnapshotOrigin: { ...sourceSnapshotOrigin, document: { ...sourceSnapshotOrigin.document, version: 3 } } },
    ]) expect(parseEditorMessage(altered)).toBeUndefined();
  });
  it('accepts a bounded independent omission and refuses malformed or oversized omissions', () => {
    expect(parseEditorMessage({ ...message, sourceOccurrenceUnavailable: 'No fresh occurrence record was produced.' })).toBeDefined();
    for (const omission of [null, {}, 'x'.repeat(4097)]) expect(parseEditorMessage({ ...message, sourceOccurrenceUnavailable: omission })).toBeUndefined();
  });
});
