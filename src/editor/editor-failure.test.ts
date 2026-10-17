import { describe, expect, it } from 'vitest';
import type { StatementNode } from '../core';
import { GUIDED_CONTEXT_CONTRACT } from './guided-context-contract';
import { EDITOR_UNREADABLE, editorFailureTitle, readableEditorMessage } from './editor-failure';
import { parseEditorMessage, type EditorDocument, type EditorMessage } from './host';

const document: EditorDocument = { uri: 'file:///fixture.lean', fileName: 'fixture.lean', version: 4, selection: { start: { line: 1, character: 0 }, end: { line: 1, character: 8 } } };
const leaf: StatementNode = { id: 'n.selected', kind: 'predicate', label: 'True', lean: 'True', children: [], expression: { kind: 'const', name: 'True' } };
/** A complete guided reading of the shape Context.lean exports: a context parameter around the selected term. */
const analysis = {
  ok: true, source: 'example (n : Nat) : True := trivial', pretty: 'True', type: 'Prop', guidedContextContract: GUIDED_CONTEXT_CONTRACT,
  validation: 'kernel-type-checked-context-fragment', provenance: { assistant: 'lean', inputMode: 'editor' }, diagnostics: [], metrics: [],
  tree: { id: 'context', kind: 'parameter', label: 'Context parameter n', lean: 'Nat', children: [leaf],
    binder: { id: 'context.binder', name: 'n', type: 'Nat', role: 'parameter', dependsOn: [] },
    expression: { kind: 'lambda', binder: { id: 'context.binder', name: 'n', type: 'Nat' }, binderType: { kind: 'const', name: 'Nat' }, body: leaf.expression } },
  expression: { kind: 'const', name: 'True' },
};
const envelope = { type: 'statementlens.analysis', requestId: '2', document, analysis };

describe('a reading from the Lean editor', () => {
  it('passes through unchanged when it has the shape the reader draws', () => {
    const parsed = parseEditorMessage(envelope)!;
    expect(parsed.type).toBe('statementlens.analysis');
    expect(readableEditorMessage(parsed)).toBe(parsed);
  });

  it('becomes an error naming the first bad field when a part deep in the tree is malformed', () => {
    // parseEditorMessage checks only the root of the tree, so this reading reaches the page.
    const malformed = { ...analysis, tree: { ...analysis.tree, children: [{ ...leaf, expression: { kind: 'app', fn: { kind: 'const', name: 'f' } } }] } };
    const parsed = parseEditorMessage({ ...envelope, analysis: malformed })!;
    expect(parsed.type).toBe('statementlens.analysis');
    const checked = readableEditorMessage(parsed);
    expect(checked).toMatchObject({ type: 'statementlens.error', requestId: '2', document, code: EDITOR_UNREADABLE, source: analysis.source,
      message: "Definograph could not read Lean's answer: tree.children[0].expression.args is not a list." });
    expect(editorFailureTitle(EDITOR_UNREADABLE)).toBe("Definograph could not read Lean's answer.");
  });

  it('leaves errors and status messages alone', () => {
    const error: EditorMessage = { type: 'statementlens.error', requestId: '2', document, message: 'x', code: 'EDITOR_TRUST' };
    expect(readableEditorMessage(error)).toBe(error);
    const status: EditorMessage = { type: 'statementlens.status', requestId: '2', document, phase: 'analyzing' };
    expect(readableEditorMessage(status)).toBe(status);
  });
});

describe('the title of an editor error', () => {
  it('blames the input only for errors about the input', () => {
    for (const code of ['EDITOR_SELECTION', 'EDITOR_FILE', 'EDITOR_PROJECT', 'EDITOR_SOURCE_LIMIT']) expect(editorFailureTitle(code), code).toBe('The input could not be read.');
    for (const code of ['EDITOR_TRUST', 'EDITOR_TIMEOUT', 'EDITOR_VERSION', 'EDITOR_CONFIG', 'EDITOR_STALE', 'EDITOR_PROTOCOL', 'EDITOR_COMPATIBILITY', 'EDITOR_UNAVAILABLE', 'EDITOR_FAILED', 'EDITOR_OUTPUT_LIMIT', 'EDITOR_OCCURRENCE'])
      expect(editorFailureTitle(code), code).not.toMatch(/input|statement/i);
    expect(editorFailureTitle('EDITOR_TIMEOUT')).toBe('Lean was stopped at its time limit.');
  });

  it('names neither Lean nor the input when there is no code', () => {
    // The extension sends no code for Lean's or Definograph's refusal of a selection, nor for its own messages.
    for (const code of [undefined, '', 'SOMETHING_NEW']) expect(editorFailureTitle(code)).toBe('This selection was not read.');
  });
});
