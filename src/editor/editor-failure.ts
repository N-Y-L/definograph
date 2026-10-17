import { analysisShapeIssue } from '../core/analysis-shape';
import type { EditorMessage } from './host';

/** The code of an editor reading that arrived but does not have the shape the reader draws. */
export const EDITOR_UNREADABLE = 'EDITOR_UNREADABLE';

/** An editor reading is checked like a browser reading before anything is drawn. One with a malformed part
 * becomes an error naming the first bad field, so it is reported instead of reaching the semantic compiler.
 * The source attachments, already checked by parseEditorMessage, are kept unchanged. */
export function readableEditorMessage(message: EditorMessage): EditorMessage {
  if (message.type !== 'statementlens.analysis') return message;
  const issue = analysisShapeIssue(message.analysis);
  if (!issue) return message;
  const { analysis, ...attachments } = message;
  return { ...attachments, type: 'statementlens.error', source: analysis.source, code: EDITOR_UNREADABLE,
    message: `Definograph could not read Lean's answer: ${issue}.` };
}

/** Error codes sent by server/editor-context.ts through the extension, and the one above. */
const EDITOR_TITLES: Record<string, string> = {
  EDITOR_SELECTION: 'The input could not be read.', EDITOR_FILE: 'The input could not be read.',
  EDITOR_PROJECT: 'The input could not be read.', EDITOR_SOURCE_LIMIT: 'The input could not be read.',
  EDITOR_TRUST: 'This workspace is not trusted.',
  EDITOR_VERSION: 'This project uses another Lean version.',
  EDITOR_CONFIG: 'Definograph could not use this project or engine setup.',
  EDITOR_UNAVAILABLE: 'The Lean context process could not start.',
  EDITOR_TIMEOUT: 'Lean was stopped at its time limit.',
  EDITOR_OUTPUT_LIMIT: 'Lean wrote more output than Definograph accepts.',
  EDITOR_STALE: 'The source or the engine changed during this reading.',
  EDITOR_COMPATIBILITY: 'The editor package, this reader and the Lean engine do not match.',
  EDITOR_OCCURRENCE: 'This step could not be continued.', EDITOR_HEAD_EXPOSURE: 'This step could not be continued.',
  EDITOR_DECOMPOSITION: 'This step could not be continued.',
  EDITOR_PROTOCOL: 'Definograph could not use the answer of its Lean context process.',
  EDITOR_FAILED: 'The Lean context process stopped unexpectedly.',
  [EDITOR_UNREADABLE]: "Definograph could not read Lean's answer.",
};

/** A short title that is true for the error's code. Without a code the error is Lean's or Definograph's
 * refusal of the selection, or the extension's own message, so the title names neither. */
export function editorFailureTitle(code: string | undefined): string {
  return (code && EDITOR_TITLES[code]) || 'This selection was not read.';
}
