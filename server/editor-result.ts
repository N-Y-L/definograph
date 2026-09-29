import { createExactJsonTools } from '../src/packets/packet.js';
import { WorkerError, type WorkerResult } from './protocol.js';

/** Keep legacy JSON number/tree behavior while parsing the new exact attachment
 * from its original bytes. JSON.parse alone would erase its duplicate keys and
 * round unsafe integers. The top-level scan is iterative and string-aware. */
export function parseEditorResult(text: string): WorkerResult {
  let result: unknown;
  try { result = JSON.parse(text); }
  catch { throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned invalid JSON.'); }
  if (!result || typeof result !== 'object' || Array.isArray(result)
    || typeof (result as WorkerResult).ok !== 'boolean' || !Array.isArray((result as WorkerResult).diagnostics)) {
    throw new WorkerError('EDITOR_PROTOCOL', 'The context worker returned an invalid response.');
  }
  let at = 0;
  const space = () => { while (/\s/.test(text[at] ?? '') && at < text.length) at++; };
  const stringEnd = () => {
    at++;
    while (at < text.length) { const c = text[at++]; if (c === '"') return; if (c === '\\') at++; }
  };
  const keys = new Set<string>();
  space(); at++; space();
  while (text[at] !== '}') {
    const keyStart = at; stringEnd();
    const key = JSON.parse(text.slice(keyStart, at)) as string;
    if (keys.has(key)) throw new WorkerError('EDITOR_PROTOCOL', 'Duplicate context response key: ' + key);
    keys.add(key); space(); at++; space();
    const start = at;
    let depth = 0;
    while (at < text.length) {
      const c = text[at];
      if (c === '"') { stringEnd(); continue; }
      if (c === '[' || c === '{') {
        if (++depth > 2048) throw new WorkerError('EDITOR_PROTOCOL', 'Context response nesting exceeds its limit.');
      } else if (c === ']' || c === '}') { if (depth === 0) break; depth--; }
      else if (c === ',' && depth === 0) break;
      at++;
    }
    if (key === 'sourceSnapshot' || key === 'sourceOccurrence' || key === 'sourceHeadExposure' || key === 'sourceDecomposition') (result as WorkerResult)[key] = createExactJsonTools().parse(text.slice(start, at));
    if (text[at] === '}') break;
    at++; space();
  }
  return result as WorkerResult;
}
