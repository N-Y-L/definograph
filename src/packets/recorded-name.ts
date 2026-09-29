import type { JsonValue } from './packet';
import { nameText } from './syntax';

/** Lean 4.28 Name.hasMacroScopes: numeric suffixes recurse, a string node tests
 * only its terminal component. Anonymous names are separately unnamed here. */
export function recordedName(value: JsonValue, noun: 'binder' | 'context entry'): string {
  if (Array.isArray(value) && value[0] === 'anonymous') return `unnamed ${noun}`;
  let node = value;
  while (Array.isArray(node) && node[0] === 'num') node = node[1];
  if (Array.isArray(node) && node[0] === 'str' && node[2] === '_hyg') return `unnamed ${noun}`;
  try { return nameText(value as never); } catch { return `unnamed ${noun}`; }
}
