import { describe, expect, it } from 'vitest';
import type { JsonValue } from './packet';
import { recordedName } from './recorded-name';

const str = (parent: JsonValue, text: string): JsonValue => ['str', parent, text];
const anonymous: JsonValue = ['anonymous'];
const path = (...parts: string[]): JsonValue => parts.reduce<JsonValue>(str, anonymous);
const num = (parent: JsonValue, value: number): JsonValue => ['num', parent, ['nat', String(value)]];

/** Expected classes are literal cases from Lean's structural rule, not a
 * second call to the formatting helper or substring matching. */
describe('recorded names follow Lean macro scopes and original anonymity', () => {
  it.each([
    { title: 'ordinary', value: path('x'), expected: 'x' },
    { title: 'internal hygiene', value: num(path('a', '_@', '_internal', '_hyg'), 0), expected: null },
    { title: 'multiple macro scopes', value: num(num(path('a', '_@', 'M', '_hyg'), 3), 5), expected: null },
    { title: 'anonymous', value: anonymous, expected: null },
    { title: 'nonterminal marker', value: path('a', '_hyg', 'b'), expected: 'a._hyg.b' },
    { title: 'substring only', value: path('x_hyg'), expected: 'x_hyg' },
    { title: 'ordinary numeric suffix', value: num(path('x'), 0), expected: 'x.#0' },
    { title: 'numeric name rooted at anonymous', value: num(anonymous, 0), expected: '#0' },
    { title: 'nested numeric name rooted at anonymous', value: num(num(anonymous, 3), 5), expected: '#3.#5' },
    { title: 'terminal marker', value: path('a', '_hyg'), expected: null },
  ])('$title has the prescribed class for both display nouns', ({ value, expected }) => {
    const before = JSON.stringify(value);
    for (const noun of ['binder', 'context entry'] as const) expect(recordedName(value, noun)).toBe(expected ?? `unnamed ${noun}`);
    expect(JSON.stringify(value)).toBe(before);
  });
});
