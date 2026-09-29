import { createHash } from 'node:crypto';
import { describe, expect, it } from 'vitest';
import { boundedNatural, encodeNatural, MAX_NATURAL_DIGITS, NaturalError, naturalText, readNatural } from './natural';

describe('versioned exact naturals', () => {
  it('preserves adjacent naturals beyond the browser integer range without numeric conversion', () => {
    const first = readNatural(['nat', '9007199254740992'], 2), second = readNatural(['nat', '9007199254740993'], 2);
    expect(first).not.toEqual(second);
    expect(naturalText(first, 2)).toBe('9007199254740992');
    expect(naturalText(second, 2)).toBe('9007199254740993');
    expect(JSON.stringify(first)).toBe('["nat","9007199254740992"]');
    expect(JSON.stringify(second)).toBe('["nat","9007199254740993"]');
    const sha = (value: unknown) => createHash('sha256').update(JSON.stringify(value), 'utf8').digest('hex');
    // Independently calculated SHA-256 of the literal ASCII byte strings above.
    expect(sha(first)).toBe('17195c76a1d0199f07a75a7e0afb91ec4a27ac1af91d41d2bbd3d7cd2c20f7d0');
    expect(sha(second)).toBe('ba3ec0081f464f3cfcd8726e04e08073c7eef20e65ab4539ef86a551ee580845');
    expect(sha(first)).not.toBe(sha(second));
  });

  it.each(['0', '1', '42', '9007199254740991', '9007199254740993'])('accepts the canonical v2 spelling %s and preserves v1 where representable', digits => {
    expect(readNatural(['nat', digits], 2)).toEqual(['nat', digits]);
    expect(naturalText(['nat', digits])).toBe(digits);
    const value = Number(digits);
    if (Number.isSafeInteger(value)) {
      expect(readNatural(value, 1)).toBe(value);
      expect(naturalText(value)).toBe(digits);
      expect(encodeNatural(value, 1)).toBe(value);
      expect(encodeNatural(value, 2)).toEqual(['nat', digits]);
    }
  });

  it.each(['', '00', '01', '+1', '-0', '-1', ' 1', '1 ', '1\n', '1.0', '1e2', '1_000', '١', '１', '∞'])('rejects noncanonical decimal text %j', digits => {
    expect(() => readNatural(['nat', digits], 2)).toThrow(NaturalError);
  });

  it.each([0, 1, '1', ['nat'], ['nat', 1], ['nat', '1', 'extra'], ['natural', '1'], null, true, { nat: '1' }])('rejects the wrong v2 role representation %j', value => {
    expect(() => readNatural(value, 2)).toThrow('v2 natural');
  });

  it('rejects extended or sparse tuples and wrong-profile encodings', () => {
    const extended = ['nat', '1']; Object.defineProperty(extended, 'extra', { value: 2 });
    const symbolic = ['nat', '1']; Object.defineProperty(symbolic, Symbol('extra'), { value: 2 });
    const sparse = new Array(2); sparse[0] = 'nat';
    for (const value of [extended, symbolic, sparse]) expect(() => readNatural(value, 2)).toThrow('v2 natural');
    expect(() => readNatural(['nat', '0'], 1)).toThrow('v1 natural');
    expect(() => naturalText(0, 2)).toThrow('v2 natural');
    expect(() => naturalText(['nat', '0'], 1)).toThrow('v1 natural');
    for (const value of [-1, 0.5, Infinity, NaN, Number.MAX_SAFE_INTEGER + 1]) expect(() => encodeNatural(value, 2)).toThrow('v1 natural');
  });

  it('makes the finite digit limit explicit without shortening the accepted value', () => {
    const accepted = '9'.repeat(MAX_NATURAL_DIGITS);
    expect(naturalText(readNatural(['nat', accepted], 2), 2)).toBe(accepted);
    try { readNatural(['nat', accepted + '9'], 2); throw new Error('unexpected acceptance'); }
    catch (error) { expect(error).toBeInstanceOf(NaturalError); expect((error as NaturalError).code).toBe('limit'); }
  });

  it('checks exact magnitude before converting a bounded index', () => {
    expect(boundedNatural(['nat', '9'], 2, 10)).toBe(9);
    expect(boundedNatural(9, 1, 10)).toBe(9);
    expect(boundedNatural(['nat', '9007199254740990'], 2, Number.MAX_SAFE_INTEGER)).toBe(9007199254740990);
    for (const digits of ['10', '11', '9007199254740992', '9007199254740993', '9'.repeat(1000)]) expect(() => boundedNatural(['nat', digits], 2, 10)).toThrow('less than 10');
    expect(() => boundedNatural(['nat', '0'], 2, 0)).toThrow('less than 0');
    for (const bound of [-1, 0.5, Infinity, NaN, Number.MAX_SAFE_INTEGER + 1]) expect(() => boundedNatural(['nat', '0'], 2, bound)).toThrow('safe integer');
    expect(() => boundedNatural(['nat', '01'], 2, 10)).toThrow('canonical ASCII');
  });
});
