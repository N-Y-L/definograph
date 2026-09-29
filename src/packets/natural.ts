/** Semantic naturals use canonical decimal tags in v2. Operational collection
 * indices remain safe JSON numbers; this codec never relaxes JSON parsing. */
export type NaturalProfile = 1 | 2;
export type TaggedNatural = ['nat', string];
export type ExactNatural = number | TaggedNatural;
export const MAX_NATURAL_DIGITS = 10_000;

export class NaturalError extends Error {
  constructor(readonly code: 'malformed' | 'unsupported' | 'limit', message: string) {
    super(message); this.name = 'NaturalError';
  }
}

function profileIsSupported(profile: NaturalProfile): void {
  if (profile !== 1 && profile !== 2) throw new NaturalError('unsupported', 'unsupported natural encoding profile');
}

export function readNatural(value: unknown, profile: NaturalProfile): ExactNatural {
  profileIsSupported(profile);
  if (profile === 1) {
    if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0)
      throw new NaturalError('malformed', 'v1 natural must be a nonnegative safe integer');
    return value;
  }
  if (!Array.isArray(value) || value.length !== 2 || Reflect.ownKeys(value).length !== 3 || !Object.hasOwn(value, 0) || !Object.hasOwn(value, 1) || value[0] !== 'nat' || typeof value[1] !== 'string')
    throw new NaturalError('malformed', 'v2 natural must be ["nat", canonical ASCII decimal digits]');
  if (value[1].length > MAX_NATURAL_DIGITS)
    throw new NaturalError('limit', `natural exceeds the ${MAX_NATURAL_DIGITS}-digit implementation limit`);
  if (value[1].length === 0 || /[^0-9]/.test(value[1]) || (value[1].length > 1 && value[1][0] === '0'))
    throw new NaturalError('malformed', 'v2 natural must be ["nat", canonical ASCII decimal digits]');
  return ['nat', value[1]];
}

/** Inference is for readable presentation only. Validation boundaries pass the
 * enclosing profile explicitly, so a mixed representation cannot be accepted. */
export function naturalText(value: unknown, profile?: NaturalProfile): string {
  const natural = readNatural(value, profile ?? (typeof value === 'number' ? 1 : 2));
  return typeof natural === 'number' ? String(natural) : natural[1];
}

/** Compare exact decimal magnitude before converting an index to a machine
 * number. Large source values can never round into the permitted interval. */
export function boundedNatural(value: unknown, profile: NaturalProfile, exclusiveBound: number): number {
  if (!Number.isSafeInteger(exclusiveBound) || exclusiveBound < 0)
    throw new NaturalError('malformed', 'exclusive natural bound must be a nonnegative safe integer');
  const digits = naturalText(value, profile), bound = String(exclusiveBound);
  if (digits.length > bound.length || (digits.length === bound.length && digits >= bound))
    throw new NaturalError('limit', `natural must be less than ${bound}`);
  return Number(digits);
}

export function encodeNatural(value: number, profile: NaturalProfile): ExactNatural {
  profileIsSupported(profile);
  const natural = readNatural(value, 1) as number;
  return profile === 1 ? natural : ['nat', String(natural)];
}
