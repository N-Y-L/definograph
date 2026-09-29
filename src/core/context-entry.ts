import type { Binder } from './types';

/** Recorded declaration kinds describe the capture, not authorship or logical use. */
export function contextEntryTitle(binder: Pick<Binder, 'name' | 'declarationKind'>): string {
  return `${binder.declarationKind === 'auxDecl' ? 'Auxiliary entry' : 'Context entry'} ${binder.name}, recorded kind ${binder.declarationKind ?? 'unavailable'}`;
}

/** Shown once per reading when recorded kinds were given but could not be matched to its context. */
export const UNMATCHED_RECORDED_KINDS = 'The recorded declaration kinds could not be matched to this context; its entries are shown without roles.';

/** The recorded nondefault kinds, which read neutrally in every view. */
export function neutralEntryKind(kind: string | null | undefined): kind is 'auxDecl' | 'implDetail' {
  return kind === 'auxDecl' || kind === 'implDetail';
}

/** The neutral label for an entry of a nondefault recorded kind; an ordinary entry has none.
 * The recorded kind decides, never the entry's name or constructor. */
export function recordedEntryLabel(kind: string | null | undefined): string | undefined {
  return neutralEntryKind(kind) ? `${kind === 'auxDecl' ? 'Auxiliary entry' : 'Context entry'}, recorded kind ${kind}` : undefined;
}
