import { createContext, useContext } from 'react';
import type { SemanticDocument } from '../semantic/types';

/** Identity hues in order of assignment. No two share a lightness (CIE L* runs from 30 to 49 in steps of about 3), so
 * they stay apart without colour vision, and each keeps 4.5:1 contrast on the light surface. The darkest is the
 * closest to neutral ink on a thin glyph, so it comes last and is the hue a statement uses least. */
export const IDENTITY_PALETTE = ['#4a68c6', '#725001', '#618004', '#9d438d', '#613897', '#016b4c', '#004f53'] as const;
/** Compound expressions, hypotheses, recorded context entries and objects beyond the palette. Neutral ink is not a
 * hue: past the seventh object, different objects share it and are told apart by their labels. */
export const NEUTRAL_INK = 'var(--ink)';
export type IdentityColors = ReadonlyMap<string, string>;

const none: IdentityColors = new Map();

/** One hue per object that a binder introduces, in order of first introduction, never reused within the statement.
 * The statement's own binders, which are the skeleton's binder rows, come first; binders local to one expression
 * (a function body, a bounded union) take what is left. A hypothesis is drawn as a clause and a recorded context
 * entry is not a choice, so neither takes a hue. A reading nested inside another one (a field law) passes the
 * enclosing assignment as `inherited`: shared objects keep their hue and new ones take only hues still unused.
 * Colour is never the only carrier; every object keeps its label. */
export function assignIdentityColors(document: Pick<SemanticDocument, 'objects' | 'tree'>, inherited: IdentityColors = none): IdentityColors {
  const colors = new Map(inherited);
  const used = new Set(inherited.values());
  const free = IDENTITY_PALETTE.filter(color => !used.has(color));
  const ownBinders = new Set<string>();
  for (const pending = [document.tree]; pending.length;) {
    const node = pending.pop()!;
    if (node.binder) ownBinders.add(node.binder.id);
    pending.push(...node.children);
  }
  const eligible = document.objects.filter(object => object.binder && object.binder.role !== 'assumption' && object.binder.role !== 'auxiliary' && !colors.has(object.id));
  for (const object of [...eligible.filter(object => ownBinders.has(object.binder!.id)), ...eligible.filter(object => !ownBinders.has(object.binder!.id))]) {
    if (!free.length) break;
    colors.set(object.id, free.shift()!);
  }
  return colors;
}

const IdentityColorContext = createContext<IdentityColors>(none);
/** Supplied once per reading by StatementReadingView; every figure inside it draws from the same assignment. */
export const IdentityColorProvider = IdentityColorContext.Provider;
export function useIdentityColors(): IdentityColors { return useContext(IdentityColorContext); }
/** The hue assigned to an object in the enclosing reading, or neutral ink. */
export function useIdentityColor(): (id: string | undefined) => string {
  const colors = useIdentityColors();
  return id => (id ? colors.get(id) : undefined) ?? NEUTRAL_INK;
}
