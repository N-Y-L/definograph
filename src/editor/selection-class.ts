/** How Lean's elaborator classified the selected term: a proposition, a proof of
 * one, or neither. The native adapter reports `Meta.isProp` of the term and of
 * its inferred type. It is not a kernel check and establishes no receipt. */
export type SelectionClass = 'proposition' | 'proof' | 'other';
export function isSelectionClass(value: unknown): value is SelectionClass {
  return value === 'proposition' || value === 'proof' || value === 'other';
}
