/** A requested refusal must be captured as a decomposition record. An outer
 * transport omission cannot serve as evidence of the operation's refusal.
 * The caller still validates the record and its recorded refusal outcome. */
export function requireRecordedRefusal(response: {
  sourceDecomposition?: unknown;
  sourceDecompositionUnavailable?: unknown;
}, expected: boolean, label: string): void {
  if (expected && (response.sourceDecompositionUnavailable !== undefined || response.sourceDecomposition === undefined)) {
    throw new Error(`Expected an explicit refusal record for ${label}, but no decomposition record was returned.`);
  }
}
