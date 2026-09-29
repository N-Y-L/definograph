/** English count phrases for the reader's prose. A count takes the singular noun only when it is exactly 1: "1 entry",
 * "0 entries", "2 entries". Pass the plural when adding "s" is wrong (entry/entries, child/children). */
export function counted(count: number, singular: string, plural = `${singular}s`): string {
  return `${count} ${count === 1 ? singular : plural}`;
}
