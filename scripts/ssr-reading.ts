import assert from 'node:assert/strict';

/** Extract the outer active guide from production React SSR. Supplementary
 * field laws have their own complete readers, so an inner details marker is
 * not the boundary of the surrounding guide. React escapes source text and
 * attribute values; balancing actual section tags keeps this dependency-free. */
export function activeReadingGuide(html: string): string {
  const start = html.indexOf('<section class="reading-guide"');
  assert.ok(start >= 0, 'The production reader must include an active guide');
  const sections = /<(\/?)section\b[^>]*>/g;
  sections.lastIndex = start;
  let depth = 0, tag: RegExpExecArray | null;
  while ((tag = sections.exec(html))) {
    depth += tag[1] ? -1 : 1;
    if (depth === 0) return html.slice(start, sections.lastIndex);
  }
  assert.fail('The production active guide must have a balanced outer section');
}
