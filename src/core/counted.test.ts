import { readdirSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';
import { counted } from './counted';

describe('counted', () => {
  it.each([[0, '0 entries'], [1, '1 entry'], [2, '2 entries']] as const)('writes %i entries with the noun in the right number', (count, phrase) => {
    expect(counted(count, 'entry', 'entries')).toBe(phrase);
  });
  it.each([[0, '0 frames'], [1, '1 frame'], [2, '2 frames']] as const)('adds "s" for %i frames unless the count is 1', (count, phrase) => {
    expect(counted(count, 'frame')).toBe(phrase);
  });
  it.each([[0, '0 further ordered children'], [1, '1 further ordered child'], [2, '2 further ordered children']] as const)('takes an irregular plural for %i children', (count, phrase) => {
    expect(counted(count, 'further ordered child', 'further ordered children')).toBe(phrase);
  });
});

// Every count the reader writes before a noun goes through counted() or chooses its noun by the count. This scan finds a
// count written directly before a fixed plural noun in the reader's editor, packet and visual sources. Each exception names
// a text whose number is never 1 there, or is not a count of that noun.
const SOURCES = fileURLToPath(new URL('..', import.meta.url));
const NOUNS = 'entries|frames|outcomes|operations|steps|objects|boundaries|nodes|positions|snapshots|ports|inputs|contexts|relations|binders|choices|dependencies|coordinates|fields|checks|children|declarations|assumptions|clauses|occurrences';
// A JSX attribute value ({relation} relations={...}) is not prose: neither an interpolation after "=" nor a noun before "=".
const COUNT_BEFORE_PLURAL = new RegExp(String.raw`(?:\$\{|(?<!=)\{)[^{}\n]{1,160}\}[ \t]+(?:[a-z-]+[ \t]+){0,3}(?:${NOUNS})\b(?!=)`, 'g');
const EXCEPTIONS: [string, string][] = [
  ['editor/SourceDecompositionReading.tsx', 'aria-label={`Step ${index + 1} outcomes`}'],                   // step N's outcomes: an ordinal
  ['editor/SourceProvenanceReading.tsx', 'accepted > 1\n      ? `These ${accepted} accepted outcomes'],     // written only for more than one
  ['editor/source-snapshot.ts', 'bad(`string exceeds ${maximum} characters`'],                            // validation limits of 36 or more
  ['packets/StructuralReading.tsx', "unused.' : drawing.contextDeclarationIds.length ? `All ${drawing.contextDeclarationIds.length} context entries"],
  ['visual/DistanceProfileView.tsx', "'the 1 coordinate' : `all ${profile.dimension} coordinates"],      // the branch for two or more (twice)
  ['visual/GuidedReading.tsx', "=== 1 ? 'Given' : `${assumptions.length} assumptions"],                  // the branch for two or more
];
it('writes no count before a fixed plural noun in src/editor, src/packets and src/visual', () => {
  const found: string[] = [];
  for (const dir of ['editor', 'packets', 'visual']) for (const file of readdirSync(path.join(SOURCES, dir))) {
    if (!/\.tsx?$/.test(file) || /\.test\.|test-fixtures/.test(file)) continue;
    const source = readFileSync(path.join(SOURCES, dir, file), 'utf8');
    for (const match of source.matchAll(COUNT_BEFORE_PLURAL)) {
      const around = source.slice(Math.max(0, match.index! - 120), match.index! + match[0].length + 2);
      if (!EXCEPTIONS.some(([where, text]) => where === `${dir}/${file}` && around.includes(text))) found.push(`${dir}/${file}: ${match[0]}`);
    }
  }
  expect(found).toEqual([]);
});
