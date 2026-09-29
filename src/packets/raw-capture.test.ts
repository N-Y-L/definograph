import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { parseRawSourceText } from './raw-import';
import { readRawInspection } from './raw';
import { RawSourceReading } from './RawSourceReading';
import type { JsonObject, JsonValue } from './packet';

const path = process.env.DEFINOGRAPH_RAW_CAPTURES;
const cases = path ? JSON.parse(readFileSync(path, 'utf8')) as { label: string; frame: JsonObject }[] : [];
describe.skipIf(!path)('actual Lean raw frame corpus', () => {
  it('imports, independently reconstructs and renders every retained actual constructor frame', async () => {
    expect(cases.length).toBeGreaterThanOrEqual(27);
    for (const test of cases) {
      const imported = await parseRawSourceText(JSON.stringify(test.frame));
      const readback = readRawInspection(imported.drawing);
      expect(readback.ok, test.label).toBe(true);
      if (!readback.ok) throw new Error(readback.error.message);
      expect(readback.value).toEqual({ family: 'frame', value: test.frame });
      const html = renderToStaticMarkup(createElement(RawSourceReading, { drawing: imported.drawing }));
      expect(html, test.label).toContain('Exact constructor readback checked');
      expect(html, test.label).not.toContain('data-reference-target');
      expect(html, test.label).not.toContain('data-home');
      expect(Object.isFrozen(imported.drawing.nodes)).toBe(true);
    }
  });

  it('preserves exact 10000-digit natural text in the actual source and visible-field model', async () => {
    const test = cases.find(test => test.label.includes('10000'))!;
    expect(test).toBeDefined();
    const imported = await parseRawSourceText(JSON.stringify(test.frame));
    const fields = imported.drawing.nodes.flatMap(node => node.fields).filter(field => field.kind === 'natural' && field.value[1].length === 10000);
    expect(fields.length).toBeGreaterThan(0);
    // The generator constructs 10^9999, independently of the wire decoder.
    const digits = '1' + '0'.repeat(9999);
    expect(fields.some(field => (field.value as JsonValue[])[1] === digits)).toBe(true);
  });
});
