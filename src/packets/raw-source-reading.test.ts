import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import { buildRawInspection, type RawFamily, type RawInspectionDrawing } from './raw';
import { RawSourceReading, expandRawBranch } from './RawSourceReading';
import RawSourceReader from './RawSourceReader';
import { PacketReading } from './PacketReader';
import { parsePacket, type JsonValue } from './packet';

const name: JsonValue = ['str', ['anonymous'], 'unresolved'];
const raw: JsonValue = ['mdata', ['mdataEntries', [[name, ['ofInt', ['negSucc', ['nat', '9007199254740993']]]], [name, ['ofSyntax', ['ident', ['none'], ['substring', 'α\u200b', ['nat', '99'], ['nat', '0']], name, []]]]]], ['app', ['mvar', name], ['bvar', ['nat', '17']]]];
function drawing(value: JsonValue, family: RawFamily = 'expression') {
  const result = buildRawInspection({ family, value }, { sourceIdentity: 'ui-control' });
  if (!result.ok) throw new Error(result.error.message);
  return result.value;
}
function render(model: RawInspectionDrawing) { return renderToStaticMarkup(createElement(RawSourceReading, { drawing: model })); }

describe('raw constructor inspection UI', () => {
  it('shows family-qualified ordered constructor roles and no semantic reference links', () => {
    const model = drawing(raw), html = render(model);
    expect(html).toContain('aria-label="Raw source data"');
    expect(html).toContain('Exact constructor readback checked');
    expect(html).toContain('without checking scope, typing or mathematical validity');
    for (const family of ['expression', 'metadata', 'metadataEntry', 'integer', 'syntax', 'substring']) expect(html).toContain(`data-raw-family="${family}"`);
    expect(html).toContain('data-raw-constructor="negSucc"');
    expect(html).toContain('Stored reference identifier; no declaration is resolved');
    expect(html).toContain('Positions are not applied to the string');
    expect(html).not.toContain('data-reference-target'); expect(html).not.toContain('data-home');
    expect(html).not.toContain('aria-controls'); expect(html).not.toContain('<a ');
    expect(html).not.toContain('<pre>');
    expect(model.nodes.filter(node => node.family === 'metadataEntry')).toHaveLength(2);
  });

  it('bounds the visible frontier of wide collections instead of mounting all folded siblings', () => {
    const model = drawing(Array.from({ length: 1000 }, () => ['missing']), 'syntaxList');
    const html = render(model);
    expect(html.match(/data-raw-order=/g)?.length).toBe(40);
    expect(html).toContain('960 further ordered children');
    expect(html).toContain('Show next 40 child positions');
    expect(expandRawBranch(model, new Set(), model.rootId, 32).size).toBe(32);
    const initial = expandRawBranch(model, new Set(), model.rootId, 32);
    expect(expandRawBranch(model, initial, model.rootId).size).toBe(72);
  });

  it('refuses mutated drawing connections before rendering a success label', () => {
    const model = structuredClone(drawing(raw));
    model.nodes[0].children[0].nodeId = 'missing';
    const html = render(model);
    expect(html).toContain('role="alert"');
    expect(html).not.toContain('Exact constructor readback checked');
  });

  it('provides local frame input and navigation to both existing readers', () => {
    const html = renderToStaticMarkup(createElement(RawSourceReader));
    expect(html).toContain('type="file"'); expect(html).toContain('id="raw-source-text"');
    expect(html).toContain('href="/packet"'); expect(html).toContain('href="/"');
    expect(html).toContain('does not run Lean');
  });
});

const fixtures = process.env.DEFINOGRAPH_V2_PACKET_FIXTURES;
describe.skipIf(!fixtures)('actual packet raw view evidence boundaries', () => {
  for (const file of ['let-context', 'missing', 'incoherent', 'refused', 'timeout']) {
    it(`preserves imported ${file} outcomes while selecting raw data`, async () => {
      const packet = await parsePacket(readFileSync(join(fixtures!, file + '.packet.json'), 'utf8'));
      const html = renderToStaticMarkup(createElement(PacketReading, { packet, initialView: 'raw' }));
      expect(html).toContain('Unverified imported packet');
      expect(html).toContain('no joint certification is established');
      expect(html).toContain(`<dd>${packet.payload.results[0].report.formation.tag}</dd>`);
      expect(html).toContain(`<dd>${packet.payload.results[0].report.evidence.tag}</dd>`);
      expect(html).not.toContain('data-reference-target');
    });
  }
});
