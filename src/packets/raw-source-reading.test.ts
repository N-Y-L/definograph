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

  it('shows the caller’s content in place of a closed child position and keeps the branch in the checked drawing', () => {
    const frame: JsonValue = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: [],
      sourceTerm: ['app', ['const', name, []], ['lit', ['natVal', ['nat', '3']]]], sourceType: ['const', name, []] };
    const model = drawing(frame, 'frame'), asked: string[] = [];
    const html = renderToStaticMarkup(createElement(RawSourceReading, { drawing: model, closedEdge: (node, edge) => {
      asked.push(`${node.family}:${edge.role}`);
      return node.family === 'frame' && edge.role === 'sourceTerm' ? createElement('p', { 'data-closed-content': '' }, 'closed by the caller') : undefined;
    } }));
    const term = html.split('data-raw-role="sourceTerm"')[1].split('data-raw-role="sourceType"')[0];
    expect(term).toContain('data-raw-closed="true"'); expect(term).toContain('closed by the caller');
    expect(term).not.toContain('data-raw-constructor'); expect(term).not.toContain('data-raw-fold');
    expect(html.match(/data-raw-closed=/g)).toHaveLength(1);
    expect(html.split('data-raw-role="sourceType"')[1]).toContain('data-raw-constructor="const"');
    expect(html).toContain('Exact constructor readback checked');
    expect(html).toContain(`${model.nodes.length} constructor nodes retained`);
    // The closed branch is never visited, by the initial fold or by the drawing, so no position inside it can be closed or chosen.
    expect([...new Set(asked)].sort()).toEqual(['expression:levels', 'frame:originalDeclarations', 'frame:sourceTerm', 'frame:sourceType']);
    expect(render(model)).toContain('data-raw-constructor="app"'); expect(render(model)).not.toContain('data-raw-closed');
  });

  it('spends none of the initial fold on a closed branch, so what follows it starts drawn', () => {
    let sourceTerm: JsonValue = ['lit', ['natVal', ['nat', '3']]];
    for (let depth = 0; depth < 10; depth++) sourceTerm = ['app', ['const', name, []], sourceTerm];
    const model = drawing({ schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: [], sourceTerm, sourceType: ['const', name, []] }, 'frame');
    const type = (html: string) => html.split('data-raw-role="sourceType"')[1];
    // Drawn whole, the term takes the initial 32 nodes and the type after it starts folded.
    expect(type(render(model))).toContain('data-raw-fold'); expect(type(render(model))).not.toContain('data-raw-constructor="const"');
    const closing = (node: { family: string }, edge: { role: string }) => node.family === 'frame' && edge.role === 'sourceTerm';
    const closed = renderToStaticMarkup(createElement(RawSourceReading, { drawing: model, closedEdge: (node, edge) => closing(node, edge) ? 'closed' : undefined }));
    expect(type(closed)).toContain('data-raw-constructor="const"'); expect(type(closed)).not.toContain('data-raw-fold');
    const visible = expandRawBranch(model, new Set(), model.rootId, 32, closing);
    const term = model.nodes.find(node => node.id === model.rootId)!.children.find(edge => edge.role === 'sourceTerm')!.nodeId;
    expect(visible.has(term)).toBe(false); expect(visible.size).toBeLessThan(32);
    expect(expandRawBranch(model, new Set(), model.rootId, 32).has(term)).toBe(true);
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
