import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';
import type { SemanticObject } from '../semantic/types';
import { RestrictedRegionDiagram } from './RestrictedMapFigure';
import { layoutRestrictedMap, type RestrictedRegionText } from './restricted-map-layout';

const size = (width: number, height = 22): DiagramTextSize => ({ width, height, ascent: height * .8, descent: height * .2 });
const region = (carrierWidth: number, nameWidth: number): RestrictedRegionText => ({
  carrier: size(carrierWidth), carrierRole: size(76, 13), role: size(106, 14), name: size(nameWidth), note: size(73, 13),
});
const contains = (outer: DiagramRect, inner: DiagramRect) => inner.x >= outer.x && inner.y >= outer.y
  && inner.x + inner.width <= outer.x + outer.width && inner.y + inner.height <= outer.y + outer.height;
const overlaps = (a: DiagramRect, b: DiagramRect) => a.x < b.x + b.width && a.x + a.width > b.x
  && a.y < b.y + b.height && a.y + a.height > b.y;

describe('restricted map label layout', () => {
  it('fits wide glyph labels in their owning regions and carriers', () => {
    // The Unicode regression exceeded the old 204-unit carrier and 168-unit region.
    const layout = layoutRestrictedMap(region(240, 290), region(270, 320), size(225), size(238), size(160, 13), size(330, 13));
    expect(layout.width).toBeGreaterThan(680);
    for (const side of [layout.source, layout.target]) {
      expect(contains(side.carrier, side.region)).toBe(true);
      for (const key of ['carrier', 'carrierRole'] as const) expect(contains(side.carrier, side.labels[key])).toBe(true);
      for (const key of ['role', 'name', 'note'] as const) expect(contains(side.region, side.labels[key])).toBe(true);
    }
    for (const label of [layout.forward, layout.inverse, layout.continuity]) {
      expect(label.x).toBeGreaterThan(layout.source.carrier.x + layout.source.carrier.width);
      expect(label.x + label.width).toBeLessThan(layout.target.carrier.x);
    }
  });

  it('keeps tall or asymmetric glyph boxes and arrow lanes disjoint', () => {
    const source = { ...region(30, 900), carrier: size(30, 180), name: size(900, 240) };
    const target = { ...region(780, 30), carrierRole: size(76, 95), role: size(106, 140), note: size(73, 110) };
    const layout = layoutRestrictedMap(source, target, size(320, 450), size(420, 370), size(560, 320), size(2200, 130));
    const labels = [...Object.values(layout.source.labels), ...Object.values(layout.target.labels), layout.forward, layout.inverse, layout.continuity, layout.note];
    const frame = { x: 0, y: 0, width: layout.width, height: layout.height };
    for (const label of labels) expect(contains(frame, label)).toBe(true);
    for (let i = 0; i < labels.length; i++) for (let j = i + 1; j < labels.length; j++) expect(overlaps(labels[i], labels[j])).toBe(false);
    for (const arrow of Object.values(layout.arrows)) {
      const lane = { x: Math.min(arrow.from.x, arrow.to.x), y: arrow.from.y - 6, width: Math.abs(arrow.to.x - arrow.from.x), height: 12 };
      for (const label of labels) expect(overlaps(lane, label)).toBe(false);
    }
  });

  it('attaches both arrow directions to the region boundaries after asymmetric resizing', () => {
    const layout = layoutRestrictedMap(region(750, 300), region(35, 70), size(600), size(630), size(170, 13), size(330, 13));
    const sourcePort = layout.source.region.x + layout.source.region.width, targetPort = layout.target.region.x;
    expect(layout.arrows.forward.from.x).toBe(sourcePort);
    expect(layout.arrows.forward.to.x).toBe(targetPort);
    expect(layout.arrows.inverse.from.x).toBe(targetPort);
    expect(layout.arrows.inverse.to.x).toBe(sourcePort);
    for (const side of [layout.source, layout.target]) for (const arrow of Object.values(layout.arrows)) {
      expect(arrow.from.y).toBeGreaterThan(side.region.y);
      expect(arrow.from.y).toBeLessThan(side.region.y + side.region.height);
    }
  });

  it('renders complete Unicode names and keeps observed region identities', () => {
    const object = (id: string, label: string): SemanticObject => ({ id, label, kind: 'variable', type: 'abstract type',
      expression: { kind: 'var', id, name: label, type: 'abstract type' }, scopeId: 'scope:clause', provenance: [] });
    const map = object('map', '局所座標変換同相写像'.repeat(3)), carrier = object('carrier', '重み付き配置空間全体型'.repeat(3));
    const source = object('source-region', `${map.label}.source`);
    const html = renderToStaticMarkup(createElement(RestrictedRegionDiagram, { structure: {
      map, sourceCarrier: carrier, targetCarrier: carrier, source: { role: 'source', label: source.label, object: source, empty: false },
      target: { role: 'target', label: `${map.label}.target`, empty: false }, direction: 'forward', sameCarrier: true,
      properties: { sourceOpen: true, targetOpen: true, forwardContinuousOnSource: true, inverseContinuousOnTarget: true },
    }, selectedRegion: 'source', onObjectSelect: () => {} }));
    expect(html).toContain(`data-diagram-label="source-carrier"`);
    expect(html).toContain(`data-diagram-source="${carrier.label}"`);
    expect(html).toContain(`data-diagram-source="${source.label}"`);
    expect(html).toContain(`data-diagram-source="${map.label}⁻¹"`);
    expect(html).toContain('class="katex"');
    expect(html).toContain('<foreignObject');
    expect(html).toContain('data-reading-object="source-region"');
    expect(html).toContain(`aria-label="${source.label}"`);
    expect(html).toContain('data-region-evidence="source-expression" data-region-selected="true"');
    expect(html).not.toContain('…');
  });
});
