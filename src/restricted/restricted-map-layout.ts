import type { DiagramRect, DiagramTextSize } from '../components/map-diagram-layout';

export interface RestrictedRegionText {
  carrier: DiagramTextSize;
  carrierRole: DiagramTextSize;
  role: DiagramTextSize;
  name: DiagramTextSize;
  note: DiagramTextSize;
}
export interface RestrictedLabelBox extends DiagramRect { baseline: number }
export interface RestrictedRegionLayout {
  carrier: DiagramRect;
  region: DiagramRect;
  labels: Record<keyof RestrictedRegionText, RestrictedLabelBox>;
}

/** Carrier and region labels stay in their own frames. The map labels occupy
 * the corridor between carriers, with two clear horizontal arrow lanes. */
export function layoutRestrictedMap(source: RestrictedRegionText, target: RestrictedRegionText,
  forward: DiagramTextSize, inverse: DiagramTextSize, continuity: DiagramTextSize, note: DiagramTextSize) {
  const frameWidths = (text: RestrictedRegionText) => {
    const region = Math.max(168, text.role.width + 32, text.name.width + 32, text.note.width + 32);
    return { region, carrier: Math.max(204, region + 36, text.carrier.width + 32, text.carrierRole.width + 32) };
  };
  const sourceWidths = frameWidths(source), targetWidths = frameWidths(target);
  const gap = Math.max(252, forward.width + 40, inverse.width + 40, continuity.width + 40);
  const contentWidth = sourceWidths.carrier + gap + targetWidths.carrier;
  const width = Math.max(contentWidth + 20, note.width + 32);
  const sourceX = (width - contentWidth) / 2, targetX = sourceX + sourceWidths.carrier + gap;
  const carrierNameTop = 42;
  const carrierRoleTop = carrierNameTop + Math.max(source.carrier.height, target.carrier.height) + 6;
  const regionTop = carrierRoleTop + Math.max(source.carrierRole.height, target.carrierRole.height) + 18;
  const roleTop = regionTop + 16;
  const forwardY = Math.max(roleTop + Math.max(source.role.height, target.role.height) + 16, forward.height + 26);
  const middleHeight = Math.max(source.name.height, target.name.height, continuity.height);
  const middleY = forwardY + 14 + middleHeight / 2;
  const inverseY = middleY + middleHeight / 2 + 14;
  const regionNoteTop = inverseY + 14;
  const regionBottom = regionNoteTop + Math.max(source.note.height, target.note.height) + 16;
  const carrierBottom = regionBottom + 26;
  const noteTop = Math.max(carrierBottom, inverseY + 14 + inverse.height) + 14;
  const place = (text: DiagramTextSize, center: number, top: number): RestrictedLabelBox =>
    ({ x: center - text.width / 2, y: top, width: text.width, height: text.height, baseline: top + text.ascent });
  const region = (text: RestrictedRegionText, x: number, widths: ReturnType<typeof frameWidths>): RestrictedRegionLayout => {
    const center = x + widths.carrier / 2;
    return {
      carrier: { x, y: 26, width: widths.carrier, height: carrierBottom - 26 },
      region: { x: center - widths.region / 2, y: regionTop, width: widths.region, height: regionBottom - regionTop },
      labels: {
        carrier: place(text.carrier, center, carrierNameTop), carrierRole: place(text.carrierRole, center, carrierRoleTop),
        role: place(text.role, center, roleTop), name: place(text.name, center, middleY - text.name.height / 2),
        note: place(text.note, center, regionNoteTop),
      },
    };
  };
  const sourceLayout = region(source, sourceX, sourceWidths), targetLayout = region(target, targetX, targetWidths);
  const mapX = sourceX + sourceWidths.carrier + gap / 2;
  const sourcePortX = sourceLayout.region.x + sourceLayout.region.width, targetPortX = targetLayout.region.x;
  return {
    width, height: noteTop + note.height + 12, source: sourceLayout, target: targetLayout,
    forward: place(forward, mapX, forwardY - 12 - forward.height),
    inverse: place(inverse, mapX, inverseY + 14),
    continuity: place(continuity, mapX, middleY - continuity.height / 2),
    note: place(note, width / 2, noteTop),
    arrows: {
      forward: { from: { x: sourcePortX, y: forwardY }, to: { x: targetPortX, y: forwardY } },
      inverse: { from: { x: targetPortX, y: inverseY }, to: { x: sourcePortX, y: inverseY } },
    },
  };
}
