import assert from 'node:assert/strict';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { planReadingPresentation, visibleReadingNodes, type ReadingRegion } from '../reading/presentation';
import type { ReadingDocument } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';
import { readSkeleton, type SkeletonRow } from './skeleton-readback';
import { StatementReadingView } from './StatementReadingView';

/** What a drawn skeleton must say: kind, source nodes and ordered children of every region, written here from the
 * region tree alone and independently of the renderer. A region outside the visible set is one counted stub. */
export interface RegionView { kind: string; nodeIds: readonly string[]; folded?: number; children: { edge: string; row: RegionView }[] }
/** The edges of the region tree, written here apart from the renderer's regionParts; the role oracle walks them too. */
export function regionEdges(region: ReadingRegion): { edge: string; region: ReadingRegion }[] {
  if (region.kind === 'binders') return region.body ? [{ edge: 'body', region: region.body }] : [];
  if (region.kind === 'implication') return [...region.assumptions.map(assumption => ({ edge: 'assumption', region: assumption })), { edge: 'conclusion', region: region.conclusion }];
  if (region.kind === 'negation') return [{ edge: 'negated', region: region.body }];
  if (region.kind === 'clause') return [];
  const edge = { all: 'conjunct', alternatives: 'alternative', equivalence: 'side', structure: 'part' }[region.kind];
  return region.children.map(child => ({ edge, region: child }));
}
const size = (region: ReadingRegion): number => 1 + regionEdges(region).reduce((sum, child) => sum + size(child.region), 0);
export function regionView(region: ReadingRegion, visible?: ReadonlySet<string>): RegionView {
  if (visible && !region.sourceNodeIds.some(id => visible.has(id))) return { kind: region.kind, nodeIds: region.sourceNodeIds, folded: size(region), children: [] };
  return { kind: region.kind, nodeIds: region.sourceNodeIds, children: regionEdges(region).map(child => ({ edge: child.edge, row: regionView(child.region, visible) })) };
}
/** The structure a readback carries, without the labels drawn on it. */
export function rowView(row: SkeletonRow): RegionView {
  return { kind: row.kind, nodeIds: row.nodeIds, ...(row.folded === undefined ? {} : { folded: row.folded }), children: row.children.map(child => ({ edge: child.edge, row: rowView(child.row) })) };
}

/** The one mark each role is drawn with, stated here apart from the renderer's own table: a row that printed ∀ on a
 * witness would otherwise read back as the right tree. A stub prints no separate mark. */
const MARKS: Record<string, string> = { forall: '∀', exists: '∃', all: '∧', alternatives: '∨', equivalence: '↔', negation: '¬' };
function assertMarks(row: SkeletonRow): void {
  const expected = MARKS[row.binder ?? row.kind];
  if (expected && row.folded === undefined) assert.equal(row.mark, expected, `Skeleton row ${row.id} is drawn with the wrong role mark.`);
  row.children.forEach(child => assertMarks(child.row));
}

export function renderReading(document: SemanticDocument, reading: ReadingDocument): string {
  return renderToStaticMarkup(createElement(StatementReadingView, { document, reading, onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
}
/** Draw the reading and require its skeleton to read back to the region tree the reader plans for it, each quantifier
 * and connective row under its own mark. Used by the unit tests and, on real Lean exports, by
 * scripts/atlas-integration.ts; it throws on a mismatch. */
export function assertSkeletonReadsBack(document: SemanticDocument, reading: ReadingDocument, html = renderReading(document, reading)): SkeletonRow {
  const component = document.presentation?.kind === 'component' && document.presentation.targetNodeId;
  const root = planReadingPresentation(reading, { boundaryNodeIds: component ? [component] : [] }).root;
  const row = readSkeleton(html);
  assert.deepEqual(rowView(row), regionView(root, visibleReadingNodes(reading, 100)), 'The drawn skeleton does not read back to the region tree.');
  assertMarks(row);
  return row;
}
