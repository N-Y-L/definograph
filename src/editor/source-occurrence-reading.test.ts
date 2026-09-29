import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { SourceOccurrenceReading } from './SourceSnapshotReading';
import { sourceOccurrenceReading } from './source-occurrence-reading';
import { validateSourceSnapshot } from './source-snapshot';
import { validateSourceOccurrence, type SourceOccurrence } from './source-occurrence';

describe('occurrence guided adapter boundaries', () => {
  it('does not invent a reading when extraction is unavailable or has no selected candidate', () => {
    const unavailable = { checking: { status: 'unavailable' } } as SourceOccurrence;
    const absent = { checking: { status: 'captured', selected: null } } as SourceOccurrence;
    for (const target of ['term', 'type'] as const) {
      expect(sourceOccurrenceReading(unavailable, target)).toBeUndefined();
      expect(sourceOccurrenceReading(absent, target)).toBeUndefined();
    }
  });
});

const corpus = process.env.DEFINOGRAPH_POSITIONAL_GUIDED_CAPTURES;
describe.skipIf(!corpus)('actual occurrence guided editor presentation', () => {
  const rows = corpus ? JSON.parse(readFileSync(corpus, 'utf8')) as { label: string; response: Record<string, unknown> }[] : [];
  function occurrence(index: number): SourceOccurrence {
    const response = rows[index].response;
    return validateSourceOccurrence(response.sourceOccurrence, validateSourceSnapshot(response.sourceSnapshot));
  }

  it('defaults to the shared guide with exact source and separate recorded outcomes', () => {
    expect(rows.length).toBe(5);
    const value = occurrence(0);
    const html = renderToStaticMarkup(createElement(SourceOccurrenceReading, { value }));
    expect(html).toContain('6 kernel outcomes retained');
    expect(html).toContain('data-occurrence-target="term"');
    expect(html).toContain('Chosen occurrence guided reading');
    expect(html).toContain('Full visual reading');
    expect(html).toContain('Expression and context');
    expect(html).toContain('Exact occurrence source');
    expect(html).toContain('data-occurrence-source-path="[&quot;checking&quot;,&quot;selected&quot;,&quot;term&quot;]"');
    expect(html).not.toContain('Full visual statement');
    expect(html).not.toContain('Whole statement');
    expect(html).not.toContain('Unverified imported packet');
  });

  it('retains the complete positional structure as an independent alternative', () => {
    const html = renderToStaticMarkup(createElement(SourceOccurrenceReading, { value: occurrence(0), initialView: 'structure' }));
    expect(html).toContain('data-positional="true"');
    expect(html).toContain('data-structure-root="term"');
    expect(html).toContain('data-structure-root="type"');
    expect(html).toContain('6 kernel outcomes retained');
    expect(html).not.toContain('data-occurrence-target=');
  });

  it('presents a captured proof term and its inferred type as separately addressed targets', () => {
    const value = occurrence(4);
    if (value.checking.status !== 'captured' || !value.checking.selected) throw new Error('missing proof capture');
    const term = sourceOccurrenceReading(value, 'term')!, type = sourceOccurrenceReading(value, 'type')!;
    expect(term.document).toBeDefined(); expect(type.document).toBeDefined();
    expect(term.sourceById[term.targetNodeId!].syntax).toEqual(value.checking.selected.term);
    expect(type.sourceById[type.targetNodeId!].syntax).toEqual(value.checking.selected.type);
    expect(term.sourceById[term.targetNodeId!].syntax).not.toEqual(type.sourceById[type.targetNodeId!].syntax);
    expect(term.contextNodeIds).toEqual(type.contextNodeIds);
    expect(term.targetNodeId).not.toEqual(type.targetNodeId);
    expect(term.targetNodeId).toContain(value.captureId);
    expect(term.sourceById[term.targetNodeId!].path).toEqual(['checking', 'selected', 'term']);
    expect(type.sourceById[type.targetNodeId!].path).toEqual(['checking', 'selected', 'type']);
  });

  it('changes source identities on a fresh occurrence capture without changing its syntax', () => {
    const value = occurrence(0);
    const fresh = { ...value, captureId: '00000000-0000-0000-0000-000000000999' };
    const original = sourceOccurrenceReading(value, 'term')!, changed = sourceOccurrenceReading(fresh, 'term')!;
    expect(original.targetNodeId).not.toEqual(changed.targetNodeId);
    expect(original.document?.source).toBe(changed.document?.source);
    expect(Object.keys(original.sourceById).some(id => id in changed.sourceById)).toBe(false);
  });
});
