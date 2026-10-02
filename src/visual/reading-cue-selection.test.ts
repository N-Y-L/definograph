import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it, vi } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic/compiler';
import { compileReading } from '../reading/compiler';
import { compileReadingCues } from '../reading/cues';
import { GuidedReading } from './GuidedReading';
import { StatementReadingView } from './StatementReadingView';
import { createReadingCueSelection, notifyReadingCueSelection, resolveReadingCue, type ReadingCueSelection } from './reading-cue-selection';

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, type: string): Binder => ({ id, name: id, type, role: 'universal', dependsOn: [] });
const variable = (binding: Binder): Expr => ({ kind: 'var', id: binding.id, name: binding.name, type: binding.type });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value') });
const leaf = (id: string, expression: Expr): StatementNode => ({ id, kind: 'predicate', label: id, lean: `${id} source`, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });

function fixture() {
  const image = app('Set.image', [variable(binder('f', 'X → Y')), variable(binder('A', 'Set X'))]);
  const tree = node('conditions', 'and', [leaf('inclusion', app('Set.Subset', [image, variable(binder('B', 'Set Y'))])), leaf('unresolved', constant('Unfamiliar.claim'))]);
  const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
  const reading = compileReading(document, { selectedNodeId: 'inclusion' });
  const plan = compileReadingCues(reading, document);
  const construction = plan.cues.find(cue => cue.stage.kind === 'construction' && cue.stage.relationKind === 'image')!;
  const inclusion = plan.cues.find(cue => cue.stage.relationKind === 'subset')!;
  expect(construction).toBeDefined();
  expect(inclusion).toBeDefined();
  expect(construction.nodeId).toBe(inclusion.nodeId);
  const resolve = (selection?: ReadingCueSelection | null, selectedNodeId = reading.selection.nodeId, selectedRelationId?: string) => resolveReadingCue({
    plan, document, selectedNodeId, rootNodeId: reading.root.id, selectedRelationId, selection,
  });
  return { document, reading, plan, construction, inclusion, resolve };
}

describe('exact guided-reading attention', () => {
  it('restores the inclusion stage after remounting instead of the preceding construction in the same clause', () => {
    const { document, reading, construction, inclusion, resolve } = fixture();
    const selectedCue = createReadingCueSelection(document, inclusion);
    expect(resolve()).toBe(construction);
    expect(resolve(selectedCue)).toBe(inclusion);
    for (let mount = 0; mount < 2; mount++) {
      const html = renderToStaticMarkup(createElement(StatementReadingView, {
        document, reading: compileReading(document, { selectedNodeId: reading.selection.nodeId }), selectedCue,
      }));
      expect(html).toContain(`data-cue-id="${inclusion.id}"`);
      expect(html).not.toContain(`data-cue-id="${construction.id}"`);
    }
  });

  it('refuses an earlier document even when every cue and source ID is reused', () => {
    const original = fixture(), replacement = fixture();
    expect(replacement.document).not.toBe(original.document);
    expect(replacement.plan.cues.map(cue => cue.id)).toEqual(original.plan.cues.map(cue => cue.id));
    expect(replacement.resolve(createReadingCueSelection(original.document, original.inclusion))).toBe(replacement.construction);
  });

  it('requires the retained cue, source node, and staged relation to agree', () => {
    const { document, inclusion, construction, resolve } = fixture();
    const selection = createReadingCueSelection(document, inclusion);
    for (const invalid of [
      { ...selection, cueId: 'cue:missing' },
      { ...selection, nodeId: 'unresolved' },
      { ...selection, relationId: construction.stage.relationId },
      { ...selection, relationId: undefined },
    ]) expect(resolve(invalid)).toBe(construction);
  });

  it('lets an explicit different node or relation override retained attention', () => {
    const { document, inclusion, construction, plan, resolve } = fixture();
    const selection = createReadingCueSelection(document, inclusion);
    const other = plan.cues.find(cue => cue.nodeId === 'unresolved')!;
    expect(resolve(selection, 'unresolved')).toBe(other);
    expect(resolve(selection, inclusion.nodeId, construction.stage.relationId)).toBe(construction);
    expect(resolve(selection, 'unresolved', construction.stage.relationId)).toBe(other);
    expect(resolve(selection, inclusion.nodeId, 'relation:missing')).toBe(construction);
  });

  it('accepts source nodes grouped into the same introduction without guessing by their names', () => {
    const tree = node('bind-x', 'forall', [node('bind-y', 'forall', [leaf('claim', constant('Unfamiliar.claim'))], binder('y', 'X'))], binder('x', 'X'));
    const document = compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
    const reading = compileReading(document, { selectedNodeId: 'bind-x' });
    const plan = compileReadingCues(reading, document);
    const introduction = plan.cues[0];
    expect(introduction.nodeId).toBe('bind-y');
    expect(introduction.sourceNodeIds).toEqual(['bind-x', 'bind-y']);
    const selection = createReadingCueSelection(document, introduction, 'bind-x');
    expect(resolveReadingCue({ plan, document, rootNodeId: reading.root.id, selectedNodeId: 'bind-y', selection })).toBe(introduction);
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, selectedCue: selection }));
    expect(html).toContain(`data-cue-id="${introduction.id}"`);
  });

  it('routes keyboard navigation through node, exact source, then retained-cue callbacks', () => {
    const { document, reading, plan, construction, inclusion } = fixture();
    const events: string[] = [];
    let retained: ReadingCueSelection | null = null;
    const onChoose = (cue: typeof inclusion) => notifyReadingCueSelection(createReadingCueSelection(document, cue), {
      onNodeSelect: id => { events.push(`node:${id}`); retained = null; },
      onSourceSelect: id => events.push(`source:${id}`),
      onCueChange: selection => { events.push(`cue:${selection?.cueId}`); retained = selection; },
    });
    vi.stubGlobal('HTMLSelectElement', class {});
    try {
      const guide = GuidedReading({ plan, cue: construction, reading, document, onChoose, children: null });
      const navigation = guide.props.children[0];
      const preventDefault = vi.fn();
      navigation.props.onKeyDown({ target: {}, key: 'ArrowRight', preventDefault });
      expect(preventDefault).toHaveBeenCalledOnce();
      expect(events).toEqual([`node:${inclusion.nodeId}`, `source:${inclusion.stage.relationId}`, `cue:${inclusion.id}`]);
      expect(retained).toEqual(createReadingCueSelection(document, inclusion));
      events.length = 0;
      const previousGuide = GuidedReading({ plan, cue: inclusion, reading, document, onChoose, children: null });
      previousGuide.props.children[0].props.onKeyDown({ target: {}, key: 'ArrowLeft', preventDefault });
      expect(events).toEqual([`node:${construction.nodeId}`, `source:${construction.stage.relationId}`, `cue:${construction.id}`]);
    } finally { vi.unstubAllGlobals(); }
  });

  it('preserves source-node notifications for stages without a relation', () => {
    const { document, plan } = fixture();
    const logic = plan.cues.find(cue => cue.stage.kind === 'logic')!;
    const events: string[] = [];
    notifyReadingCueSelection(createReadingCueSelection(document, logic), {
      onNodeSelect: id => events.push(`node:${id}`), onSourceSelect: id => events.push(`source:${id}`),
      onCueChange: selection => events.push(`cue:${selection?.cueId}`),
    });
    expect(events).toEqual([`node:${logic.nodeId}`, `source:${logic.nodeId}`, `cue:${logic.id}`]);
  });
});
