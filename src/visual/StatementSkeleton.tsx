import type { CSSProperties, ReactNode } from 'react';
import { FigureScroll } from '../components/FigureScroll';
import { contextEntryTitle } from '../core/context-entry';
import { counted } from '../core/counted';
import type { ReadingRegion } from '../reading/presentation';
import { formatExpression } from '../semantic/expression';
import type { SemanticDocument } from '../semantic/types';
import { compactLabel } from './layout';
import { useIdentityColor } from './object-identity';
import { binderGroupTitle, componentMode, connectiveWords, roleSymbol } from './region-words';
import './statement-skeleton.css';

export interface StatementSkeletonProps {
  root: ReadingRegion;
  document: SemanticDocument;
  /** A region with no node in this set is drawn as one stub that counts the rows it holds. */
  visibleNodes: ReadonlySet<string>;
  /** The region of the current reading step. */
  activeRegionId?: string;
  /** The selected node. In a hypothesis chain it picks the one Given mark that carries the current step. */
  activeNodeId?: string;
  selectedObjectId?: string;
  onNodeSelect?: (id: string) => void;
}

type Part = { edge: 'body' | 'assumption' | 'conclusion' | 'negated' | 'conjunct' | 'alternative' | 'side' | 'part'; region: ReadingRegion };
function parts(region: ReadingRegion): Part[] {
  switch (region.kind) {
    case 'binders': return region.body ? [{ edge: 'body', region: region.body }] : [];
    case 'implication': return [...region.assumptions.map(assumption => ({ edge: 'assumption' as const, region: assumption })), { edge: 'conclusion', region: region.conclusion }];
    case 'negation': return [{ edge: 'negated', region: region.body }];
    case 'clause': return [];
    default: return region.children.map(child => ({ edge: region.kind === 'all' ? 'conjunct' as const : region.kind === 'alternatives' ? 'alternative' as const : region.kind === 'equivalence' ? 'side' as const : 'part' as const, region: child }));
  }
}
const rowCount = (region: ReadingRegion): number => 1 + parts(region).reduce((sum, part) => sum + rowCount(part.region), 0);
/** A clause or structure row's own text: Lean's where the node has it, and the region kind before an empty row. */
const ownText = (region: ReadingRegion): string => (region.kind === 'structure' ? region.node.phrase || region.node.lean : region.node.lean || region.node.phrase) || region.kind;

/** The statement drawn as nested scope frames, straight from the region tree. A row governs exactly the rows inside
 * its frame, at every depth. The only text is the node's Lean text, a binder's name and type, the role words the
 * full reading already uses and, in place of an empty row, the region kind; nothing is inferred here.
 * skeleton-readback.ts reads this markup back into the tree. */
export function StatementSkeleton(props: StatementSkeletonProps) {
  return skeletonFrames({ ...props, colorOf: useIdentityColor() });
}

/** The frames themselves, free of hooks so that a test can press their rows. */
export function skeletonFrames({ root, document, visibleNodes, activeRegionId, activeNodeId, selectedObjectId, onNodeSelect, colorOf }: StatementSkeletonProps & { colorOf: (id: string | undefined) => string }) {
  const component = componentMode(document);
  const name = component ? 'Expression and context' : 'Whole statement';
  const row = (region: ReadingRegion, content: ReactNode, nodeId = region.id, current = region.id === activeRegionId) => <button type="button" className={`sk-row${current ? ' sk-selected' : ''}`}
    aria-current={current ? 'true' : undefined} title={nodeId === region.id && region.kind !== 'clause' ? region.node.lean : undefined} onClick={() => onNodeSelect?.(nodeId)}>{content}</button>;
  const within = (part: Part) => <div key={part.region.id} className="sk-children" data-skeleton-edge={part.edge}>{draw(part.region)}</div>;
  function draw(region: ReadingRegion): ReactNode {
    const identity = { 'data-skeleton-row': region.id, 'data-skeleton-kind': region.kind, 'data-skeleton-nodes': region.sourceNodeIds.join(' ') };
    if (!region.sourceNodeIds.some(id => visibleNodes.has(id))) {
      const title = region.kind === 'binders' ? `${roleSymbol[region.node.binder!.role]} ${region.binders.map(node => node.binder!.name).join(', ')}`
        : region.kind === 'implication' ? 'Given' : region.kind === 'clause' || region.kind === 'structure' ? ownText(region) : `${connectiveWords[region.kind].symbol} ${connectiveWords[region.kind].title}`;
      return <button type="button" className="sk-stub" {...identity} data-skeleton-folded={rowCount(region)} title={region.node.lean} onClick={() => onNodeSelect?.(region.id)}>{compactLabel(title, 70)} · {counted(rowCount(region), 'folded row')}</button>;
    }
    if (region.kind === 'binders') {
      const role = region.node.binder!.role;
      const quantifier = role === 'universal' || role === 'existential';
      return <div className={`sk-region sk-binders sk-${role}`} {...identity} data-skeleton-binder={region.node.kind}>
        {row(region, <><span className="sk-mark" data-skeleton-mark="">{roleSymbol[role]}</span>{(component || !quantifier) && <span className="sk-words">{binderGroupTitle(region.binders, document)}</span>}
          {region.binders.map(node => {
            const binder = node.binder!;
            return <span className="sk-binder" key={node.id}><span className={`sk-name${binder.objectId && binder.objectId === selectedObjectId ? ' sk-object-selected' : ''}`} data-skeleton-name="" data-reading-object={binder.objectId}
              style={{ '--object-color': colorOf(binder.objectId) } as CSSProperties}>{role === 'auxiliary' ? contextEntryTitle(binder) : binder.name}</span><span className="sk-type">: {binder.type}{binder.definition && ` := ${formatExpression(binder.definition.value)}`}</span></span>;
          })}</>)}
        {parts(region).map(within)}
      </div>;
    }
    if (region.kind === 'implication') {
      // One Given mark carries the current step: the one whose own node is selected, otherwise the first.
      const marked = activeNodeId ? Math.max(0, region.sourceNodeIds.indexOf(activeNodeId)) : 0;
      return <div className="sk-region sk-implication" {...identity}>
        {region.assumptions.map((assumption, index) => <div className="sk-given" data-skeleton-edge="assumption" key={assumption.id}>{row(region, 'Given', region.sourceNodeIds[index], region.id === activeRegionId && index === marked)}{draw(assumption)}</div>)}
        {within({ edge: 'conclusion', region: region.conclusion })}
      </div>;
    }
    if (region.kind === 'clause') return <div className="sk-region sk-clause" {...identity}>{row(region, ownText(region))}</div>;
    return <div className={`sk-region sk-${region.kind}`} {...identity}>
      {row(region, region.kind === 'structure' ? ownText(region) : <><span className="sk-mark" data-skeleton-mark="">{connectiveWords[region.kind].symbol}</span><span className="sk-words">{connectiveWords[region.kind].title}</span></>)}
      {parts(region).map(within)}
    </div>;
  }
  return <section className="statement-skeleton" aria-label={name}><FigureScroll label={`${name}; scroll to see all of it`}>{draw(root)}</FigureScroll></section>;
}
