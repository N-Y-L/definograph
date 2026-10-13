import type { ReadingRegion } from '../reading/presentation';
import type { ReadingBinder, ReadingNode } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';

/** One mark and one wording per logical role, shared by the skeleton and the full reading. */
export const roleSymbol: Record<ReadingBinder['role'], string> = { universal: '∀', existential: '∃', parameter: '↦', lambda: '↦', assumption: '⇒', definition: ':=', auxiliary: '·' };
export const connectiveWords = {
  all: { symbol: '∧', title: 'Together' },
  alternatives: { symbol: '∨', title: 'At least one alternative' },
  equivalence: { symbol: '↔', title: 'Equivalent conditions' },
  negation: { symbol: '¬', title: 'Not' },
} as const satisfies Partial<Record<ReadingRegion['kind'], { symbol: string; title: string }>>;

export const componentMode = (document: SemanticDocument): boolean => document.presentation?.kind === 'component';
export const ambientNodes = (nodes: readonly ReadingNode[], document: SemanticDocument): boolean => nodes.every(node => document.presentation?.contextNodeIds?.includes(node.id));

function componentBinderTitle(nodes: readonly ReadingNode[], document: SemanticDocument): string {
  if (nodes.some(node => node.id === document.presentation?.logicalRootNodeId))
    return nodes[0]?.binder?.role === 'existential' ? 'Candidate within the existential statement' : 'For every';
  return nodes[0]?.binder?.role === 'definition' ? ambientNodes(nodes, document) ? 'Context definitions' : 'Local definitions'
    : ambientNodes(nodes, document) ? 'Names in scope' : 'Function inputs';
}

/** The words for a group of adjacent binders of one role. */
export function binderGroupTitle(nodes: readonly ReadingNode[], document: SemanticDocument): string {
  const role = nodes[0]?.binder?.role;
  if (role === 'auxiliary') return 'Recorded context entries';
  if (componentMode(document)) return componentBinderTitle(nodes, document);
  return role === 'universal' ? 'For every' : role === 'existential' ? 'A witness is required' : role === 'definition' ? 'Local definitions' : 'Parameters';
}
