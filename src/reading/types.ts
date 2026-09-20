import type { Binder, StatementNode } from '../core/types';
import type { FragmentCoverage } from '../semantic/types';

export const READING_DOCUMENT_VERSION = '1.0.0' as const;
export type ReadingEdgeRole = 'body' | 'assumption' | 'conclusion' | 'conjunct' | 'alternative' | 'equivalence-left' | 'equivalence-right' | 'negated' | 'result';
export interface ReadingEdge {
  readonly role: ReadingEdgeRole;
  readonly label: string;
  readonly index: number;
}
export interface ReadingBinder {
  readonly binderId: string;
  readonly objectId?: string;
  readonly choiceId?: string;
  readonly name: string;
  readonly type: string;
  readonly role: Binder['role'];
  readonly dependsOn: readonly string[];
  readonly scopeId: string;
}
export interface ReadingDirection {
  readonly id: string;
  readonly label: string;
  readonly assumptionNodeId: string;
  readonly conclusionNodeId: string;
}
export interface ReadingNode {
  /** Identical to the source StatementNode.id; no guessed source correspondence. */
  readonly id: string;
  readonly kind: StatementNode['kind'];
  readonly phrase: string;
  readonly lean: string;
  readonly children: readonly ReadingNode[];
  readonly parentId?: string;
  readonly edgeFromParent?: ReadingEdge;
  readonly binder?: ReadingBinder;
  readonly scopeId: string;
  readonly context: readonly string[];
  readonly assumptionNodeIds: readonly string[];
  readonly relationIds: readonly string[];
  readonly objectIds: readonly string[];
  readonly coverage?: FragmentCoverage['status'];
  readonly panelId?: string;
  /** Explicitly directional: an equivalence is two implications, never an equality. */
  readonly directions?: readonly ReadingDirection[];
}
export interface ReadingConnection {
  readonly objectId: string;
  readonly fromRelationId: string;
  readonly toRelationId: string;
  readonly kind: 'feeds' | 'shared';
}
export interface ReadingRelationGroup {
  readonly id: string;
  readonly scopeId: string;
  readonly role: 'clause' | 'local-expression';
  readonly relationIds: readonly string[];
  readonly rootRelationIds: readonly string[];
  readonly objectIds: readonly string[];
  readonly connections: readonly ReadingConnection[];
  readonly context: readonly string[];
}
export interface ReadingPanel {
  readonly id: string;
  readonly nodeId: string;
  readonly phrase: string;
  readonly relationIds: readonly string[];
  readonly rootRelationIds: readonly string[];
  readonly objectIds: readonly string[];
  readonly sceneIds: readonly string[];
  readonly opaqueRegionIds: readonly string[];
  readonly coverage: FragmentCoverage['status'];
  /** Composition stays within one atomic clause and one expression scope. */
  readonly groups: readonly ReadingRelationGroup[];
}
export interface ReadingQuantifierGroup {
  readonly id: string;
  readonly kind: 'forall' | 'exists' | 'parameter';
  readonly nodeIds: readonly string[];
  readonly binders: readonly ReadingBinder[];
  readonly bodyNodeId?: string;
  /** Every containing logical position, so groups never migrate between branches. */
  readonly branchPath: readonly { readonly nodeId: string; readonly edge: ReadingEdge }[];
}
export interface ReadingSelection {
  readonly nodeId: string;
  readonly descendantNodeIds: readonly string[];
  readonly ancestorNodeIds: readonly string[];
  readonly assumptionNodeIds: readonly string[];
  readonly scopeObjectIds: readonly string[];
  readonly panelIds: readonly string[];
}
export interface ReadingStep {
  readonly id: string;
  readonly nodeId: string;
  readonly kind: 'binder' | 'connective' | 'clause';
  /** Reading order, not a claim that logical alternatives occur in temporal sequence. */
  readonly ordinal: number;
  readonly ancestorNodeIds: readonly string[];
  readonly branchPath: ReadingQuantifierGroup['branchPath'];
  readonly panelId?: string;
}
export interface ReadingDocument {
  readonly schemaVersion: typeof READING_DOCUMENT_VERSION;
  readonly root: ReadingNode;
  /** All source nodes, once each, in source preorder; selecting never removes context. */
  readonly nodes: readonly ReadingNode[];
  readonly panels: readonly ReadingPanel[];
  readonly quantifierGroups: readonly ReadingQuantifierGroup[];
  /** Each step retains its enclosing logic; consumers must not treat alternatives as conjuncts. */
  readonly sequence: readonly ReadingStep[];
  readonly selection: ReadingSelection;
  readonly diagnostics: readonly string[];
}
export interface ReadingOptions { readonly selectedNodeId?: string }
