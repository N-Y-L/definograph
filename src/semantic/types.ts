import type { Analysis, Binder, Expr, Scene, StatementNode } from '../core/types';

/** The document format is independent of a renderer and of prover transport. */
export const SEMANTIC_DOCUMENT_VERSION = '1.0.0' as const;
export type SemanticObjectKind = 'variable' | 'scalar' | 'point' | 'set' | 'function' | 'type' | 'literal' | 'expression' | 'symbol';
export type SemanticFidelity = 'structural' | 'symbolic' | 'numerical';
export interface Provenance {
  readonly nodeId: string;
  readonly expressionPath: string;
  readonly origin: 'elaborated-expression';
}
export interface SemanticObject {
  readonly id: string;
  readonly kind: SemanticObjectKind;
  readonly label: string;
  readonly type: string;
  readonly expression: Expr;
  readonly binder?: Binder;
  readonly scopeId: string;
  readonly provenance: readonly Provenance[];
}
export type RelationKind = 'membership' | 'subset' | 'equality' | 'inequality' | 'application' | 'image' | 'preimage' | 'function-property' | 'metric-region' | 'distance' | 'predicate';
export interface RelationPort {
  readonly role: string;
  readonly objectId: string;
}
export interface SemanticRelation {
  readonly id: string;
  readonly kind: RelationKind;
  readonly label: string;
  readonly ports: readonly RelationPort[];
  readonly expression: Expr;
  readonly scopeId: string;
  readonly nodeId: string;
  readonly pluginId: string;
  readonly fidelity: SemanticFidelity;
  readonly provenance: Provenance;
  readonly conditions: readonly string[];
}
export interface SemanticScope {
  readonly id: string;
  readonly parentId?: string;
  readonly nodeId: string;
  readonly kind: StatementNode['kind'];
  readonly label: string;
  readonly objectIds: readonly string[];
  /** These predicates are local assumptions, never global assertions. */
  readonly assumptionNodeIds: readonly string[];
  readonly context: readonly string[];
}
export interface QuantifierChoice {
  readonly id: string;
  readonly objectId: string;
  readonly binderId: string;
  readonly nodeId: string;
  readonly role: Binder['role'];
  readonly dependsOn: readonly string[];
  readonly availableObjectIds: readonly string[];
  readonly scopeId: string;
  readonly explanation: string;
}
export interface OpaqueRegion {
  readonly id: string;
  readonly nodeId: string;
  readonly scopeId: string;
  readonly expression: Expr;
  readonly label: string;
  readonly reason: string;
  readonly supportedRelationIds: readonly string[];
  readonly provenance: Provenance;
}
export interface FragmentCoverage {
  readonly nodeId: string;
  readonly status: 'structural' | 'partial' | 'interpreted';
  readonly relationIds: readonly string[];
  readonly sceneIds: readonly string[];
  readonly opaqueRegionIds: readonly string[];
  readonly objectIds: readonly string[];
}
export interface SemanticDocument {
  readonly schemaVersion: typeof SEMANTIC_DOCUMENT_VERSION;
  readonly prover: 'lean' | 'rocq';
  readonly source: string;
  readonly tree: StatementNode;
  readonly objects: readonly SemanticObject[];
  readonly relations: readonly SemanticRelation[];
  readonly scopes: readonly SemanticScope[];
  readonly choices: readonly QuantifierChoice[];
  readonly opaqueRegions: readonly OpaqueRegion[];
  readonly coverage: readonly FragmentCoverage[];
  readonly scenes: readonly Scene[];
  readonly diagnostics: readonly string[];
}
export interface SemanticRuleMatch {
  readonly kind: RelationKind;
  readonly label: string;
  readonly arguments: readonly { readonly role: string; readonly expression: Expr }[];
  readonly fidelity: SemanticFidelity;
  readonly conditions?: readonly string[];
}
/** Plugins recognize elaborated constructors, never theorem titles or source spelling. */
export interface SemanticPlugin {
  readonly id: string;
  readonly version: string;
  readonly title: string;
  readonly capabilities: readonly RelationKind[];
  readonly limitations: readonly string[];
  match(expression: Expr): SemanticRuleMatch | undefined;
}
export type PlannedViewKind = 'semantic-map' | 'relation-map' | 'quantifier-flow' | Scene['kind'];
export interface RepresentationCapability {
  readonly kind: PlannedViewKind;
  readonly fidelity: SemanticFidelity;
  readonly baseScore: number;
  readonly requires: readonly string[];
  readonly preserves: readonly string[];
  readonly doesNotEncode: readonly string[];
}
export interface PlannedView {
  readonly id: string;
  readonly kind: PlannedViewKind;
  readonly title: string;
  readonly score: number;
  readonly reason: string;
  readonly fidelity: SemanticFidelity;
  readonly nodeIds: readonly string[];
  readonly objectIds: readonly string[];
  readonly relationIds: readonly string[];
  readonly sceneIds: readonly string[];
  readonly conditions: readonly string[];
}
export interface ViewPlan {
  readonly selectedNodeId: string;
  /** A ranked composition: the first view is primary, all retained views contribute. */
  readonly views: readonly PlannedView[];
  readonly primaryViewId: string;
  readonly sharedObjectIds: readonly string[];
  readonly coverage: {
    readonly fragments: number;
    readonly interpreted: number;
    readonly partial: number;
    readonly structural: number;
  };
  readonly explanation: string;
}
export interface PlannerOptions {
  readonly selectedNodeId?: string;
  readonly maxDetailedViews?: number;
}
export type AnalysisInput = Pick<Analysis, 'source' | 'tree' | 'expression'>;
