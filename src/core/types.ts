/** Portable output of the Lean expression exporter. Display names are never identities. */
export type Domain = 'real' | 'sup2' | 'euclidean2' | 'supN' | 'euclideanN' | 'realFunction' | 'unknown';
export type Metric = 'real' | 'sup2' | 'euclidean2' | 'supN' | 'euclideanN' | 'unknown';
export type NumericOperator = 'add' | 'sub' | 'mul' | 'div' | 'neg' | 'pow' | 'abs' | 'min' | 'max' | 'lt' | 'le' | 'eq' | 'ne' | 'pair' | 'proj1' | 'proj2' | 'ofNat';

/** Structural type information supplied by the prover; never inferred from variable names. */
export interface TypeDescriptor {
  kind: 'real' | 'natural' | 'integer' | 'rational' | 'finite' | 'type' | 'set' | 'map' | 'relation' | 'proposition' | 'structure' | 'unknown';
  lean: string;
  head?: string;
  dimension?: number;
  cardinality?: number;
  element?: TypeDescriptor;
  domain?: TypeDescriptor;
  codomain?: TypeDescriptor;
  dependent?: boolean;
}

export interface Binder {
  id: string;
  name: string;
  type: string;
  role: 'universal' | 'existential' | 'assumption' | 'lambda' | 'parameter';
  dependsOn: string[];
  domain?: Domain;
  dimension?: number;
  typeExpression?: Expr;
  typeDescriptor?: TypeDescriptor;
}

export type Expr =
  | { kind: 'const'; name: string; levels?: string[]; canonical?: boolean; type?: string; typeDescriptor?: TypeDescriptor }
  | { kind: 'var'; id: string; name: string; type: string; typeDescriptor?: TypeDescriptor }
  | { kind: 'literal'; value: number | string }
  | { kind: 'app'; fn: Expr; args: Expr[]; metric?: Metric; metricInstance?: string; dimension?: number; domain?: Domain; standard?: boolean; type?: string; operator?: NumericOperator; typeDescriptor?: TypeDescriptor; argumentKinds?: ('instance' | 'proof' | 'type' | 'value')[] }
  | { kind: 'forall' | 'lambda'; binder: Binder; body: Expr; binderType?: Expr }
  | { kind: 'sort'; name: string }
  | { kind: 'opaque'; text: string };

export type NodeKind = 'forall' | 'exists' | 'implies' | 'and' | 'or' | 'iff' | 'not' | 'predicate' | 'parameter';
export interface StatementNode {
  id: string;
  kind: NodeKind;
  label: string;
  lean: string;
  children: StatementNode[];
  binder?: Binder;
  expression: Expr;
  scope?: string[];
  expansion?: { constant: string; before: string; after: string; originalExpression?: Expr; definitionalEquality: true; depth?: number };
}

export interface Analysis {
  ok: true;
  source: string;
  pretty: string;
  type: string;
  tree: StatementNode;
  expression: Expr;
  originalExpression?: Expr;
  metrics: unknown[];
  diagnostics: unknown[];
  schemaVersion?: number;
  validation?: 'kernel-type-checked-statement' | 'kernel-type-checked-declaration-type' | 'kernel-type-checked-context-fragment';
  provenance?: { assistant: string; inputMode: 'term' | 'declaration' | 'editor'; declaration?: { name: string; kind: string; module?: string; type: string }; [key: string]: unknown };
  definitions?: { name: string; kind: string; type: string; module?: string; canExpand: boolean }[];
  sourceTerms?: { startByte: number; endByte: number; lean: string; type: string; isBinder: boolean; origin: 'lean-infotree' }[];
  readableMath?: {provider:'leantex';status:'rendered'|'unavailable';latex?:string;reason?:string};
  definitionReadableMath?: {provider:'leantex';status:'rendered'|'unavailable';latex?:string;reason?:string};
  definitionExpression?: Expr | null;
  definitionTree?: StatementNode | null;
  definitionBodyStatus?: 'available' | 'export-size-limit' | 'not-a-definition';
  expansionPolicy?: unknown;
}

export type Point2 = [number, number];
export type ScenarioValue = number | number[];
export type Scenario = Record<string, ScenarioValue>;
export type NumericResult =
  | { status: 'value'; value: ScenarioValue; approximate: true }
  | { status: 'unknown'; reason: string };
export type PredicateResult =
  | { status: 'true' | 'false'; approximate: true; explanation: string }
  | { status: 'unknown'; reason: string };

export interface SceneBase {
  id: string;
  nodeId: string;
  title: string;
  expression: Expr;
  /** Binders lexically in scope, in introduction order. */
  scope: Binder[];
  /** Active implication antecedents; these are assumptions, not proved facts. */
  guards: Expr[];
  /** Negation / implication-antecedent / disjunction context must remain visible. */
  context: string[];
}

export interface BallScene extends SceneBase {
  kind: 'ball';
  metric: Exclude<Metric, 'unknown'>;
  dimension: number;
  metricInstance?: string;
  center: Expr;
  radius: Expr;
  boundary: 'open' | 'closed' | 'sphere';
  point?: Expr;
}

export interface IntervalScene extends SceneBase {
  kind: 'interval';
  variable: Binder;
  relation: 'lt' | 'le' | 'eq' | 'ne';
  left: Expr;
  right: Expr;
}

export interface GraphScene extends SceneBase {
  kind: 'graph';
  input: Binder;
  body: Expr;
  fn: Expr;
}

export interface MappingScene extends SceneBase {
  kind: 'mapping';
  fn: Expr;
  input?: Expr;
  property?: 'injective' | 'surjective' | 'bijective';
}

export type Scene = BallScene | IntervalScene | GraphScene | MappingScene;

export interface SamplePoint {
  x: number;
  y: number | null;
}

/** Numeric geometry is only an illustration of the recognized mathematical object. */
export type BallGeometry =
  | { status: 'unknown'; reason: string }
  | { status: 'geometry'; metric: Exclude<Metric, 'unknown'>; dimension: number; center: ScenarioValue; radius: number; empty: boolean; singleton: boolean; boundary: BallScene['boundary']; point?: ScenarioValue; membership?: PredicateResult };

export interface SliceView {
  /** Two distinct coordinate indices. Real one-dimensional spaces are handled by ballGeometry. */
  axes?: [number, number];
  /** Ambient coordinates fixed off the two displayed axes; omitted coordinates default to zero. */
  fixed?: number[];
}

export type SliceGeometry =
  | { status: 'unknown'; reason: string }
  | { status: 'geometry'; metric: Exclude<Metric, 'unknown'>; center: Point2; radius: number; empty: boolean; singleton: boolean; boundary: BallScene['boundary']; ambientDimension: number; intrinsicDimension: number; axes: [number, number]; fixed: number[]; isSlice: boolean; point?: Point2; pointInSlice?: boolean; membership?: PredicateResult; note: string };
