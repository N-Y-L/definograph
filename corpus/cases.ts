/** Small, hand-reviewed vocabulary probes. These are statements, not asserted theorems. */
export interface CorpusCase {
  id: string;
  title: string;
  category: 'supported' | 'partially-supported' | 'currently-unsupported';
  mode: 'standalone' | 'editor';
  source: string;
  /** Exact proposition selected from the editor buffer. */
  selection?: string;
  expected: {
    relationKinds?: string[];
    absentKinds?: string[];
    opaqueHeads?: string[];
    noOpaque?: boolean;
    noNumericalScenes?: boolean;
    rootOpaque?: boolean;
    binderRoles?: string[];
    witnessDependencyCount?: number;
    branchRoles?: string[];
    dependentSignature?: boolean;
    compareRenameWith?: string;
  };
  interpretation: string;
  missing: string[];
}

const editor = (imports: string[], term: string) => `${imports.map(name => `import ${name}`).join('\n')}\n#check ${term}\n`;
const setImage = '∀ (X Y : Type) (f : X → Y) (s : Set X) (t : Set Y) (x : X), x ∈ s → Set.image f s ⊆ t → f x ∈ t';
const renamedSetImage = '∀ (A B : Type) (h : A → B) (u : Set A) (v : Set B) (p : A), p ∈ u → Set.image h u ⊆ v → h p ∈ v';
const wrapped = '∀ x : ℝ, Corpus.Uncharted (x ∈ Metric.ball 0 1)';
const localMap = '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) (x : X), x ∈ e.source → e.symm (e x) = x';
const localRank = '∀ (D : ℝ → (ℝ →ₗ[ℝ] ℝ)) (U : Set ℝ) (r : ℕ), ∀ x ∈ U, Module.finrank ℝ (LinearMap.range (D x)) = r';
const topological = '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (s : Set X) (t : Set Y), Continuous f → s ⊆ Set.preimage f t';
const coloring = '∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (u v : V), G.Adj u v → c u ≠ c v';
const colorable = '∀ (V : Type) (G : SimpleGraph V), G.Colorable 4';
const graphBranches = '∀ (V : Type) (G : SimpleGraph V) (u v w : V), G.Adj u v → ¬(G.Adj v w ∨ G.Adj u w)';

export const corpusCases: readonly CorpusCase[] = [
  { id: 'sets-and-image', title: 'Image inclusion with shared objects', category: 'supported', mode: 'standalone', source: setImage,
    expected: { relationKinds: ['membership', 'image', 'subset', 'application'], noOpaque: true },
    interpretation: 'Set membership, image, inclusion, application, and conditional scopes.', missing: [] },
  { id: 'renamed-sets-and-image', title: 'Binder renaming preserves interpretation', category: 'supported', mode: 'standalone', source: renamedSetImage,
    expected: { relationKinds: ['membership', 'image', 'subset', 'application'], noOpaque: true, compareRenameWith: 'sets-and-image' },
    interpretation: 'The preceding construction with all user binder names changed.', missing: [] },
  { id: 'boolean-set-expression', title: 'Composed Boolean set operations', category: 'supported', mode: 'standalone', source: '∀ (X : Type) (A B C : Set X) (x : X), x ∈ (A ∪ B) \\ (C ∩ Aᶜ)',
    expected: { relationKinds: ['membership', 'set-construction'], noOpaque: true },
    interpretation: 'Ordered union, intersection, complement, and difference without nonemptiness assumptions.', missing: [] },
  { id: 'dependent-witness', title: 'Witness chosen after the center', category: 'supported', mode: 'standalone', source: '∀ c : ℝ, ∃ p : ℝ, p ∈ Metric.ball c 1',
    expected: { relationKinds: ['membership', 'metric-region'], noOpaque: true, binderRoles: ['universal', 'existential'], witnessDependencyCount: 1 },
    interpretation: 'A metric condition with the witness permitted to depend on the earlier center.', missing: [] },
  { id: 'fixed-witness', title: 'Witness fixed before the center', category: 'supported', mode: 'standalone', source: '∃ p : ℝ, ∀ c : ℝ, p ∈ Metric.ball c 1',
    expected: { relationKinds: ['membership', 'metric-region'], noOpaque: true, binderRoles: ['existential', 'universal'], witnessDependencyCount: 0 },
    interpretation: 'The same local relation with different quantifier order; no claim this proposition is true.', missing: [] },
  { id: 'conditional-alternatives', title: 'Negated alternatives retain their premise', category: 'supported', mode: 'standalone', source: '∀ (P : Prop) (x : ℝ), P → ¬(x ∈ Metric.ball 0 1 ∨ x ∈ Metric.ball 1 2)',
    expected: { relationKinds: ['membership', 'metric-region'], noOpaque: true, branchRoles: ['conclusion', 'negated', 'alternative'] },
    interpretation: 'Metric fragments stay within the implication, negation, and disjunction.', missing: [] },
  { id: 'custom-membership', title: 'Unaudited membership instance', category: 'currently-unsupported', mode: 'standalone', source: '∀ (X : Type) (m : Membership X (Set X)) (x : X) (s : Set X), @Membership.mem X (Set X) m s x',
    expected: { absentKinds: ['membership'], opaqueHeads: ['Membership.mem'], noNumericalScenes: true },
    interpretation: 'Typed arguments are retained; set membership is deliberately not inferred.', missing: ['Meaning of the supplied Membership instance.'] },
  { id: 'topological-continuity', title: 'Continuity on arbitrary spaces', category: 'currently-unsupported', mode: 'standalone', source: '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y), Continuous f',
    expected: { opaqueHeads: ['Continuous'], noNumericalScenes: true },
    interpretation: 'Typed domain and codomain can be shown; continuity itself has no interpreted visual grammar.', missing: ['Continuity and topological neighborhood structure.'] },
  { id: 'nonempty-ball', title: 'Supported region inside unsupported nonemptiness', category: 'partially-supported', mode: 'standalone', source: 'Set.Nonempty (Metric.ball (0 : ℝ) 1)',
    expected: { relationKinds: ['metric-region'], opaqueHeads: ['Set.Nonempty'], rootOpaque: true },
    interpretation: 'The ball is recognized inside a retained nonemptiness predicate.', missing: ['An explicit nonemptiness/witness representation.'] },
  { id: 'project-wrapper', title: 'Imported project wrapper retains a known child', category: 'partially-supported', mode: 'editor', source: editor(['ProjectDependency', 'Mathlib.Topology.MetricSpace.Basic'], wrapped), selection: wrapped,
    expected: { relationKinds: ['membership', 'metric-region'], opaqueHeads: ['Corpus.Uncharted'], rootOpaque: true, noNumericalScenes: true },
    interpretation: 'An actual compiled project definition stays primary while its metric child remains inspectable.', missing: ['The project definition has not been expanded or assigned semantics.'] },
  { id: 'dependent-section', title: 'A section as a dependent function in local context', category: 'supported', mode: 'editor', source: 'example (B : Type) (E : B → Type) (s : (x : B) → E x) (x : B) : s x = s x := rfl\n', selection: 's x = s x',
    expected: { relationKinds: ['application', 'equality'], noOpaque: true, dependentSignature: true, binderRoles: ['parameter', 'parameter', 'parameter', 'parameter'] },
    interpretation: 'The dependent signature and equality are represented. This does not introduce bundle, smoothness, or vector-space semantics.', missing: [] },
  { id: 'local-homeomorphism', title: 'Local inverse law with a source restriction', category: 'partially-supported', mode: 'editor', source: editor(['Mathlib.Topology.OpenPartialHomeomorph.Defs'], localMap), selection: localMap,
    expected: { relationKinds: ['membership', 'equality'], opaqueHeads: ['PartialEquiv.source'], noNumericalScenes: true },
    interpretation: 'The source membership and equality are understood, but local-map projections and inverse semantics remain opaque.', missing: ['Source/target-restricted maps, inverse laws, and continuity of a local homeomorphism.'] },
  { id: 'local-linear-rank', title: 'Constant rank of a family on a subset', category: 'partially-supported', mode: 'editor', source: editor(['Mathlib.Data.Real.Basic', 'Mathlib.LinearAlgebra.Dimension.Finrank'], localRank), selection: localRank,
    expected: { relationKinds: ['membership', 'equality'], opaqueHeads: ['Module.finrank'], noNumericalScenes: true },
    interpretation: 'The local quantification, set condition, and equality are retained. D is a supplied family of linear maps, not an inferred derivative.', missing: ['Linear-map range and dimension/rank; derivatives and chart normal forms are not supplied by this fixture.'] },
  { id: 'topological-preimage', title: 'A topological assumption around set geometry', category: 'partially-supported', mode: 'editor', source: editor(['Mathlib.Topology.ContinuousOn'], topological), selection: topological,
    expected: { relationKinds: ['subset', 'preimage'], opaqueHeads: ['Continuous'], noNumericalScenes: true },
    interpretation: 'Preimage and inclusion are interpreted while continuity stays an explicit uninterpreted assumption.', missing: ['Continuity semantics.'] },
  { id: 'graph-coloring', title: 'Adjacent vertices have distinct assigned colors', category: 'supported', mode: 'editor', source: editor(['Mathlib.Combinatorics.SimpleGraph.Coloring'], coloring), selection: coloring,
    expected: { relationKinds: ['graph-adjacency', 'graph-coloring', 'equality'], noOpaque: true, noNumericalScenes: true },
    interpretation: 'Symbolic adjacency and proper-color constraints on named vertices; no finite graph or planar embedding is invented.', missing: [] },
  { id: 'graph-colorability', title: 'Four-color existence as a constraint', category: 'supported', mode: 'editor', source: editor(['Mathlib.Combinatorics.SimpleGraph.Coloring'], colorable), selection: colorable,
    expected: { relationKinds: ['graph-colorable'], noOpaque: true, noNumericalScenes: true },
    interpretation: 'A colorability condition on an arbitrary graph; this is not the four-color theorem or a constructed coloring.', missing: [] },
  { id: 'graph-branches', title: 'Adjacency inside scoped negated alternatives', category: 'supported', mode: 'editor', source: editor(['Mathlib.Combinatorics.SimpleGraph.Coloring'], graphBranches), selection: graphBranches,
    expected: { relationKinds: ['graph-adjacency'], noOpaque: true, branchRoles: ['conclusion', 'negated', 'alternative'], noNumericalScenes: true },
    interpretation: 'Named edge constraints retain the exact surrounding logical scope.', missing: [] },
  { id: 'fake-graph-name', title: 'Project-local familiar graph spelling', category: 'currently-unsupported', mode: 'editor', source: 'namespace SimpleGraph\ndef Adj (x y : Nat) : Prop := x = y\nend SimpleGraph\n#check ∀ x y : Nat, SimpleGraph.Adj x y\n', selection: '∀ x y : Nat, SimpleGraph.Adj x y',
    expected: { absentKinds: ['graph-adjacency'], opaqueHeads: ['SimpleGraph.Adj'], noNumericalScenes: true },
    interpretation: 'A same-spelled project constant is not the canonical graph relation.', missing: ['The project-local definition has no assigned semantic contract.'] },
];
