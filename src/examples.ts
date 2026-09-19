export interface Example { id: string; title: string; description: string; source: string }
export const examples: Example[] = [
  { id: 'epsilon', title: 'A point in an ε-ball', description: 'An arbitrary point under a geometric assumption.', source: '∀ (c : EuclideanSpace ℝ (Fin 2)) (ε : ℝ),\n  0 < ε → ∀ P : EuclideanSpace ℝ (Fin 2),\n  P ∈ Metric.ball c ε → dist P c < ε' },
  { id: 'sets', title: 'Sets, membership, and inclusion', description: 'Shared objects connect conditions across the statement.', source: '∀ (A B : Set ℝ) (x : ℝ),\n  A ⊆ B → x ∈ A → x ∈ B' },
  { id: 'maps', title: 'Functions between arbitrary types', description: 'Explore symbolic structure without choosing numerical coordinates.', source: '∀ (α β : Type) (f : α → β),\n  Function.Injective f →\n  ∀ x y : α, f x = f y → x = y' },
  { id: 'relations', title: 'A relation and its arguments', description: 'An abstract predicate retains its typed objects and application structure.', source: '∀ (α : Type) (R : α → α → Prop),\n  (∀ x : α, R x x) →\n  ∀ x : α, ∃ y : α, R x y' },
  { id: 'product', title: 'The same notation, a different metric', description: 'The standard product metric makes a square ball.', source: '∀ (c P : ℝ × ℝ) (ε : ℝ),\n  P ∈ Metric.ball c ε → dist P c < ε' },
  { id: 'sphere', title: 'A 3-sphere in four dimensions', description: 'Inspect a coordinate slice of a sphere in ℝ⁴.', source: '∀ P : EuclideanSpace ℝ (Fin 4),\n  P ∈ Metric.sphere 0 2' },
  { id: 'six', title: 'A ball in six dimensions', description: 'Move the omitted coordinates and see the slice change.', source: '∀ (P : EuclideanSpace ℝ (Fin 6)) (ε : ℝ),\n  P ∈ Metric.closedBall 0 ε' },
  { id: 'interval', title: 'An interval on the real line', description: 'Open and closed endpoints carry mathematical meaning.', source: '∀ (x c ε : ℝ),\n  x ∈ Metric.ball c ε ↔ |x - c| < ε' },
  { id: 'depends', title: 'For every x, some y', description: 'The witness may depend on the earlier choice.', source: '∀ x : ℝ, ∃ y : ℝ, x < y' },
  { id: 'fixed', title: 'Some y, for every x', description: 'The witness is fixed before x is chosen.', source: '∃ y : ℝ, ∀ x : ℝ, x < y' },
  { id: 'continuity', title: 'Read ε–δ continuity in pieces', description: 'Separate choices, assumptions, and a nonlinear condition.', source: '∀ ε : ℝ, 0 < ε →\n  ∃ δ : ℝ, 0 < δ ∧\n  ∀ x : ℝ, |x| < δ → |x * x| < ε' },
  { id: 'function', title: 'A function and its inputs', description: 'An explicit real function can be sampled and graphed.', source: 'Function.Injective (fun x : ℝ => 2 * x + 1)' },
  { id: 'partial', title: 'Geometry inside a larger statement', description: 'Keep a recognized fragment even when the rest has no plot.', source: '∀ (P : ℝ × ℝ) (ε : ℝ),\n  P ∈ Metric.ball 0 ε → Nat.Prime 17' },
];
