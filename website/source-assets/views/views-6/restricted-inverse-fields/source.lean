∀ (A B : Type) (e : PartialEquiv A B) (x : A),
  x ∈ e.source → e.symm (e x) = x
