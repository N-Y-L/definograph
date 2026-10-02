∀ (V C : Type) (G : SimpleGraph V)
  (c : G.Coloring C) (u v : V),
  G.Adj u v → c u ≠ c v
