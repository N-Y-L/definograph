∀ (α β : Type) (f : α → β),
  Function.Injective f →
  ∀ x y : α, f x = f y → x = y
