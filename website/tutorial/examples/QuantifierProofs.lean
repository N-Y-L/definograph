theorem each_has_equal : ∀ x : Nat, ∃ y : Nat, y = x := by
  intro x
  exact ⟨x, rfl⟩

theorem no_one_equals_all : ¬ (∃ y : Nat, ∀ x : Nat, y = x) := by
  intro h
  obtain ⟨y, hy⟩ := h
  have impossible : (0 : Nat) = 1 := (hy 0).symm.trans (hy 1)
  exact Nat.noConfusion impossible

#print axioms each_has_equal
#print axioms no_one_equals_all
