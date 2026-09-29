#check ∀ x : Nat, ∃ y : Nat, y = x
#check ∃ y : Nat, ∀ x : Nat, y = x
#check ∀ input : Nat, ∃ output : Nat, output = input
#check ∀ x : Nat, ∃ y : Nat, y = 0

example : Prop := ∀ x : Nat, ∃ y : Nat, y = x
example : Prop := ∃ y : Nat, ∀ x : Nat, y = x
