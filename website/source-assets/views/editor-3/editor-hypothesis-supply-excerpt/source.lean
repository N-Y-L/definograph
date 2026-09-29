theorem from_hypothesis (P : Prop) (h : P) : P := h
#print axioms from_hypothesis

theorem claimed : 2 + 2 = 5 := sorry
example : 2 + 2 = 5 := claimed
#print axioms claimed
