structure Rotor where
  Carrier : Type
  turn : Carrier → Carrier
  fixed : ∀ x, turn x = x
example (owner : Rotor) (unused : Nat) : Rotor := owner
