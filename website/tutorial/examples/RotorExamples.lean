structure Rotor where
  Carrier : Type
  turn : Carrier → Carrier
  fixed : ∀ x, turn x = x

def naturalRotor : Rotor where
  Carrier := Nat
  turn := fun x => x
  fixed := fun _ => rfl

def emptyRotor : Rotor where
  Carrier := Empty
  turn := fun x => x
  fixed := fun _ => rfl

theorem law_at_input (owner : Rotor) (x : owner.Carrier) :
    owner.turn x = x := owner.fixed x

#check naturalRotor.fixed (3 : Nat)
#check law_at_input
#print axioms naturalRotor
#print axioms emptyRotor
#print axioms law_at_input
