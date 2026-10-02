structure ReturnMap where
  Source : Type
  Target : Type
  send : Source → Target
  back : Target → Source
  returns : ∀ x, back (send x) = x

example (system : ReturnMap) (unused : Nat) :
    ∀ x : system.Source, system.back (system.send x) = x :=
  system.returns

def unitToBool : ReturnMap where
  Source := Unit
  Target := Bool
  send := fun _ => false
  back := fun _ => ()
  returns := by
    intro x
    cases x
    rfl

example : unitToBool.back (unitToBool.send ()) = () := rfl

theorem reverse_trip_fails :
    unitToBool.send (unitToBool.back true) ≠ true := by
  change false ≠ true
  decide

theorem send_injective (system : ReturnMap) :
    ∀ a b : system.Source, system.send a = system.send b → a = b := by
  intro a b same
  calc
    a = system.back (system.send a) := (system.returns a).symm
    _ = system.back (system.send b) := congrArg system.back same
    _ = b := system.returns b

#print axioms unitToBool
#print axioms reverse_trip_fails
#print axioms send_injective
