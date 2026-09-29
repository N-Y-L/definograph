import SourceCapture

/- Run with the compiled SourceCapture import directory on LEAN_PATH. The JSON
   lines are external test inputs, not authenticated browser certificates. -/
namespace StructuralCaptureControls
open Lean Meta Definograph DefinographAdmission V6Compose

structure Pair where
  left : Nat
  right : Nat

def emit (label : String) (term : Expr) (universes : List Name := []) : MetaM Unit := do
  let type ← inferType term
  let .ok captured ← captureNamedSource "structural-controls" label {
      declarationPrefix := Name.str `StructuralCaptureControls.checked label
      universeParams := universes
      heartbeatFor := fun _ => 200000 * 1000
    } term type | throwError "source capture unsupported: {label}"
  let .ok result := captured.capture.value | throwError "source capture failed: {label}"
  unless allAccepted result.checks do throwError "source capture rejected: {label}"
  IO.println s!"STRUCTURAL_SOURCE={(Json.mkObj [
    ("label", toJson label), ("binding", captured.binding),
    ("checks", Json.arr captured.capture.checks)]).compress}"

def run : MetaM Unit := do
  withLocalDeclD `same (mkConst ``Nat) fun n =>
    withLetDecl `same (mkConst ``Nat) n fun seed =>
      withLocalDeclD `same (mkApp (mkConst ``Fin) seed) fun x =>
        emit "dependent external home" x
  withLetDecl `same (mkConst ``Nat) (mkConst ``True) (nondep := true) fun x =>
    emit "opaque stored metadata" x
  let nat := mkConst ``Nat
  let pair := mkApp2 (mkConst ``Pair.mk) (.bvar 0) (.bvar 1)
  let body := Expr.letE `same nat (.bvar 0) (.proj ``Pair 1 pair) false
  emit "nested definition and projection" (mkApp (.lam `same nat body .default) (.lit (.natVal 3)))
  let ownedHave := Expr.letE `same nat (.lit (.natVal 7)) (.bvar 0) true
  emit "owned have" (mkApp (.lam `unused nat ownedHave .default) (.lit (.natVal 1)))
  let u := Level.param `u
  emit "dependent function type" (.forallE `same (.sort u)
    (.forallE `same (.bvar 0) (.bvar 1) .strictImplicit) .implicit) [`u]
  emit "structured universes" (.const ``id [.imax (.max u .zero) (.succ (.param `v))]) [`u, `v]
  emit "string literal" (.lit (.strVal "line one\nλ and \"quotes\""))


  for (label, n) in [("natural zero", 0), ("natural one", 1),
      ("natural safe maximum", 9007199254740991), ("natural first unsafe", 9007199254740992),
      ("natural adjacent unsafe", 9007199254740993), ("natural two to sixty four", 18446744073709551616),
      ("natural long decimal", 10^127 + 7)] do
    emit label (.lit (.natVal n))
  let numbered := Name.num `same 9007199254740993
  emit "numeric binder names" (.lam numbered nat (.bvar 0) .default)
  withLocalDeclD numbered nat fun x => emit "numeric external user name" x
  let numberedUniverse := Name.num `u 9007199254740993
  emit "numeric universe name" (.sort (.param numberedUniverse)) [numberedUniverse]

end StructuralCaptureControls

#eval StructuralCaptureControls.run
