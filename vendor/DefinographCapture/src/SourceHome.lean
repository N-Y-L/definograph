import OccurrenceDecomposition
import ComponentAdmission

/- Full actual homes for ordinary source occurrences. This module deliberately
   uses Core: a derived call body requires its own admitted template interface,
   which arity-only View does not store. No dependent typing theorem is assumed. -/
namespace OccurrenceDecomposition
open DerivedViewSyntax V6Structured V6Compose

def Frame.sourceHome : Frame false n m → CTel n → CTel m
  | .appFun _, C => C
  | .appArg _, C => C
  | .lamDomain _ _, C => C
  | .lamBody attrs D, C => .port C attrs D
  | .piDomain _ _, C => C
  | .piBody attrs D, C => .port C attrs D
  | .letType _ _ _ _, C => C
  | .letValue _ _ _ _, C => C
  | .letBody name nondep T value, C => .letE C name nondep T value
  | .projValue _ _, C => C
  | .uniqueArg impossible _ _ _, _ => nomatch impossible
  | .instBody impossible _, _ => nomatch impossible
  | .instActual impossible _ _ _, _ => nomatch impossible

def Context.sourceHome : Context false n m → CTel n → CTel m
  | .hole, C => C
  | .step outer frame, C => frame.sourceHome (outer.sourceHome C)

theorem Context.home_prepend (f : Frame false n k) (c : Context false k m)
    (C : CTel n) :
    (c.prepend f).sourceHome C = c.sourceHome (f.sourceHome C) := by
  induction c with
  | hole => rfl
  | step outer frame ih => simp only [Context.prepend, Context.sourceHome, ih]

structure SourceHome (C : CTel n) (t : Core n) where
  extraction : Extraction t
  telescope : CTel extraction.home
  exactHome : telescope = extraction.context.sourceHome C

def extractSource (C : CTel n) (t : Core n) (path : List Step) : Option (SourceHome C t) :=
  (extract t path).map (fun e => ⟨e, e.context.sourceHome C, rfl⟩)

theorem SourceHome.exact_rebuild (h : SourceHome C t) :
    h.extraction.context.fill h.extraction.component = t := h.extraction.recover

theorem SourceHome.exact_telescope (h : SourceHome C t) :
    h.telescope = h.extraction.context.sourceHome C := h.exactHome

theorem extractSource_complete (C : CTel n) (h : IsOccurrence false (n := n) t path m u) :
    ∃ out, extractSource C t path = some out ∧
      (⟨out.extraction.home, out.extraction.component⟩ : (k : Nat) × Core k) = ⟨m, u⟩ := by
  obtain ⟨e, hextract, heq⟩ := extract_complete h
  simpa [extractSource, hextract] using heq

namespace HomeControls
def attrs : BinderAttrs := ⟨`n, .default⟩
def nat {n : Nat} : Core n := .const ``Nat []
def fin {n : Nat} (x : Core n) : Core n := .app (.const ``Fin []) x

/- The inner genuine let repeats the original n label. Its dependent child
   can use the let equation n(inner) := n(outer) during conversion. -/
def dependentLet : Core 0 :=
  .lam attrs nat (.letE `n false nat (.var 0)
    (.lam ⟨`x, .default⟩ (fin (.var 0)) (.var 0)))

def parentHome : CTel 2 := .letE (.port .nil attrs nat) `n false nat (.var 0)
def childHome : CTel 3 := .port parentHome ⟨`x, .default⟩ (fin (.var 0))

def valueSelection : SourceHome .nil dependentLet :=
  (extractSource .nil dependentLet [.lamBody, .letValue]).get (by decide)

def domainSelection : SourceHome .nil dependentLet :=
  (extractSource .nil dependentLet [.lamBody, .letBody, .lamDomain]).get (by decide)

def bodySelection : SourceHome .nil dependentLet :=
  (extractSource .nil dependentLet [.lamBody, .letBody, .lamBody]).get (by decide)

theorem value_home_exact :
    (⟨valueSelection.extraction.home, valueSelection.telescope⟩ : (n : Nat) × CTel n) =
      ⟨1, .port .nil attrs nat⟩ := rfl

theorem domain_home_exact :
    (⟨domainSelection.extraction.home, domainSelection.telescope⟩ : (n : Nat) × CTel n) =
      ⟨2, parentHome⟩ := rfl

theorem body_home_exact :
    (⟨bodySelection.extraction.home, bodySelection.telescope⟩ : (n : Nat) × CTel n) =
      ⟨3, childHome⟩ := rfl

theorem body_component_exact :
    (⟨bodySelection.extraction.home, bodySelection.extraction.component⟩ : (n : Nat) × Core n) =
      ⟨3, .var 0⟩ := rfl

theorem dependent_body_position :
    IsOccurrence false dependentLet [.lamBody, .letBody, .lamBody] 3 (.var 0) :=
  .child .lamBody (.child .letBody (.child .lamBody .root))
end HomeControls

#print axioms Context.home_prepend
#print axioms SourceHome.exact_rebuild
#print axioms SourceHome.exact_telescope
#print axioms extractSource_complete
#print axioms HomeControls.value_home_exact
#print axioms HomeControls.domain_home_exact
#print axioms HomeControls.body_home_exact
#print axioms HomeControls.body_component_exact
#print axioms HomeControls.dependent_body_position
#print axioms Frame.sourceHome
#print axioms Context.sourceHome
#print axioms extractSource
end OccurrenceDecomposition
