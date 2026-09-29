import CoreExprBridge
import UniqueOutputMatcher
import FVarCoreBridge

/- Actual-expression coverage and composition consequences for the scoped
   derived-view syntax. No rendering, typing or native-substitution claim. -/
namespace FoundationIntegration
open DerivedViewSyntax CoreExprBridge

-- Reuse the matcher's ordinary-signature inclusion; no second embedding.
def embed (t : Core n) : View n := coreToView t

theorem expand_embed (t : Core n) : expand (embed t) = t :=
  expand_coreToView t

def decodeView (t : View n) : Lean.Expr := decode (expand t)

def encodeView (e : Lean.Expr) (n : Nat) : Option (View n) :=
  (reifyNormalized e n).map embed

theorem encodeView_readback (e : Lean.Expr) (n : Nat) (t : View n)
    (h : encodeView e n = some t) :
    decodeView t = ExprReferenceGraph.eraseMetadata e := by
  unfold encodeView at h
  cases hr : reifyNormalized e n with
  | none => simp only [hr, Option.map_none] at h; cases h
  | some c =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst t
      unfold decodeView
      rw [expand_embed]
      exact normalized_readback e n c hr

theorem admitted_view_coverage (e : Lean.Expr) (n : Nat)
    (h : Admitted (ExprReferenceGraph.eraseMetadata e) n) :
    ∃ t : View n, encodeView e n = some t ∧
      decodeView t = ExprReferenceGraph.eraseMetadata e := by
  obtain ⟨c, hc⟩ := (normalized_admission e n).mp h
  have he : encodeView e n = some (embed c) := by
    simp only [encodeView, hc, Option.map_some]
  exact ⟨embed c, he, encodeView_readback e n (embed c) he⟩

theorem decoded_plug (consumer : View (n+1)) (producer : View r)
    (actuals : Fin r → View n) :
    decodeView (plug consumer producer actuals) =
      decode (corePlug (expand consumer) (expand producer)
        (fun i => expand (actuals i))) := by
  unfold decodeView
  rw [expand_plug]

-- Matching strict actual expressions is separate from explicitly removing metadata.
def matchExpr (u : ULevel) (e : Lean.Expr) (n : Nat) : Option (UniqueMatch n) := do
  let c ← reify e n
  matchUnique u c

theorem matchExpr_readback (e : Lean.Expr) (n : Nat) (u : ULevel)
    (result : UniqueMatch n) (h : matchExpr u e n = some result) :
    decodeView result.fold = e := by
  cases hc : reify e n with
  | none => simp [matchExpr, hc] at h
  | some c =>
      have hm : matchUnique u c = some result := by simpa [matchExpr, hc] using h
      unfold decodeView
      rw [matchUnique_expanded_sound c u result hm]
      exact (reify_readback e n c hc).2

theorem matchExpr_complete (result : UniqueMatch n) :
    matchExpr result.attrs.u (decode result.rebuild) n = some result := by
  simp [matchExpr, reify_decode, matchUnique_complete]

def matchNormalizedExpr (u : ULevel) (e : Lean.Expr) (n : Nat) : Option (UniqueMatch n) :=
  matchExpr u (ExprReferenceGraph.eraseMetadata e) n

theorem matchNormalizedExpr_readback (e : Lean.Expr) (n : Nat) (u : ULevel)
    (result : UniqueMatch n) (h : matchNormalizedExpr u e n = some result) :
    decodeView result.fold = ExprReferenceGraph.eraseMetadata e :=
  matchExpr_readback _ n u result h

theorem matchExpr_withoutUniqueness (result : UniqueMatch n) (u : ULevel) :
    matchExpr u (decode result.withoutUniqueness) n = none := by
  simp [matchExpr, reify_decode, matchUnique_withoutUniqueness]

namespace Registered

def decodeView (registry : List Lean.FVarId) (d : Nat)
    (t : View (registry.length+d)) : Lean.Expr :=
  FVarCoreBridge.decode registry d (expand t)

def encodeView (registry : List Lean.FVarId) (e : Lean.Expr) (d : Nat) :
    Option (View (registry.length+d)) :=
  (FVarCoreBridge.reifyNormalized registry e d).map embed

theorem encodeView_readback (registry : List Lean.FVarId) (e : Lean.Expr) (d : Nat)
    (t : View (registry.length+d)) (h : encodeView registry e d = some t) :
    decodeView registry d t = ExprReferenceGraph.eraseMetadata e := by
  unfold encodeView at h
  cases hr : FVarCoreBridge.reifyNormalized registry e d with
  | none => simp only [hr, Option.map_none] at h; cases h
  | some c =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst t
      unfold decodeView
      rw [expand_embed]
      exact FVarCoreBridge.normalized_readback registry e d c hr

theorem admitted_view_coverage (registry : List Lean.FVarId) (e : Lean.Expr) (d : Nat)
    (h : FVarCoreBridge.Admitted registry (ExprReferenceGraph.eraseMetadata e) d) :
    ∃ t : View (registry.length+d), encodeView registry e d = some t ∧
      decodeView registry d t = ExprReferenceGraph.eraseMetadata e := by
  obtain ⟨c, hc⟩ := (FVarCoreBridge.normalized_admission registry e d).mp h
  have he : encodeView registry e d = some (embed c) := by
    simp only [encodeView, hc, Option.map_some]
  exact ⟨embed c, he, encodeView_readback registry e d (embed c) he⟩

def matchExpr (registry : List Lean.FVarId) (u : ULevel) (e : Lean.Expr) (d : Nat) :
    Option (UniqueMatch (registry.length+d)) := do
  let c ← FVarCoreBridge.reify registry e d
  matchUnique u c

theorem matchExpr_readback (registry : List Lean.FVarId) (e : Lean.Expr) (d : Nat)
    (u : ULevel) (result : UniqueMatch (registry.length+d))
    (h : matchExpr registry u e d = some result) :
    decodeView registry d result.fold = e := by
  cases hc : FVarCoreBridge.reify registry e d with
  | none => simp [matchExpr, hc] at h
  | some c =>
      have hm : matchUnique u c = some result := by simpa [matchExpr, hc] using h
      unfold decodeView
      rw [matchUnique_expanded_sound c u result hm]
      exact (FVarCoreBridge.reify_readback registry e d c hc).2

theorem matchExpr_complete (registry : List Lean.FVarId) (hd : registry.Nodup) (d : Nat)
    (result : UniqueMatch (registry.length+d)) :
    matchExpr registry result.attrs.u (FVarCoreBridge.decode registry d result.rebuild) d =
      some result := by
  simp [matchExpr, FVarCoreBridge.reify_decode registry hd, matchUnique_complete]

def matchNormalizedExpr (registry : List Lean.FVarId) (u : ULevel) (e : Lean.Expr) (d : Nat) :
    Option (UniqueMatch (registry.length+d)) :=
  matchExpr registry u (ExprReferenceGraph.eraseMetadata e) d

theorem matchNormalizedExpr_readback (registry : List Lean.FVarId) (e : Lean.Expr)
    (d : Nat) (u : ULevel) (result : UniqueMatch (registry.length+d))
    (h : matchNormalizedExpr registry u e d = some result) :
    decodeView registry d result.fold = ExprReferenceGraph.eraseMetadata e :=
  matchExpr_readback registry _ d u result h

theorem matchExpr_withoutUniqueness (registry : List Lean.FVarId) (hd : registry.Nodup)
    (d : Nat) (result : UniqueMatch (registry.length+d)) (u : ULevel) :
    matchExpr registry u (FVarCoreBridge.decode registry d result.withoutUniqueness) d = none := by
  simp [matchExpr, FVarCoreBridge.reify_decode registry hd, matchUnique_withoutUniqueness]

end Registered

#print axioms expand_embed
#print axioms encodeView_readback
#print axioms admitted_view_coverage
#print axioms decoded_plug
#print axioms embed
#print axioms encodeView
#print axioms matchExpr_readback
#print axioms matchExpr_complete
#print axioms matchNormalizedExpr_readback
#print axioms matchExpr_withoutUniqueness

#print axioms Registered.encodeView_readback
#print axioms Registered.admitted_view_coverage
#print axioms Registered.matchExpr_readback
#print axioms Registered.matchExpr_complete
#print axioms Registered.matchNormalizedExpr_readback
#print axioms Registered.matchExpr_withoutUniqueness

end FoundationIntegration
