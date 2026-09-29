import CoreExprBridge

/- Independent transparent actions on actual Lean Expr syntax.
   These are specified operations, not Lean's opaque native instantiate/lift APIs.
   The bridge is structural equality, not a dependent typing theorem. -/
namespace ExprSubstitutionSpec
open Lean DerivedViewSyntax

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

def rename (ρ : Nat → Nat) : Expr → Expr
  | .bvar i => .bvar (ρ i)
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app fn arg => .app (rename ρ fn) (rename ρ arg)
  | .lam name domain body info =>
    .lam name (rename ρ domain) (rename (liftRen ρ) body) info
  | .forallE name domain body info =>
    .forallE name (rename ρ domain) (rename (liftRen ρ) body) info
  | .letE name type value body nondep =>
    .letE name (rename ρ type) (rename ρ value) (rename (liftRen ρ) body) nondep
  | .proj name index value => .proj name index (rename ρ value)
  | .mdata data body => .mdata data (rename ρ body)

def liftSub (σ : Nat → Expr) : Nat → Expr
  | 0 => .bvar 0
  | i + 1 => rename Nat.succ (σ i)

def subst (σ : Nat → Expr) : Expr → Expr
  | .bvar i => σ i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app fn arg => .app (subst σ fn) (subst σ arg)
  | .lam name domain body info =>
    .lam name (subst σ domain) (subst (liftSub σ) body) info
  | .forallE name domain body info =>
    .forallE name (subst σ domain) (subst (liftSub σ) body) info
  | .letE name type value body nondep =>
    .letE name (subst σ type) (subst σ value) (subst (liftSub σ) body) nondep
  | .proj name index value => .proj name index (subst σ value)
  | .mdata data body => .mdata data (subst σ body)

theorem liftRen_agrees (ρ : Fin n → Fin m) (r : Nat → Nat)
    (h : ∀ i, r i.val = (ρ i).val) :
    ∀ i, liftRen r i.val = (DerivedViewSyntax.liftRen ρ i).val := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact congrArg Nat.succ (h j)

theorem decode_rename (t : Core n) (ρ : Fin n → Fin m) (r : Nat → Nat)
    (h : ∀ i, r i.val = (ρ i).val) :
    CoreExprBridge.decode (DerivedViewSyntax.rename ρ t) =
      rename r (CoreExprBridge.decode t) := by
  induction t generalizing m r with
  | var i => exact congrArg Expr.bvar (h i).symm
  | sort u | const name levels | lit value => rfl
  | app fn arg ihf iha =>
    simp only [DerivedViewSyntax.rename, CoreExprBridge.decode, rename, ihf ρ r h, iha ρ r h]
  | lam attrs domain body ihd ihb | pi attrs domain body ihd ihb =>
    simp only [DerivedViewSyntax.rename, CoreExprBridge.decode, rename,
      ihd ρ r h, ihb _ _ (liftRen_agrees ρ r h)]
  | letE name nondep type value body iht ihv ihb =>
    simp only [DerivedViewSyntax.rename, CoreExprBridge.decode, rename,
      iht ρ r h, ihv ρ r h, ihb _ _ (liftRen_agrees ρ r h)]
  | proj name index value ih =>
    simp only [DerivedViewSyntax.rename, CoreExprBridge.decode, rename, ih ρ r h]
  | unique impossible | inst impossible => contradiction

theorem liftSub_agrees (σ : Fin n → Core m) (s : Nat → Expr)
    (h : ∀ i, s i.val = CoreExprBridge.decode (σ i)) :
    ∀ i, liftSub s i.val = CoreExprBridge.decode (DerivedViewSyntax.liftSub σ i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change rename Nat.succ (s j.val) =
      CoreExprBridge.decode (DerivedViewSyntax.rename Fin.succ (σ j))
    rw [h j]
    exact (decode_rename (σ j) Fin.succ Nat.succ (fun _ => rfl)).symm

theorem decode_subst (t : Core n) (σ : Fin n → Core m) (s : Nat → Expr)
    (h : ∀ i, s i.val = CoreExprBridge.decode (σ i)) :
    CoreExprBridge.decode (DerivedViewSyntax.subst σ t) =
      subst s (CoreExprBridge.decode t) := by
  induction t generalizing m s with
  | var i => exact (h i).symm
  | sort u | const name levels | lit value => rfl
  | app fn arg ihf iha =>
    simp only [DerivedViewSyntax.subst, CoreExprBridge.decode, subst, ihf σ s h, iha σ s h]
  | lam attrs domain body ihd ihb | pi attrs domain body ihd ihb =>
    simp only [DerivedViewSyntax.subst, CoreExprBridge.decode, subst,
      ihd σ s h, ihb _ _ (liftSub_agrees σ s h)]
  | letE name nondep type value body iht ihv ihb =>
    simp only [DerivedViewSyntax.subst, CoreExprBridge.decode, subst,
      iht σ s h, ihv σ s h, ihb _ _ (liftSub_agrees σ s h)]
  | proj name index value ih =>
    simp only [DerivedViewSyntax.subst, CoreExprBridge.decode, subst, ih σ s h]
  | unique impossible | inst impossible => contradiction

-- This applies to every independently admitted source expression, not only
-- expressions accompanied by an encoder's history.
theorem admitted_subst (e : Expr) (he : CoreExprBridge.Admitted e n)
    (σ : Fin n → Core m) (s : Nat → Expr)
    (h : ∀ i, s i.val = CoreExprBridge.decode (σ i)) :
    subst s e = CoreExprBridge.decode
      (DerivedViewSyntax.subst σ (CoreExprBridge.ofAdmitted e n he)) := by
  rw [decode_subst _ σ s h, CoreExprBridge.decode_ofAdmitted]

theorem admitted_subst_closed (e : Expr) (he : CoreExprBridge.Admitted e n)
    (σ : Fin n → Core m) (s : Nat → Expr)
    (h : ∀ i, s i.val = CoreExprBridge.decode (σ i)) :
    CoreExprBridge.Admitted (subst s e) m := by
  rw [admitted_subst e he σ s h]
  exact CoreExprBridge.decode_admitted _

-- The transparent single-slot specification lowers the surviving ambient
-- slots, while liftSub handles all local binders encountered during traversal.
def single (replacement : Expr) : Nat → Expr
  | 0 => replacement
  | i + 1 => .bvar i

def instantiate1Spec (body replacement : Expr) : Expr := subst (single replacement) body

theorem decode_instantiate1Spec (body : Core (n+1)) (replacement : Core n) :
    CoreExprBridge.decode (DerivedViewSyntax.subst (Fin.cases replacement Term.var) body) =
      instantiate1Spec (CoreExprBridge.decode body) (CoreExprBridge.decode replacement) := by
  apply decode_subst
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

-- Metadata is retained explicitly, rather than silently erased by either action.
theorem rename_metadata (ρ : Nat → Nat) (data : MData) (body : Expr) :
    rename ρ (.mdata data body) = .mdata data (rename ρ body) := rfl

theorem subst_metadata (σ : Nat → Expr) (data : MData) (body : Expr) :
    subst σ (.mdata data body) = .mdata data (subst σ body) := rfl

#print axioms rename
#print axioms subst
#print axioms liftRen_agrees
#print axioms decode_rename
#print axioms liftSub_agrees
#print axioms decode_subst
#print axioms admitted_subst
#print axioms admitted_subst_closed
#print axioms decode_instantiate1Spec
#print axioms rename_metadata
#print axioms subst_metadata

end ExprSubstitutionSpec
