import Lean
import DerivedViewSyntax
import ContextualViewDAG
import ContextualDAGCoverage
import UniqueOutputMatcher
import CoreExprBridge

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## 0. A list-based evaluator for run time, proved equal to `ContextualViewDAG.evalArgs`

`ContextualViewDAG.evalArgs` returns `Fin.cases (evalOcc values first) (evalArgs values rest)`. Lean's
compiled `Fin.cases` goes through `Fin.induction`, which evaluates the step function at every
smaller index first, so looking up entry `j` of an actual vector costs time exponential in `j`, and
the cost multiplies when actual vectors are nested. This section defines the same denotation with
actual vectors evaluated once into lists, proves it equal to `unroll` and `unrollArgs` as functions,
and registers the equalities with `@[csimp]`, so that code compiled after this point runs the list
version. Nothing here changes a definition, a theorem statement or a kernel decision: `@[csimp]`
only replaces compiled code, and only through a proved equality. -/

namespace V6FastEval
open DerivedViewSyntax
open ContextualViewDAG (Table Occ Args Row Ref Values evalOcc evalArgs evalRow tableValues unroll unrollArgs)

variable {Γ : List Nat}

def dflt {n : Nat} : View n := .sort .zero

mutual
  def evalOccL (values : Values Γ) {n : Nat} : Occ Γ n → View n
    | .var i => .var i
    | .use ref actuals =>
      let l := evalArgsL values actuals
      DerivedViewSyntax.subst (fun j => l.getD j.val dflt) (values ref)
  def evalArgsL (values : Values Γ) {n : Nat} : {r : Nat} → Args Γ n r → List (View n)
    | _, .nil => []
    | _, .cons first rest => evalOccL values first :: evalArgsL values rest
end

mutual
  theorem evalOccL_eq (values : Values Γ) {n : Nat} : ∀ (o : Occ Γ n), evalOccL values o = evalOcc values o
    | .var _ => rfl
    | .use ref actuals => by
      simp only [evalOccL, evalOcc]
      congr 1
      funext j
      exact evalArgsL_getD values actuals j
  theorem evalArgsL_getD (values : Values Γ) {n : Nat} : ∀ {r : Nat} (a : Args Γ n r) (j : Fin r),
      (evalArgsL values a).getD j.val dflt = evalArgs values a j
    | _, .nil, j => j.elim0
    | _, .cons first rest, j => by
      cases j using Fin.cases with
      | zero => simp only [evalArgsL, evalArgs, Fin.val_zero, List.getD_cons_zero, Fin.cases_zero,
          evalOccL_eq values first]
      | succ k => simp only [evalArgsL, evalArgs, Fin.val_succ, List.getD_cons_succ, Fin.cases_succ,
          evalArgsL_getD values rest k]
end

def evalRowL (values : Values Γ) {n : Nat} : Row Γ n → View n
  | .var i => .var i
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app fn arg => .app (evalOccL values fn) (evalOccL values arg)
  | .lam attrs domain body => .lam attrs (evalOccL values domain) (evalOccL values body)
  | .pi attrs domain body => .pi attrs (evalOccL values domain) (evalOccL values body)
  | .letE name nondep type value body =>
    .letE name nondep (evalOccL values type) (evalOccL values value) (evalOccL values body)
  | .proj name index value => .proj name index (evalOccL values value)
  | .unique attrs A B step advance relation =>
    .unique rfl attrs (evalOccL values A) (evalOccL values B) (evalOccL values step)
      (evalOccL values advance) (evalOccL values relation)
  | .inst body actuals =>
    let l := evalArgsL values actuals
    .inst rfl (evalOccL values body) (fun j => l.getD j.val dflt)

theorem evalRowL_eq (values : Values Γ) {n : Nat} (row : Row Γ n) : evalRowL values row = evalRow values row := by
  cases row <;> simp only [evalRowL, evalRow, evalOccL_eq]
  case inst body actuals =>
    congr 1
    funext j
    exact evalArgsL_getD values actuals j

def tableValuesL : {Γ : List Nat} → Table Γ → Values Γ
  | _, .empty => fun ref => nomatch ref
  | _, .snoc prior row => fun ref =>
    match ref with
    | .here => evalRowL (tableValuesL prior) row
    | .there previous => tableValuesL prior previous

theorem tableValuesL_eq : ∀ {Γ : List Nat} (tb : Table Γ) {r : Nat} (ref : Ref Γ r),
    tableValuesL tb ref = tableValues tb ref
  | _, .empty, _, ref => nomatch ref
  | _, .snoc prior row, _, .here => by
    have h : (fun {r : Nat} (ref : Ref _ r) => tableValuesL prior ref) =
        (fun {r : Nat} (ref : Ref _ r) => tableValues prior ref) := by
      funext r ref
      exact tableValuesL_eq prior ref
    simp only [tableValuesL, tableValues, evalRowL_eq]
    exact congrArg (fun (v : Values _) => evalRow v row) h
  | _, .snoc prior _, _, .there previous => by
    simp only [tableValuesL, tableValues]
    exact tableValuesL_eq prior previous

def unrollL {Γ : List Nat} {n : Nat} (table : Table Γ) (occurrence : Occ Γ n) : View n :=
  evalOccL (tableValuesL table) occurrence

def unrollArgsL {Γ : List Nat} {n r : Nat} (table : Table Γ) (actuals : Args Γ n r) : Fin r → View n :=
  let l := evalArgsL (tableValuesL table) actuals
  fun j => l.getD j.val dflt

theorem tableValuesL_fun {Γ : List Nat} (tb : Table Γ) :
    (fun {r : Nat} (ref : Ref Γ r) => tableValuesL tb ref) = (fun {r : Nat} (ref : Ref Γ r) => tableValues tb ref) := by
  funext r ref
  exact tableValuesL_eq tb ref

@[csimp] theorem unroll_eq_unrollL : @unroll = @unrollL := by
  funext Γ n table o
  simp only [unroll, unrollL, evalOccL_eq]
  exact congrArg (fun (v : Values Γ) => evalOcc v o) (tableValuesL_fun table).symm

@[csimp] theorem unrollArgs_eq_unrollArgsL : @unrollArgs = @unrollArgsL := by
  funext Γ n r table a j
  simp only [unrollArgs, unrollArgsL, evalArgsL_getD]
  exact congrArg (fun (v : Values Γ) => evalArgs v a j) (tableValuesL_fun table).symm

end V6FastEval

namespace V6BinderShared

open DerivedViewSyntax

/-! ## 1. Selections through application fields and product or let bodies -/

/-- A finite selector over `DerivedViewSyntax.Term`. It descends through both fields of an application
    and through the BODY field of a product (`pi`) or a `let`; it never enters a binder domain, a
    let type or a let value. `hole i` marks declared use `i`. -/
inductive BSel where
  | none
  | hole (i : Nat)
  | app (f a : BSel)
  | pi (body : BSel)
  | letE (body : BSel)
  deriving Repr, Inhabited, DecidableEq

/-- A depth-indexed family over home arity `n`: at depth `e` (binders crossed below the home),
    hole `i` receives a term of arity `n + e`. Origins and suppliers are given this way. -/
abbrev Fam (b : Bool) (n : Nat) := (e : Nat) → Nat → Term b (n + e)

variable {b : Bool}

/-- Fill the holes of `s` in `t`, a term `e` binders below the home. Everything outside the holes
    is kept, including binder attributes and domains and let names, flags, types and values. -/
def fillD {n : Nat} (e : Nat) (t : Term b (n + e)) (s : BSel) (O : Fam b n) : Term b (n + e) :=
  match s with
  | .none => t
  | .hole i => O e i
  | .app sf sa =>
    match t with
    | .app f a => .app (fillD e f sf O) (fillD e a sa O)
    | t => t
  | .pi sb =>
    match t with
    | .pi attrs dom body => .pi attrs dom (fillD (e+1) body sb O)
    | t => t
  | .letE sb =>
    match t with
    | .letE name nondep ty val body => .letE name nondep ty val (fillD (e+1) body sb O)
    | t => t
termination_by structural s

/-- Every selected constructor exists (the positions are real). -/
def Shape {k : Nat} (t : Term b k) (s : BSel) : Prop :=
  match s with
  | .none => True
  | .hole _ => True
  | .app sf sa =>
    match t with
    | .app f a => Shape f sf ∧ Shape a sa
    | _ => False
  | .pi sb =>
    match t with
    | .pi _ _ body => Shape body sb
    | _ => False
  | .letE sb =>
    match t with
    | .letE _ _ _ _ body => Shape body sb
    | _ => False
termination_by structural s

/-- The term carries `O e i` at every hole `i` (found at depth `e`). -/
def FitsD {n : Nat} (e : Nat) (t : Term b (n + e)) (s : BSel) (O : Fam b n) : Prop :=
  match s with
  | .none => True
  | .hole i => t = O e i
  | .app sf sa =>
    match t with
    | .app f a => FitsD e f sf O ∧ FitsD e a sa O
    | _ => False
  | .pi sb =>
    match t with
    | .pi _ _ body => FitsD (e+1) body sb O
    | _ => False
  | .letE sb =>
    match t with
    | .letE _ _ _ _ body => FitsD (e+1) body sb O
    | _ => False
termination_by structural s

/-- Independent constructor comparison outside the holes: the same constructors along the selected
    paths, equal binder attributes and domains, equal let names, flags, types and values, and equal
    subterms off the selected paths. Nothing is compared inside a hole. -/
def Agree {k : Nat} (t u : Term b k) (s : BSel) : Prop :=
  match s with
  | .none => t = u
  | .hole _ => True
  | .app sf sa =>
    match t, u with
    | .app f a, .app f' a' => Agree f f' sf ∧ Agree a a' sa
    | _, _ => False
  | .pi sb =>
    match t, u with
    | .pi xt dt bt, .pi xu du bu => xt = xu ∧ dt = du ∧ Agree bt bu sb
    | _, _ => False
  | .letE sb =>
    match t, u with
    | .letE nt ft tt vt bt, .letE nu fu tu vu bu =>
        nt = nu ∧ ft = fu ∧ tt = tu ∧ vt = vu ∧ Agree bt bu sb
    | _, _ => False
termination_by structural s

/-! ### Recovery and incidence -/

/-- Filling a term with what it already carries returns the term. -/
theorem fillD_self (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O : Fam b n),
    FitsD e t s O → fillD e t s O = t := by
  induction s with
  | none => intro n e t O _; rfl
  | hole i => intro n e t O h; exact Eq.symm h
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [FitsD] at h
      simp only [fillD, ihf e f O h.1, iha e a O h.2]
    all_goals simp only [FitsD] at h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [FitsD] at h
      simp only [fillD, ih (e+1) body O h]
    all_goals simp only [FitsD] at h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [FitsD] at h
      simp only [fillD, ih (e+1) body O h]
    all_goals simp only [FitsD] at h

/-- Refilling: only the holes change, so a second fill overrides the first. -/
theorem fillD_fillD (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O O' : Fam b n),
    fillD e (fillD e t s O) s O' = fillD e t s O' := by
  induction s with
  | none => intro n e t O O'; rfl
  | hole i => intro n e t O O'; rfl
  | app sf sa ihf iha =>
    intro n e t O O'
    cases t
    case app f a => simp only [fillD, ihf e f O O', iha e a O O']
    all_goals rfl
  | pi sb ih =>
    intro n e t O O'
    cases t
    case pi attrs dom body => simp only [fillD, ih (e+1) body O O']
    all_goals rfl
  | letE sb ih =>
    intro n e t O O'
    cases t
    case letE name nondep ty val body => simp only [fillD, ih (e+1) body O O']
    all_goals rfl

/-- Incidence: after filling, every hole carries its assigned term. -/
theorem fillD_fits (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O : Fam b n),
    Shape t s → FitsD e (fillD e t s O) s O := by
  induction s with
  | none => intro n e t O _; trivial
  | hole i => intro n e t O _; rfl
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [fillD, FitsD]
      exact ⟨ihf e f O h.1, iha e a O h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [fillD, FitsD]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [fillD, FitsD]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h

/-- Filling keeps the selected constructors. -/
theorem shape_fillD (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O : Fam b n),
    Shape t s → Shape (fillD e t s O) s := by
  induction s with
  | none => intro n e t O _; trivial
  | hole i => intro n e t O _; trivial
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [fillD, Shape]
      exact ⟨ihf e f O h.1, iha e a O h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [fillD, Shape]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [fillD, Shape]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h

/-- Nonselected structure is preserved: the filled term agrees with the original outside holes. -/
theorem agree_fillD (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O : Fam b n),
    Shape t s → Agree t (fillD e t s O) s := by
  induction s with
  | none => intro n e t O _; rfl
  | hole i => intro n e t O _; trivial
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [fillD, Agree]
      exact ⟨ihf e f O h.1, iha e a O h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [fillD, Agree, true_and]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [fillD, Agree, true_and]
      exact ih (e+1) body O h
    all_goals simp only [Shape] at h

/-- Reconstruction from the independent comparison: if `t` agrees with `u` outside the holes and
    `u` carries `O` at the holes, filling `t` with `O` gives exactly `u`. -/
theorem agree_fill (s : BSel) : ∀ {n : Nat} (e : Nat) (t u : Term b (n + e)) (O : Fam b n),
    Agree t u s → FitsD e u s O → fillD e t s O = u := by
  induction s with
  | none => intro n e t u O hA _; exact hA
  | hole i => intro n e t u O _ hF; exact Eq.symm hF
  | app sf sa ihf iha =>
    intro n e t u O hA hF
    cases t
    case app f a =>
      cases u
      case app f' a' =>
        simp only [Agree] at hA
        simp only [FitsD] at hF
        simp only [fillD, ihf e f f' O hA.1 hF.1, iha e a a' O hA.2 hF.2]
      all_goals simp only [Agree] at hA
    all_goals simp only [Agree] at hA
  | pi sb ih =>
    intro n e t u O hA hF
    cases t
    case pi xt dt bt =>
      cases u
      case pi xu du bu =>
        simp only [Agree] at hA
        simp only [FitsD] at hF
        obtain ⟨h1, h2, h3⟩ := hA
        subst h1 h2
        simp only [fillD, ih (e+1) bt bu O h3 hF]
      all_goals simp only [Agree] at hA
    all_goals simp only [Agree] at hA
  | letE sb ih =>
    intro n e t u O hA hF
    cases t
    case letE nt ft tt vt bt =>
      cases u
      case letE nu fu tu vu bu =>
        simp only [Agree] at hA
        simp only [FitsD] at hF
        obtain ⟨h1, h2, h3, h4, h5⟩ := hA
        subst h1 h2 h3 h4
        simp only [fillD, ih (e+1) bt bu O h5 hF]
      all_goals simp only [Agree] at hA
    all_goals simp only [Agree] at hA

/-- (b) Restoring the view origins recovers the exact view. -/
theorem restore_view {n : Nat} (V : Term b n) (s : BSel) (P Ov : Fam b n)
    (hV : FitsD 0 V s Ov) : fillD 0 (fillD 0 V s P) s Ov = V := by
  rw [fillD_fillD]
  exact fillD_self s 0 V Ov hV

/-- (b) Restoring the source origins recovers the exact source, from the independent comparison
    of view and source outside the holes and the source's own origins at the holes. -/
theorem restore_source {n : Nat} (V T : Term b n) (s : BSel) (P Os : Fam b n)
    (hA : Agree V T s) (hT : FitsD 0 T s Os) : fillD 0 (fillD 0 V s P) s Os = T := by
  rw [fillD_fillD]
  exact agree_fill s 0 V T Os hA hT

/-! ### Ambient substitution (c) -/

/-- Iterated `liftSub`: the ambient substitution seen `e` binders below the home. -/
def liftSubN {n m : Nat} : (e : Nat) → (Fin n → Term b m) → Fin (n + e) → Term b (m + e)
  | 0, σ => σ
  | e+1, σ => liftSub (liftSubN e σ)

theorem liftSubN_zero {n m : Nat} (σ : Fin n → Term b m) : liftSubN 0 σ = σ := rfl

theorem liftSubN_succ {n m : Nat} (e : Nat) (σ : Fin n → Term b m) :
    liftSubN (e+1) σ = liftSub (liftSubN e σ) := rfl

/-- Origins transported by the ambient substitution at their own depth. -/
def substFam {n m : Nat} (σ : Fin n → Term b m) (O : Fam b n) : Fam b m :=
  fun e i => subst (liftSubN e σ) (O e i)

theorem shape_rename (s : BSel) : ∀ {k k' : Nat} (ρ : Fin k → Fin k') (t : Term b k),
    Shape t s → Shape (rename ρ t) s := by
  induction s with
  | none => intro k k' ρ t _; trivial
  | hole i => intro k k' ρ t _; trivial
  | app sf sa ihf iha =>
    intro k k' ρ t h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [rename, Shape]
      exact ⟨ihf ρ f h.1, iha ρ a h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro k k' ρ t h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [rename, Shape]
      exact ih (liftRen ρ) body h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro k k' ρ t h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [rename, Shape]
      exact ih (liftRen ρ) body h
    all_goals simp only [Shape] at h

theorem shape_subst (s : BSel) : ∀ {k k' : Nat} (σ : Fin k → Term b k') (t : Term b k),
    Shape t s → Shape (subst σ t) s := by
  induction s with
  | none => intro k k' σ t _; trivial
  | hole i => intro k k' σ t _; trivial
  | app sf sa ihf iha =>
    intro k k' σ t h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [subst, Shape]
      exact ⟨ihf σ f h.1, iha σ a h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro k k' σ t h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [subst, Shape]
      exact ih (liftSub σ) body h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro k k' σ t h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [subst, Shape]
      exact ih (liftSub σ) body h
    all_goals simp only [Shape] at h

/-- The comparison outside holes is stable under any substitution. -/
theorem agree_subst (s : BSel) : ∀ {k k' : Nat} (σ : Fin k → Term b k') (t u : Term b k),
    Agree t u s → Agree (subst σ t) (subst σ u) s := by
  induction s with
  | none => intro k k' σ t u h; simp only [Agree] at h ⊢; rw [h]
  | hole i => intro k k' σ t u _; trivial
  | app sf sa ihf iha =>
    intro k k' σ t u h
    cases t
    case app f a =>
      cases u
      case app f' a' =>
        simp only [Agree] at h
        simp only [subst, Agree]
        exact ⟨ihf σ f f' h.1, iha σ a a' h.2⟩
      all_goals simp only [Agree] at h
    all_goals simp only [Agree] at h
  | pi sb ih =>
    intro k k' σ t u h
    cases t
    case pi xt dt bt =>
      cases u
      case pi xu du bu =>
        simp only [Agree] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1 h2
        simp only [subst, Agree, true_and]
        exact ih (liftSub σ) bt bu h3
      all_goals simp only [Agree] at h
    all_goals simp only [Agree] at h
  | letE sb ih =>
    intro k k' σ t u h
    cases t
    case letE nt ft tt vt bt =>
      cases u
      case letE nu fu tu vu bu =>
        simp only [Agree] at h
        obtain ⟨h1, h2, h3, h4, h5⟩ := h
        subst h1 h2 h3 h4
        simp only [subst, Agree, true_and]
        exact ih (liftSub σ) bt bu h5
      all_goals simp only [Agree] at h
    all_goals simp only [Agree] at h

/-- Fill and ambient substitution commute: the ambient substitution acts on the unselected fields
    (domains, let types and values included) and, at depth `e`, on each hole's term through
    `liftSubN e`. The selection itself is transported unchanged. -/
theorem subst_fillD {n m : Nat} (σ : Fin n → Term b m) (s : BSel) :
    ∀ (e : Nat) (t : Term b (n + e)) (O : Fam b n), Shape t s →
      subst (liftSubN e σ) (fillD e t s O) = fillD e (subst (liftSubN e σ) t) s (substFam σ O) := by
  induction s with
  | none => intro e t O _; rfl
  | hole i => intro e t O _; rfl
  | app sf sa ihf iha =>
    intro e t O h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [fillD, subst, ihf e f O h.1, iha e a O h.2]
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro e t O h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      exact congrArg (Term.pi attrs (subst (liftSubN e σ) dom)) (ih (e+1) body O h)
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      exact congrArg (Term.letE name nondep (subst (liftSubN e σ) ty) (subst (liftSubN e σ) val))
        (ih (e+1) body O h)
    all_goals simp only [Shape] at h

/-- Origins carried at the holes are transported with the term. -/
theorem fitsD_subst {n m : Nat} (σ : Fin n → Term b m) (s : BSel) :
    ∀ (e : Nat) (t : Term b (n + e)) (O : Fam b n), FitsD e t s O →
      FitsD e (subst (liftSubN e σ) t) s (substFam σ O) := by
  induction s with
  | none => intro e t O _; trivial
  | hole i =>
    intro e t O h
    simp only [FitsD] at h ⊢
    rw [h]
    rfl
  | app sf sa ihf iha =>
    intro e t O h
    cases t
    case app f a =>
      simp only [FitsD] at h
      simp only [subst, FitsD]
      exact ⟨ihf e f O h.1, iha e a O h.2⟩
    all_goals simp only [FitsD] at h
  | pi sb ih =>
    intro e t O h
    cases t
    case pi attrs dom body =>
      simp only [FitsD] at h
      exact ih (e+1) body O h
    all_goals simp only [FitsD] at h
  | letE sb ih =>
    intro e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [FitsD] at h
      exact ih (e+1) body O h
    all_goals simp only [FitsD] at h

/-! ### Explicit actual vectors and the transported home supplier -/

/-- The explicit actual vector of a prefix weakening by `e` binders: home position `j` ↦ `j + e`. -/
def weakActs (n e : Nat) : Fin n → Term b (n + e) := fun j => .var (j.addNat e)

/-- The home supplier `p`, transported to depth `e` through its explicit actual vector. -/
def lifted {n : Nat} (p : Term b n) : Fam b n := fun e _ => subst (weakActs n e) p

theorem liftSubN_addNat {n m : Nat} (σ : Fin n → Term b m) (e : Nat) (j : Fin n) :
    liftSubN e σ (j.addNat e) = rename (fun k => k.addNat e) (σ j) := by
  induction e with
  | zero =>
    have h1 : (fun k : Fin m => k.addNat 0) = id := funext fun k => Fin.ext (Nat.add_zero _)
    rw [h1, rename_id]
    rfl
  | succ e ih =>
    have h2 : j.addNat (e+1) = (j.addNat e).succ :=
      Fin.ext (by simp only [Fin.val_addNat, Fin.val_succ]; omega)
    rw [liftSubN_succ, h2, liftSub_succ, ih, rename_comp]
    rfl

/-- (c) on the explicit local actuals: the ambient substitution seen at depth `e`, applied to the
    actual vector of the prefix weakening, is the substitution followed by that weakening. -/
theorem acts_subst {n m : Nat} (σ : Fin n → Term b m) (e : Nat) :
    (fun j => subst (liftSubN e σ) (weakActs n e j)) = (fun j => subst (weakActs m e) (σ j)) := by
  funext j
  simp only [weakActs, subst]
  rw [liftSubN_addNat, rename_eq_subst]
  rfl

theorem substFam_lifted {n m : Nat} (σ : Fin n → Term b m) (p : Term b n) :
    substFam σ (lifted p) = lifted (subst σ p) := by
  funext e i
  simp only [substFam, lifted]
  rw [subst_comp, subst_comp]
  exact congrArg (fun f => subst f p) (acts_subst σ e)

/-- (c) Sharing commutes with ambient substitution: the fixed selection of the substituted view
    carries the substituted home supplier. No recognition or representative choice is rerun. -/
theorem shared_subst {n m : Nat} (σ : Fin n → Term b m) (V : Term b n) (s : BSel) (p : Term b n)
    (hV : Shape V s) :
    subst σ (fillD 0 V s (lifted p)) = fillD 0 (subst σ V) s (lifted (subst σ p)) := by
  have h := subst_fillD σ s 0 V (lifted p) hV
  rw [substFam_lifted] at h
  exact h

/-- (c) Restoration commutes with ambient substitution, for either origin family. -/
theorem restore_subst {n m : Nat} (σ : Fin n → Term b m) (V : Term b n) (s : BSel)
    (P O : Fam b n) (hV : Shape V s) :
    subst σ (fillD 0 (fillD 0 V s P) s O) = fillD 0 (subst σ (fillD 0 V s P)) s (substFam σ O) :=
  subst_fillD σ s 0 _ O (shape_fillD s 0 V P hV)

/-- (b) after (c): the transported origins restore the transported view and source exactly. -/
theorem restore_after_subst {n m : Nat} (σ : Fin n → Term b m) (V T : Term b n) (s : BSel)
    (p : Term b n) (Ov Os : Fam b n) (hV : Shape V s) (hOv : FitsD 0 V s Ov)
    (hA : Agree V T s) (hT : FitsD 0 T s Os) :
    fillD 0 (subst σ (fillD 0 V s (lifted p))) s (substFam σ Ov) = subst σ V ∧
    fillD 0 (subst σ (fillD 0 V s (lifted p))) s (substFam σ Os) = subst σ T := by
  rw [shared_subst σ V s p hV]
  exact ⟨restore_view (subst σ V) s _ _ (fitsD_subst σ s 0 V Ov hOv),
    restore_source (subst σ V) (subst σ T) s _ _ (agree_subst s σ V T hA) (fitsD_subst σ s 0 T Os hT)⟩

/-! ### (a) One home supplier at every selected position -/

/-- (a) After sharing, each selected position at depth `e` holds the home supplier instantiated at
    the explicit actual vector `weakActs n e`, and the term agrees with the original outside the
    holes (constructors, binder attributes and domains, let fields). -/
theorem shared_incidence {n : Nat} (V : Term b n) (s : BSel) (p : Term b n) (hV : Shape V s) :
    FitsD 0 (fillD 0 V s (lifted p)) s (fun e _ => subst (weakActs n e) p) ∧
      Agree V (fillD 0 V s (lifted p)) s :=
  ⟨fillD_fits s 0 V (lifted p) hV, agree_fillD s 0 V (lifted p) hV⟩

/-! ### The consumer at `H,M` and the one plugged producer -/

/-- The new binder `M` seen at depth `e` below the home of `H,M`: index `e`, not index 0. -/
def nodeVar {n : Nat} : Fam b (n+1) := fun e _ => .var ⟨e, by omega⟩

/-- The consumer, constructed independently of the plug: weaken the original term past the new
    binder `M` and put `M` (index `e` at depth `e`) at every selected position. -/
def consumer {n : Nat} (V : Term b n) (s : BSel) : Term b (n+1) :=
  fillD 0 (rename Fin.succ V) s nodeVar

theorem substFam_nodeVar {n : Nat} (p : Term b n) :
    substFam (Fin.cases p Term.var : Fin (n+1) → Term b n) nodeVar = lifted p := by
  funext e i
  simp only [substFam, nodeVar, lifted, subst]
  have h : (⟨e, by omega⟩ : Fin (n + 1 + e)) = (0 : Fin (n+1)).addNat e :=
    Fin.ext (by simp only [Fin.val_addNat, Fin.val_zero]; omega)
  rw [h, liftSubN_addNat, rename_eq_subst]
  rfl

/-- Plugging the producer `p` for `M` gives the shared term: every selected position holds `p`
    through its lifted actuals. -/
theorem plug_shared {n : Nat} (V : Term b n) (s : BSel) (p : Term b n) (hV : Shape V s) :
    subst (Fin.cases p Term.var) (consumer V s) = fillD 0 V s (lifted p) := by
  have h1 := subst_fillD (Fin.cases p Term.var : Fin (n+1) → Term b n) s 0 (rename Fin.succ V)
    nodeVar (shape_rename s Fin.succ V hV)
  rw [substFam_nodeVar] at h1
  have h2 : subst (Fin.cases p Term.var : Fin (n+1) → Term b n) (rename Fin.succ V) = V := by
    rw [subst_rename]
    exact subst_id V
  unfold consumer
  exact h1.trans (congrArg (fun t => fillD 0 t s (lifted p)) h2)

theorem substFam_liftSub_nodeVar {n m : Nat} (σ : Fin n → Term b m) :
    substFam (liftSub σ) (nodeVar (n := n)) = (nodeVar (n := m)) := by
  funext e i
  simp only [substFam, nodeVar, subst]
  have h : (⟨e, by omega⟩ : Fin (n + 1 + e)) = (0 : Fin (n+1)).addNat e :=
    Fin.ext (by simp only [Fin.val_addNat, Fin.val_zero]; omega)
  rw [h, liftSubN_addNat, liftSub_zero]
  exact congrArg Term.var (Fin.ext (by simp only [Fin.val_addNat, Fin.val_zero]; omega))

/-- (c) for the consumer: the ambient substitution, lifted past the new binder `M`, transports the
    consumer of a fixed selection to the consumer of the substituted term with the same selection. -/
theorem consumer_subst {n m : Nat} (σ : Fin n → Term b m) (V : Term b n) (s : BSel)
    (hV : Shape V s) : subst (liftSub σ) (consumer V s) = consumer (subst σ V) s := by
  have h1 := subst_fillD (liftSub σ) s 0 (rename Fin.succ V) nodeVar (shape_rename s Fin.succ V hV)
  rw [substFam_liftSub_nodeVar] at h1
  unfold consumer
  rw [← subst_weaken V σ]
  exact h1

/-- `DerivedViewSyntax.corePlug` with the identity actual map at the home. -/
theorem corePlug_shared {n : Nat} (V : Core n) (s : BSel) (p : Core n) (hV : Shape V s) :
    corePlug (consumer V s) p Term.var = fillD 0 V s (lifted p) := by
  unfold corePlug
  rw [subst_id]
  exact plug_shared V s p hV

/-- `DerivedViewSyntax.plug` on View terms: each selected position holds the explicit instantiation node of the
    one producer at the explicit actual vector of its depth. -/
theorem viewPlug_shared {n : Nat} (V : View n) (s : BSel) (P : View n) (hV : Shape V s) :
    DerivedViewSyntax.plug (consumer V s) P Term.var =
      fillD 0 V s (fun e _ => .inst rfl P (weakActs n e)) := by
  unfold DerivedViewSyntax.plug
  rw [plug_shared V s _ hV]
  rfl

/-- Expansion commutes with filling on real positions. -/
theorem expand_fillD (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Term b (n + e)) (O : Fam b n),
    Shape t s → expand (fillD e t s O) = fillD e (expand t) s (fun e i => expand (O e i)) := by
  induction s with
  | none => intro n e t O _; rfl
  | hole i => intro n e t O _; rfl
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [fillD, expand, ihf e f O h.1, iha e a O h.2]
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      exact congrArg (Term.pi attrs (expand dom)) (ih (e+1) body O h)
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      exact congrArg (Term.letE name nondep (expand ty) (expand val)) (ih (e+1) body O h)
    all_goals simp only [Shape] at h

theorem expand_consumer {n : Nat} (V : View n) (s : BSel) (hV : Shape V s) :
    expand (consumer V s) = consumer (expand V) s := by
  unfold consumer
  rw [expand_fillD s 0 (rename Fin.succ V) nodeVar (shape_rename s Fin.succ V hV), expand_rename]
  rfl

theorem shape_expand (s : BSel) : ∀ {k : Nat} (t : Term b k), Shape t s → Shape (expand t) s := by
  induction s with
  | none => intro k t _; trivial
  | hole i => intro k t _; trivial
  | app sf sa ihf iha =>
    intro k t h
    cases t
    case app f a =>
      simp only [Shape] at h
      simp only [expand, Shape]
      exact ⟨ihf f h.1, iha a h.2⟩
    all_goals simp only [Shape] at h
  | pi sb ih =>
    intro k t h
    cases t
    case pi attrs dom body =>
      simp only [Shape] at h
      simp only [expand, Shape]
      exact ih body h
    all_goals simp only [Shape] at h
  | letE sb ih =>
    intro k t h
    cases t
    case letE name nondep ty val body =>
      simp only [Shape] at h
      simp only [expand, Shape]
      exact ih body h
    all_goals simp only [Shape] at h

/-! ### (d) The finite contextual table: consumer and one producer row -/

section Table
open ContextualViewDAG

theorem unrollArgs_ids {Γ : List Nat} {n : Nat} (table : Table Γ) :
    unrollArgs table (Args.ofFn (Occ.var : Fin n → Occ Γ n)) = Term.var := by
  unfold unrollArgs
  rw [evalArgs_ofFn]
  rfl

/-- (d) Given a finite table that represents the consumer at `H,M` and the producer at `H`, the
    table plug in `ContextualViewDAG` (one new `inst` row, `plugTable`, and `plugOccurrence`) unrolls to the shared
    view: each selected position holds the one producer at its explicit lifted actuals. -/
theorem table_shared {Γ : List Nat} {n : Nat} (table : Table Γ) (cOcc : Occ Γ (n+1))
    (pOcc : Occ Γ n) (V : View n) (s : BSel) (hV : Shape V s)
    (hc : unroll table cOcc = consumer V s) :
    unroll (plugTable table pOcc (Args.ofFn Occ.var)) (plugOccurrence cOcc) =
      fillD 0 V s (fun e _ => .inst rfl (unroll table pOcc) (weakActs n e)) := by
  rw [unroll_plug, hc, unrollArgs_ids]
  exact viewPlug_shared V s _ hV

/-- (d) Selected common incidence: every selected position holds the unrolling of the same
    occurrence, the single `freshUse` of the one plugged row, transported by the explicit actual
    vector of its depth. -/
theorem table_incidence {Γ : List Nat} {n : Nat} (table : Table Γ) (cOcc : Occ Γ (n+1))
    (pOcc : Occ Γ n) (V : View n) (s : BSel) (hV : Shape V s)
    (hc : unroll table cOcc = consumer V s) :
    unroll (plugTable table pOcc (Args.ofFn Occ.var)) (plugOccurrence cOcc) =
      fillD 0 V s (fun e _ =>
        DerivedViewSyntax.subst (weakActs n e)
          (unroll (plugTable table pOcc (Args.ofFn Occ.var)) (freshUse (Γ := Γ) (n := n)))) := by
  rw [table_shared table cOcc pOcc V s hV hc, unroll_freshUse, unrollArgs_ids]
  rfl

/-- (d) The Core expansion, through `ContextualViewDAG.expand_unroll_plug` and `DerivedViewSyntax.corePlug`. -/
theorem table_shared_expand {Γ : List Nat} {n : Nat} (table : Table Γ) (cOcc : Occ Γ (n+1))
    (pOcc : Occ Γ n) (V : Core n) (s : BSel) (hV : Shape V s)
    (hc : expand (unroll table cOcc) = consumer V s) :
    expand (unroll (plugTable table pOcc (Args.ofFn Occ.var)) (plugOccurrence cOcc)) =
      fillD 0 V s (lifted (expand (unroll table pOcc))) := by
  rw [expand_unroll_plug, hc]
  have ha : (fun i => expand (unrollArgs table (Args.ofFn (Occ.var : Fin n → Occ Γ n)) i)) =
      (Term.var : Fin n → Core n) := by
    rw [unrollArgs_ids]
    rfl
  rw [ha]
  exact corePlug_shared V s _ hV

end Table

/-! ### Executable checks with field-preserving Core equality, and their soundness -/

def shapeB {k : Nat} (t : Term b k) (s : BSel) : Bool :=
  match s with
  | .none => true
  | .hole _ => true
  | .app sf sa =>
    match t with
    | .app f a => shapeB f sf && shapeB a sa
    | _ => false
  | .pi sb =>
    match t with
    | .pi _ _ body => shapeB body sb
    | _ => false
  | .letE sb =>
    match t with
    | .letE _ _ _ _ body => shapeB body sb
    | _ => false
termination_by structural s

theorem shapeB_sound (s : BSel) : ∀ {k : Nat} (t : Term b k), shapeB t s = true → Shape t s := by
  induction s with
  | none => intro k t _; trivial
  | hole i => intro k t _; trivial
  | app sf sa ihf iha =>
    intro k t h
    cases t
    case app f a =>
      simp only [shapeB, Bool.and_eq_true] at h
      exact ⟨ihf f h.1, iha a h.2⟩
    all_goals simp only [shapeB] at h; cases h
  | pi sb ih =>
    intro k t h
    cases t
    case pi attrs dom body =>
      simp only [shapeB] at h
      exact ih body h
    all_goals simp only [shapeB] at h; cases h
  | letE sb ih =>
    intro k t h
    cases t
    case letE name nondep ty val body =>
      simp only [shapeB] at h
      exact ih body h
    all_goals simp only [shapeB] at h; cases h

/-- The comparison outside holes, computed with `DerivedViewSyntax.coreEq`, which preserves fields (names,
    binder information, levels and literals included; no `Expr` equality anywhere). -/
def agreeCB {k : Nat} (t u : Core k) (s : BSel) : Bool :=
  match s with
  | .none => coreEq t u
  | .hole _ => true
  | .app sf sa =>
    match t, u with
    | .app f a, .app f' a' => agreeCB f f' sf && agreeCB a a' sa
    | _, _ => false
  | .pi sb =>
    match t, u with
    | .pi xt dt bt, .pi xu du bu => decide (xt = xu) && coreEq dt du && agreeCB bt bu sb
    | _, _ => false
  | .letE sb =>
    match t, u with
    | .letE nt ft tt vt bt, .letE nu fu tu vu bu =>
        decide (nt = nu ∧ ft = fu) && coreEq tt tu && coreEq vt vu && agreeCB bt bu sb
    | _, _ => false
termination_by structural s

theorem agreeCB_sound (s : BSel) : ∀ {k : Nat} (t u : Core k), agreeCB t u s = true → Agree t u s := by
  induction s with
  | none => intro k t u h; exact (coreEq_iff t u).mp h
  | hole i => intro k t u _; trivial
  | app sf sa ihf iha =>
    intro k t u h
    cases t
    case app f a =>
      cases u
      case app f' a' =>
        simp only [agreeCB, Bool.and_eq_true] at h
        exact ⟨ihf f f' h.1, iha a a' h.2⟩
      all_goals simp only [agreeCB] at h; cases h
    all_goals simp only [agreeCB] at h; cases h
  | pi sb ih =>
    intro k t u h
    cases t
    case pi xt dt bt =>
      cases u
      case pi xu du bu =>
        simp only [agreeCB, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1, (coreEq_iff dt du).mp h.1.2, ih bt bu h.2⟩
      all_goals simp only [agreeCB] at h; cases h
    all_goals simp only [agreeCB] at h; cases h
  | letE sb ih =>
    intro k t u h
    cases t
    case letE nt ft tt vt bt =>
      cases u
      case letE nu fu tu vu bu =>
        simp only [agreeCB, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1.1.1, h.1.1.1.2, (coreEq_iff tt tu).mp h.1.1.2, (coreEq_iff vt vu).mp h.1.2,
          ih bt bu h.2⟩
      all_goals simp only [agreeCB] at h; cases h
    all_goals simp only [agreeCB] at h; cases h

def fitsCB {n : Nat} (e : Nat) (t : Core (n + e)) (s : BSel) (O : Fam false n) : Bool :=
  match s with
  | .none => true
  | .hole i => coreEq t (O e i)
  | .app sf sa =>
    match t with
    | .app f a => fitsCB e f sf O && fitsCB e a sa O
    | _ => false
  | .pi sb =>
    match t with
    | .pi _ _ body => fitsCB (e+1) body sb O
    | _ => false
  | .letE sb =>
    match t with
    | .letE _ _ _ _ body => fitsCB (e+1) body sb O
    | _ => false
termination_by structural s

theorem fitsCB_sound (s : BSel) : ∀ {n : Nat} (e : Nat) (t : Core (n + e)) (O : Fam false n),
    fitsCB e t s O = true → FitsD e t s O := by
  induction s with
  | none => intro n e t O _; trivial
  | hole i => intro n e t O h; exact (coreEq_iff _ _).mp h
  | app sf sa ihf iha =>
    intro n e t O h
    cases t
    case app f a =>
      simp only [fitsCB, Bool.and_eq_true] at h
      exact ⟨ihf e f O h.1, iha e a O h.2⟩
    all_goals simp only [fitsCB] at h; cases h
  | pi sb ih =>
    intro n e t O h
    cases t
    case pi attrs dom body =>
      simp only [fitsCB] at h
      exact ih (e+1) body O h
    all_goals simp only [fitsCB] at h; cases h
  | letE sb ih =>
    intro n e t O h
    cases t
    case letE name nondep ty val body =>
      simp only [fitsCB] at h
      exact ih (e+1) body O h
    all_goals simp only [fitsCB] at h; cases h

/-- Admission of one use's explicit actual vector: only the prefix weakening of its depth, checked
    entry by entry with `coreEq`. Equal arity, equal types or a repeated printed name is not an
    actual map. -/
def isPrefixWeakening {n : Nat} (e : Nat) (acts : Fin n → Core (n + e)) : Bool :=
  (List.finRange n).all fun j => coreEq (acts j) (weakActs n e j)

theorem isPrefixWeakening_sound {n : Nat} (e : Nat) (acts : Fin n → Core (n + e))
    (h : isPrefixWeakening e acts = true) : acts = weakActs n e := by
  funext j
  unfold isPrefixWeakening at h
  rw [List.all_eq_true] at h
  exact (coreEq_iff _ _).mp (h j (List.mem_finRange j))

/-- An admitted actual vector instantiates the home supplier to exactly its lifted occurrence. -/
theorem admitted_occurrence {n : Nat} (e : Nat) (acts : Fin n → Core (n + e)) (p : Core n)
    (h : isPrefixWeakening e acts = true) (i : Nat) : subst acts p = lifted p e i := by
  rw [isPrefixWeakening_sound e acts h]
  rfl

end V6BinderShared

/-! ## 2. The finite structured reading record -/

namespace V6Structured

open Lean (Name)
open DerivedViewSyntax V6BinderShared
open ContextualViewDAG (Table Occ Args Row Ref RefMap unroll unrollArgs evalOcc evalArgs tableValues
  evalRow)

/-- Iterated renaming lift: `liftRenN e ρ` acts as `ρ` below `e` local binders. -/
def liftRenN {n m : Nat} : (e : Nat) → (Fin n → Fin m) → Fin (n + e) → Fin (m + e)
  | 0, ρ => ρ
  | e+1, ρ => liftRen (liftRenN e ρ)

/-- Iterated lift of a finite occurrence map of the table, below `e` local binders. -/
def liftOccN {Γ : List Nat} {n m : Nat} :
    (e : Nat) → (Fin n → Occ Γ m) → Fin (n + e) → Occ Γ (m + e)
  | 0, σ => σ
  | e+1, σ => ContextualViewDAG.liftSub (liftOccN e σ)

/-- The owner telescope: universally closed ports and lets, newest last. Every domain, let type
    and let value is a component reference into the table. -/
inductive OTel (Γ : List Nat) : Nat → Type where
  | nil : OTel Γ 0
  | port {k : Nat} : OTel Γ k → BinderAttrs → Occ Γ k → OTel Γ (k+1)
  | letE {k : Nat} : OTel Γ k → Name → Bool → Occ Γ k → Occ Γ k → OTel Γ (k+1)

/-- The decision recorded for one origin: exact, or class B by a named kernel certificate applied
    to explicit actuals at the use (arity `a`). -/
inductive CertR (Γ : List Nat) (a : Nat) where
  | exact
  | classB (name : Name) (k : Nat) (actuals : Args Γ a k)

/-- One selected use, `e` binders below the owner home `n`: its source-origin and view-origin
    components, its explicit actual vector (owner declaration ↦ occurrence at the use) and the
    certificates of both origins, and its occurrence identity `oid`. Its path and local scope are
    its position in the template (listed per use by `Tmpl.uses` below). -/
structure UseR (Γ : List Nat) (n e : Nat) where
  oid : Nat
  src : Occ Γ (n + e)
  view : Occ Γ (n + e)
  acts : Args Γ (n + e) n
  srcCert : CertR Γ (n + e)
  viewCert : CertR Γ (n + e)

/-- The reading template below the owner home: the call and region organisation along the
    selected paths (ordered application fields, product regions with their binder attributes and
    domain components, genuine-let regions with name, flag, type and value components), component
    references off the paths, and the selected uses at the leaves. The index is the depth. -/
inductive Tmpl (Γ : List Nat) (n : Nat) : Nat → Type where
  | leaf {e : Nat} : Occ Γ (n + e) → Tmpl Γ n e
  | hole {e : Nat} : UseR Γ n e → Tmpl Γ n e
  | app {e : Nat} : Tmpl Γ n e → Tmpl Γ n e → Tmpl Γ n e
  | pi {e : Nat} : BinderAttrs → Occ Γ (n + e) → Tmpl Γ n (e+1) → Tmpl Γ n e
  | letE {e : Nat} : Name → Bool → Occ Γ (n + e) → Occ Γ (n + e) → Tmpl Γ n (e+1) → Tmpl Γ n e

/-- The finite structured reading: one table, one owner, one ledger node whose value is the one
    shared supplier, and the template. -/
structure SRec where
  homes : List Nat
  table : Table homes
  n : Nat
  owner : OTel homes n
  nodeName : Name
  nodeTy : Occ homes n
  sup : Occ homes n
  body : Tmpl homes n 0

/-! ### The total structural decoder -/

section Decode
variable {Γ : List Nat} (tb : Table Γ)

def ev {k : Nat} (o : Occ Γ k) : Core k := expand (unroll tb o)

def evA {k r : Nat} (a : Args Γ k r) : Fin r → Core k := fun j => expand (unrollArgs tb a j)

/-- The recovered source body: outside-hole structure and components, source origins at holes. -/
def Tmpl.src {n : Nat} : {e : Nat} → Tmpl Γ n e → Core (n + e)
  | _, .leaf o => ev tb o
  | _, .hole u => ev tb u.src
  | _, .app f a => .app (Tmpl.src f) (Tmpl.src a)
  | _, .pi x d b => .pi x (ev tb d) (Tmpl.src (n := n) b)
  | _, .letE nm nd ty v b => .letE nm nd (ev tb ty) (ev tb v) (Tmpl.src (n := n) b)

/-- The recovered view body: the same outside-hole structure, view origins at holes. -/
def Tmpl.view {n : Nat} : {e : Nat} → Tmpl Γ n e → Core (n + e)
  | _, .leaf o => ev tb o
  | _, .hole u => ev tb u.view
  | _, .app f a => .app (Tmpl.view f) (Tmpl.view a)
  | _, .pi x d b => .pi x (ev tb d) (Tmpl.view (n := n) b)
  | _, .letE nm nd ty v b => .letE nm nd (ev tb ty) (ev tb v) (Tmpl.view (n := n) b)

/-- The shared body: the supplier `p` at every use, through that use's recorded actual vector. -/
def Tmpl.shared {n : Nat} (p : Core n) : {e : Nat} → Tmpl Γ n e → Core (n + e)
  | _, .leaf o => ev tb o
  | _, .hole u => subst (evA tb u.acts) p
  | _, .app f a => .app (Tmpl.shared p f) (Tmpl.shared p a)
  | _, .pi x d b => .pi x (ev tb d) (Tmpl.shared (n := n) p b)
  | _, .letE nm nd ty v b => .letE nm nd (ev tb ty) (ev tb v) (Tmpl.shared (n := n) p b)

/-- The reading body at `H, M`: the node `M` (index `e` at depth `e`) at every use, and nowhere
    else by construction; the other components are weakened past `M`. -/
def Tmpl.reading {n : Nat} : {e : Nat} → Tmpl Γ n e → Core (n + 1 + e)
  | e, .leaf o => rename (liftRenN e Fin.succ) (ev tb o)
  | e, .hole _ => .var ⟨e, by omega⟩
  | _, .app f a => .app (Tmpl.reading f) (Tmpl.reading a)
  | e, .pi x d b => .pi x (rename (liftRenN e Fin.succ) (ev tb d)) (Tmpl.reading (n := n) b)
  | e, .letE nm nd ty v b =>
    .letE nm nd (rename (liftRenN e Fin.succ) (ev tb ty)) (rename (liftRenN e Fin.succ) (ev tb v))
      (Tmpl.reading (n := n) b)

/-- Universal closure over the owner telescope. -/
def OTel.close : {k : Nat} → OTel Γ k → Core k → Core 0
  | _, .nil, b => b
  | _, .port T x d, b => OTel.close T (.pi x (ev tb d) b)
  | _, .letE T nm nd ty v, b => OTel.close T (.letE nm nd (ev tb ty) (ev tb v) b)

end Decode

def SRec.reading (R : SRec) : Core 0 :=
  R.owner.close R.table
    (.letE R.nodeName false (ev R.table R.nodeTy) (ev R.table R.sup) (R.body.reading R.table))

def SRec.source (R : SRec) : Core 0 := R.owner.close R.table (R.body.src R.table)
def SRec.view (R : SRec) : Core 0 := R.owner.close R.table (R.body.view R.table)
def SRec.shared (R : SRec) : Core 0 := R.owner.close R.table (R.body.shared R.table (ev R.table R.sup))

/-! ### Admission: finite checks, none of them a decode or recovery equality

Reference ranks and bounds, scopes and actual-vector arities are enforced by the types: a `Ref`
names an earlier row of the table, rows refer only to earlier rows, and every variable is a `Fin`
of its scope. The checks below are the remaining finite conditions. -/

/-- Entry `j` of the vector is the variable `j + e` (a prefix weakening), from position `j0`. -/
def weakB {Γ : List Nat} {a : Nat} (e : Nat) : {r : Nat} → Args Γ a r → Nat → Bool
  | _, .nil, _ => true
  | _, .cons (.var i) rest, j => i.val == j + e && weakB e rest (j + 1)
  | _, .cons (.use _ _) _, _ => false

/-- Every actual vector is a prefix weakening (the use sees the owner's declarations unchanged). -/
def Tmpl.actsB {Γ : List Nat} {n : Nat} : {e : Nat} → Tmpl Γ n e → Bool
  | e, .hole u => weakB e u.acts 0
  | _, .leaf _ => true
  | _, .app f a => Tmpl.actsB f && Tmpl.actsB a
  | _, .pi _ _ b => Tmpl.actsB b
  | _, .letE _ _ _ _ b => Tmpl.actsB b

/-- Every let region on a selected path is a genuine (dependent) let. -/
def Tmpl.letsB {Γ : List Nat} {n : Nat} : {e : Nat} → Tmpl Γ n e → Bool
  | _, .hole _ => true
  | _, .leaf _ => true
  | _, .app f a => Tmpl.letsB f && Tmpl.letsB a
  | _, .pi _ _ b => Tmpl.letsB b
  | _, .letE _ nd _ _ b => !nd && Tmpl.letsB b

def OTel.admitB {Γ : List Nat} : {k : Nat} → OTel Γ k → Bool
  | _, .nil => true
  | _, .port T _ _ => OTel.admitB T
  | _, .letE T _ nd _ _ => !nd && OTel.admitB T

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- The selection underlying a template; each hole carries its use's occurrence identity. -/
def Tmpl.erase {Γ : List Nat} {n : Nat} : {e : Nat} → Tmpl Γ n e → BSel
  | _, .leaf _ => .none
  | _, .hole u => .hole u.oid
  | _, .app f a => .app (Tmpl.erase f) (Tmpl.erase a)
  | _, .pi _ _ b => .pi (Tmpl.erase b)
  | _, .letE _ _ _ _ b => .letE (Tmpl.erase b)

/-! ### Per-use listing: path, local scope and the use record -/

/-- One step of a selection path: function or argument field of a call, body of a product region,
    body of a let region. -/
inductive Step where
  | fn | arg | piBody | letBody
  deriving Repr, DecidableEq

/-- Follow a path in a selection. -/
def followSel : BSel → List Step → Option BSel
  | s, [] => some s
  | .app f _, .fn :: p => followSel f p
  | .app _ a, .arg :: p => followSel a p
  | .pi b, .piBody :: p => followSel b p
  | .letE b, .letBody :: p => followSel b p
  | _, _ :: _ => none

/-- A local binder crossed on the way to a use: its depth below the owner home and its component
    references at its own scope. -/
inductive LB (Γ : List Nat) (n : Nat) where
  | pi (e : Nat) (x : BinderAttrs) (dom : Occ Γ (n + e))
  | letE (e : Nat) (name : Name) (nondep : Bool) (ty val : Occ Γ (n + e))

/-- A use as listed: its depth, its path from the owner home, the local binders on that path
    (outermost first) and the use record itself. -/
structure UseEntry (Γ : List Nat) (n : Nat) where
  e : Nat
  path : List Step
  scope : List (LB Γ n)
  use : UseR Γ n e

def Tmpl.uses {Γ : List Nat} {n : Nat} : {e : Nat} → Tmpl Γ n e → List (UseEntry Γ n)
  | e, .hole u => [⟨e, [], [], u⟩]
  | _, .leaf _ => []
  | _, .app f a =>
    (Tmpl.uses f).map (fun y => { y with path := .fn :: y.path }) ++
      (Tmpl.uses a).map (fun y => { y with path := .arg :: y.path })
  | e, .pi x d b =>
    (Tmpl.uses b).map (fun y => { y with path := .piBody :: y.path, scope := .pi e x d :: y.scope })
  | e, .letE nm nd ty v b =>
    (Tmpl.uses b).map (fun y =>
      { y with path := .letBody :: y.path, scope := .letE e nm nd ty v :: y.scope })

def Tmpl.oids {Γ : List Nat} {n e : Nat} (t : Tmpl Γ n e) : List Nat := t.uses.map (·.use.oid)

/-- Admission of the template: prefix-weakening actual vectors, genuine lets on selected paths and
    distinct occurrence identities. -/
def Tmpl.admitB {Γ : List Nat} {n e : Nat} (t : Tmpl Γ n e) : Bool :=
  t.actsB && t.letsB && nodupB t.oids

def SRec.admitB (R : SRec) : Bool := R.owner.admitB && R.body.admitB

theorem Tmpl.uses_follow {Γ : List Nat} {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e),
    ∀ y ∈ t.uses, followSel t.erase y.path = some (BSel.hole y.use.oid) := by
  intro e t
  induction t with
  | leaf o => intro y hy; simp [Tmpl.uses] at hy
  | hole u => intro y hy; simp only [Tmpl.uses, List.mem_singleton] at hy; subst hy; rfl
  | app f a ihf iha =>
    intro y hy
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact ihf z hz
    · exact iha z hz
  | pi x d b ih =>
    intro y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ih z hz
  | letE nm nd ty v b ih =>
    intro y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ih z hz

theorem Tmpl.uses_depth {Γ : List Nat} {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e),
    ∀ y ∈ t.uses, y.e = e + y.scope.length ∧ y.scope.length = (y.path.filter
      (fun st => st == .piBody || st == .letBody)).length := by
  intro e t
  induction t with
  | leaf o => intro y hy; simp [Tmpl.uses] at hy
  | hole u => intro y hy; simp only [Tmpl.uses, List.mem_singleton] at hy; subst hy; simp
  | app f a ihf iha =>
    intro y hy
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · have := ihf z hz; simpa using this
    · have := iha z hz; simpa using this
  | pi x d b ih =>
    intro y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := ih z hz
    simp only [List.length_cons, List.filter_cons]
    simp at this ⊢
    omega
  | letE nm nd ty v b ih =>
    intro y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := ih z hz
    simp only [List.length_cons, List.filter_cons]
    simp at this ⊢
    omega

/-- Selection paths to holes are prefix-free: a hole is a leaf of the selection. -/
theorem followSel_prefix_free : ∀ (s : BSel) (p q : List Step) (i : Nat) (s' : BSel),
    followSel s p = some (BSel.hole i) → followSel s (p ++ q) = some s' → q = [] := by
  intro s p
  induction p generalizing s with
  | nil =>
    intro q i s' h1 h2
    simp only [followSel, Option.some.injEq] at h1
    subst h1
    cases q with
    | nil => rfl
    | cons st q => simp [followSel] at h2
  | cons st p ih =>
    intro q i s' h1 h2
    cases s <;> cases st <;> simp only [followSel, List.cons_append, reduceCtorEq] at h1 h2
    all_goals first | exact ih _ q i s' h1 h2

theorem weakB_get {Γ : List Nat} {A : Nat} (e : Nat) :
    ∀ {r : Nat} (a : Args Γ A r) (j0 : Nat), weakB e a j0 = true →
      ∀ j : Fin r, ∃ i : Fin A, a.get j = .var i ∧ i.val = j0 + j.val + e
  | _, .nil, _, _, j => Fin.elim0 j
  | _, .cons (.var i) rest, j0, h, j => by
    simp only [weakB, Bool.and_eq_true, beq_iff_eq] at h
    refine Fin.cases ⟨i, rfl, by simp [h.1]⟩ (fun j' => ?_) j
    obtain ⟨i', hi', hv⟩ := weakB_get e rest (j0 + 1) h.2 j'
    exact ⟨i', hi', by simp only [Fin.val_succ]; omega⟩
  | _, .cons (.use _ _) _, _, h, _ => by simp [weakB] at h

/-- An admitted actual vector denotes exactly the prefix weakening `weakActs n e`. -/
theorem evA_weak {Γ : List Nat} (tb : Table Γ) {n e : Nat} (a : Args Γ (n + e) n)
    (h : weakB e a 0 = true) : evA tb a = weakActs n e := by
  funext j
  obtain ⟨i, hi, hv⟩ := weakB_get e a 0 h j
  simp only [evA, unrollArgs, ContextualViewDAG.evalArgs_get, hi, evalOcc, weakActs]
  show Term.var i = Term.var (j.addNat e)
  congr 1
  exact Fin.ext (by simp only [Fin.val_addNat]; omega)

/-! ### Structure of every admitted record -/

section Structure
variable {Γ : List Nat} (tb : Table Γ)

theorem Tmpl.shape_src {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), Shape (t.src tb) t.erase := by
  intro e t
  induction t with
  | leaf o => trivial
  | hole u => trivial
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | pi x d b ih => exact ih
  | letE nm nd ty v b ih => exact ih

/-- Source and view agree outside the holes, for every record (admitted or not). -/
theorem Tmpl.agree_src_view {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e),
    Agree (t.src tb) (t.view tb) t.erase := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => trivial
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | pi x d b ih => exact ⟨rfl, rfl, ih⟩
  | letE nm nd ty v b ih => exact ⟨rfl, rfl, rfl, rfl, ih⟩

/-- Common-supplier incidence: in an admitted record the shared body is the source body with every
    selected position refilled by the one supplier at its lifted actuals. -/
theorem Tmpl.shared_fill {n : Nat} (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e), t.actsB = true →
    t.shared tb p = fillD e (t.src tb) t.erase (lifted p) := by
  intro e t
  induction t with
  | leaf o => intro _; rfl
  | hole u =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.shared, Tmpl.erase, fillD, lifted, evA_weak tb u.acts h]
  | app f a ihf iha =>
    intro h
    simp only [Tmpl.actsB, Bool.and_eq_true] at h
    simp only [Tmpl.shared, Tmpl.src, Tmpl.erase, fillD, ihf h.1, iha h.2]
  | pi x d b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.shared, Tmpl.src, Tmpl.erase, fillD, ih h]
  | letE nm nd ty v b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.shared, Tmpl.src, Tmpl.erase, fillD, ih h]

/-- Incidence, restated with the selection predicates `FitsD` and `Agree`. -/
theorem Tmpl.incidence {n : Nat} (p : Core n) {e : Nat} (t : Tmpl Γ n e) (h : t.actsB = true) :
    FitsD e (t.shared tb p) t.erase (lifted p) ∧ Agree (t.src tb) (t.shared tb p) t.erase := by
  rw [t.shared_fill tb p h]
  exact ⟨fillD_fits _ e _ _ (t.shape_src tb), agree_fillD _ e _ _ (t.shape_src tb)⟩

theorem liftRenN_zero {n m : Nat} (ρ : Fin n → Fin m) : liftRenN 0 ρ = ρ := rfl

theorem liftSubN_liftRenN_succ {n : Nat} (p : Core n) : ∀ e : Nat,
    (fun i => liftSubN e (Fin.cases p Term.var : Fin (n+1) → Core n) (liftRenN e Fin.succ i)) =
      (Term.var : Fin (n + e) → Core (n + e)) := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih =>
    have h := liftSub_liftRen (liftRenN e Fin.succ) (liftSubN e (Fin.cases p Term.var : Fin (n+1) → Core n))
    show (fun i => liftSub (liftSubN e (Fin.cases p Term.var)) (liftRen (liftRenN e Fin.succ) i)) = _
    rw [h, ih]
    exact liftSub_var

/-- The reading's ledger node, zeta-expanded, gives the shared body (admitted records). -/
theorem Tmpl.reading_zeta {n : Nat} (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e), t.actsB = true →
    subst (liftSubN e (Fin.cases p Term.var)) (t.reading tb) = t.shared tb p := by
  intro e t
  have hw : ∀ (e : Nat) (x : Core (n + e)),
      subst (liftSubN e (Fin.cases p Term.var)) (rename (liftRenN e Fin.succ) x) = x := by
    intro e x
    rw [subst_rename, liftSubN_liftRenN_succ p e]
    exact subst_id x
  induction t with
  | leaf o => intro _; exact hw _ _
  | hole u =>
    rename_i e
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.reading, Tmpl.shared, subst, evA_weak tb u.acts h]
    have hk : (⟨e, by omega⟩ : Fin (n + 1 + e)) = (0 : Fin (n+1)).addNat e :=
      Fin.ext (by simp only [Fin.val_addNat, Fin.val_zero]; omega)
    rw [hk, liftSubN_addNat, rename_eq_subst]
    rfl
  | app f a ihf iha =>
    intro h
    simp only [Tmpl.actsB, Bool.and_eq_true] at h
    simp only [Tmpl.reading, Tmpl.shared, subst, ihf h.1, iha h.2]
  | pi x d b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.reading, Tmpl.shared, subst]
    rw [hw, ← liftSubN_succ, ih h]
  | letE nm nd ty v b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.reading, Tmpl.shared, subst]
    rw [hw, hw, ← liftSubN_succ, ih h]

end Structure

end V6Structured

/-! ## 3. A structural construction for every member of the profile -/

namespace V6Structured

open Lean (Name)
open DerivedViewSyntax V6BinderShared
open ContextualViewDAG (Table Occ Args Row Ref RefMap unroll unrollArgs evalOcc evalArgs tableValues
  evalRow)
open ContextualDAGCoverage (Extension rootOfRow unroll_rootOfRow)

/-! ### Rows for a Core term, with a general unrolling theorem

`buildRows` adds one row per constructor layer through `ContextualDAGCoverage.Extension` (`add`,
`trans`, `map`, `rootOfRow`). `buildRows_unroll` is its table-unrolling equation, proved for every
Core term by structural induction, so no witness-specific unrolling premise is assumed. -/

def buildRows : {k : Nat} → Core k → {Γ : List Nat} → (table : Table Γ) →
    (ex : Extension table) × Occ ex.homes k
  | _, .var i, _, table => ⟨Extension.refl table, .var i⟩
  | _, .sort u, _, table => ⟨Extension.add table (.sort u), rootOfRow⟩
  | _, .const c ls, _, table => ⟨Extension.add table (.const c ls), rootOfRow⟩
  | _, .lit l, _, table => ⟨Extension.add table (.lit l), rootOfRow⟩
  | _, .app f a, _, table =>
    let r1 := buildRows f table
    let r2 := buildRows a r1.1.table
    ⟨(r1.1.trans r2.1).trans (Extension.add r2.1.table (.app (r2.1.map r1.2) r2.2)), rootOfRow⟩
  | _, .lam x d body, _, table =>
    let r1 := buildRows d table
    let r2 := buildRows body r1.1.table
    ⟨(r1.1.trans r2.1).trans (Extension.add r2.1.table (.lam x (r2.1.map r1.2) r2.2)), rootOfRow⟩
  | _, .pi x d body, _, table =>
    let r1 := buildRows d table
    let r2 := buildRows body r1.1.table
    ⟨(r1.1.trans r2.1).trans (Extension.add r2.1.table (.pi x (r2.1.map r1.2) r2.2)), rootOfRow⟩
  | _, .letE nm nd ty v body, _, table =>
    let r1 := buildRows ty table
    let r2 := buildRows v r1.1.table
    let r3 := buildRows body r2.1.table
    ⟨((r1.1.trans r2.1).trans r3.1).trans
      (Extension.add r3.1.table (.letE nm nd (r3.1.map (r2.1.map r1.2)) (r3.1.map r2.2) r3.2)),
      rootOfRow⟩
  | _, .proj nm i v, _, table =>
    let r1 := buildRows v table
    ⟨r1.1.trans (Extension.add r1.1.table (.proj nm i r1.2)), rootOfRow⟩
  | _, .unique h .., _, _ => nomatch h
  | _, .inst h .., _, _ => nomatch h

theorem buildRows_unroll : ∀ {k : Nat} (t : Core k) {Γ : List Nat} (table : Table Γ),
    unroll (buildRows t table).1.table (buildRows t table).2 = coreToView t
  | _, .var i, _, table => rfl
  | _, .sort u, _, table => unroll_rootOfRow table (.sort u)
  | _, .const c ls, _, table => unroll_rootOfRow table (.const c ls)
  | _, .lit l, _, table => unroll_rootOfRow table (.lit l)
  | _, .app f a, _, table => by
    have h := unroll_rootOfRow (buildRows a (buildRows f table).1.table).1.table
      (.app ((buildRows a (buildRows f table).1.table).1.map (buildRows f table).2)
        (buildRows a (buildRows f table).1.table).2)
    refine h.trans ?_
    show Term.app (unroll _ (Extension.map _ _)) (unroll _ _) = _
    rw [Extension.unroll_map, buildRows_unroll f, buildRows_unroll a]
    rfl
  | _, .lam x d body, _, table => by
    have h := unroll_rootOfRow (buildRows body (buildRows d table).1.table).1.table
      (.lam x ((buildRows body (buildRows d table).1.table).1.map (buildRows d table).2)
        (buildRows body (buildRows d table).1.table).2)
    refine h.trans ?_
    show Term.lam x (unroll _ (Extension.map _ _)) (unroll _ _) = _
    rw [Extension.unroll_map, buildRows_unroll d, buildRows_unroll body]
    rfl
  | _, .pi x d body, _, table => by
    have h := unroll_rootOfRow (buildRows body (buildRows d table).1.table).1.table
      (.pi x ((buildRows body (buildRows d table).1.table).1.map (buildRows d table).2)
        (buildRows body (buildRows d table).1.table).2)
    refine h.trans ?_
    show Term.pi x (unroll _ (Extension.map _ _)) (unroll _ _) = _
    rw [Extension.unroll_map, buildRows_unroll d, buildRows_unroll body]
    rfl
  | _, .letE nm nd ty v body, _, table => by
    have h := unroll_rootOfRow
      (buildRows body (buildRows v (buildRows ty table).1.table).1.table).1.table
      (.letE nm nd
        ((buildRows body (buildRows v (buildRows ty table).1.table).1.table).1.map
          ((buildRows v (buildRows ty table).1.table).1.map (buildRows ty table).2))
        ((buildRows body (buildRows v (buildRows ty table).1.table).1.table).1.map
          (buildRows v (buildRows ty table).1.table).2)
        (buildRows body (buildRows v (buildRows ty table).1.table).1.table).2)
    refine h.trans ?_
    show Term.letE nm nd (unroll _ (Extension.map _ (Extension.map _ _)))
      (unroll _ (Extension.map _ _)) (unroll _ _) = _
    rw [Extension.unroll_map, Extension.unroll_map, Extension.unroll_map, buildRows_unroll ty,
      buildRows_unroll v, buildRows_unroll body]
    rfl
  | _, .proj nm i v, _, table => by
    have h := unroll_rootOfRow (buildRows v table).1.table (.proj nm i (buildRows v table).2)
    refine h.trans ?_
    show Term.proj nm i (unroll _ _) = _
    rw [buildRows_unroll v]
    rfl
  | _, .unique h .., _, _ => nomatch h
  | _, .inst h .., _, _ => nomatch h

theorem buildRows_ev {k : Nat} (t : Core k) {Γ : List Nat} (table : Table Γ) :
    ev (buildRows t table).1.table (buildRows t table).2 = t := by
  simp only [ev, buildRows_unroll, expand_coreToView]

theorem ev_map {Γ : List Nat} {tb : Table Γ} (ex : Extension tb) {k : Nat} (o : Occ Γ k) :
    ev ex.table (ex.map o) = ev tb o := by
  simp only [ev, Extension.unroll_map]

theorem evA_cons_zero {Γ : List Nat} (tb : Table Γ) {k r : Nat} (o : Occ Γ k) (rest : Args Γ k r) :
    evA tb (.cons o rest) 0 = ev tb o := rfl

theorem evA_cons_succ {Γ : List Nat} (tb : Table Γ) {k r : Nat} (o : Occ Γ k) (rest : Args Γ k r)
    (j : Fin r) : evA tb (.cons o rest) j.succ = evA tb rest j := rfl

/-- Rows for a finite vector of Core actuals. -/
def buildArgs {a : Nat} : {k : Nat} → (Fin k → Core a) → {Γ : List Nat} → (tb : Table Γ) →
    (ex : Extension tb) × Args ex.homes a k
  | 0, _, _, tb => ⟨Extension.refl tb, .nil⟩
  | _+1, f, _, tb =>
    let r1 := buildRows (f 0) tb
    let r2 := buildArgs (fun i => f i.succ) r1.1.table
    ⟨r1.1.trans r2.1, .cons (r2.1.map r1.2) r2.2⟩

theorem buildArgs_evA {a : Nat} : ∀ {k : Nat} (f : Fin k → Core a) {Γ : List Nat} (tb : Table Γ),
    evA (buildArgs f tb).1.table (buildArgs f tb).2 = f
  | 0, f, _, tb => funext (fun j => Fin.elim0 j)
  | k+1, f, _, tb => by
    funext j
    have ih := buildArgs_evA (fun i => f i.succ) (buildRows (f 0) tb).1.table
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [buildArgs, Extension.trans, evA_cons_zero, ev_map, buildRows_ev]
    · simp only [buildArgs, Extension.trans, evA_cons_succ, ih]

/-! ### Certificates: a Core-level specification and its finite record -/

/-- A certificate as specified at the Core level: exact, or a named kernel certificate with its
    actuals at the use. -/
inductive CertC (a : Nat) where
  | exact
  | classB (name : Name) (k : Nat) (actuals : Fin k → Core a)

/-- Certificates of the source and the view origin of every use, by depth and occurrence
    identity. -/
abbrev CertSpec (n : Nat) := (e : Nat) → Nat → CertC (n + e) × CertC (n + e)

def CertR.dec {Γ : List Nat} (tb : Table Γ) {a : Nat} : CertR Γ a → CertC a
  | .exact => .exact
  | .classB nm k acts => .classB nm k (evA tb acts)

def encCert {a : Nat} : CertC a → {Γ : List Nat} → (tb : Table Γ) →
    (ex : Extension tb) × CertR ex.homes a
  | .exact, _, tb => ⟨Extension.refl tb, .exact⟩
  | .classB nm k f, _, tb => ⟨(buildArgs f tb).1, .classB nm k (buildArgs f tb).2⟩

theorem encCert_dec {a : Nat} (c : CertC a) {Γ : List Nat} (tb : Table Γ) :
    (encCert c tb).2.dec (encCert c tb).1.table = c := by
  cases c with
  | exact => rfl
  | classB nm k f => simp only [encCert, CertR.dec, buildArgs_evA]

/-! ### Prefix-weakening actual vectors -/

def weakArgs {Γ : List Nat} (n e : Nat) : Args Γ (n + e) n := Args.ofFn (fun j => Occ.var (j.addNat e))

theorem evA_weakArgs {Γ : List Nat} (tb : Table Γ) (n e : Nat) :
    evA tb (weakArgs n e) = weakActs n e := by
  funext j
  simp only [evA, unrollArgs, weakArgs, ContextualViewDAG.evalArgs_ofFn, evalOcc, weakActs]
  rfl

theorem weakB_of_get {Γ : List Nat} {A : Nat} (e : Nat) : ∀ {r : Nat} (a : Args Γ A r) (j0 : Nat),
    (∀ j : Fin r, ∃ i : Fin A, a.get j = .var i ∧ i.val = j0 + j.val + e) → weakB e a j0 = true
  | _, .nil, _, _ => rfl
  | _, .cons o rest, j0, h => by
    obtain ⟨i, hi, hv⟩ := h 0
    have hi' : o = .var i := hi
    subst hi'
    simp only [weakB, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simpa using hv, weakB_of_get e rest (j0 + 1) (fun j => ?_)⟩
    obtain ⟨i', hi', hv'⟩ := h j.succ
    exact ⟨i', hi', by simp only [Fin.val_succ] at hv'; omega⟩

theorem weakB_weakArgs {Γ : List Nat} (n e : Nat) : weakB e (weakArgs (Γ := Γ) n e) 0 = true := by
  apply weakB_of_get
  intro j
  refine ⟨j.addNat e, ?_, by simp⟩
  simp only [weakArgs, ContextualViewDAG.Args.get_ofFn]

/-! ### Moving a record's references into a larger table -/

section MapR
variable {Γ Δ : List Nat} (f : RefMap Γ Δ)

def CertR.mapR {a : Nat} : CertR Γ a → CertR Δ a
  | .exact => .exact
  | .classB nm k acts => .classB nm k (ContextualViewDAG.mapArgs f acts)

def UseR.mapR {n e : Nat} (u : UseR Γ n e) : UseR Δ n e :=
  ⟨u.oid, ContextualViewDAG.mapRefs f u.src, ContextualViewDAG.mapRefs f u.view,
    ContextualViewDAG.mapArgs f u.acts, u.srcCert.mapR f, u.viewCert.mapR f⟩

def Tmpl.mapR {n : Nat} : {e : Nat} → Tmpl Γ n e → Tmpl Δ n e
  | _, .leaf o => .leaf (ContextualViewDAG.mapRefs f o)
  | _, .hole u => .hole (u.mapR f)
  | _, .app g a => .app (Tmpl.mapR g) (Tmpl.mapR a)
  | _, .pi x d b => .pi x (ContextualViewDAG.mapRefs f d) (Tmpl.mapR b)
  | _, .letE nm nd ty v b =>
    .letE nm nd (ContextualViewDAG.mapRefs f ty) (ContextualViewDAG.mapRefs f v) (Tmpl.mapR b)

def OTel.mapR : {k : Nat} → OTel Γ k → OTel Δ k
  | _, .nil => .nil
  | _, .port T x d => .port (OTel.mapR T) x (ContextualViewDAG.mapRefs f d)
  | _, .letE T nm nd ty v =>
    .letE (OTel.mapR T) nm nd (ContextualViewDAG.mapRefs f ty) (ContextualViewDAG.mapRefs f v)

variable {tb : Table Γ} {tb' : Table Δ}
  (hf : ∀ {r : Nat} (ref : Ref Γ r), tableValues tb' (f ref) = tableValues tb ref)
include hf

theorem ev_mapR {k : Nat} (o : Occ Γ k) : ev tb' (ContextualViewDAG.mapRefs f o) = ev tb o := by
  simp only [ev, unroll]
  rw [ContextualViewDAG.eval_mapRefs f (tableValues tb) (tableValues tb') @hf o]

theorem evA_mapR {k r : Nat} (a : Args Γ k r) : evA tb' (ContextualViewDAG.mapArgs f a) = evA tb a := by
  funext j
  simp only [evA, unrollArgs]
  rw [ContextualViewDAG.eval_mapArgs f (tableValues tb) (tableValues tb') @hf a]

theorem CertR.dec_mapR {a : Nat} (c : CertR Γ a) : (c.mapR f).dec tb' = c.dec tb := by
  cases c with
  | exact => rfl
  | classB nm k acts => simp only [CertR.mapR, CertR.dec, evA_mapR f hf]

theorem Tmpl.src_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).src tb' = t.src tb := by
  intro e t
  induction t with
  | leaf o => exact ev_mapR f hf o
  | hole u => exact ev_mapR f hf u.src
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.src, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.src, ih, ev_mapR f hf]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.src, ih, ev_mapR f hf]

theorem Tmpl.view_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).view tb' = t.view tb := by
  intro e t
  induction t with
  | leaf o => exact ev_mapR f hf o
  | hole u => exact ev_mapR f hf u.view
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.view, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.view, ih, ev_mapR f hf]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.view, ih, ev_mapR f hf]

theorem Tmpl.shared_mapR {n : Nat} (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.mapR f).shared tb' p = t.shared tb p := by
  intro e t
  induction t with
  | leaf o => exact ev_mapR f hf o
  | hole u => simp only [Tmpl.mapR, UseR.mapR, Tmpl.shared, evA_mapR f hf]
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.shared, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.shared, ih, ev_mapR f hf]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.shared, ih, ev_mapR f hf]

theorem Tmpl.reading_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.mapR f).reading tb' = t.reading tb := by
  intro e t
  induction t with
  | leaf o => simp only [Tmpl.mapR, Tmpl.reading, ev_mapR f hf]
  | hole u => rfl
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.reading, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.reading, ih, ev_mapR f hf]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.reading, ih, ev_mapR f hf]

theorem OTel.close_mapR : ∀ {k : Nat} (T : OTel Γ k) (b : Core k),
    (T.mapR f).close tb' b = T.close tb b := by
  intro k T
  induction T with
  | nil => intro b; rfl
  | port T x d ih => intro b; simp only [OTel.mapR, OTel.close, ih, ev_mapR f hf]
  | letE T nm nd ty v ih => intro b; simp only [OTel.mapR, OTel.close, ih, ev_mapR f hf]

omit hf in
theorem weakB_mapR {A : Nat} (e : Nat) : ∀ {r : Nat} (a : Args Γ A r) (j : Nat),
    weakB e (ContextualViewDAG.mapArgs f a) j = weakB e a j
  | _, .nil, _ => rfl
  | _, .cons (.var i) rest, j => by
    simp only [ContextualViewDAG.mapArgs, ContextualViewDAG.mapRefs, weakB, weakB_mapR e rest]
  | _, .cons (.use _ _) _, _ => rfl

omit hf in
theorem Tmpl.erase_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).erase = t.erase := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.erase, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.erase, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.erase, ih]

omit hf in
theorem Tmpl.actsB_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).actsB = t.actsB := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => simp only [Tmpl.mapR, UseR.mapR, Tmpl.actsB, weakB_mapR]
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.actsB, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.actsB, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.actsB, ih]

omit hf in
theorem Tmpl.letsB_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).letsB = t.letsB := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha => simp only [Tmpl.mapR, Tmpl.letsB, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapR, Tmpl.letsB, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapR, Tmpl.letsB, ih]

omit hf in
theorem Tmpl.oids_mapR {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapR f).oids = t.oids := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha =>
    simp only [Tmpl.oids] at ihg iha ⊢
    simp only [Tmpl.mapR, Tmpl.uses, List.map_append, List.map_map, Function.comp_def, ihg, iha]
  | pi x d b ih =>
    simp only [Tmpl.oids] at ih ⊢
    simp only [Tmpl.mapR, Tmpl.uses, List.map_map, Function.comp_def, ih]
  | letE nm nd ty v b ih =>
    simp only [Tmpl.oids] at ih ⊢
    simp only [Tmpl.mapR, Tmpl.uses, List.map_map, Function.comp_def, ih]

omit hf in
theorem OTel.admitB_mapR : ∀ {k : Nat} (T : OTel Γ k), (T.mapR f).admitB = T.admitB := by
  intro k T
  induction T with
  | nil => rfl
  | port T x d ih => simp only [OTel.mapR, OTel.admitB, ih]
  | letE T nm nd ty v ih => simp only [OTel.mapR, OTel.admitB, ih]

end MapR

/-! ### Per-use exactness along a selection -/

/-- A predicate on every use, paired with the subterms of two terms at that use's position. The
    two terms must have the template's call and region constructors along every selected path. -/
def Tmpl.PerUse {Γ : List Nat} {n : Nat} (Q : (e : Nat) → UseR Γ n e → Core (n + e) → Core (n + e) → Prop) :
    {e : Nat} → Tmpl Γ n e → Core (n + e) → Core (n + e) → Prop
  | e, .hole u, X, Y => Q e u X Y
  | _, .leaf _, _, _ => True
  | _, .app f a, X, Y =>
    match X, Y with
    | .app Xf Xa, .app Yf Ya => Tmpl.PerUse Q f Xf Yf ∧ Tmpl.PerUse Q a Xa Ya
    | _, _ => False
  | _, .pi _ _ b, X, Y =>
    match X, Y with
    | .pi _ _ Xb, .pi _ _ Yb => Tmpl.PerUse Q b Xb Yb
    | _, _ => False
  | _, .letE _ _ _ _ b, X, Y =>
    match X, Y with
    | .letE _ _ _ _ Xb, .letE _ _ _ _ Yb => Tmpl.PerUse Q b Xb Yb
    | _, _ => False

/-- A use is exact against source subterm `X` and view subterm `Y`: its source-origin and
    view-origin components denote them, its actual vector denotes the prefix weakening, and its
    two certificates denote the specified ones (actuals included). -/
def UseExact {Γ : List Nat} (tb : Table Γ) {n : Nat} (cs : CertSpec n) (e : Nat) (u : UseR Γ n e)
    (X Y : Core (n + e)) : Prop :=
  ev tb u.src = X ∧ ev tb u.view = Y ∧ evA tb u.acts = weakActs n e ∧
    u.srcCert.dec tb = (cs e u.oid).1 ∧ u.viewCert.dec tb = (cs e u.oid).2

theorem Tmpl.perUse_mapR {Γ Δ : List Nat} (f : RefMap Γ Δ) {n : Nat}
    {Q : (e : Nat) → UseR Γ n e → Core (n + e) → Core (n + e) → Prop}
    {Q' : (e : Nat) → UseR Δ n e → Core (n + e) → Core (n + e) → Prop}
    (hQ : ∀ e u X Y, Q e u X Y → Q' e (u.mapR f) X Y) :
    ∀ {e : Nat} (t : Tmpl Γ n e) (X Y : Core (n + e)), t.PerUse Q X Y → (t.mapR f).PerUse Q' X Y := by
  intro e t
  induction t with
  | leaf o => intro X Y _; trivial
  | hole u => intro X Y h; exact hQ _ u X Y h
  | app g a ihg iha =>
    intro X Y h
    cases X <;> cases Y <;> simp only [Tmpl.PerUse, Tmpl.mapR] at h ⊢
    exact ⟨ihg _ _ h.1, iha _ _ h.2⟩
  | pi x d b ih =>
    intro X Y h
    cases X <;> cases Y <;> simp only [Tmpl.PerUse, Tmpl.mapR] at h ⊢
    exact ih _ _ h
  | letE nm nd ty v b ih =>
    intro X Y h
    cases X <;> cases Y <;> simp only [Tmpl.PerUse, Tmpl.mapR] at h ⊢
    exact ih _ _ h

theorem useExact_mapR {Γ Δ : List Nat} (f : RefMap Γ Δ) {tb : Table Γ} {tb' : Table Δ}
    (hf : ∀ {r : Nat} (ref : Ref Γ r), tableValues tb' (f ref) = tableValues tb ref)
    {n : Nat} (cs : CertSpec n) (e : Nat) (u : UseR Γ n e) (X Y : Core (n + e)) :
    UseExact tb cs e u X Y → UseExact tb' cs e (u.mapR f) X Y := by
  intro ⟨h1, h2, h3, h4, h5⟩
  exact ⟨(ev_mapR f hf u.src).trans h1, (ev_mapR f hf u.view).trans h2,
    (evA_mapR f hf u.acts).trans h3, (CertR.dec_mapR f hf u.srcCert).trans h4,
    (CertR.dec_mapR f hf u.viewCert).trans h5⟩

/-! ### The template encoder -/

/-- Lets on the selected paths of `t` are genuine. -/
def genuineB {k : Nat} (t : Core k) (s : BSel) : Bool :=
  match s with
  | .none => true
  | .hole _ => true
  | .app sf sa =>
    match t with
    | .app f a => genuineB f sf && genuineB a sa
    | _ => true
  | .pi sb =>
    match t with
    | .pi _ _ b => genuineB b sb
    | _ => true
  | .letE sb =>
    match t with
    | .letE _ nd _ _ b => !nd && genuineB b sb
    | _ => true
termination_by structural s

/-- The hole labels of a selection, in path order. -/
def selLabels : BSel → List Nat
  | .none => []
  | .hole i => [i]
  | .app sf sa => selLabels sf ++ selLabels sa
  | .pi sb => selLabels sb
  | .letE sb => selLabels sb

/-- The template of a member body at depth `e`: rows for everything off the selected paths, the
    call and region organisation along them, and at every hole the source origin, the view origin,
    the prefix-weakening actual vector and the two certificates. The view gives the outside-hole
    fields; `Agree` makes them the source's too. -/
def encT {n : Nat} (cs : CertSpec n) (e : Nat) (V T : Core (n + e)) (s : BSel) {Γ : List Nat}
    (tb : Table Γ) : (ex : Extension tb) × Tmpl ex.homes n e :=
  match s with
  | .none => ⟨(buildRows V tb).1, .leaf (buildRows V tb).2⟩
  | .hole i =>
    let r1 := buildRows T tb
    let r2 := buildRows V r1.1.table
    let r3 := encCert (cs e i).1 r2.1.table
    let r4 := encCert (cs e i).2 r3.1.table
    ⟨((r1.1.trans r2.1).trans r3.1).trans r4.1,
      .hole { oid := i, src := r4.1.map (r3.1.map (r2.1.map r1.2)), view := r4.1.map (r3.1.map r2.2),
              acts := weakArgs n e, srcCert := r3.2.mapR r4.1.refs, viewCert := r4.2 }⟩
  | .app sf sa =>
    match V, T with
    | .app Vf Va, .app Tf Ta =>
      let r1 := encT cs e Vf Tf sf tb
      let r2 := encT cs e Va Ta sa r1.1.table
      ⟨r1.1.trans r2.1, .app (r1.2.mapR r2.1.refs) r2.2⟩
    | _, _ => ⟨(buildRows V tb).1, .leaf (buildRows V tb).2⟩
  | .pi sb =>
    match V, T with
    | .pi x d Vb, .pi _ _ Tb =>
      let r1 := buildRows d tb
      let r2 := encT cs (e+1) Vb Tb sb r1.1.table
      ⟨r1.1.trans r2.1, .pi x (r2.1.map r1.2) r2.2⟩
    | _, _ => ⟨(buildRows V tb).1, .leaf (buildRows V tb).2⟩
  | .letE sb =>
    match V, T with
    | .letE nm nd ty v Vb, .letE _ _ _ _ Tb =>
      let r1 := buildRows ty tb
      let r2 := buildRows v r1.1.table
      let r3 := encT cs (e+1) Vb Tb sb r2.1.table
      ⟨(r1.1.trans r2.1).trans r3.1, .letE nm nd (r3.1.map (r2.1.map r1.2)) (r3.1.map r2.2) r3.2⟩
    | _, _ => ⟨(buildRows V tb).1, .leaf (buildRows V tb).2⟩
termination_by structural s

/-- Everything the template encoder guarantees. -/
def EncOK {n : Nat} (cs : CertSpec n) (e : Nat) (V T : Core (n + e)) (s : BSel) {Γ : List Nat}
    {tb : Table Γ} (R : (ex : Extension tb) × Tmpl ex.homes n e) : Prop :=
  R.2.src R.1.table = T ∧ R.2.view R.1.table = V ∧ R.2.erase = s ∧ R.2.actsB = true ∧
    R.2.letsB = genuineB V s ∧ R.2.oids = selLabels s ∧ R.2.PerUse (UseExact R.1.table cs) T V

theorem encT_exact {n : Nat} (cs : CertSpec n) (s : BSel) :
    ∀ (e : Nat) (V T : Core (n + e)) {Γ : List Nat} (tb : Table Γ),
      Shape V s → Agree V T s → EncOK cs e V T s (encT cs e V T s tb) := by
  induction s with
  | none =>
    intro e V T Γ tb _ hA
    simp only [Agree] at hA
    subst hA
    exact ⟨buildRows_ev _ _, buildRows_ev _ _, rfl, rfl, rfl, rfl, trivial⟩
  | hole i =>
    intro e V T Γ tb _ _
    have hs : ev ((buildRows V (buildRows T tb).1.table).1.table) ((buildRows V (buildRows T tb).1.table).1.map (buildRows T tb).2) = T := by
      rw [ev_map, buildRows_ev]
    refine ⟨?_, ?_, rfl, weakB_weakArgs n e, rfl, rfl, ?_⟩
    · simp only [encT, Tmpl.src, Extension.trans, ev_map, buildRows_ev]
    · simp only [encT, Tmpl.view, Extension.trans, ev_map, buildRows_ev]
    · simp only [encT, Tmpl.PerUse, UseExact, Extension.trans, ev_map, buildRows_ev, evA_weakArgs,
        true_and]
      refine ⟨?_, ?_⟩
      · rw [CertR.dec_mapR _ (fun ref => (encCert (cs e i).2 _).1.preserved ref), encCert_dec]
      · exact encCert_dec _ _
  | app sf sa ihf iha =>
    intro e V T Γ tb hS hA
    cases V <;> simp only [Shape] at hS
    cases T <;> simp only [Agree] at hA
    rename_i Vf Va Tf Ta
    obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := ihf e Vf Tf tb hS.1 hA.1
    obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := iha e Va Ta (encT cs e Vf Tf sf tb).1.table hS.2 hA.2
    have hp := fun {r : Nat} (ref : Ref _ r) => (encT cs e Va Ta sa (encT cs e Vf Tf sf tb).1.table).1.preserved ref
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [encT, Tmpl.src, Extension.trans]
      rw [Tmpl.src_mapR _ hp, hf1, ha1]
    · simp only [encT, Tmpl.view, Extension.trans]
      rw [Tmpl.view_mapR _ hp, hf2, ha2]
    · simp only [encT, Tmpl.erase, Tmpl.erase_mapR, hf3, ha3]
    · simp only [encT, Tmpl.actsB, Tmpl.actsB_mapR, hf4, ha4, Bool.and_self]
    · simp only [encT, Tmpl.letsB, Tmpl.letsB_mapR, hf5, ha5, genuineB]
    · have h6 := Tmpl.oids_mapR (encT cs e Va Ta sa (encT cs e Vf Tf sf tb).1.table).1.refs
        (encT cs e Vf Tf sf tb).2
      simp only [Tmpl.oids] at hf6 ha6 h6 ⊢
      simp only [encT, Tmpl.uses, List.map_append, List.map_map, Function.comp_def]
      exact (congrArg (· ++ _) (h6.trans hf6)).trans (congrArg (selLabels sf ++ ·) ha6)
    · simp only [encT, Tmpl.PerUse, Extension.trans]
      exact ⟨Tmpl.perUse_mapR _ (useExact_mapR _ hp cs) _ _ _ hf7, ha7⟩
  | pi sb ih =>
    intro e V T Γ tb hS hA
    cases V <;> simp only [Shape] at hS
    cases T <;> simp only [Agree] at hA
    rename_i x d Vb x' d' Tb
    obtain ⟨hx, hd, hA⟩ := hA
    subst hx hd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (e+1) Vb Tb (buildRows d tb).1.table hS hA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [encT, Tmpl.src, Extension.trans, ev_map, buildRows_ev]
      rw [h1]
    · simp only [encT, Tmpl.view, Extension.trans, ev_map, buildRows_ev]
      rw [h2]
    · simp only [encT, Tmpl.erase, h3]
    · simp only [encT, Tmpl.actsB, h4]
    · simp only [encT, Tmpl.letsB, h5, genuineB]
    · simp only [Tmpl.oids] at h6 ⊢
      simp only [encT, Tmpl.uses, List.map_map, Function.comp_def]
      exact h6
    · simp only [encT, Tmpl.PerUse, Extension.trans]
      exact h7
  | letE sb ih =>
    intro e V T Γ tb hS hA
    cases V <;> simp only [Shape] at hS
    cases T <;> simp only [Agree] at hA
    rename_i nm nd ty v Vb nm' nd' ty' v' Tb
    obtain ⟨hnm, hnd, hty, hv, hA⟩ := hA
    subst hnm hnd hty hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (e+1) Vb Tb (buildRows v (buildRows ty tb).1.table).1.table hS hA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [encT, Tmpl.src, Extension.trans, ev_map, buildRows_ev]
      rw [h1]
    · simp only [encT, Tmpl.view, Extension.trans, ev_map, buildRows_ev]
      rw [h2]
    · simp only [encT, Tmpl.erase, h3]
    · simp only [encT, Tmpl.actsB, h4]
    · simp only [encT, Tmpl.letsB, h5, genuineB]
    · simp only [Tmpl.oids] at h6 ⊢
      simp only [encT, Tmpl.uses, List.map_map, Function.comp_def]
      exact h6
    · simp only [encT, Tmpl.PerUse, Extension.trans]
      exact h7

end V6Structured

/-! ## 4. Exact recovery, incidence and the scoped action bridge -/

namespace V6Structured

open Lean (Name)
open DerivedViewSyntax V6BinderShared
open ContextualViewDAG (Table Occ Args Row Ref RefMap unroll unrollArgs evalOcc evalArgs tableValues
  evalRow)
open ContextualDAGCoverage (Extension rootOfRow unroll_rootOfRow)

/-! ### Outside-hole agreement -/

theorem fillD_agree (s : BSel) : ∀ {n : Nat} (e : Nat) (t u : Core (n + e)) (O : Fam false n),
    Agree t u s → fillD e t s O = fillD e u s O := by
  induction s with
  | none => intro n e t u O h; simp only [Agree] at h; rw [h]
  | hole i => intro n e t u O _; rfl
  | app sf sa ihf iha =>
    intro n e t u O h
    cases t <;> cases u <;> simp only [Agree] at h
    simp only [fillD, ihf e _ _ O h.1, iha e _ _ O h.2]
  | pi sb ih =>
    intro n e t u O h
    cases t <;> cases u <;> simp only [Agree] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2
    simp only [fillD, ih (e+1) _ _ O h3]
  | letE sb ih =>
    intro n e t u O h
    cases t <;> cases u <;> simp only [Agree] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    subst h1 h2 h3 h4
    simp only [fillD, ih (e+1) _ _ O h5]

theorem agree_rename (s : BSel) {k k' : Nat} (ρ : Fin k → Fin k') (t u : Core k) (h : Agree t u s) :
    Agree (rename ρ t) (rename ρ u) s := by
  rw [rename_eq_subst, rename_eq_subst]
  exact agree_subst s _ t u h

/-! ### The reading of every record, in closed form -/

section Reading
variable {Γ : List Nat} (tb : Table Γ)

/-- The decoded reading body is the consumer form: the source weakened past `M`, with `M` at every
    selected position. -/
theorem Tmpl.reading_eq {n : Nat} : ∀ {e : Nat} (t : Tmpl Γ n e),
    t.reading tb = fillD e (rename (liftRenN e Fin.succ) (t.src tb)) t.erase nodeVar := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app f a ihf iha => simp only [Tmpl.reading, Tmpl.src, Tmpl.erase, rename, fillD, ihf, iha]
  | pi x d b ih =>
    simp only [Tmpl.reading, Tmpl.src, Tmpl.erase, rename, fillD, ih]
    rfl
  | letE nm nd ty v b ih =>
    simp only [Tmpl.reading, Tmpl.src, Tmpl.erase, rename, fillD, ih]
    rfl

/-- Restore each use's source origin into a term, along the template. -/
def Tmpl.restoreSrc {n : Nat} : {e : Nat} → Tmpl Γ n e → Core (n + e) → Core (n + e)
  | _, .hole u, _ => ev tb u.src
  | _, .leaf _, X => X
  | _, .app f a, X =>
    match X with
    | .app Xf Xa => .app (Tmpl.restoreSrc f Xf) (Tmpl.restoreSrc a Xa)
    | X => X
  | _, .pi _ _ b, X =>
    match X with
    | .pi x d Xb => .pi x d (Tmpl.restoreSrc (n := n) b Xb)
    | X => X
  | _, .letE _ _ _ _ b, X =>
    match X with
    | .letE nm nd ty v Xb => .letE nm nd ty v (Tmpl.restoreSrc (n := n) b Xb)
    | X => X

/-- Restore each use's view origin into a term, along the template. -/
def Tmpl.restoreView {n : Nat} : {e : Nat} → Tmpl Γ n e → Core (n + e) → Core (n + e)
  | _, .hole u, _ => ev tb u.view
  | _, .leaf _, X => X
  | _, .app f a, X =>
    match X with
    | .app Xf Xa => .app (Tmpl.restoreView f Xf) (Tmpl.restoreView a Xa)
    | X => X
  | _, .pi _ _ b, X =>
    match X with
    | .pi x d Xb => .pi x d (Tmpl.restoreView (n := n) b Xb)
    | X => X
  | _, .letE _ _ _ _ b, X =>
    match X with
    | .letE nm nd ty v Xb => .letE nm nd ty v (Tmpl.restoreView (n := n) b Xb)
    | X => X

/-- The source and the view are recovered separately from the shared body, the represented
    outside-hole structure and the represented origins (every record, every supplier). -/
theorem Tmpl.restore_shared {n : Nat} (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e),
    t.restoreSrc tb (t.shared tb p) = t.src tb ∧ t.restoreView tb (t.shared tb p) = t.view tb := by
  intro e t
  induction t with
  | leaf o => exact ⟨rfl, rfl⟩
  | hole u => exact ⟨rfl, rfl⟩
  | app f a ihf iha =>
    simp only [Tmpl.shared, Tmpl.restoreSrc, Tmpl.restoreView, Tmpl.src, Tmpl.view, ihf.1, ihf.2,
      iha.1, iha.2, and_self]
  | pi x d b ih =>
    simp only [Tmpl.shared, Tmpl.restoreSrc, Tmpl.restoreView, Tmpl.src, Tmpl.view, ih.1, ih.2,
      and_self]
  | letE nm nd ty v b ih =>
    simp only [Tmpl.shared, Tmpl.restoreSrc, Tmpl.restoreView, Tmpl.src, Tmpl.view, ih.1, ih.2,
      and_self]

end Reading

/-- Actual common-supplier incidence of a record: its one node value, plugged by
    `DerivedViewSyntax.corePlug` into the decoded reading, gives the shared body; every selected position of that
    body holds the supplier at the use's actual vector; outside the positions it is the source; and
    zeta-expanding the node gives the same body. -/
theorem SRec.incidence (R : SRec) (h : R.body.actsB = true) :
    corePlug (R.body.reading R.table) (ev R.table R.sup) Term.var =
        R.body.shared R.table (ev R.table R.sup) ∧
      FitsD 0 (R.body.shared R.table (ev R.table R.sup)) R.body.erase (lifted (ev R.table R.sup)) ∧
      Agree (R.body.src R.table) (R.body.shared R.table (ev R.table R.sup)) R.body.erase ∧
      subst (Fin.cases (ev R.table R.sup) Term.var) (R.body.reading R.table) =
        R.body.shared R.table (ev R.table R.sup) := by
  refine ⟨?_, (R.body.incidence R.table _ h).1, (R.body.incidence R.table _ h).2,
    R.body.reading_zeta R.table _ h⟩
  rw [R.body.reading_eq R.table, R.body.shared_fill R.table _ h]
  exact corePlug_shared _ _ _ (R.body.shape_src R.table)

/-! ### The owner telescope and the whole record -/

/-- A Core owner telescope: ports and lets, newest last. -/
inductive CTel : Nat → Type where
  | nil : CTel 0
  | port {k : Nat} : CTel k → BinderAttrs → Core k → CTel (k+1)
  | letE {k : Nat} : CTel k → Name → Bool → Core k → Core k → CTel (k+1)

def CTel.close : {k : Nat} → CTel k → Core k → Core 0
  | _, .nil, b => b
  | _, .port C x d, b => CTel.close C (.pi x d b)
  | _, .letE C nm nd ty v, b => CTel.close C (.letE nm nd ty v b)

def CTel.genuineB : {k : Nat} → CTel k → Bool
  | _, .nil => true
  | _, .port C _ _ => CTel.genuineB C
  | _, .letE C _ nd _ _ => !nd && CTel.genuineB C

def encTel : {k : Nat} → CTel k → {Γ : List Nat} → (tb : Table Γ) →
    (ex : Extension tb) × OTel ex.homes k
  | _, .nil, _, tb => ⟨Extension.refl tb, .nil⟩
  | _, .port C x d, _, tb =>
    let r1 := encTel C tb
    let r2 := buildRows d r1.1.table
    ⟨r1.1.trans r2.1, .port (r1.2.mapR r2.1.refs) x r2.2⟩
  | _, .letE C nm nd ty v, _, tb =>
    let r1 := encTel C tb
    let r2 := buildRows ty r1.1.table
    let r3 := buildRows v r2.1.table
    ⟨(r1.1.trans r2.1).trans r3.1,
      .letE ((r1.2.mapR r2.1.refs).mapR r3.1.refs) nm nd (r3.1.map r2.2) r3.2⟩

theorem encTel_exact : ∀ {k : Nat} (C : CTel k) {Γ : List Nat} (tb : Table Γ),
    (∀ b : Core k, (encTel C tb).2.close (encTel C tb).1.table b = C.close b) ∧
      (encTel C tb).2.admitB = C.genuineB
  | _, .nil, _, tb => ⟨fun _ => rfl, rfl⟩
  | _, .port C x d, _, tb => by
    obtain ⟨ih1, ih2⟩ := encTel_exact C tb
    have hp := fun {r : Nat} (ref : Ref _ r) => (buildRows d (encTel C tb).1.table).1.preserved ref
    refine ⟨fun b => ?_, ?_⟩
    · simp only [encTel, Extension.trans, OTel.close, buildRows_ev]
      rw [OTel.close_mapR _ hp, ih1]
      rfl
    · simp only [encTel, OTel.admitB, OTel.admitB_mapR, ih2]
      rfl
  | _, .letE C nm nd ty v, _, tb => by
    obtain ⟨ih1, ih2⟩ := encTel_exact C tb
    have hp2 := fun {r : Nat} (ref : Ref _ r) => (buildRows ty (encTel C tb).1.table).1.preserved ref
    have hp3 := fun {r : Nat} (ref : Ref _ r) =>
      (buildRows v (buildRows ty (encTel C tb).1.table).1.table).1.preserved ref
    refine ⟨fun b => ?_, ?_⟩
    · simp only [encTel, Extension.trans, OTel.close, buildRows_ev, ev_map]
      rw [OTel.close_mapR _ hp3, OTel.close_mapR _ hp2, ih1]
      rfl
    · simp only [encTel, OTel.admitB, OTel.admitB_mapR, ih2]
      rfl

/-- A member of the declared profile at the Core level: one owner, one node (name, type, the one
    shared supplier), the source and view bodies, the selection with occurrence identities, and the
    certificates of both origins at every use. -/
structure Member where
  n : Nat
  owner : CTel n
  nodeName : Name
  nodeTy : Core n
  sup : Core n
  src : Core n
  view : Core n
  sel : BSel
  certs : CertSpec n

/-- The member conditions checked by admission: genuine owner lets, genuine lets on the selected
    paths, distinct occurrence identities. -/
def Member.okB (M : Member) : Bool :=
  M.owner.genuineB && genuineB M.view M.sel && nodupB (selLabels M.sel)

/-- The structural construction of the finite record of a member. -/
def encode (M : Member) : SRec :=
  let r0 := encTel M.owner Table.empty
  let r1 := buildRows M.nodeTy r0.1.table
  let r2 := buildRows M.sup r1.1.table
  let r3 := encT M.certs 0 M.view M.src M.sel r2.1.table
  { homes := r3.1.homes, table := r3.1.table, n := M.n,
    owner := ((r0.2.mapR r1.1.refs).mapR r2.1.refs).mapR r3.1.refs,
    nodeName := M.nodeName,
    nodeTy := r3.1.map (r2.1.map r1.2), sup := r3.1.map r2.2, body := r3.2 }

/-- General exact recovery: for every member whose view has the selected constructors and agrees
    with its source outside the holes, the total decoders of its finite record give back the
    reading, the source and the view separately, the node fields, the selection with its
    identities, and at every use the two origins, the actual vector and both certificates;
    admission of the record is exactly the member conditions. -/
theorem encode_exact (M : Member) (hS : Shape M.view M.sel) (hA : Agree M.view M.src M.sel) :
    (encode M).reading = M.owner.close (.letE M.nodeName false M.nodeTy M.sup (consumer M.view M.sel)) ∧
    (encode M).source = M.owner.close M.src ∧
    (encode M).view = M.owner.close M.view ∧
    (encode M).shared = M.owner.close (fillD 0 M.view M.sel (lifted M.sup)) ∧
    ev (encode M).table (encode M).nodeTy = M.nodeTy ∧ ev (encode M).table (encode M).sup = M.sup ∧
    (encode M).body.erase = M.sel ∧ (encode M).body.oids = selLabels M.sel ∧
    (encode M).body.PerUse (UseExact (encode M).table M.certs) M.src M.view ∧
    (encode M).admitB = M.okB := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := encT_exact M.certs M.sel 0 M.view M.src
    (buildRows M.sup (buildRows M.nodeTy (encTel M.owner Table.empty).1.table).1.table).1.table hS hA
  obtain ⟨hc, ho⟩ := encTel_exact M.owner Table.empty
  have p1 := fun {r : Nat} (ref : Ref _ r) =>
    (buildRows M.nodeTy (encTel M.owner Table.empty).1.table).1.preserved ref
  have p2 := fun {r : Nat} (ref : Ref _ r) =>
    (buildRows M.sup (buildRows M.nodeTy (encTel M.owner Table.empty).1.table).1.table).1.preserved ref
  have p3 := fun {r : Nat} (ref : Ref _ r) =>
    (encT M.certs 0 M.view M.src M.sel
      (buildRows M.sup (buildRows M.nodeTy (encTel M.owner Table.empty).1.table).1.table).1.table).1.preserved ref
  have hcl : ∀ b : Core M.n, (encode M).owner.close (encode M).table b = M.owner.close b := by
    intro b
    simp only [encode]
    rw [OTel.close_mapR _ p3, OTel.close_mapR _ p2, OTel.close_mapR _ p1, hc]
  have hTy : ev (encode M).table (encode M).nodeTy = M.nodeTy := by
    simp only [encode, ev_map, buildRows_ev]
  have hSup : ev (encode M).table (encode M).sup = M.sup := by
    simp only [encode, ev_map, buildRows_ev]
  have hsrc : (encode M).body.src (encode M).table = M.src := h1
  have hview : (encode M).body.view (encode M).table = M.view := h2
  have herase : (encode M).body.erase = M.sel := h3
  have hacts : (encode M).body.actsB = true := h4
  refine ⟨?_, ?_, ?_, ?_, hTy, hSup, herase, h6, h7, ?_⟩
  · simp only [SRec.reading]
    rw [hcl, hTy, hSup, Tmpl.reading_eq, hsrc, herase]
    exact congrArg (fun B => M.owner.close (.letE M.nodeName false M.nodeTy M.sup B))
      (fillD_agree M.sel 0 _ _ nodeVar (agree_rename M.sel Fin.succ _ _ hA)).symm
  · simp only [SRec.source]; rw [hcl, hsrc]
  · simp only [SRec.view]; rw [hcl, hview]
  · simp only [SRec.shared]
    rw [hcl, hSup, Tmpl.shared_fill _ _ _ hacts, hsrc, herase,
      fillD_agree M.sel 0 M.view M.src _ hA]
  · have hown : (encode M).owner.admitB = M.owner.genuineB := by
      simp only [encode, OTel.admitB_mapR]
      exact ho
    have hl : (encode M).body.letsB = genuineB M.view M.sel := h5
    have hi : (encode M).body.oids = selLabels M.sel := h6
    simp only [SRec.admitB, Tmpl.admitB, Member.okB, hown, hacts, hl, hi, Bool.true_and, Bool.and_assoc]

/-! ### The action: a separate finite actual map on a fixed template

A reading instance keeps its template record (rows, homes, owner, template occurrences) and a
separate finite contextual actual map: one occurrence of the table per owner declaration, at the
instance context. Lambda-valued actuals are occurrences of existing `lam` rows. Applying the map
keeps the rows and homes and changes only occurrence actuals: every component reference below `e`
local binders is substituted by the map lifted `e` times, certificate actuals likewise, and each
use's actual vector becomes the prefix weakening of the instance context. -/

theorem ev_liftOccN {Γ : List Nat} (tb : Table Γ) {n m : Nat} (σ : Fin n → Occ Γ m) :
    ∀ e : Nat, (fun i => ev tb (liftOccN e σ i)) = liftSubN e (fun i => ev tb (σ i))
  | 0 => rfl
  | e+1 => by
    funext i
    have h1 := congrFun (ContextualViewDAG.unroll_liftSub tb (liftOccN e σ)) i
    have h2 := congrFun (expand_liftSub (fun i => unroll tb (liftOccN e σ i))) i
    show expand (unroll tb (ContextualViewDAG.liftSub (liftOccN e σ) i)) = _
    rw [h1, h2]
    exact congrArg (fun g => liftSub g i) (ev_liftOccN tb σ e)

theorem ev_substOcc {Γ : List Nat} (tb : Table Γ) {n m : Nat} (σ : Fin n → Occ Γ m) (e : Nat)
    (o : Occ Γ (n + e)) :
    ev tb (ContextualViewDAG.subst (liftOccN e σ) o) = subst (liftSubN e (fun i => ev tb (σ i))) (ev tb o) := by
  unfold ev
  rw [ContextualViewDAG.expand_unroll_subst]
  exact congrArg (fun g => subst g (expand (unroll tb o))) (ev_liftOccN tb σ e)

theorem evA_substArgs {Γ : List Nat} (tb : Table Γ) {a b r : Nat} (τ : Fin a → Occ Γ b)
    (acts : Args Γ a r) :
    evA tb (ContextualViewDAG.substArgs τ acts) = fun j => subst (fun i => ev tb (τ i)) (evA tb acts j) := by
  funext j
  simp only [evA, unrollArgs, ContextualViewDAG.evalArgs_subst, expand_subst]
  rfl

theorem evA_eq_get {Γ : List Nat} (tb : Table Γ) {a r : Nat} (acts : Args Γ a r) :
    evA tb acts = fun j => ev tb (acts.get j) := by
  funext j
  simp only [evA, unrollArgs, ContextualViewDAG.evalArgs_get, ev, unroll]

/-- A Core certificate under an ambient substitution. -/
def CertC.subst {a b : Nat} (τ : Fin a → Core b) : CertC a → CertC b
  | .exact => .exact
  | .classB nm k f => .classB nm k (fun j => DerivedViewSyntax.subst τ (f j))

section Action
variable {Γ : List Nat}

def CertR.act {a b : Nat} (τ : Fin a → Occ Γ b) : CertR Γ a → CertR Γ b
  | .exact => .exact
  | .classB nm k acts => .classB nm k (ContextualViewDAG.substArgs τ acts)

def UseR.act {n m e : Nat} (σ : Fin n → Occ Γ m) (u : UseR Γ n e) : UseR Γ m e :=
  { oid := u.oid,
    src := ContextualViewDAG.subst (liftOccN e σ) u.src,
    view := ContextualViewDAG.subst (liftOccN e σ) u.view,
    acts := weakArgs m e,
    srcCert := u.srcCert.act (liftOccN e σ),
    viewCert := u.viewCert.act (liftOccN e σ) }

def Tmpl.act {n m : Nat} (σ : Fin n → Occ Γ m) : {e : Nat} → Tmpl Γ n e → Tmpl Γ m e
  | e, .leaf o => .leaf (ContextualViewDAG.subst (liftOccN e σ) o)
  | _, .hole u => .hole (u.act σ)
  | _, .app f a => .app (Tmpl.act σ f) (Tmpl.act σ a)
  | e, .pi x d b => .pi x (ContextualViewDAG.subst (liftOccN e σ) d) (Tmpl.act σ b)
  | e, .letE nm nd ty v b =>
    .letE nm nd (ContextualViewDAG.subst (liftOccN e σ) ty) (ContextualViewDAG.subst (liftOccN e σ) v)
      (Tmpl.act σ b)

def LB.act {n m : Nat} (σ : Fin n → Occ Γ m) : LB Γ n → LB Γ m
  | .pi e x d => .pi e x (ContextualViewDAG.subst (liftOccN e σ) d)
  | .letE e nm nd ty v =>
    .letE e nm nd (ContextualViewDAG.subst (liftOccN e σ) ty) (ContextualViewDAG.subst (liftOccN e σ) v)

def UseEntry.act {n m : Nat} (σ : Fin n → Occ Γ m) (y : UseEntry Γ n) : UseEntry Γ m :=
  ⟨y.e, y.path, y.scope.map (LB.act σ), y.use.act σ⟩

variable (tb : Table Γ)

theorem CertR.dec_act {a b : Nat} (τ : Fin a → Occ Γ b) (c : CertR Γ a) :
    (c.act τ).dec tb = (c.dec tb).subst (fun i => ev tb (τ i)) := by
  cases c with
  | exact => rfl
  | classB nm k acts => simp only [CertR.act, CertR.dec, CertC.subst, evA_substArgs]

/-- Per use: the acted use's origins, actual vector and certificate actuals, decoded. -/
theorem UseR.act_dec {n m e : Nat} (σ : Fin n → Occ Γ m) (u : UseR Γ n e) :
    ev tb (u.act σ).src = subst (liftSubN e (fun i => ev tb (σ i))) (ev tb u.src) ∧
    ev tb (u.act σ).view = subst (liftSubN e (fun i => ev tb (σ i))) (ev tb u.view) ∧
    evA tb (u.act σ).acts = weakActs m e ∧
    (u.act σ).srcCert.dec tb = (u.srcCert.dec tb).subst (liftSubN e (fun i => ev tb (σ i))) ∧
    (u.act σ).viewCert.dec tb = (u.viewCert.dec tb).subst (liftSubN e (fun i => ev tb (σ i))) ∧
    (u.act σ).oid = u.oid := by
  refine ⟨ev_substOcc tb σ e u.src, ev_substOcc tb σ e u.view, evA_weakArgs tb m e, ?_, ?_, rfl⟩
  · simp only [UseR.act, CertR.dec_act, ev_liftOccN]
  · simp only [UseR.act, CertR.dec_act, ev_liftOccN]

/-- The transported actual vector of an admitted use is the instance's prefix weakening composed
    with the actual map: what changes at the use is exactly the actual map. -/
theorem acts_transport {n m e : Nat} (σ : Fin n → Occ Γ m) (acts : Args Γ (n + e) n)
    (h : weakB e acts 0 = true) :
    evA tb (ContextualViewDAG.substArgs (liftOccN e σ) acts) =
      fun j => subst (weakActs m e) (ev tb (σ j)) := by
  rw [evA_substArgs, evA_weak tb acts h, ev_liftOccN]
  exact acts_subst _ e

theorem Tmpl.act_src {n m : Nat} (σ : Fin n → Occ Γ m) : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.act σ).src tb = subst (liftSubN e (fun i => ev tb (σ i))) (t.src tb) := by
  intro e t
  induction t with
  | leaf o => exact ev_substOcc tb σ _ o
  | hole u => exact ev_substOcc tb σ _ u.src
  | app f a ihf iha => simp only [Tmpl.act, Tmpl.src, subst, ihf, iha]
  | pi x d b ih => simp only [Tmpl.act, Tmpl.src, subst, ih, ev_substOcc, liftSubN_succ]
  | letE nm nd ty v b ih => simp only [Tmpl.act, Tmpl.src, subst, ih, ev_substOcc, liftSubN_succ]

theorem Tmpl.act_view {n m : Nat} (σ : Fin n → Occ Γ m) : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.act σ).view tb = subst (liftSubN e (fun i => ev tb (σ i))) (t.view tb) := by
  intro e t
  induction t with
  | leaf o => exact ev_substOcc tb σ _ o
  | hole u => exact ev_substOcc tb σ _ u.view
  | app f a ihf iha => simp only [Tmpl.act, Tmpl.view, subst, ihf, iha]
  | pi x d b ih => simp only [Tmpl.act, Tmpl.view, subst, ih, ev_substOcc, liftSubN_succ]
  | letE nm nd ty v b ih => simp only [Tmpl.act, Tmpl.view, subst, ih, ev_substOcc, liftSubN_succ]

theorem Tmpl.act_shared {n m : Nat} (σ : Fin n → Occ Γ m) (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e),
    t.actsB = true →
    (t.act σ).shared tb (subst (fun i => ev tb (σ i)) p) =
      subst (liftSubN e (fun i => ev tb (σ i))) (t.shared tb p) := by
  intro e t
  induction t with
  | leaf o => intro _; exact ev_substOcc tb σ _ o
  | hole u =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.act, UseR.act, Tmpl.shared, evA_weakArgs, evA_weak tb u.acts h, subst_comp]
    exact congrArg (fun g => subst g p) (acts_subst _ _).symm
  | app f a ihf iha =>
    intro h
    simp only [Tmpl.actsB, Bool.and_eq_true] at h
    simp only [Tmpl.act, Tmpl.shared, subst, ihf h.1, iha h.2]
  | pi x d b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.act, Tmpl.shared, subst, ih h, ev_substOcc, liftSubN_succ]
  | letE nm nd ty v b ih =>
    intro h
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.act, Tmpl.shared, subst, ih h, ev_substOcc, liftSubN_succ]

theorem liftSubN_liftSub_liftRenN {n m : Nat} (τ : Fin n → Core m) : ∀ (e : Nat) (i : Fin (n + e)),
    liftSubN e (liftSub τ) (liftRenN e Fin.succ i) = rename (liftRenN e Fin.succ) (liftSubN e τ i)
  | 0, i => rfl
  | e+1, i => by
    refine Fin.cases rfl (fun j => ?_) i
    show liftSub (liftSubN e (liftSub τ)) (liftRen (liftRenN e Fin.succ) j.succ) =
      rename (liftRen (liftRenN e Fin.succ)) (liftSub (liftSubN e τ) j.succ)
    rw [liftRen_succ, liftSub_succ, liftSub_succ, liftSubN_liftSub_liftRenN τ e j, rename_comp,
      rename_comp]
    rfl

theorem rename_subst_liftSub {n m : Nat} (τ : Fin n → Core m) (e : Nat) (x : Core (n + e)) :
    rename (liftRenN e Fin.succ) (subst (liftSubN e τ) x) =
      subst (liftSubN e (liftSub τ)) (rename (liftRenN e Fin.succ) x) := by
  rw [rename_subst, subst_rename]
  exact congrArg (fun g => subst g x) (funext fun i => (liftSubN_liftSub_liftRenN τ e i).symm)

theorem Tmpl.act_reading {n m : Nat} (σ : Fin n → Occ Γ m) : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.act σ).reading tb = subst (liftSubN e (liftSub (fun i => ev tb (σ i)))) (t.reading tb) := by
  intro e t
  induction t with
  | leaf o =>
    simp only [Tmpl.act, Tmpl.reading, ev_substOcc]
    exact rename_subst_liftSub _ _ _
  | hole u =>
    rename_i e
    have h := congrFun (congrFun (substFam_liftSub_nodeVar (n := n) (fun i => ev tb (σ i))) e) 0
    simp only [substFam, nodeVar] at h
    exact h.symm
  | app f a ihf iha => simp only [Tmpl.act, Tmpl.reading, subst, ihf, iha]
  | pi x d b ih =>
    simp only [Tmpl.act, Tmpl.reading, subst, ih, ev_substOcc, rename_subst_liftSub, liftSubN_succ]
  | letE nm nd ty v b ih =>
    simp only [Tmpl.act, Tmpl.reading, subst, ih, ev_substOcc, rename_subst_liftSub, liftSubN_succ]

omit tb in
theorem Tmpl.act_structure {n m : Nat} (σ : Fin n → Occ Γ m) : ∀ {e : Nat} (t : Tmpl Γ n e),
    (t.act σ).erase = t.erase ∧ (t.act σ).actsB = true ∧ (t.act σ).letsB = t.letsB ∧
      (t.act σ).uses = t.uses.map (UseEntry.act σ) := by
  intro e t
  induction t with
  | leaf o => exact ⟨rfl, rfl, rfl, rfl⟩
  | hole u => exact ⟨rfl, weakB_weakArgs _ _, rfl, rfl⟩
  | app f a ihf iha =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Tmpl.act, Tmpl.erase, ihf.1, iha.1]
    · simp only [Tmpl.act, Tmpl.actsB, ihf.2.1, iha.2.1, Bool.and_self]
    · simp only [Tmpl.act, Tmpl.letsB, ihf.2.2.1, iha.2.2.1]
    · simp only [Tmpl.act, Tmpl.uses, ihf.2.2.2, iha.2.2.2, List.map_append, List.map_map]
      rfl
  | pi x d b ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Tmpl.act, Tmpl.erase, ih.1]
    · simp only [Tmpl.act, Tmpl.actsB, ih.2.1]
    · simp only [Tmpl.act, Tmpl.letsB, ih.2.2.1]
    · simp only [Tmpl.act, Tmpl.uses, ih.2.2.2, List.map_map]
      rfl
  | letE nm nd ty v b ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Tmpl.act, Tmpl.erase, ih.1]
    · simp only [Tmpl.act, Tmpl.actsB, ih.2.1]
    · simp only [Tmpl.act, Tmpl.letsB, ih.2.2.1]
    · simp only [Tmpl.act, Tmpl.uses, ih.2.2.2, List.map_map]
      rfl

omit tb in
theorem Tmpl.act_oids {n m : Nat} (σ : Fin n → Occ Γ m) {e : Nat} (t : Tmpl Γ n e) :
    (t.act σ).oids = t.oids := by
  simp only [Tmpl.oids, (t.act_structure σ).2.2.2, List.map_map]
  rfl

end Action

/-- A reading instance: the template record and, separately, its finite contextual actual map at
    an instance context. -/
structure SInst where
  tmpl : SRec
  m : Nat
  ctx : OTel tmpl.homes m
  actuals : Args tmpl.homes m tmpl.n

def SInst.admitB (I : SInst) : Bool := I.tmpl.admitB && I.ctx.admitB

/-- The instance's record: the same homes and rows; the owner is the instance context; every
    occurrence is acted on by the actual map. -/
def SInst.apply (I : SInst) : SRec :=
  { homes := I.tmpl.homes, table := I.tmpl.table, n := I.m, owner := I.ctx,
    nodeName := I.tmpl.nodeName,
    nodeTy := ContextualViewDAG.subst I.actuals.get I.tmpl.nodeTy,
    sup := ContextualViewDAG.subst I.actuals.get I.tmpl.sup,
    body := I.tmpl.body.act I.actuals.get }

/-- The scoped action bridge: decoding commutes with the action. `σ` is the decoded actual map. -/
theorem SInst.apply_decode (I : SInst) (h : I.admitB = true) :
    let tb := I.tmpl.table
    let σ := evA tb I.actuals
    I.apply.admitB = true ∧
    I.apply.source = I.ctx.close tb (subst σ (I.tmpl.body.src tb)) ∧
    I.apply.view = I.ctx.close tb (subst σ (I.tmpl.body.view tb)) ∧
    I.apply.shared = I.ctx.close tb (subst σ (I.tmpl.body.shared tb (ev tb I.tmpl.sup))) ∧
    I.apply.reading = I.ctx.close tb (.letE I.tmpl.nodeName false (subst σ (ev tb I.tmpl.nodeTy))
      (subst σ (ev tb I.tmpl.sup)) (subst (liftSub σ) (I.tmpl.body.reading tb))) ∧
    I.apply.body.uses = I.tmpl.body.uses.map (UseEntry.act I.actuals.get) ∧
    I.apply.homes = I.tmpl.homes := by
  intro tb σ
  have hσ : σ = fun i => ev tb (I.actuals.get i) := evA_eq_get tb I.actuals
  simp only [SInst.admitB, SRec.admitB, Tmpl.admitB, Bool.and_eq_true] at h
  obtain ⟨⟨_, ⟨hacts, hlets⟩, hnodup⟩, hctx⟩ := h
  have hstr := I.tmpl.body.act_structure I.actuals.get
  refine ⟨?_, ?_, ?_, ?_, ?_, hstr.2.2.2, rfl⟩
  · simp only [SRec.admitB, SInst.apply, Tmpl.admitB, hctx, hstr.2.1, hstr.2.2.1, hlets,
      Tmpl.act_oids, hnodup, Bool.and_self]
  · simp only [SRec.source, SInst.apply]
    rw [Tmpl.act_src, hσ]
    rfl
  · simp only [SRec.view, SInst.apply]
    rw [Tmpl.act_view, hσ]
    rfl
  · simp only [SRec.shared, SInst.apply]
    have hs := ev_substOcc tb I.actuals.get 0 I.tmpl.sup
    simp only [liftOccN, liftSubN] at hs
    rw [hs, Tmpl.act_shared _ _ _ _ hacts, hσ]
    rfl
  · simp only [SRec.reading, SInst.apply]
    have hs := ev_substOcc tb I.actuals.get 0 I.tmpl.sup
    have ht := ev_substOcc tb I.actuals.get 0 I.tmpl.nodeTy
    simp only [liftOccN, liftSubN] at hs ht
    rw [hs, ht, Tmpl.act_reading, hσ]
    rfl

/-- Moving a record into a larger table (new rows appended; nothing decoded changes). -/
def SRec.extend (R : SRec) (ex : Extension R.table) : SRec :=
  { homes := ex.homes, table := ex.table, n := R.n, owner := R.owner.mapR ex.refs,
    nodeName := R.nodeName, nodeTy := ex.map R.nodeTy, sup := ex.map R.sup,
    body := R.body.mapR ex.refs }

theorem SRec.extend_decode (R : SRec) (ex : Extension R.table) :
    (R.extend ex).reading = R.reading ∧ (R.extend ex).source = R.source ∧
    (R.extend ex).view = R.view ∧ (R.extend ex).shared = R.shared ∧
    (R.extend ex).admitB = R.admitB ∧ (R.extend ex).body.erase = R.body.erase ∧
    (∀ b, (R.extend ex).owner.close (R.extend ex).table b = R.owner.close R.table b) ∧
    (R.extend ex).body.src (R.extend ex).table = R.body.src R.table ∧
    (R.extend ex).body.view (R.extend ex).table = R.body.view R.table ∧
    (R.extend ex).body.reading (R.extend ex).table = R.body.reading R.table ∧
    ev (R.extend ex).table (R.extend ex).nodeTy = ev R.table R.nodeTy ∧
    ev (R.extend ex).table (R.extend ex).sup = ev R.table R.sup := by
  have hp := fun {r : Nat} (ref : Ref _ r) => ex.preserved ref
  have hc : ∀ b, (R.owner.mapR ex.refs).close ex.table b = R.owner.close R.table b :=
    OTel.close_mapR _ hp R.owner
  refine ⟨?_, ?_, ?_, ?_, ?_, Tmpl.erase_mapR _ _, hc, Tmpl.src_mapR _ hp _, Tmpl.view_mapR _ hp _,
    Tmpl.reading_mapR _ hp _, ev_map _ _, ev_map _ _⟩
  · simp only [SRec.reading, SRec.extend, hc, ev_map, Tmpl.reading_mapR _ hp]
  · simp only [SRec.source, SRec.extend, hc, Tmpl.src_mapR _ hp]
  · simp only [SRec.view, SRec.extend, hc, Tmpl.view_mapR _ hp]
  · simp only [SRec.shared, SRec.extend, hc, ev_map, Tmpl.shared_mapR _ hp]
  · simp only [SRec.admitB, SRec.extend, Tmpl.admitB, OTel.admitB_mapR, Tmpl.actsB_mapR,
      Tmpl.letsB_mapR, Tmpl.oids_mapR]

end V6Structured

namespace V6Structured

def Tmpl.mapUses {Γ : List Nat} {n : Nat} (f : (e : Nat) → UseR Γ n e → UseR Γ n e) :
    {e : Nat} → Tmpl Γ n e → Tmpl Γ n e
  | e, .hole u => .hole (f e u)
  | _, .leaf o => .leaf o
  | _, .app g a => .app (Tmpl.mapUses f g) (Tmpl.mapUses f a)
  | _, .pi x d b => .pi x d (Tmpl.mapUses f b)
  | _, .letE nm nd ty v b => .letE nm nd ty v (Tmpl.mapUses f b)

end V6Structured

universe u v w z

namespace CompositionLaws

def Preserves {A : Type v} {B : Type w}
    (mulA : A → A → A) (mulB : B → B → B) (f : A → B) : Prop :=
  ∀ x y, f (mulA x y) = mulB (f x) (f y)

theorem preserves_comp {A : Type v} {B : Type w} {C : Type z}
    (mulA : A → A → A) (mulB : B → B → B) (mulC : C → C → C)
    (f : A → B) (g : B → C)
    (hf : Preserves mulA mulB f) (hg : Preserves mulB mulC g) :
    Preserves mulA mulC (fun x => g (f x)) := by
  intro x y
  change g (f (mulA x y)) = mulC (g (f x)) (g (f y))
  rw [hf x y, hg (f x) (f y)]

theorem dependent_preserves_comp {I : Type u}
    (A : I → Type v) (B : I → Type w) (C : I → Type z)
    (mulA : (i : I) → A i → A i → A i)
    (mulB : (i : I) → B i → B i → B i)
    (mulC : (i : I) → C i → C i → C i)
    (f : (i : I) → A i → B i) (g : (i : I) → B i → C i)
    (hf : ∀ i, Preserves (mulA i) (mulB i) (f i))
    (hg : ∀ i, Preserves (mulB i) (mulC i) (g i)) :
    ∀ i, Preserves (mulA i) (mulC i) (fun x => g i (f i x)) := by
  intro i
  exact preserves_comp (mulA i) (mulB i) (mulC i) (f i) (g i) (hf i) (hg i)

end CompositionLaws

/-! ## 6 to 8. The rule, its records, and the construction with its four clauses -/

set_option linter.constructorNameAsVariable false

namespace V6Compose

open Lean (Name)
open DerivedViewSyntax V6BinderShared V6Structured
open ContextualViewDAG (Table Occ Args Row Ref RefMap unroll unrollArgs evalOcc evalArgs tableValues
  evalRow)
open ContextualDAGCoverage (Extension)

/-! ## 6. The rule templates, specified as Core terms -/

/-- Universe levels of one map interface: `I : Type u`, `X : I → Type x`, `Y : I → Type y`. -/
structure Lv3 where
  u : ULevel
  x : ULevel
  y : ULevel
  deriving DecidableEq

/-- Universe levels of the composite interface: `I : Type u`, `A B C : I → Type a/b/c`. -/
structure Lv4 where
  u : ULevel
  a : ULevel
  b : ULevel
  c : ULevel
  deriving DecidableEq

def Lv4.left (l : Lv4) : Lv3 := ⟨l.u, l.a, l.b⟩
def Lv4.right (l : Lv4) : Lv3 := ⟨l.u, l.b, l.c⟩
def Lv4.outer (l : Lv4) : Lv3 := ⟨l.u, l.a, l.c⟩

def bx (s : Name) : BinderAttrs := ⟨s, .default⟩
def anon : BinderAttrs := ⟨.anonymous, .default⟩

/-- `I → Type l`, for the index at `I`. -/
def famTy {n : Nat} (I : Fin n) (lv : ULevel) : Core n := .pi anon (.var I) (.sort (.succ lv))

/-- `∀ i : I, F i → F i → F i`. -/
def opTy {n : Nat} (I F : Fin n) : Core n :=
  .pi (bx `i) (.var I)
    (.pi anon (.app (.var F.succ) (.var 0))
      (.pi anon (.app (.var F.succ.succ) (.var 1)) (.app (.var F.succ.succ.succ) (.var 2))))

/-- `∀ i : I, X i → Y i`. -/
def mapTy {n : Nat} (I X Y : Fin n) : Core n :=
  .pi (bx `i) (.var I) (.pi anon (.app (.var X.succ) (.var 0)) (.app (.var Y.succ.succ) (.var 1)))

/-- The single-map interface `I, X, Y, μX, μY, φ` (φ is the newest port, index 0). -/
def mapTel (l : Lv3) : CTel 6 :=
  .port (.port (.port (.port (.port (.port .nil (bx `I) (.sort (.succ l.u)))
    (bx `X) (famTy 0 l.x))
    (bx `Y) (famTy 1 l.y))
    (bx `μX) (opTy 2 1))
    (bx `μY) (opTy 3 1))
    (bx `φ) (mapTy 4 3 2)

/-- The preservation law of one map, at its six ports:
    `∀ i x y, φ i (μX i x y) = μY i (φ i x) (φ i y)`. -/
def lawSrc (l : Lv3) : Core 6 :=
  .pi (bx `i) (.var 5)
    (.pi (bx `x) (.app (.var 5) (.var 0))
      (.pi (bx `y) (.app (.var 6) (.var 1))
        (.app (.app (.app (.const ``Eq [.succ l.y]) (.app (.var 6) (.var 2)))
            (.app (.app (.var 3) (.var 2)) (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0))))
          (.app (.app (.app (.var 4) (.var 2)) (.app (.app (.var 3) (.var 2)) (.var 1)))
            (.app (.app (.var 3) (.var 2)) (.var 0))))))

/-- The composite interface `I, A, B, C, μA, μB, μC, f, g` (g is index 0, I is index 8). -/
def compTel (l : Lv4) : CTel 9 :=
  .port (.port (.port (.port (.port (.port (.port (.port (.port .nil
    (bx `I) (.sort (.succ l.u)))
    (bx `A) (famTy 0 l.a))
    (bx `B) (famTy 1 l.b))
    (bx `C) (famTy 2 l.c))
    (bx `μA) (opTy 3 2))
    (bx `μB) (opTy 4 2))
    (bx `μC) (opTy 5 2))
    (bx `f) (mapTy 6 5 4))
    (bx `g) (mapTy 7 5 4)

/-- Where the first map's ports sit in the composite: φ ↦ f, μY ↦ μB, μX ↦ μA, Y ↦ B, X ↦ A, I ↦ I. -/
def ιFn : Fin 6 → Fin 9
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 7
  | _ => 8

/-- Where the second map's ports sit: φ ↦ g, μY ↦ μC, μX ↦ μB, Y ↦ C, X ↦ B, I ↦ I. -/
def ιGn : Fin 6 → Fin 9
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 6
  | _ => 8

/-- The composite function `fun i x => g i (f i x)` at the composite interface. -/
def hSrc : Core 9 :=
  .lam (bx `i) (.var 8)
    (.lam (bx `x) (.app (.var 8) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.var 3) (.var 1)) (.var 0))))

def hTy : Core 9 := mapTy 8 7 5
def μBTy : Core 9 := opTy 8 6

/-- The law's ports for the composite: φ ↦ h, μY ↦ μC, μX ↦ μA, Y ↦ C, X ↦ A, I ↦ I. -/
def ιPh : Fin 6 → Core 9
  | ⟨0, _⟩ => hSrc
  | ⟨1, _⟩ => .var 2
  | ⟨2, _⟩ => .var 4
  | ⟨3, _⟩ => .var 5
  | ⟨4, _⟩ => .var 7
  | _ => .var 8

def pfT (l : Lv4) : Core 9 := subst (fun j => .var (ιFn j)) (lawSrc l.left)
def pgT (l : Lv4) : Core 9 := subst (fun j => .var (ιGn j)) (lawSrc l.right)
def phT (l : Lv4) : Core 9 := subst ιPh (lawSrc l.outer)

/-- The two input laws, retained together: `Pf ∧ Pg`. -/
def lawsT (l : Lv4) : Core 9 := .app (.app (.const ``And []) (pfT l)) (pgT l)

/-- The use of `μB` in `Pf` (hole 0) and in `Pg` (hole 1). -/
def pfSel : BSel := .pi (.pi (.pi (.app .none (.app (.app (.app (.hole 0) .none) .none) .none))))
def pgSel : BSel :=
  .pi (.pi (.pi (.app (.app .none (.app .none (.app (.app (.app (.hole 1) .none) .none) .none))) .none)))
def rinSel : BSel := .app (.app .none pfSel) pgSel

/-- The three uses of `h` in `Ph`. -/
def phSel : BSel :=
  .pi (.pi (.pi (.app (.app .none (.app (.app (.hole 0) .none) .none))
    (.app (.app .none (.app (.app (.hole 1) .none) .none)) (.app (.app (.hole 2) .none) .none)))))

/-- Iterated application `h a₀ … a_{k-1}`. -/
def appArgs {a : Nat} : Core a → (k : Nat) → (Fin k → Core a) → Core a
  | h, 0, _ => h
  | h, k+1, f => appArgs (.app h (f 0)) k (fun i => f i.succ)

theorem subst_appArgs {a b : Nat} (σ : Fin a → Core b) : ∀ (k : Nat) (h : Core a) (f : Fin k → Core a),
    subst σ (appArgs h k f) = appArgs (subst σ h) k (fun i => subst σ (f i))
  | 0, _, _ => rfl
  | k+1, h, f => by
    simp only [appArgs]
    rw [subst_appArgs σ k]
    rfl

def dpcName : Name := ``CompositionLaws.dependent_preserves_comp

/-- The generic proof: `CompositionLaws.dependent_preserves_comp` at the four levels, applied to the nine
    ports and the two evidence ports `hf` (index 1) and `hg` (index 0). -/
def certT (l : Lv4) : Core 11 :=
  appArgs (.const dpcName [l.u, l.a, l.b, l.c]) 11 (fun j => .var ⟨10 - j.val, by omega⟩)

def exactCerts : CertSpec 9 := fun _ _ => (.exact, .exact)

def memIn (l : Lv4) : Member :=
  { n := 9, owner := compTel l, nodeName := `μB, nodeTy := μBTy, sup := .var 3,
    src := lawsT l, view := lawsT l, sel := rinSel, certs := exactCerts }

def memOut (l : Lv4) : Member :=
  { n := 9, owner := compTel l, nodeName := `h, nodeTy := hTy, sup := hSrc,
    src := phT l, view := phT l, sel := phSel, certs := exactCerts }

theorem agree_refl (s : BSel) : ∀ {k : Nat} (t : Core k), Shape t s → Agree t t s := by
  induction s with
  | none => intro k t _; rfl
  | hole i => intro k t _; trivial
  | app sf sa ihf iha =>
    intro k t h
    cases t <;> simp only [Shape] at h
    exact ⟨ihf _ h.1, iha _ h.2⟩
  | pi sb ih =>
    intro k t h
    cases t <;> simp only [Shape] at h
    exact ⟨rfl, rfl, ih _ h⟩
  | letE sb ih =>
    intro k t h
    cases t <;> simp only [Shape] at h
    exact ⟨rfl, rfl, rfl, rfl, ih _ h⟩

theorem shape_in (l : Lv4) : Shape (lawsT l) rinSel := shapeB_sound _ _ rfl
theorem shape_out (l : Lv4) : Shape (phT l) phSel := shapeB_sound _ _ rfl
theorem fits_in (l : Lv4) : FitsD 0 (lawsT l) rinSel (lifted (.var 3)) := fitsCB_sound _ _ _ _ rfl
theorem fits_out (l : Lv4) : FitsD 0 (phT l) phSel (lifted hSrc) := fitsCB_sound _ _ _ _ rfl
theorem okB_in (l : Lv4) : (memIn l).okB = true := rfl
theorem okB_out (l : Lv4) : (memOut l).okB = true := rfl


/-! ## 7. The rule's records over one table -/

/-- A member's components encoded after the rows of a given table. -/
structure Located {Γ : List Nat} (tb : Table Γ) (n : Nat) where
  ex : Extension tb
  owner : OTel ex.homes n
  nodeTy : Occ ex.homes n
  sup : Occ ex.homes n
  body : Tmpl ex.homes n 0

/-- `encode`, started from a given table instead of the empty one. -/
def encodeAt {Γ : List Nat} (tb : Table Γ) (M : Member) : Located tb M.n :=
  let r0 := encTel M.owner tb
  let r1 := buildRows M.nodeTy r0.1.table
  let r2 := buildRows M.sup r1.1.table
  let r3 := encT M.certs 0 M.view M.src M.sel r2.1.table
  { ex := ((r0.1.trans r1.1).trans r2.1).trans r3.1,
    owner := ((r0.2.mapR r1.1.refs).mapR r2.1.refs).mapR r3.1.refs,
    nodeTy := r3.1.map (r2.1.map r1.2), sup := r3.1.map r2.2, body := r3.2 }

def Located.toRec {Γ : List Nat} {tb : Table Γ} {n : Nat} (A : Located tb n) (nm : Name) : SRec :=
  ⟨A.ex.homes, A.ex.table, n, A.owner, nm, A.nodeTy, A.sup, A.body⟩

/-- From the empty table, `encodeAt` is the accepted `encode`. -/
theorem encode_eq_encodeAt (M : Member) : encode M = (encodeAt Table.empty M).toRec M.nodeName := rfl

/-- Exactness of `encodeAt`, for every table and every member of the profile (the proof of
    `encode_exact`, with the base table left general). -/
theorem encodeAt_exact {Γ : List Nat} (tb : Table Γ) (M : Member) (hS : Shape M.view M.sel)
    (hA : Agree M.view M.src M.sel) :
    (∀ b, (encodeAt tb M).owner.close (encodeAt tb M).ex.table b = M.owner.close b) ∧
    (encodeAt tb M).owner.admitB = M.owner.genuineB ∧
    ev (encodeAt tb M).ex.table (encodeAt tb M).nodeTy = M.nodeTy ∧
    ev (encodeAt tb M).ex.table (encodeAt tb M).sup = M.sup ∧
    (encodeAt tb M).body.src (encodeAt tb M).ex.table = M.src ∧
    (encodeAt tb M).body.view (encodeAt tb M).ex.table = M.view ∧
    (encodeAt tb M).body.erase = M.sel ∧ (encodeAt tb M).body.actsB = true ∧
    (encodeAt tb M).body.letsB = genuineB M.view M.sel ∧
    (encodeAt tb M).body.oids = selLabels M.sel ∧
    (encodeAt tb M).body.PerUse (UseExact (encodeAt tb M).ex.table M.certs) M.src M.view := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := encT_exact M.certs M.sel 0 M.view M.src
    (buildRows M.sup (buildRows M.nodeTy (encTel M.owner tb).1.table).1.table).1.table hS hA
  obtain ⟨hc, ho⟩ := encTel_exact M.owner tb
  have p1 := fun {r : Nat} (ref : Ref _ r) =>
    (buildRows M.nodeTy (encTel M.owner tb).1.table).1.preserved ref
  have p2 := fun {r : Nat} (ref : Ref _ r) =>
    (buildRows M.sup (buildRows M.nodeTy (encTel M.owner tb).1.table).1.table).1.preserved ref
  have p3 := fun {r : Nat} (ref : Ref _ r) =>
    (encT M.certs 0 M.view M.src M.sel
      (buildRows M.sup (buildRows M.nodeTy (encTel M.owner tb).1.table).1.table).1.table).1.preserved ref
  refine ⟨fun b => ?_, ?_, ?_, ?_, h1, h2, h3, h4, h5, h6, h7⟩
  · simp only [encodeAt, Extension.trans]
    rw [OTel.close_mapR _ p3, OTel.close_mapR _ p2, OTel.close_mapR _ p1, hc]
  · simp only [encodeAt, OTel.admitB_mapR]
    exact ho
  · simp only [encodeAt, Extension.trans, ev_map, buildRows_ev]
  · simp only [encodeAt, Extension.trans, ev_map, buildRows_ev]

/-- The rule for one universe instance: its two template records over one table. `rin` reads the
    retained input laws `Pf ∧ Pg` with node `μB`; `rout` reads the derived law `Ph` with node `h`. -/
structure Bank where
  l : Lv4
  homes : List Nat
  table : Table homes
  inOwner : OTel homes 9
  inTy : Occ homes 9
  inSup : Occ homes 9
  inBody : Tmpl homes 9 0
  outOwner : OTel homes 9
  outTy : Occ homes 9
  outSup : Occ homes 9
  outBody : Tmpl homes 9 0

def Bank.rin (B : Bank) : SRec := ⟨B.homes, B.table, 9, B.inOwner, `μB, B.inTy, B.inSup, B.inBody⟩
def Bank.rout (B : Bank) : SRec := ⟨B.homes, B.table, 9, B.outOwner, `h, B.outTy, B.outSup, B.outBody⟩

/-- What the rule's records decode to: the independently specified templates, field for field. -/
structure Bank.Exact (B : Bank) : Prop where
  inClose : ∀ b, B.inOwner.close B.table b = (compTel B.l).close b
  outClose : ∀ b, B.outOwner.close B.table b = (compTel B.l).close b
  inOwnerOk : B.inOwner.admitB = true
  outOwnerOk : B.outOwner.admitB = true
  inTy : ev B.table B.inTy = μBTy
  inSup : ev B.table B.inSup = .var 3
  inSrc : B.inBody.src B.table = lawsT B.l
  inView : B.inBody.view B.table = lawsT B.l
  inErase : B.inBody.erase = rinSel
  inActs : B.inBody.actsB = true
  inLets : B.inBody.letsB = true
  inOids : B.inBody.oids = [0, 1]
  inUses : B.inBody.PerUse (UseExact B.table exactCerts) (lawsT B.l) (lawsT B.l)
  outTy : ev B.table B.outTy = hTy
  outSup : ev B.table B.outSup = hSrc
  outSrc : B.outBody.src B.table = phT B.l
  outView : B.outBody.view B.table = phT B.l
  outErase : B.outBody.erase = phSel
  outActs : B.outBody.actsB = true
  outLets : B.outBody.letsB = true
  outOids : B.outBody.oids = [0, 1, 2]
  outUses : B.outBody.PerUse (UseExact B.table exactCerts) (phT B.l) (phT B.l)

/-- The rule's rows, built once per universe instance from the templates of section 6: first the
    input-laws record, then the derived-law record after it. (Irreducible only to keep the
    elaborator from unfolding the table during unification; `bankIn_eq` and `bankOut_eq` unfold
    them.) -/
@[irreducible] def bankIn (l : Lv4) : Located Table.empty 9 := encodeAt Table.empty (memIn l)

theorem bankIn_eq (l : Lv4) : bankIn l = encodeAt Table.empty (memIn l) := by unfold bankIn; rfl

@[irreducible] def bankOut (l : Lv4) : Located (bankIn l).ex.table 9 :=
  encodeAt (bankIn l).ex.table (memOut l)

theorem bankOut_eq (l : Lv4) : bankOut l = encodeAt (bankIn l).ex.table (memOut l) := by
  unfold bankOut; rfl

theorem bankIn_exact (l : Lv4) :
    (∀ b, (bankIn l).owner.close (bankIn l).ex.table b = (compTel l).close b) ∧
    (bankIn l).owner.admitB = true ∧
    ev (bankIn l).ex.table (bankIn l).nodeTy = μBTy ∧ ev (bankIn l).ex.table (bankIn l).sup = .var 3 ∧
    (bankIn l).body.src (bankIn l).ex.table = lawsT l ∧ (bankIn l).body.view (bankIn l).ex.table = lawsT l ∧
    (bankIn l).body.erase = rinSel ∧ (bankIn l).body.actsB = true ∧ (bankIn l).body.letsB = true ∧
    (bankIn l).body.oids = [0, 1] ∧
    (bankIn l).body.PerUse (UseExact (bankIn l).ex.table exactCerts) (lawsT l) (lawsT l) := by
  rw [bankIn_eq]
  exact encodeAt_exact Table.empty (memIn l) (shape_in l) (agree_refl _ _ (shape_in l))

theorem bankOut_exact (l : Lv4) :
    (∀ b, (bankOut l).owner.close (bankOut l).ex.table b = (compTel l).close b) ∧
    (bankOut l).owner.admitB = true ∧
    ev (bankOut l).ex.table (bankOut l).nodeTy = hTy ∧ ev (bankOut l).ex.table (bankOut l).sup = hSrc ∧
    (bankOut l).body.src (bankOut l).ex.table = phT l ∧ (bankOut l).body.view (bankOut l).ex.table = phT l ∧
    (bankOut l).body.erase = phSel ∧ (bankOut l).body.actsB = true ∧ (bankOut l).body.letsB = true ∧
    (bankOut l).body.oids = [0, 1, 2] ∧
    (bankOut l).body.PerUse (UseExact (bankOut l).ex.table exactCerts) (phT l) (phT l) := by
  rw [bankOut_eq]
  exact encodeAt_exact (bankIn l).ex.table (memOut l) (shape_out l) (agree_refl _ _ (shape_out l))

def mkBank (l : Lv4) : Bank :=
  { l, homes := (bankOut l).ex.homes, table := (bankOut l).ex.table,
    inOwner := (bankIn l).owner.mapR (bankOut l).ex.refs, inTy := (bankOut l).ex.map (bankIn l).nodeTy,
    inSup := (bankOut l).ex.map (bankIn l).sup, inBody := (bankIn l).body.mapR (bankOut l).ex.refs,
    outOwner := (bankOut l).owner, outTy := (bankOut l).nodeTy, outSup := (bankOut l).sup,
    outBody := (bankOut l).body }

theorem mkBank_exact (l : Lv4) : (mkBank l).Exact := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := bankIn_exact l
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := bankOut_exact l
  have hp := fun {r : Nat} (ref : Ref _ r) => (bankOut l).ex.preserved ref
  exact
    { inClose := fun b => (OTel.close_mapR _ hp _ b).trans (a1 b)
      outClose := b1
      inOwnerOk := (OTel.admitB_mapR _ _).trans a2
      outOwnerOk := b2
      inTy := (ev_map _ _).trans a3
      inSup := (ev_map _ _).trans a4
      inSrc := (Tmpl.src_mapR _ hp _).trans a5
      inView := (Tmpl.view_mapR _ hp _).trans a6
      inErase := (Tmpl.erase_mapR _ _).trans a7
      inActs := (Tmpl.actsB_mapR _ _).trans a8
      inLets := (Tmpl.letsB_mapR _ _).trans a9
      inOids := (Tmpl.oids_mapR _ _).trans a10
      inUses := Tmpl.perUse_mapR _ (useExact_mapR _ hp exactCerts) _ _ _ a11
      outTy := b3
      outSup := b4
      outSrc := b5
      outView := b6
      outErase := b7
      outActs := b8
      outLets := b9
      outOids := b10
      outUses := b11 }

/-- Rows appended after the rule's rows change nothing it decodes to. -/
def Bank.extend (B : Bank) (ex : Extension B.table) : Bank :=
  { l := B.l, homes := ex.homes, table := ex.table,
    inOwner := B.inOwner.mapR ex.refs, inTy := ex.map B.inTy, inSup := ex.map B.inSup,
    inBody := B.inBody.mapR ex.refs,
    outOwner := B.outOwner.mapR ex.refs, outTy := ex.map B.outTy, outSup := ex.map B.outSup,
    outBody := B.outBody.mapR ex.refs }

theorem Bank.extend_exact (B : Bank) (ex : Extension B.table) (h : B.Exact) : (B.extend ex).Exact := by
  have hp := fun {r : Nat} (ref : Ref _ r) => ex.preserved ref
  exact
    { inClose := fun b => (OTel.close_mapR _ hp _ b).trans (h.inClose b)
      outClose := fun b => (OTel.close_mapR _ hp _ b).trans (h.outClose b)
      inOwnerOk := (OTel.admitB_mapR _ _).trans h.inOwnerOk
      outOwnerOk := (OTel.admitB_mapR _ _).trans h.outOwnerOk
      inTy := (ev_map _ _).trans h.inTy
      inSup := (ev_map _ _).trans h.inSup
      inSrc := (Tmpl.src_mapR _ hp _).trans h.inSrc
      inView := (Tmpl.view_mapR _ hp _).trans h.inView
      inErase := (Tmpl.erase_mapR _ _).trans h.inErase
      inActs := (Tmpl.actsB_mapR _ _).trans h.inActs
      inLets := (Tmpl.letsB_mapR _ _).trans h.inLets
      inOids := (Tmpl.oids_mapR _ _).trans h.inOids
      inUses := Tmpl.perUse_mapR _ (useExact_mapR _ hp exactCerts) _ _ _ h.inUses
      outTy := (ev_map _ _).trans h.outTy
      outSup := (ev_map _ _).trans h.outSup
      outSrc := (Tmpl.src_mapR _ hp _).trans h.outSrc
      outView := (Tmpl.view_mapR _ hp _).trans h.outView
      outErase := (Tmpl.erase_mapR _ _).trans h.outErase
      outActs := (Tmpl.actsB_mapR _ _).trans h.outActs
      outLets := (Tmpl.letsB_mapR _ _).trans h.outLets
      outOids := (Tmpl.oids_mapR _ _).trans h.outOids
      outUses := Tmpl.perUse_mapR _ (useExact_mapR _ hp exactCerts) _ _ _ h.outUses }

/-! ## 8. Supplied maps, admission, the composite and its four clauses -/

section ArgsLemmas
variable {Γ : List Nat} {n : Nat}

theorem Args.ofFn_get : ∀ {r : Nat} (a : Args Γ n r), Args.ofFn a.get = a
  | 0, .nil => rfl
  | _+1, .cons o rest => by
    show Args.cons o (Args.ofFn (fun i => rest.get i)) = _
    rw [Args.ofFn_get rest]

theorem Args.ext {r : Nat} (a b : Args Γ n r) (h : a.get = b.get) : a = b := by
  rw [← Args.ofFn_get a, ← Args.ofFn_get b, h]

theorem substArgs_get {m : Nat} (σ : Fin n → Occ Γ m) : ∀ {r : Nat} (a : Args Γ n r) (j : Fin r),
    (ContextualViewDAG.substArgs σ a).get j = ContextualViewDAG.subst σ (a.get j)
  | 0, .nil, j => Fin.elim0 j
  | _+1, .cons o rest, j => by
    refine Fin.cases rfl (fun j' => ?_) j
    exact substArgs_get σ rest j'

theorem substArgs_ofFn {m r : Nat} (σ : Fin n → Occ Γ m) (f : Fin r → Occ Γ n) :
    ContextualViewDAG.substArgs σ (Args.ofFn f) = Args.ofFn (fun j => ContextualViewDAG.subst σ (f j)) := by
  apply Args.ext
  funext j
  rw [substArgs_get, ContextualViewDAG.Args.get_ofFn, ContextualViewDAG.Args.get_ofFn]

end ArgsLemmas

/-- A certificate with its universe instance, stored alongside the accepted `CertR` (which has no
    universe-instance list). -/
structure CertU (Γ : List Nat) (a : Nat) where
  base : CertR Γ a
  lvls : List ULevel

def CertU.act {Γ : List Nat} {a b : Nat} (τ : Fin a → Occ Γ b) (c : CertU Γ a) : CertU Γ b :=
  ⟨c.base.act τ, c.lvls⟩

/-- The proof term a class B certificate denotes: its declaration at its universe instance,
    applied to its decoded actuals. An exact certificate denotes no term. -/
def CertU.term {Γ : List Nat} (tb : Table Γ) {a : Nat} (c : CertU Γ a) : Option (Core a) :=
  match c.base with
  | .exact => none
  | .classB nm k acts => some (appArgs (.const nm c.lvls) k (evA tb acts))

/-- The role of supplied evidence: a scoped assumption of the instance context, or a proof term. -/
inductive Role where
  | assumption
  | proof
  deriving DecidableEq, Repr

/-- A supplied operation-preserving map at an instance context of arity `m`: its universe levels,
    its six port actuals (the chosen view; index 0 is φ, 1 μY, 2 μX, 3 Y, 4 X, 5 I), the source
    route of each port, a certificate per port with its universe instance, and optional evidence
    for its law with its role. -/
structure MapIn (Γ : List Nat) (m : Nat) where
  lv : Lv3
  ports : Args Γ m 6
  srcPorts : Args Γ m 6
  certs : Fin 6 → CertU Γ m
  ev : Option (Role × Occ Γ m)

section Decoded
variable {Γ : List Nat} (tb : Table Γ) {m : Nat}

/-- The map's law at its chosen view actuals, and at its source routes. -/
def MapIn.viewLaw (F : MapIn Γ m) : Core m := subst (evA tb F.ports) (lawSrc F.lv)
def MapIn.srcLaw (F : MapIn Γ m) : Core m := subst (evA tb F.srcPorts) (lawSrc F.lv)

/-- An exact port's route decodes to its view actual; a class B certificate is allowed only at the
    port `k` that meets the shared supplier. -/
def MapIn.routesB (F : MapIn Γ m) (k : Fin 6) : Bool :=
  (List.finRange 6).all fun j =>
    match (F.certs j).base with
    | .exact => coreEq (V6Structured.ev tb (F.srcPorts.get j)) (V6Structured.ev tb (F.ports.get j))
    | .classB .. => j == k

end Decoded

/-- Admission of the pair for the rule `B`: the rule's universe instance, an admitted instance
    context, and one actual shared middle: the same index, the same middle carrier and the same
    middle operation, each compared exactly after decoding; routes as in `MapIn.routesB`. Nothing
    here is a typing check. -/
def midB (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m) : Bool :=
  ctx.admitB && B.l == ⟨F.lv.u, F.lv.x, F.lv.y, G.lv.y⟩ && G.lv.u == F.lv.u && G.lv.x == F.lv.y &&
    coreEq (ev B.table (G.ports.get 5)) (ev B.table (F.ports.get 5)) &&
    coreEq (ev B.table (G.ports.get 4)) (ev B.table (F.ports.get 3)) &&
    coreEq (ev B.table (G.ports.get 2)) (ev B.table (F.ports.get 1)) &&
    F.routesB B.table 1 && G.routesB B.table 2

/-- Lineage of each composite port (`true`: the first map `F`): g ← G.φ, f ← F.φ, μC ← G.μY,
    μB ← F.μY, μA ← F.μX, C ← G.Y, B ← F.Y, A ← F.X, I ← F.I. -/
def glueSel : Fin 9 → Bool × Fin 6
  | ⟨0, _⟩ => (false, 0)
  | ⟨1, _⟩ => (true, 0)
  | ⟨2, _⟩ => (false, 1)
  | ⟨3, _⟩ => (true, 1)
  | ⟨4, _⟩ => (true, 2)
  | ⟨5, _⟩ => (false, 3)
  | ⟨6, _⟩ => (true, 3)
  | ⟨7, _⟩ => (true, 4)
  | _ => (true, 5)

def pick {α : Type} (s : Bool × Fin 6) (a b : Fin 6 → α) : α := if s.1 then a s.2 else b s.2

/-- The composite's actual vector: a selection of the inputs' own occurrences, nothing decoded. -/
def glue {Γ : List Nat} {m : Nat} (a b : Args Γ m 6) : Args Γ m 9 :=
  Args.ofFn (fun j => pick (glueSel j) a.get b.get)

/-- The generic proof's actuals in application order: I, A, B, C, μA, μB, μC, f, g, hf, hg. -/
def certArgs {Γ : List Nat} {m : Nat} (σ : Args Γ m 9) (hf hg : Occ Γ m) : Args Γ m 11 :=
  Args.ofFn (fun j => if h : j.val < 9 then σ.get ⟨8 - j.val, by omega⟩ else if j.val = 9 then hf else hg)

/-- The composite: the retained inputs, the instance context, the glued actual vector, and the
    optional evidence (a class B certificate by the generic proof, with its universe instance). -/
structure Comp (B : Bank) where
  m : Nat
  ctx : OTel B.homes m
  F : MapIn B.homes m
  G : MapIn B.homes m
  σ : Args B.homes m 9
  ev : Option (CertU B.homes m)

def evComp {Γ : List Nat} {m : Nat} (l : Lv4) (σ : Args Γ m 9) :
    Option (Role × Occ Γ m) → Option (Role × Occ Γ m) → Option (CertU Γ m)
  | some (_, hf), some (_, hg) => some ⟨.classB dpcName 11 (certArgs σ hf hg), [l.u, l.a, l.b, l.c]⟩
  | _, _ => none

/-- The composite of a pair, as finite data: the inputs kept, their occurrences selected into one
    actual vector, and evidence formed only from the inputs' own evidence. Nothing is decoded. -/
def mkComp (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m) : Comp B :=
  { m, ctx, F, G, σ := glue F.ports G.ports, ev := evComp B.l (glue F.ports G.ports) F.ev G.ev }

/-- The partial operation. It forms the composite exactly when the pair is admitted; evidence is
    attached only when both inputs carry evidence. -/
def compose (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m) : Option (Comp B) :=
  if midB B ctx F G then some (mkComp B ctx F G) else none

def Comp.inInst {B : Bank} (K : Comp B) : SInst := ⟨B.rin, K.m, K.ctx, K.σ⟩
def Comp.outInst {B : Bank} (K : Comp B) : SInst := ⟨B.rout, K.m, K.ctx, K.σ⟩

/-- The weakening of an instance context into `e` local binders. -/
def wkMap {Γ : List Nat} (m e : Nat) : Fin m → Occ Γ (m + e) := fun j => .var (j.addNat e)
def wkOcc {Γ : List Nat} {m : Nat} (e : Nat) (o : Occ Γ m) : Occ Γ (m + e) :=
  ContextualViewDAG.subst (wkMap m e) o

/-- The inputs' own source routes and certificates, installed at the two uses of the shared
    supplier: use 0 (in `Pf`) gets F's μY route, use 1 (in `Pg`) gets G's μX route. -/
def install {Γ : List Nat} {m : Nat} (F G : MapIn Γ m) (e : Nat) (u : UseR Γ m e) : UseR Γ m e :=
  if u.oid = 0 then
    { u with src := wkOcc e (F.srcPorts.get 1), srcCert := (F.certs 1).base.act (wkMap m e) }
  else if u.oid = 1 then
    { u with src := wkOcc e (G.srcPorts.get 2), srcCert := (G.certs 2).base.act (wkMap m e) }
  else u

/-- The retained input laws, read with the one node `μB`, with the inputs' routes at its uses. -/
def Comp.lawsIn {B : Bank} (K : Comp B) : SRec :=
  { K.inInst.apply with body := K.inInst.apply.body.mapUses (install K.F K.G) }

/-- The derived law, read with the node `h`. Its node value is the composite function. -/
def Comp.law {B : Bank} (K : Comp B) : SRec := K.outInst.apply

/-- The universe instances stored alongside the two installed use certificates. -/
def Comp.useLvls {B : Bank} (K : Comp B) (oid : Nat) : List ULevel :=
  if oid = 0 then (K.F.certs 1).lvls else if oid = 1 then (K.G.certs 2).lvls else []

/-! ### Decoding the glued vector -/

section Glue
variable {Γ : List Nat} (tb : Table Γ) {m : Nat}

theorem ev_var {k : Nat} (i : Fin k) : ev tb (.var i : Occ Γ k) = .var i := rfl

theorem evA_glue (a b : Args Γ m 6) :
    evA tb (glue a b) = fun j => pick (glueSel j) (evA tb a) (evA tb b) := by
  rw [evA_eq_get, evA_eq_get tb a, evA_eq_get tb b]
  funext j
  simp only [glue, ContextualViewDAG.Args.get_ofFn, pick]
  split <;> rfl

/-- The first map's ports are read off the glued vector unchanged. -/
theorem glue_F (a b : Args Γ m 6) : (fun j => evA tb (glue a b) (ιFn j)) = evA tb a := by
  rw [evA_glue]
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- The second map's ports are read off the glued vector, given the shared index, carrier and
    operation (exact decoded equalities). -/
theorem glue_G (a b : Args Γ m 6) (h5 : evA tb b 5 = evA tb a 5) (h4 : evA tb b 4 = evA tb a 3)
    (h2 : evA tb b 2 = evA tb a 1) : (fun j => evA tb (glue a b) (ιGn j)) = evA tb b := by
  rw [evA_glue]
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => exact h2.symm
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => exact h4.symm
  | ⟨5, _⟩ => exact h5.symm

theorem glue_get (a b : Args Γ m 6) (j : Fin 9) : (glue a b).get j = pick (glueSel j) a.get b.get := by
  simp only [glue, ContextualViewDAG.Args.get_ofFn]

theorem ev_wkOcc (e : Nat) (o : Occ Γ m) : ev tb (wkOcc e o) = subst (weakActs m e) (ev tb o) :=
  ev_substOcc tb (wkMap m e) 0 o

theorem routes_eq (F : MapIn Γ m) (k : Fin 6) (h : F.routesB tb k = true) (j : Fin 6) (hj : j ≠ k) :
    evA tb F.srcPorts j = evA tb F.ports j := by
  unfold MapIn.routesB at h
  rw [List.all_eq_true] at h
  have hj' := h j (List.mem_finRange j)
  rw [evA_eq_get, evA_eq_get tb F.ports]
  revert hj'
  cases (F.certs j).base with
  | exact => intro hj'; exact (coreEq_iff _ _).mp hj'
  | classB nm k' acts => intro hj'; exact absurd (eq_of_beq hj') hj

end Glue

/-! ### The route lemmas: filling the supplier's use with a route gives the law at the routes -/

theorem weak3 {m : Nat} (r : Core m) :
    subst (weakActs m 3) r = rename Fin.succ (rename Fin.succ (rename Fin.succ r)) := by
  rw [rename_comp, rename_comp, rename_eq_subst]
  rfl

theorem law_route_F (l : Lv3) {m : Nat} (P : Fin 6 → Core m) (r : Core m) (O : Fam false m)
    (hO : O 3 0 = subst (weakActs m 3) r) :
    fillD 0 (subst P (lawSrc l)) pfSel O = subst (fun j => if j.val = 1 then r else P j) (lawSrc l) := by
  simp only [lawSrc, subst, fillD, pfSel, Nat.reduceAdd, hO, weak3]
  rfl

theorem law_route_G (l : Lv3) {m : Nat} (P : Fin 6 → Core m) (r : Core m) (O : Fam false m)
    (hO : O 3 1 = subst (weakActs m 3) r) :
    fillD 0 (subst P (lawSrc l)) pgSel O = subst (fun j => if j.val = 2 then r else P j) (lawSrc l) := by
  simp only [lawSrc, subst, fillD, pgSel, Nat.reduceAdd, hO, weak3]
  rfl

/-! ### Per-use lemmas for templates -/

section PerUse
variable {Γ : List Nat} (tb : Table Γ) {n : Nat}

theorem Tmpl.mapUses_view (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (hv : ∀ e u, (φ e u).view = u.view) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).view tb = t.view tb := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => simp only [Tmpl.mapUses, Tmpl.view, hv]
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.view, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.view, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.view, ih]

omit tb in
theorem Tmpl.mapUses_erase (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (ho : ∀ e u, (φ e u).oid = u.oid) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).erase = t.erase := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => simp only [Tmpl.mapUses, Tmpl.erase, ho]
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.erase, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.erase, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.erase, ih]

omit tb in
theorem Tmpl.mapUses_actsB (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (ha : ∀ e u, (φ e u).acts = u.acts) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).actsB = t.actsB := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => simp only [Tmpl.mapUses, Tmpl.actsB, ha]
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.actsB, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.actsB, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.actsB, ih]

omit tb in
theorem Tmpl.mapUses_letsB (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).letsB = t.letsB := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.letsB, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.letsB, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.letsB, ih]

theorem Tmpl.mapUses_reading (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).reading tb = t.reading tb := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.reading, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.reading, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.reading, ih]

theorem Tmpl.mapUses_shared (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (ha : ∀ e u, (φ e u).acts = u.acts)
    (p : Core n) : ∀ {e : Nat} (t : Tmpl Γ n e), (t.mapUses φ).shared tb p = t.shared tb p := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => simp only [Tmpl.mapUses, Tmpl.shared, ha]
  | app g a ihg iha => simp only [Tmpl.mapUses, Tmpl.shared, ihg, iha]
  | pi x d b ih => simp only [Tmpl.mapUses, Tmpl.shared, ih]
  | letE nm nd ty v b ih => simp only [Tmpl.mapUses, Tmpl.shared, ih]

omit tb in
theorem Tmpl.mapUses_uses (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) :
    ∀ {e : Nat} (t : Tmpl Γ n e),
      (t.mapUses φ).uses = t.uses.map (fun y => ⟨y.e, y.path, y.scope, φ y.e y.use⟩) := by
  intro e t
  induction t with
  | leaf o => rfl
  | hole u => rfl
  | app g a ihg iha =>
    simp only [Tmpl.mapUses, Tmpl.uses, ihg, iha, List.map_append, List.map_map]
    rfl
  | pi x d b ih =>
    simp only [Tmpl.mapUses, Tmpl.uses, ih, List.map_map]
    rfl
  | letE nm nd ty v b ih =>
    simp only [Tmpl.mapUses, Tmpl.uses, ih, List.map_map]
    rfl

omit tb in
theorem Tmpl.mapUses_oids (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (ho : ∀ e u, (φ e u).oid = u.oid)
    {e : Nat} (t : Tmpl Γ n e) : (t.mapUses φ).oids = t.oids := by
  simp only [Tmpl.oids, Tmpl.mapUses_uses, List.map_map]
  exact List.map_congr_left (fun y _ => ho y.e y.use)

/-- Replacing the uses' source origins fills the source at the selected positions. -/
theorem Tmpl.mapUses_src (φ : (e : Nat) → UseR Γ n e → UseR Γ n e) (O : Fam false n) :
    ∀ {e : Nat} (t : Tmpl Γ n e), (∀ y ∈ t.uses, ev tb (φ y.e y.use).src = O y.e y.use.oid) →
      (t.mapUses φ).src tb = fillD e (t.src tb) t.erase O := by
  intro e t
  induction t with
  | leaf o => intro _; rfl
  | hole u =>
    intro h
    exact h ⟨_, [], [], u⟩ (List.mem_singleton_self _)
  | app g a ihg iha =>
    intro h
    simp only [Tmpl.mapUses, Tmpl.src, Tmpl.erase, fillD]
    rw [ihg (fun y hy => (h _ (List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)) :)),
      iha (fun y hy => (h _ (List.mem_append_right _ (List.mem_map.2 ⟨y, hy, rfl⟩)) :))]
  | pi x d b ih =>
    intro h
    simp only [Tmpl.mapUses, Tmpl.src, Tmpl.erase, fillD]
    rw [ih (fun y hy => (h _ (List.mem_map.2 ⟨y, hy, rfl⟩) :))]
  | letE nm nd ty v b ih =>
    intro h
    simp only [Tmpl.mapUses, Tmpl.src, Tmpl.erase, fillD]
    rw [ih (fun y hy => (h _ (List.mem_map.2 ⟨y, hy, rfl⟩) :))]

/-- Where the view carries `O` at the selected positions, every use's view origin denotes it. -/
theorem Tmpl.view_fits (O : Fam false n) : ∀ {e : Nat} (t : Tmpl Γ n e),
    FitsD e (t.view tb) t.erase O → ∀ y ∈ t.uses, ev tb y.use.view = O y.e y.use.oid := by
  intro e t
  induction t with
  | leaf o => intro _ y hy; simp only [Tmpl.uses, List.not_mem_nil] at hy
  | hole u =>
    intro h y hy
    simp only [Tmpl.uses, List.mem_singleton] at hy
    subst hy
    exact h
  | app g a ihg iha =>
    intro h y hy
    simp only [Tmpl.view, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
    · exact ihg h.1 y' hy'
    · exact iha h.2 y' hy'
  | pi x d b ih =>
    intro h y hy
    simp only [Tmpl.view, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'
  | letE nm nd ty v b ih =>
    intro h y hy
    simp only [Tmpl.view, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'

/-- Every admitted use's actual vector denotes the prefix weakening. -/
theorem Tmpl.acts_uses : ∀ {e : Nat} (t : Tmpl Γ n e), t.actsB = true →
    ∀ y ∈ t.uses, evA tb y.use.acts = weakActs n y.e := by
  intro e t
  induction t with
  | leaf o => intro _ y hy; simp only [Tmpl.uses, List.not_mem_nil] at hy
  | hole u =>
    intro h y hy
    simp only [Tmpl.uses, List.mem_singleton] at hy
    subst hy
    exact evA_weak tb u.acts h
  | app g a ihg iha =>
    intro h y hy
    simp only [Tmpl.actsB, Bool.and_eq_true] at h
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
    · exact ihg h.1 y' hy'
    · exact iha h.2 y' hy'
  | pi x d b ih =>
    intro h y hy
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'
  | letE nm nd ty v b ih =>
    intro h y hy
    simp only [Tmpl.actsB] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'

omit tb in
/-- A per-use property along the template holds at every listed use (for some subterms). -/
theorem Tmpl.perUse_uses (Q : (e : Nat) → UseR Γ n e → Core (n + e) → Core (n + e) → Prop) :
    ∀ {e : Nat} (t : Tmpl Γ n e) (X Y : Core (n + e)), t.PerUse Q X Y →
      ∀ y ∈ t.uses, ∃ X' Y', Q y.e y.use X' Y' := by
  intro e t
  induction t with
  | leaf o => intro _ _ _ y hy; simp only [Tmpl.uses, List.not_mem_nil] at hy
  | hole u =>
    intro X Y h y hy
    simp only [Tmpl.uses, List.mem_singleton] at hy
    subst hy
    exact ⟨X, Y, h⟩
  | app g a ihg iha =>
    intro X Y h y hy
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    cases X <;> cases Y <;> simp only [Tmpl.PerUse] at h
    rcases hy with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
    · exact ihg _ _ h.1 y' hy'
    · exact iha _ _ h.2 y' hy'
  | pi x d b ih =>
    intro X Y h y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    cases X <;> cases Y <;> simp only [Tmpl.PerUse] at h
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih _ _ h y' hy'
  | letE nm nd ty v b ih =>
    intro X Y h y hy
    simp only [Tmpl.uses, List.mem_map] at hy
    cases X <;> cases Y <;> simp only [Tmpl.PerUse] at h
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih _ _ h y' hy'

end PerUse

/-! ### Clause 1: exact interpretation -/

/-- `a ∧ b` as a Core term. -/
def andT {k : Nat} (a b : Core k) : Core k := .app (.app (.const ``And []) a) b

theorem fill_laws {m : Nat} (l : Lv4) (σ : Fin 9 → Core m) (O : Fam false m) :
    fillD 0 (subst σ (lawsT l)) rinSel O =
      andT (fillD 0 (subst σ (pfT l)) pfSel O) (fillD 0 (subst σ (pgT l)) pgSel O) := by
  simp only [lawsT, rinSel, subst, fillD, andT]

section Clause1
variable (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m)

theorem midB_parts (h : midB B ctx F G = true) :
    ctx.admitB = true ∧ B.l = ⟨F.lv.u, F.lv.x, F.lv.y, G.lv.y⟩ ∧ G.lv.u = F.lv.u ∧ G.lv.x = F.lv.y ∧
      evA B.table G.ports 5 = evA B.table F.ports 5 ∧ evA B.table G.ports 4 = evA B.table F.ports 3 ∧
      evA B.table G.ports 2 = evA B.table F.ports 1 ∧
      F.routesB B.table 1 = true ∧ G.routesB B.table 2 = true := by
  simp only [midB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [evA_eq_get, evA_eq_get B.table F.ports]
  exact ⟨h1, h2, h3, h4, (coreEq_iff _ _).mp h5, (coreEq_iff _ _).mp h6, (coreEq_iff _ _).mp h7, h8, h9⟩

theorem lv_left (h : midB B ctx F G = true) : B.l.left = F.lv := by
  rw [(midB_parts B ctx F G h).2.1]
  rfl

theorem lv_right (h : midB B ctx F G = true) : B.l.right = G.lv := by
  obtain ⟨_, h2, h3, h4, _⟩ := midB_parts B ctx F G h
  rw [h2]
  show (⟨F.lv.u, F.lv.y, G.lv.y⟩ : Lv3) = G.lv
  rw [← h3, ← h4]

/-- The first input law, read off the glued vector, is the first map's law at its view ports. -/
theorem pf_inst (h : midB B ctx F G = true) :
    subst (evA B.table (glue F.ports G.ports)) (pfT B.l) = F.viewLaw B.table := by
  rw [pfT, subst_comp, lv_left B ctx F G h]
  exact congrArg (fun g => subst g (lawSrc F.lv)) (glue_F B.table F.ports G.ports)

theorem pg_inst (h : midB B ctx F G = true) :
    subst (evA B.table (glue F.ports G.ports)) (pgT B.l) = G.viewLaw B.table := by
  obtain ⟨_, _, _, _, h5, h4, h2, _⟩ := midB_parts B ctx F G h
  rw [pgT, subst_comp, lv_right B ctx F G h]
  exact congrArg (fun g => subst g (lawSrc G.lv)) (glue_G B.table F.ports G.ports h5 h4 h2)

theorem glue_mid : evA B.table (glue F.ports G.ports) 3 = evA B.table F.ports 1 := by
  rw [evA_glue]
  rfl

theorem rout_admitB (hB : B.Exact) : B.rout.admitB = true := by
  simp only [SRec.admitB, Bank.rout, Tmpl.admitB, hB.outOwnerOk, hB.outActs, hB.outLets, hB.outOids]
  rfl

theorem rin_admitB (hB : B.Exact) : B.rin.admitB = true := by
  simp only [SRec.admitB, Bank.rin, Tmpl.admitB, hB.inOwnerOk, hB.inActs, hB.inLets, hB.inOids]
  rfl

/-- Clause 1 for the derived law: its record decodes to the composite function and to `Ph`
    instantiated at the glued actuals, through the one template `phT`. -/
theorem law_decode (hB : B.Exact) (hm : midB B ctx F G = true) :
    (mkComp B ctx F G).law.admitB = true ∧ (mkComp B ctx F G).law.nodeName = `h ∧
      ev B.table (mkComp B ctx F G).law.nodeTy = subst (evA B.table (glue F.ports G.ports)) hTy ∧
      ev B.table (mkComp B ctx F G).law.sup = subst (evA B.table (glue F.ports G.ports)) hSrc ∧
      (mkComp B ctx F G).law.source = ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) (phT B.l)) ∧
      (mkComp B ctx F G).law.view = ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) (phT B.l)) ∧
      (mkComp B ctx F G).law.shared = ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) (phT B.l)) ∧
      (mkComp B ctx F G).law.reading = ctx.close B.table (.letE `h false
        (subst (evA B.table (glue F.ports G.ports)) hTy) (subst (evA B.table (glue F.ports G.ports)) hSrc)
        (subst (liftSub (evA B.table (glue F.ports G.ports))) (consumer (phT B.l) phSel))) := by
  have hI : (mkComp B ctx F G).outInst.admitB = true := by
    simp only [SInst.admitB, Comp.outInst, mkComp, rout_admitB B hB, (midB_parts B ctx F G hm).1,
      Bool.and_self]
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := SInst.apply_decode _ hI
  have hσ := evA_eq_get B.table (glue F.ports G.ports)
  have hs := ev_substOcc B.table (glue F.ports G.ports).get 0 B.outSup
  have ht := ev_substOcc B.table (glue F.ports G.ports).get 0 B.outTy
  simp only [liftOccN, liftSubN] at hs ht
  have hsh : B.outBody.shared B.table (ev B.table B.outSup) = phT B.l := by
    rw [B.outBody.shared_fill B.table _ hB.outActs, hB.outSrc, hB.outErase, hB.outSup]
    exact fillD_self _ 0 _ _ (fits_out B.l)
  have hrd : B.outBody.reading B.table = consumer (phT B.l) phSel := by
    rw [Tmpl.reading_eq, hB.outSrc, hB.outErase]
    rfl
  refine ⟨h1, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.outTy) = _
    rw [ht, hB.outTy, ← hσ]
  · show ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.outSup) = _
    rw [hs, hB.outSup, ← hσ]
  · show (mkComp B ctx F G).outInst.apply.source = _
    rw [h2]
    exact congrArg (fun t => ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) t)) hB.outSrc
  · show (mkComp B ctx F G).outInst.apply.view = _
    rw [h3]
    exact congrArg (fun t => ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) t)) hB.outView
  · show (mkComp B ctx F G).outInst.apply.shared = _
    rw [h4]
    exact congrArg (fun t => ctx.close B.table (subst (evA B.table (glue F.ports G.ports)) t)) hsh
  · show (mkComp B ctx F G).outInst.apply.reading = _
    rw [h5]
    show ctx.close B.table (.letE `h false (subst (evA B.table (glue F.ports G.ports)) (ev B.table B.outTy))
      (subst (evA B.table (glue F.ports G.ports)) (ev B.table B.outSup))
      (subst (liftSub (evA B.table (glue F.ports G.ports))) (B.outBody.reading B.table))) = _
    rw [hB.outTy, hB.outSup, hrd]

/-- The inputs' routes and certificates installed at the two uses keep each use's identity, view
    origin, actual vector and view certificate. -/
theorem install_view (e : Nat) (u : UseR B.homes m e) : (install F G e u).view = u.view := by
  unfold install; split
  · rfl
  · split <;> rfl

theorem install_oid (e : Nat) (u : UseR B.homes m e) : (install F G e u).oid = u.oid := by
  unfold install; split
  · rfl
  · split <;> rfl

theorem install_acts (e : Nat) (u : UseR B.homes m e) : (install F G e u).acts = u.acts := by
  unfold install; split
  · rfl
  · split <;> rfl

theorem install_viewCert (e : Nat) (u : UseR B.homes m e) : (install F G e u).viewCert = u.viewCert := by
  unfold install; split
  · rfl
  · split <;> rfl

/-- The origins installed at the shared supplier's two uses: F's μY route, then G's μX route. -/
def routeFam (tb : Table B.homes) : Fam false m := fun e i =>
  if i = 0 then subst (weakActs m e) (evA tb F.srcPorts 1) else subst (weakActs m e) (evA tb G.srcPorts 2)

theorem inAct_uses_oid (hB : B.Exact) (y : UseEntry B.homes m)
    (hy : y ∈ (B.inBody.act (glue F.ports G.ports).get).uses) : y.use.oid = 0 ∨ y.use.oid = 1 := by
  have h1 : y.use.oid ∈ (B.inBody.act (glue F.ports G.ports).get).oids := List.mem_map_of_mem hy
  rw [Tmpl.act_oids, hB.inOids] at h1
  simpa using h1

theorem install_src (hB : B.Exact) (y : UseEntry B.homes m)
    (hy : y ∈ (B.inBody.act (glue F.ports G.ports).get).uses) :
    ev B.table (install F G y.e y.use).src = routeFam B F G B.table y.e y.use.oid := by
  rcases inAct_uses_oid B F G hB y hy with h | h
  · simp only [install, h, if_true, routeFam, ev_wkOcc, evA_eq_get]
  · simp only [install, h, routeFam, ev_wkOcc, evA_eq_get, Nat.one_ne_zero, if_false, if_true]

/-- Clause 1 for the retained input laws: the record with node `μB` decodes to the conjunction of
    the two maps' own laws, at their source routes (source) and at their chosen views (view). -/
theorem lawsIn_decode (hB : B.Exact) (hm : midB B ctx F G = true) :
    (mkComp B ctx F G).lawsIn.admitB = true ∧ (mkComp B ctx F G).lawsIn.nodeName = `μB ∧
      ev B.table (mkComp B ctx F G).lawsIn.nodeTy = subst (evA B.table (glue F.ports G.ports)) μBTy ∧
      ev B.table (mkComp B ctx F G).lawsIn.sup = evA B.table F.ports 1 ∧
      ev B.table (mkComp B ctx F G).lawsIn.sup = evA B.table G.ports 2 ∧
      (mkComp B ctx F G).lawsIn.source = ctx.close B.table (andT (F.srcLaw B.table) (G.srcLaw B.table)) ∧
      (mkComp B ctx F G).lawsIn.view = ctx.close B.table (andT (F.viewLaw B.table) (G.viewLaw B.table)) ∧
      (mkComp B ctx F G).lawsIn.shared = ctx.close B.table (andT (F.viewLaw B.table) (G.viewLaw B.table)) ∧
      (mkComp B ctx F G).lawsIn.reading = ctx.close B.table (.letE `μB false
        (subst (evA B.table (glue F.ports G.ports)) μBTy) (evA B.table F.ports 1)
        (subst (liftSub (evA B.table (glue F.ports G.ports))) (consumer (lawsT B.l) rinSel))) := by
  obtain ⟨hc, _, _, _, _, _, h2, hrF, hrG⟩ := midB_parts B ctx F G hm
  have hI : (mkComp B ctx F G).inInst.admitB = true := by
    simp only [SInst.admitB, Comp.inInst, mkComp, rin_admitB B hB, hc, Bool.and_self]
  obtain ⟨_, _, h3, h4, h5, _, _⟩ := SInst.apply_decode _ hI
  have hσ := evA_eq_get B.table (glue F.ports G.ports)
  have hs := ev_substOcc B.table (glue F.ports G.ports).get 0 B.inSup
  have ht := ev_substOcc B.table (glue F.ports G.ports).get 0 B.inTy
  simp only [liftOccN, liftSubN] at hs ht
  have hsup : ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.inSup) =
      evA B.table F.ports 1 := by
    rw [hs, hB.inSup, ← hσ]
    exact glue_mid B F G
  let t := B.inBody.act (glue F.ports G.ports).get
  have hstr := B.inBody.act_structure (glue F.ports G.ports).get
  have hlaw : subst (evA B.table (glue F.ports G.ports)) (lawsT B.l) =
      andT (F.viewLaw B.table) (G.viewLaw B.table) := by
    show andT (subst _ (pfT B.l)) (subst _ (pgT B.l)) = _
    rw [pf_inst B ctx F G hm, pg_inst B ctx F G hm]
  have hsh : B.inBody.shared B.table (ev B.table B.inSup) = lawsT B.l := by
    rw [B.inBody.shared_fill B.table _ hB.inActs, hB.inSrc, hB.inErase, hB.inSup]
    exact fillD_self _ 0 _ _ (fits_in B.l)
  have eF : (fun j : Fin 6 => if j.val = 1 then evA B.table F.srcPorts 1 else evA B.table F.ports j) =
      evA B.table F.srcPorts := by
    funext j
    split
    · exact congrArg _ (Fin.ext (by simp only [Fin.val_one]; omega))
    · exact (routes_eq B.table F 1 hrF j (fun hj => by subst hj; simp_all)).symm
  have eG : (fun j : Fin 6 => if j.val = 2 then evA B.table G.srcPorts 2 else evA B.table G.ports j) =
      evA B.table G.srcPorts := by
    funext j
    split
    · exact congrArg _ (Fin.ext (by simp only [Fin.val_two]; omega))
    · exact (routes_eq B.table G 2 hrG j (fun hj => by subst hj; simp_all)).symm
  refine ⟨?_, rfl, ?_, hsup, hsup.trans h2.symm, ?_, ?_, ?_, ?_⟩
  · show (ctx.admitB && ((t.mapUses (install F G)).actsB && (t.mapUses (install F G)).letsB &&
      nodupB (t.mapUses (install F G)).oids)) = true
    rw [Tmpl.mapUses_actsB _ (install_acts B F G), Tmpl.mapUses_letsB, Tmpl.mapUses_oids _ (install_oid B F G),
      hstr.2.1, hstr.2.2.1, hB.inLets, Tmpl.act_oids, hB.inOids, hc]
    rfl
  · show ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.inTy) = _
    rw [ht, hB.inTy, ← hσ]
  · -- the source: each use's own route is filled in at the shared supplier's position
    show ctx.close B.table ((t.mapUses (install F G)).src B.table) = _
    refine congrArg (OTel.close B.table ctx) ?_
    rw [Tmpl.mapUses_src B.table _ (routeFam B F G B.table) t (fun y hy => install_src B F G hB y hy),
      Tmpl.act_src, hstr.1, hB.inSrc, hB.inErase, liftSubN_zero, ← hσ, fill_laws,
      pf_inst B ctx F G hm, pg_inst B ctx F G hm]
    unfold MapIn.viewLaw
    rw [law_route_F F.lv (evA B.table F.ports) (evA B.table F.srcPorts 1) _ (by simp only [routeFam, if_true]),
      law_route_G G.lv (evA B.table G.ports) (evA B.table G.srcPorts 2) _
        (by simp only [routeFam, Nat.one_ne_zero, if_false]), eF, eG]
    rfl
  · show ctx.close B.table ((t.mapUses (install F G)).view B.table) = _
    refine congrArg (OTel.close B.table ctx) ?_
    rw [Tmpl.mapUses_view B.table _ (install_view B F G), Tmpl.act_view, hB.inView, liftSubN_zero, ← hσ, hlaw]
  · show ctx.close B.table ((t.mapUses (install F G)).shared B.table
      (ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.inSup))) = _
    refine congrArg (OTel.close B.table ctx) ?_
    rw [Tmpl.mapUses_shared B.table _ (install_acts B F G), hs, Tmpl.act_shared B.table _ _ _ hB.inActs, hsh,
      liftSubN_zero, ← hσ, hlaw]
  · show ctx.close B.table (.letE `μB false (ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.inTy))
      (ev B.table (ContextualViewDAG.subst (glue F.ports G.ports).get B.inSup))
      ((t.mapUses (install F G)).reading B.table)) = _
    refine congrArg (OTel.close B.table ctx) ?_
    rw [Tmpl.mapUses_reading, hsup, ht, hB.inTy, ← hσ, Tmpl.act_reading, liftSubN_zero, Tmpl.reading_eq,
      hB.inSrc, hB.inErase, ← hσ]
    rfl

end Clause1

/-! ### Clause 2: actual incidence, per-use recovery and retained lineage -/

section SrcFits
variable {Γ : List Nat} (tb : Table Γ) {n : Nat}

/-- Where the source carries `O` at the selected positions, every use's source origin denotes it. -/
theorem Tmpl.src_fits (O : Fam false n) : ∀ {e : Nat} (t : Tmpl Γ n e),
    FitsD e (t.src tb) t.erase O → ∀ y ∈ t.uses, ev tb y.use.src = O y.e y.use.oid := by
  intro e t
  induction t with
  | leaf o => intro _ y hy; simp only [Tmpl.uses, List.not_mem_nil] at hy
  | hole u =>
    intro h y hy
    simp only [Tmpl.uses, List.mem_singleton] at hy
    subst hy
    exact h
  | app g a ihg iha =>
    intro h y hy
    simp only [Tmpl.src, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨y', hy', rfl⟩ | ⟨y', hy', rfl⟩
    · exact ihg h.1 y' hy'
    · exact iha h.2 y' hy'
  | pi x d b ih =>
    intro h y hy
    simp only [Tmpl.src, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'
  | letE nm nd ty v b ih =>
    intro h y hy
    simp only [Tmpl.src, Tmpl.erase, FitsD] at h
    simp only [Tmpl.uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ih h y' hy'

theorem CertR.exact_of_dec {a : Nat} (c : CertR Γ a) (h : c.dec tb = .exact) : c = .exact := by
  cases c with
  | exact => rfl
  | classB nm k acts => simp [CertR.dec] at h

/-- The rule's uses carry exact certificates, and the action keeps them exact. -/
theorem act_certs_exact {m : Nat} (σ : Fin n → Occ Γ m) (t : Tmpl Γ n 0) (X Y : Core n)
    (h : t.PerUse (UseExact tb (fun _ _ => (.exact, .exact))) X Y) :
    ∀ y ∈ (t.act σ).uses, y.use.srcCert = .exact ∧ y.use.viewCert = .exact := by
  intro y hy
  rw [(t.act_structure σ).2.2.2, List.mem_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨_, _, hq⟩ := Tmpl.perUse_uses _ t _ _ h y' hy'
  have h1 := CertR.exact_of_dec tb _ hq.2.2.2.1
  have h2 := CertR.exact_of_dec tb _ hq.2.2.2.2
  show (y'.use.act σ).srcCert = _ ∧ (y'.use.act σ).viewCert = _
  simp only [UseR.act, h1, h2, CertR.act, and_self]

end SrcFits

theorem wk_dec {Γ : List Nat} (tb : Table Γ) {m e : Nat} (c : CertR Γ m) :
    (c.act (wkMap m e)).dec tb = (c.dec tb).subst (weakActs m e) := by
  rw [CertR.dec_act]
  rfl

section Clause2
variable (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m)

/-- Per use of the one node `μB` in the kept input laws: its view origin is the shared supplier
    at the use, its source origin and source certificate are the input's own route and
    certificate (use 0: F's μY; use 1: G's μX), with the certificate's universe instance kept. -/
theorem lawsIn_uses (hB : B.Exact) :
    (mkComp B ctx F G).lawsIn.body.oids = [0, 1] ∧
    ∀ y ∈ (mkComp B ctx F G).lawsIn.body.uses,
      ev B.table y.use.view = subst (weakActs m y.e) (evA B.table F.ports 1) ∧
      evA B.table y.use.acts = weakActs m y.e ∧ y.use.viewCert = .exact ∧
      ((y.use.oid = 0 ∧ ev B.table y.use.src = subst (weakActs m y.e) (evA B.table F.srcPorts 1) ∧
          y.use.srcCert = (F.certs 1).base.act (wkMap m y.e) ∧
          y.use.srcCert.dec B.table = ((F.certs 1).base.dec B.table).subst (weakActs m y.e) ∧
          (mkComp B ctx F G).useLvls 0 = (F.certs 1).lvls) ∨
        (y.use.oid = 1 ∧ ev B.table y.use.src = subst (weakActs m y.e) (evA B.table G.srcPorts 2) ∧
          y.use.srcCert = (G.certs 2).base.act (wkMap m y.e) ∧
          y.use.srcCert.dec B.table = ((G.certs 2).base.dec B.table).subst (weakActs m y.e) ∧
          (mkComp B ctx F G).useLvls 1 = (G.certs 2).lvls)) := by
  have hstr := B.inBody.act_structure (glue F.ports G.ports).get
  have hσ := evA_eq_get B.table (glue F.ports G.ports)
  refine ⟨?_, ?_⟩
  · show ((B.inBody.act (glue F.ports G.ports).get).mapUses (install F G)).oids = _
    rw [Tmpl.mapUses_oids _ (install_oid B F G), Tmpl.act_oids, hB.inOids]
  · intro y hy
    change y ∈ ((B.inBody.act (glue F.ports G.ports).get).mapUses (install F G)).uses at hy
    rw [Tmpl.mapUses_uses, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hfit : FitsD 0 ((B.inBody.act (glue F.ports G.ports).get).view B.table)
        (B.inBody.act (glue F.ports G.ports).get).erase (lifted (evA B.table F.ports 1)) := by
      rw [Tmpl.act_view, hB.inView, hstr.1, hB.inErase]
      have h0 := fitsD_subst (fun i => ev B.table ((glue F.ports G.ports).get i)) rinSel 0 (lawsT B.l)
        (lifted (.var 3)) (fits_in B.l)
      rw [substFam_lifted, ← hσ] at h0
      rw [← hσ]
      have e3 : subst (evA B.table (glue F.ports G.ports)) (.var 3 : Core 9) = evA B.table F.ports 1 :=
        glue_mid B F G
      rw [e3] at h0
      exact h0
    have hv := Tmpl.view_fits B.table _ _ hfit y' hy'
    have ha := Tmpl.acts_uses B.table _ hstr.2.1 y' hy'
    have hvc := (act_certs_exact B.table (glue F.ports G.ports).get B.inBody _ _ hB.inUses y' hy').2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ev B.table (install F G y'.e y'.use).view = _
      rw [install_view]
      exact hv
    · show evA B.table (install F G y'.e y'.use).acts = _
      rw [install_acts]
      exact ha
    · show (install F G y'.e y'.use).viewCert = _
      rw [install_viewCert]
      exact hvc
    · have hsrc := install_src B F G hB y' hy'
      rcases inAct_uses_oid B F G hB y' hy' with h | h
      · have hc : (install F G y'.e y'.use).srcCert = (F.certs 1).base.act (wkMap m y'.e) := by
          simp only [install, h, if_true]
        refine Or.inl ⟨?_, ?_, hc, ?_, rfl⟩
        · show (install F G y'.e y'.use).oid = 0
          rw [install_oid]
          exact h
        · show ev B.table (install F G y'.e y'.use).src = _
          rw [hsrc, h]
          simp only [routeFam, if_true]
        · show (install F G y'.e y'.use).srcCert.dec B.table = _
          rw [hc, wk_dec]
      · have hc : (install F G y'.e y'.use).srcCert = (G.certs 2).base.act (wkMap m y'.e) := by
          simp only [install, h, Nat.one_ne_zero, if_false, if_true]
        refine Or.inr ⟨?_, ?_, hc, ?_, rfl⟩
        · show (install F G y'.e y'.use).oid = 1
          rw [install_oid]
          exact h
        · show ev B.table (install F G y'.e y'.use).src = _
          rw [hsrc, h]
          simp only [routeFam, Nat.one_ne_zero, if_false]
        · show (install F G y'.e y'.use).srcCert.dec B.table = _
          rw [hc, wk_dec]

/-- Per use of the node `h` in the derived law: both origins are the composite function at the
    use, with exact certificates. -/
theorem law_uses (hB : B.Exact) :
    (mkComp B ctx F G).law.body.oids = [0, 1, 2] ∧
    ∀ y ∈ (mkComp B ctx F G).law.body.uses,
      ev B.table y.use.src = subst (weakActs m y.e) (subst (evA B.table (glue F.ports G.ports)) hSrc) ∧
      ev B.table y.use.view = subst (weakActs m y.e) (subst (evA B.table (glue F.ports G.ports)) hSrc) ∧
      evA B.table y.use.acts = weakActs m y.e ∧ y.use.srcCert = .exact ∧ y.use.viewCert = .exact := by
  have hstr := B.outBody.act_structure (glue F.ports G.ports).get
  have hσ := evA_eq_get B.table (glue F.ports G.ports)
  have h0 := fitsD_subst (fun i => ev B.table ((glue F.ports G.ports).get i)) phSel 0 (phT B.l)
    (lifted hSrc) (fits_out B.l)
  rw [substFam_lifted, ← hσ] at h0
  refine ⟨?_, ?_⟩
  · show (B.outBody.act (glue F.ports G.ports).get).oids = _
    rw [Tmpl.act_oids, hB.outOids]
  · intro y hy
    change y ∈ (B.outBody.act (glue F.ports G.ports).get).uses at hy
    have hfs : FitsD 0 ((B.outBody.act (glue F.ports G.ports).get).src B.table)
        (B.outBody.act (glue F.ports G.ports).get).erase (lifted (subst (evA B.table (glue F.ports G.ports)) hSrc)) := by
      rw [Tmpl.act_src, hB.outSrc, hstr.1, hB.outErase, ← hσ]
      exact h0
    have hfv : FitsD 0 ((B.outBody.act (glue F.ports G.ports).get).view B.table)
        (B.outBody.act (glue F.ports G.ports).get).erase (lifted (subst (evA B.table (glue F.ports G.ports)) hSrc)) := by
      rw [Tmpl.act_view, hB.outView, hstr.1, hB.outErase, ← hσ]
      exact h0
    have hc := act_certs_exact B.table (glue F.ports G.ports).get B.outBody _ _ hB.outUses y hy
    exact ⟨Tmpl.src_fits B.table _ _ hfs y hy, Tmpl.view_fits B.table _ _ hfv y hy,
      Tmpl.acts_uses B.table _ hstr.2.1 y hy, hc.1, hc.2⟩

/-- Actual common-supplier incidence of both records: `DerivedViewSyntax.corePlug` of the one node
    value into each decoded reading gives that record's shared body, which carries the node value
    at every use (`FitsD`) and agrees with the source elsewhere (`Agree`). For the kept laws the
    node value is the one intermediate operation; for the derived law it is the composite. -/
theorem comp_incidence (hB : B.Exact) (hm : midB B ctx F G = true) :
    corePlug ((mkComp B ctx F G).lawsIn.body.reading B.table) (evA B.table F.ports 1) Term.var =
        (mkComp B ctx F G).lawsIn.body.shared B.table (evA B.table F.ports 1) ∧
      FitsD 0 ((mkComp B ctx F G).lawsIn.body.shared B.table (evA B.table F.ports 1))
        (mkComp B ctx F G).lawsIn.body.erase (lifted (evA B.table F.ports 1)) ∧
      Agree ((mkComp B ctx F G).lawsIn.body.src B.table)
        ((mkComp B ctx F G).lawsIn.body.shared B.table (evA B.table F.ports 1)) (mkComp B ctx F G).lawsIn.body.erase ∧
      corePlug ((mkComp B ctx F G).law.body.reading B.table) (subst (evA B.table (glue F.ports G.ports)) hSrc)
          Term.var =
        (mkComp B ctx F G).law.body.shared B.table (subst (evA B.table (glue F.ports G.ports)) hSrc) ∧
      FitsD 0 ((mkComp B ctx F G).law.body.shared B.table (subst (evA B.table (glue F.ports G.ports)) hSrc))
        (mkComp B ctx F G).law.body.erase (lifted (subst (evA B.table (glue F.ports G.ports)) hSrc)) := by
  obtain ⟨hadm1, _, _, hsup, _⟩ := lawsIn_decode B ctx F G hB hm
  obtain ⟨hadm2, _, _, hsup2, _⟩ := law_decode B ctx F G hB hm
  have ha1 : (mkComp B ctx F G).lawsIn.body.actsB = true := by
    simp only [SRec.admitB, Tmpl.admitB, Bool.and_eq_true] at hadm1
    exact hadm1.2.1.1
  have ha2 : (mkComp B ctx F G).law.body.actsB = true := by
    simp only [SRec.admitB, Tmpl.admitB, Bool.and_eq_true] at hadm2
    exact hadm2.2.1.1
  have i1 := SRec.incidence (mkComp B ctx F G).lawsIn ha1
  have i2 := SRec.incidence (mkComp B ctx F G).law ha2
  have i1' : corePlug ((mkComp B ctx F G).lawsIn.body.reading B.table)
      (ev B.table (mkComp B ctx F G).lawsIn.sup) Term.var =
        (mkComp B ctx F G).lawsIn.body.shared B.table (ev B.table (mkComp B ctx F G).lawsIn.sup) ∧
      FitsD 0 ((mkComp B ctx F G).lawsIn.body.shared B.table (ev B.table (mkComp B ctx F G).lawsIn.sup))
        (mkComp B ctx F G).lawsIn.body.erase (lifted (ev B.table (mkComp B ctx F G).lawsIn.sup)) ∧
      Agree ((mkComp B ctx F G).lawsIn.body.src B.table)
        ((mkComp B ctx F G).lawsIn.body.shared B.table (ev B.table (mkComp B ctx F G).lawsIn.sup))
        (mkComp B ctx F G).lawsIn.body.erase := ⟨i1.1, i1.2.1, i1.2.2.1⟩
  have i2' : corePlug ((mkComp B ctx F G).law.body.reading B.table)
      (ev B.table (mkComp B ctx F G).law.sup) Term.var =
        (mkComp B ctx F G).law.body.shared B.table (ev B.table (mkComp B ctx F G).law.sup) ∧
      FitsD 0 ((mkComp B ctx F G).law.body.shared B.table (ev B.table (mkComp B ctx F G).law.sup))
        (mkComp B ctx F G).law.body.erase (lifted (ev B.table (mkComp B ctx F G).law.sup)) :=
    ⟨i2.1, i2.2.1⟩
  rw [hsup] at i1'
  rw [hsup2] at i2'
  exact ⟨i1'.1, i1'.2.1, i1'.2.2, i2'.1, i2'.2⟩

/-- Retained inputs and lineage. The composite keeps both inputs; each entry of its one actual
    vector is an input's own occurrence (not a decoded or re-encoded term): the index and first map
    and operations from `F`, the second map and last operation from `G`. Both records use the same
    table, the same instance context and the same actual vector, and the rule's templates (homes
    and rows) are unchanged. -/
theorem mkComp_lineage :
    (mkComp B ctx F G).F = F ∧ (mkComp B ctx F G).G = G ∧
      (∀ j, (mkComp B ctx F G).σ.get j = pick (glueSel j) F.ports.get G.ports.get) ∧
      (mkComp B ctx F G).σ.get 8 = F.ports.get 5 ∧ (mkComp B ctx F G).σ.get 1 = F.ports.get 0 ∧
      (mkComp B ctx F G).σ.get 0 = G.ports.get 0 ∧ (mkComp B ctx F G).σ.get 4 = F.ports.get 2 ∧
      (mkComp B ctx F G).σ.get 3 = F.ports.get 1 ∧ (mkComp B ctx F G).σ.get 2 = G.ports.get 1 ∧
      (mkComp B ctx F G).lawsIn.table = B.table ∧ (mkComp B ctx F G).law.table = B.table ∧
      (mkComp B ctx F G).lawsIn.owner = ctx ∧ (mkComp B ctx F G).law.owner = ctx ∧
      (mkComp B ctx F G).inInst.actuals = (mkComp B ctx F G).σ ∧
      (mkComp B ctx F G).outInst.actuals = (mkComp B ctx F G).σ ∧
      (mkComp B ctx F G).inInst.tmpl = B.rin ∧ (mkComp B ctx F G).outInst.tmpl = B.rout :=
  ⟨rfl, rfl, fun j => glue_get _ _ j, glue_get _ _ 8, glue_get _ _ 1, glue_get _ _ 0, glue_get _ _ 4,
    glue_get _ _ 3, glue_get _ _ 2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Clause2

/-! ### Clause 3: the contextual action -/

/-- An ambient map `ρ` (from the instance context to another one) acting on a supplied map: every
    port, route, certificate actual and evidence occurrence is acted on; levels, certificate
    classes, universe instances and evidence roles are kept. -/
def MapIn.act {Γ : List Nat} {m m' : Nat} (ρ : Fin m → Occ Γ m') (F : MapIn Γ m) : MapIn Γ m' :=
  { lv := F.lv, ports := ContextualViewDAG.substArgs ρ F.ports,
    srcPorts := ContextualViewDAG.substArgs ρ F.srcPorts, certs := fun j => (F.certs j).act ρ,
    ev := F.ev.map (fun p => (p.1, ContextualViewDAG.subst ρ p.2)) }

/-- The ambient map acting on a composite, with the new instance context: the rule's templates are
    untouched; the actual vector, the inputs and the evidence actuals are acted on. -/
def Comp.act {B : Bank} (K : Comp B) {m' : Nat} (ctx' : OTel B.homes m') (ρ : Fin K.m → Occ B.homes m') :
    Comp B :=
  { m := m', ctx := ctx', F := K.F.act ρ, G := K.G.act ρ, σ := ContextualViewDAG.substArgs ρ K.σ,
    ev := K.ev.map (CertU.act ρ) }

section ActLemmas
variable {Γ : List Nat} {m m' : Nat} (ρ : Fin m → Occ Γ m')

theorem ev_subst0 (tb : Table Γ) (o : Occ Γ m) :
    ev tb (ContextualViewDAG.subst ρ o) = subst (fun i => ev tb (ρ i)) (ev tb o) :=
  ev_substOcc tb ρ 0 o

theorem glue_act (a b : Args Γ m 6) :
    glue (ContextualViewDAG.substArgs ρ a) (ContextualViewDAG.substArgs ρ b) =
      ContextualViewDAG.substArgs ρ (glue a b) := by
  apply Args.ext
  funext j
  rw [glue_get, substArgs_get, glue_get]
  unfold pick
  split <;> rw [substArgs_get]

theorem certArgs_act (σ : Args Γ m 9) (hf hg : Occ Γ m) :
    certArgs (ContextualViewDAG.substArgs ρ σ) (ContextualViewDAG.subst ρ hf) (ContextualViewDAG.subst ρ hg) =
      ContextualViewDAG.substArgs ρ (certArgs σ hf hg) := by
  unfold certArgs
  rw [substArgs_ofFn]
  congr 1
  funext j
  split
  · rw [substArgs_get]
  · split <;> rfl

theorem evComp_act (l : Lv4) (σ : Args Γ m 9) (a b : Option (Role × Occ Γ m)) :
    evComp l (ContextualViewDAG.substArgs ρ σ) (a.map (fun p => (p.1, ContextualViewDAG.subst ρ p.2)))
        (b.map (fun p => (p.1, ContextualViewDAG.subst ρ p.2))) =
      (evComp l σ a b).map (CertU.act ρ) := by
  rcases a with _ | ⟨ra, ha⟩ <;> rcases b with _ | ⟨rb, hb⟩
  · rfl
  · rfl
  · rfl
  · show some _ = some _
    simp only [CertU.act, CertR.act, certArgs_act]

theorem routesB_act (tb : Table Γ) (F : MapIn Γ m) (k : Fin 6) (h : F.routesB tb k = true) :
    (F.act ρ).routesB tb k = true := by
  unfold MapIn.routesB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hj' := h j hj
  show (match ((F.certs j).act ρ).base with
    | .exact => coreEq (V6Structured.ev tb ((ContextualViewDAG.substArgs ρ F.srcPorts).get j))
        (V6Structured.ev tb ((ContextualViewDAG.substArgs ρ F.ports).get j))
    | .classB .. => j == k) = true
  revert hj'
  simp only [CertU.act]
  cases (F.certs j).base with
  | exact =>
    intro hj'
    simp only [CertR.act]
    rw [substArgs_get, substArgs_get, ev_subst0, ev_subst0, (coreEq_iff _ _).mp hj']
    exact (coreEq_iff _ _).mpr rfl
  | classB nm k' acts => intro hj'; exact hj'

theorem CertU.term_act (tb : Table Γ) (c : CertU Γ m) :
    (c.act ρ).term tb = (c.term tb).map (subst (fun i => ev tb (ρ i))) := by
  rcases c with ⟨base, lvls⟩
  cases base with
  | exact => rfl
  | classB nm k acts =>
    show some _ = some _
    rw [subst_appArgs, evA_substArgs]
    rfl

/-- Lifting through `e` local binders: a per-use origin weakened after acting is the acted
    origin at the lifted map (the explicit-actuals law `acts_subst` of section 1). -/
theorem origin_lift (ρ' : Fin m → Core m') (e : Nat) (x : Core m) :
    subst (weakActs m' e) (subst ρ' x) = subst (liftSubN e ρ') (subst (weakActs m e) x) := by
  rw [subst_comp, subst_comp]
  exact congrArg (fun g => subst g x) (acts_subst ρ' e).symm

theorem liftSub_comp (σ' : Fin 9 → Core m) (ρ' : Fin m → Core m') :
    liftSub (fun j => subst ρ' (σ' j)) = fun i => subst (liftSub ρ') (liftSub σ' i) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  rw [liftSub_succ, liftSub_succ]
  exact rename_subst_liftSub ρ' 0 (σ' j)

end ActLemmas

section Clause3
variable (B : Bank) {m m' : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m)
  (ctx' : OTel B.homes m') (ρ : Fin m → Occ B.homes m')

theorem midB_act (hm : midB B ctx F G = true) (hc : ctx'.admitB = true) :
    midB B ctx' (F.act ρ) (G.act ρ) = true := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7, h8, h9⟩ := midB_parts B ctx F G hm
  have g := fun (P : Args B.homes m 6) (j : Fin 6) => congrFun (evA_eq_get B.table P) j
  have h5' : ev B.table (G.ports.get 5) = ev B.table (F.ports.get 5) := (g _ 5).symm.trans (h5.trans (g _ 5))
  have h6' : ev B.table (G.ports.get 4) = ev B.table (F.ports.get 3) := (g _ 4).symm.trans (h6.trans (g _ 3))
  have h7' : ev B.table (G.ports.get 2) = ev B.table (F.ports.get 1) := (g _ 2).symm.trans (h7.trans (g _ 1))
  simp only [midB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hc, h2⟩, h3⟩, h4⟩, ?_⟩, ?_⟩, ?_⟩, routesB_act ρ B.table F 1 h8⟩, routesB_act ρ B.table G 2 h9⟩
  · rw [coreEq_iff]
    simp only [MapIn.act, substArgs_get, ev_subst0]
    rw [h5']
  · rw [coreEq_iff]
    simp only [MapIn.act, substArgs_get, ev_subst0]
    rw [h6']
  · rw [coreEq_iff]
    simp only [MapIn.act, substArgs_get, ev_subst0]
    rw [h7']

/-- Clause 3 at the level of the finite data: constructing after acting on the inputs gives the
    composite acted on after constructing. The rule's rows and homes are not touched. -/
theorem compose_act (hm : midB B ctx F G = true) (hc : ctx'.admitB = true) :
    compose B ctx' (F.act ρ) (G.act ρ) = some ((mkComp B ctx F G).act ctx' ρ) := by
  unfold compose
  rw [if_pos (midB_act B ctx F G ctx' ρ hm hc)]
  show some (Comp.mk m' ctx' (F.act ρ) (G.act ρ) (glue (F.act ρ).ports (G.act ρ).ports)
    (evComp B.l (glue (F.act ρ).ports (G.act ρ).ports) (F.act ρ).ev (G.act ρ).ev)) = some (Comp.mk m' ctx'
      (F.act ρ) (G.act ρ) (ContextualViewDAG.substArgs ρ (glue F.ports G.ports))
      ((evComp B.l (glue F.ports G.ports) F.ev G.ev).map (CertU.act ρ)))
  simp only [MapIn.act, glue_act, evComp_act]

/-- Clause 3, decoded: every decoded output of the construction after the action is the ambient
    substitution applied to the corresponding open output before it (binders lifted), closed by
    the new instance context. -/
theorem act_decode (hB : B.Exact) (hm : midB B ctx F G = true) (hc : ctx'.admitB = true) :
    (mkComp B ctx' (F.act ρ) (G.act ρ)).law.source =
        ctx'.close B.table (subst (fun i => ev B.table (ρ i))
          (subst (evA B.table (glue F.ports G.ports)) (phT B.l))) ∧
      ev B.table (mkComp B ctx' (F.act ρ) (G.act ρ)).law.sup =
        subst (fun i => ev B.table (ρ i)) (subst (evA B.table (glue F.ports G.ports)) hSrc) ∧
      (mkComp B ctx' (F.act ρ) (G.act ρ)).law.reading = ctx'.close B.table (.letE `h false
        (subst (fun i => ev B.table (ρ i)) (subst (evA B.table (glue F.ports G.ports)) hTy))
        (subst (fun i => ev B.table (ρ i)) (subst (evA B.table (glue F.ports G.ports)) hSrc))
        (subst (liftSub (fun i => ev B.table (ρ i)))
          (subst (liftSub (evA B.table (glue F.ports G.ports))) (consumer (phT B.l) phSel)))) ∧
      (mkComp B ctx' (F.act ρ) (G.act ρ)).lawsIn.source = ctx'.close B.table
        (andT (subst (fun i => ev B.table (ρ i)) (F.srcLaw B.table))
          (subst (fun i => ev B.table (ρ i)) (G.srcLaw B.table))) ∧
      (mkComp B ctx' (F.act ρ) (G.act ρ)).lawsIn.view = ctx'.close B.table
        (andT (subst (fun i => ev B.table (ρ i)) (F.viewLaw B.table))
          (subst (fun i => ev B.table (ρ i)) (G.viewLaw B.table))) ∧
      ev B.table (mkComp B ctx' (F.act ρ) (G.act ρ)).lawsIn.sup =
        subst (fun i => ev B.table (ρ i)) (evA B.table F.ports 1) ∧
      ((mkComp B ctx' (F.act ρ) (G.act ρ)).ev.map (·.term B.table)) =
        ((mkComp B ctx F G).ev.map (·.term B.table)).map (Option.map (subst (fun i => ev B.table (ρ i)))) := by
  have hm' := midB_act B ctx F G ctx' ρ hm hc
  obtain ⟨_, _, _, h4, h5, _, _, h8⟩ := law_decode B ctx' (F.act ρ) (G.act ρ) hB hm'
  obtain ⟨_, _, _, i4, _, i6, i7, _, _⟩ := lawsIn_decode B ctx' (F.act ρ) (G.act ρ) hB hm'
  have hσ : evA B.table (glue (F.act ρ).ports (G.act ρ).ports) =
      fun j => subst (fun i => ev B.table (ρ i)) (evA B.table (glue F.ports G.ports) j) := by
    show evA B.table (glue (ContextualViewDAG.substArgs ρ F.ports) (ContextualViewDAG.substArgs ρ G.ports)) = _
    rw [glue_act, evA_substArgs]
  have hS : ∀ (P : MapIn B.homes m), (P.act ρ).srcLaw B.table = subst (fun i => ev B.table (ρ i)) (P.srcLaw B.table) := by
    intro P
    show subst (evA B.table (ContextualViewDAG.substArgs ρ P.srcPorts)) (lawSrc P.lv) = _
    rw [evA_substArgs, MapIn.srcLaw, subst_comp]
  have hV : ∀ (P : MapIn B.homes m), (P.act ρ).viewLaw B.table = subst (fun i => ev B.table (ρ i)) (P.viewLaw B.table) := by
    intro P
    show subst (evA B.table (ContextualViewDAG.substArgs ρ P.ports)) (lawSrc P.lv) = _
    rw [evA_substArgs, MapIn.viewLaw, subst_comp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5, hσ, subst_comp]
  · rw [h4, hσ, subst_comp]
  · rw [h8, hσ, subst_comp, subst_comp, liftSub_comp, subst_comp]
  · rw [i6, hS, hS]
  · rw [i7, hV, hV]
  · rw [i4]
    show evA B.table (ContextualViewDAG.substArgs ρ F.ports) 1 = _
    rw [evA_substArgs]
  · show Option.map (fun x => CertU.term B.table x)
        (evComp B.l (glue (ContextualViewDAG.substArgs ρ F.ports) (ContextualViewDAG.substArgs ρ G.ports))
          (F.ev.map (fun p => (p.1, ContextualViewDAG.subst ρ p.2)))
          (G.ev.map (fun p => (p.1, ContextualViewDAG.subst ρ p.2)))) =
      Option.map (Option.map (subst fun i => ev B.table (ρ i)))
        (Option.map (fun x => CertU.term B.table x) (evComp B.l (glue F.ports G.ports) F.ev G.ev))
    rw [glue_act, evComp_act, Option.map_map, Option.map_map]
    congr 1
    funext c
    exact CertU.term_act ρ B.table c

end Clause3

/-! ### Clause 4: formation separate from evidence; evidence decoded -/

section Clause4
variable (B : Bank) {m : Nat} (ctx : OTel B.homes m) (F G : MapIn B.homes m)

/-- Formation never reads evidence: admission, the derived law and the kept input laws are the
    same with any evidence or none. -/
theorem formation_without_evidence (a b : Option (Role × Occ B.homes m)) :
    midB B ctx { F with ev := a } { G with ev := b } = midB B ctx F G ∧
      (mkComp B ctx { F with ev := a } { G with ev := b }).law = (mkComp B ctx F G).law ∧
      (mkComp B ctx { F with ev := a } { G with ev := b }).lawsIn = (mkComp B ctx F G).lawsIn :=
  ⟨rfl, rfl, rfl⟩

/-- Evidence is attached exactly when both inputs carry evidence. -/
theorem evidence_isSome : (mkComp B ctx F G).ev.isSome = (F.ev.isSome && G.ev.isSome) := by
  show (evComp B.l (glue F.ports G.ports) F.ev G.ev).isSome = _
  generalize F.ev = a
  generalize G.ev = b
  rcases a with _ | ⟨ra, ha⟩ <;> rcases b with _ | ⟨rb, hb⟩ <;> rfl

/-- With evidence for both input laws, the evidence component is the generic proof
    `dependent_preserves_comp` at the rule's universe instance, applied to the nine glued actuals
    and the two evidence occurrences; it decodes to the proof template `certT` instantiated there. -/
theorem evidence_decode (rf rg : Role) (hf hg : Occ B.homes m) (hF : F.ev = some (rf, hf))
    (hG : G.ev = some (rg, hg)) :
    (mkComp B ctx F G).ev =
        some ⟨.classB dpcName 11 (certArgs (glue F.ports G.ports) hf hg), [B.l.u, B.l.a, B.l.b, B.l.c]⟩ ∧
      (mkComp B ctx F G).ev.bind (·.term B.table) =
        some (subst (Fin.cases (ev B.table hg) (Fin.cases (ev B.table hf) (evA B.table (glue F.ports G.ports))))
          (certT B.l)) := by
  have e1 : (mkComp B ctx F G).ev =
      some ⟨.classB dpcName 11 (certArgs (glue F.ports G.ports) hf hg), [B.l.u, B.l.a, B.l.b, B.l.c]⟩ := by
    show evComp B.l (glue F.ports G.ports) F.ev G.ev = _
    rw [hF, hG]
    rfl
  refine ⟨e1, ?_⟩
  rw [e1]
  show some (appArgs (.const dpcName [B.l.u, B.l.a, B.l.b, B.l.c]) 11
    (evA B.table (certArgs (glue F.ports G.ports) hf hg))) = _
  rw [certT, subst_appArgs]
  congr 2
  rw [evA_eq_get, evA_eq_get B.table (glue F.ports G.ports)]
  funext j
  simp only [certArgs, ContextualViewDAG.Args.get_ofFn]
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl

/-- Without evidence for one input, no evidence is formed; the statement is still formed. -/
theorem evidence_missing (hF : F.ev = none ∨ G.ev = none) : (mkComp B ctx F G).ev = none := by
  show evComp B.l (glue F.ports G.ports) F.ev G.ev = none
  rcases hF with h | h <;> rw [h]
  · rfl
  · rcases F.ev with _ | ⟨_, _⟩ <;> rfl

end Clause4

end V6Compose
