import Lean

/- Finite scoped constructor syntax and exact derived views.
   This is not a Lean Expr codec, a shared DAG, or a dependent typing theorem. -/
namespace DerivedViewSyntax
open Lean

inductive ULevel where
  | zero
  | succ (u : ULevel)
  | max (u v : ULevel)
  | imax (u v : ULevel)
  | param (name : Name)
  deriving DecidableEq

structure BinderAttrs where
  name : Name
  info : BinderInfo

structure UniqueAttrs where
  u : ULevel
  v : ULevel
  x : BinderAttrs
  yName : Name
  yNondep : Bool
  a : BinderAttrs
  b : BinderAttrs
  z : BinderAttrs
  h : BinderAttrs

/- The Boolean selects the constructor signature. Core syntax cannot contain
   unique/inst, since their permission field would require false = true.
   No constructor stores Expr or an opaque compound source term. -/
inductive Term (derived : Bool) : Nat → Type where
  | var {n} (i : Fin n) : Term derived n
  | sort {n} (u : ULevel) : Term derived n
  | const {n} (name : Name) (levels : List ULevel) : Term derived n
  | lit {n} (value : Literal) : Term derived n
  | app {n} (f a : Term derived n) : Term derived n
  | lam {n} (attrs : BinderAttrs) (domain : Term derived n)
      (body : Term derived (n+1)) : Term derived n
  | pi {n} (attrs : BinderAttrs) (domain : Term derived n)
      (body : Term derived (n+1)) : Term derived n
  | letE {n} (name : Name) (nondep : Bool) (type value : Term derived n)
      (body : Term derived (n+1)) : Term derived n
  | proj {n} (typeName : Name) (index : Nat) (value : Term derived n) : Term derived n
  | unique {n} (enabled : derived = true) (attrs : UniqueAttrs)
      (A B step advance relation : Term derived n) : Term derived n
  | inst {n r} (enabled : derived = true) (body : Term derived r)
      (actuals : Fin r → Term derived n) : Term derived n

abbrev Core := Term false
abbrev View := Term true

def liftRen (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem liftRen_zero (ρ : Fin n → Fin m) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_succ (ρ : Fin n → Fin m) (i : Fin n) :
    liftRen ρ i.succ = (ρ i).succ := rfl

def rename (ρ : Fin n → Fin m) : Term d n → Term d m
  | .var i => .var (ρ i)
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam attrs domain body => .lam attrs (rename ρ domain) (rename (liftRen ρ) body)
  | .pi attrs domain body => .pi attrs (rename ρ domain) (rename (liftRen ρ) body)
  | .letE name nondep type value body =>
      .letE name nondep (rename ρ type) (rename ρ value) (rename (liftRen ρ) body)
  | .proj name index value => .proj name index (rename ρ value)
  | .unique enabled attrs A B step advance relation =>
      .unique enabled attrs (rename ρ A) (rename ρ B) (rename ρ step)
        (rename ρ advance) (rename ρ relation)
  | .inst enabled body actuals => .inst enabled body (fun i => rename ρ (actuals i))

def liftSub (σ : Fin n → Term d m) : Fin (n+1) → Term d (m+1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

@[simp] theorem liftSub_zero (σ : Fin n → Term d m) : liftSub σ 0 = .var 0 := rfl
@[simp] theorem liftSub_succ (σ : Fin n → Term d m) (i : Fin n) :
    liftSub σ i.succ = rename Fin.succ (σ i) := rfl

def subst (σ : Fin n → Term d m) : Term d n → Term d m
  | .var i => σ i
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam attrs domain body => .lam attrs (subst σ domain) (subst (liftSub σ) body)
  | .pi attrs domain body => .pi attrs (subst σ domain) (subst (liftSub σ) body)
  | .letE name nondep type value body =>
      .letE name nondep (subst σ type) (subst σ value) (subst (liftSub σ) body)
  | .proj name index value => .proj name index (subst σ value)
  | .unique enabled attrs A B step advance relation =>
      .unique enabled attrs (subst σ A) (subst σ B) (subst σ step)
        (subst σ advance) (subst σ relation)
  | .inst enabled body actuals => .inst enabled body (fun i => subst σ (actuals i))

theorem liftRen_id : liftRen (id : Fin n → Fin n) = id := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem liftRen_comp (ρ : Fin n → Fin m) (θ : Fin m → Fin l) :
    (fun i => liftRen θ (liftRen ρ i)) = liftRen (fun i => θ (ρ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem rename_id (t : Term d n) : rename id t = t := by
  induction t with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [rename, liftRen_id, ihd, ihb]
  | pi attrs domain body ihd ihb => simp only [rename, liftRen_id, ihd, ihb]
  | letE name nondep type value body iht ihv ihb =>
      simp only [rename, liftRen_id, iht, ihv, ihb]
  | proj name index value ih => simp only [rename, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [rename, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals =>
      simp only [rename, ihactuals]

theorem rename_comp (t : Term d n) (ρ : Fin n → Fin m) (θ : Fin m → Fin l) :
    rename θ (rename ρ t) = rename (fun i => θ (ρ i)) t := by
  induction t generalizing m l with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [rename, ihd, ihb, liftRen_comp]
  | pi attrs domain body ihd ihb => simp only [rename, ihd, ihb, liftRen_comp]
  | letE name nondep type value body iht ihv ihb =>
      simp only [rename, iht, ihv, ihb, liftRen_comp]
  | proj name index value ih => simp only [rename, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [rename, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals =>
      simp only [rename, ihactuals]

theorem rename_liftSub (σ : Fin n → Term d m) (ρ : Fin m → Fin l) :
    (fun i => rename (liftRen ρ) (liftSub σ i)) =
      liftSub (fun i => rename ρ (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [liftSub_succ, rename_comp]
    rfl

theorem rename_subst (t : Term d n) (σ : Fin n → Term d m) (ρ : Fin m → Fin l) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m l with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [rename, subst, ihd, ihb, rename_liftSub]
  | pi attrs domain body ihd ihb => simp only [rename, subst, ihd, ihb, rename_liftSub]
  | letE name nondep type value body iht ihv ihb =>
      simp only [rename, subst, iht, ihv, ihb, rename_liftSub]
  | proj name index value ih => simp only [rename, subst, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [rename, subst, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals => simp only [rename, subst, ihactuals]

theorem liftSub_liftRen (ρ : Fin n → Fin m) (τ : Fin m → Term d l) :
    (fun i => liftSub τ (liftRen ρ i)) = liftSub (fun i => τ (ρ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem subst_rename (t : Term d n) (ρ : Fin n → Fin m) (τ : Fin m → Term d l) :
    subst τ (rename ρ t) = subst (fun i => τ (ρ i)) t := by
  induction t generalizing m l with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [rename, subst, ihd, ihb, liftSub_liftRen]
  | pi attrs domain body ihd ihb => simp only [rename, subst, ihd, ihb, liftSub_liftRen]
  | letE name nondep type value body iht ihv ihb =>
      simp only [rename, subst, iht, ihv, ihb, liftSub_liftRen]
  | proj name index value ih => simp only [rename, subst, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [rename, subst, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals => simp only [rename, subst, ihactuals]

theorem subst_weaken (t : Term d n) (τ : Fin n → Term d m) :
    subst (liftSub τ) (rename Fin.succ t) = rename Fin.succ (subst τ t) := by
  rw [subst_rename, rename_subst]
  rfl

theorem liftSub_comp (σ : Fin n → Term d m) (τ : Fin m → Term d l) :
    (fun i => subst (liftSub τ) (liftSub σ i)) =
      liftSub (fun i => subst τ (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [liftSub_succ, subst_weaken]

theorem liftSub_var : liftSub (Term.var (derived := d) : Fin n → Term d n) = Term.var := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem subst_id (t : Term d n) : subst Term.var t = t := by
  induction t with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [subst, liftSub_var, ihd, ihb]
  | pi attrs domain body ihd ihb => simp only [subst, liftSub_var, ihd, ihb]
  | letE name nondep type value body iht ihv ihb =>
      simp only [subst, liftSub_var, iht, ihv, ihb]
  | proj name index value ih => simp only [subst, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [subst, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals => simp only [subst, ihactuals]

theorem subst_comp (t : Term d n) (σ : Fin n → Term d m) (τ : Fin m → Term d l) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing m l with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [subst, ihd, ihb, liftSub_comp]
  | pi attrs domain body ihd ihb => simp only [subst, ihd, ihb, liftSub_comp]
  | letE name nondep type value body iht ihv ihb =>
      simp only [subst, iht, ihv, ihb, liftSub_comp]
  | proj name index value ih => simp only [subst, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [subst, ihA, ihB, ihs, ihk, ihR]
  | inst enabled body actuals ihbody ihactuals => simp only [subst, ihactuals]

def compose (σ : Fin n → Term d m) (τ : Fin m → Term d l) : Fin n → Term d l :=
  fun i => subst τ (σ i)

theorem compose_id_left (σ : Fin n → Term d m) : compose Term.var σ = σ := by
  rfl

theorem compose_id_right (σ : Fin n → Term d m) : compose σ Term.var = σ := by
  funext i
  exact subst_id (σ i)

theorem compose_assoc (σ : Fin n → Term d m) (τ : Fin m → Term d l)
    (υ : Fin l → Term d k) : compose (compose σ τ) υ = compose σ (compose τ υ) := by
  funext i
  exact subst_comp (σ i) τ υ

theorem rename_eq_subst (t : Term d n) (ρ : Fin n → Fin m) :
    rename ρ t = subst (fun i => Term.var (ρ i)) t := by
  rw [← subst_rename, subst_id]

/- Exact source-constructor template. The free-slot order is [R,k,step,B,A].
   Local order at the deepest body is [h,z,b,a,y,x]. No beta/delta reduction. -/
def uniqueTemplate (η : UniqueAttrs) : Core 5 :=
  .pi η.x (.var 4)
    (.letE η.yName η.yNondep (.var 5) (.app (.var 3) (.var 0))
      (.pi η.a (.app (.var 5) (.var 1))
        (.app (.app (.const ``Exists [η.v]) (.app (.var 6) (.var 1)))
          (.lam η.b (.app (.var 6) (.var 1))
            (.app
              (.app (.const ``And [])
                (.app (.app (.app (.var 4) (.var 2))
                  (.app (.app (.var 5) (.var 3)) (.var 1))) (.var 0)))
              (.pi η.z (.app (.var 7) (.var 2))
                (.pi η.h
                  (.app (.app (.app (.var 5) (.var 3))
                    (.app (.app (.var 6) (.var 4)) (.var 2))) (.var 0))
                  (.app (.app (.app (.const ``Eq [η.v])
                    (.app (.var 9) (.var 4))) (.var 1)) (.var 2)))))))))

def five (a b c d e : α) : Fin 5 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e Fin.elim0))))

theorem map_five (f : α → β) (a b c d e : α) :
    (fun i => f (five a b c d e i)) = five (f a) (f b) (f c) (f d) (f e) := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun j => nomatch j) i

/- Expansion is independently recursive; plugging below never invokes it. -/
def expand : Term d n → Core n
  | .var i => .var i
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app f a => .app (expand f) (expand a)
  | .lam attrs domain body => .lam attrs (expand domain) (expand body)
  | .pi attrs domain body => .pi attrs (expand domain) (expand body)
  | .letE name nondep type value body => .letE name nondep (expand type) (expand value) (expand body)
  | .proj name index value => .proj name index (expand value)
  | .unique _ attrs A B step advance relation =>
      subst (five (expand relation) (expand advance) (expand step) (expand B) (expand A))
        (uniqueTemplate attrs)
  | .inst _ body actuals => subst (fun i => expand (actuals i)) (expand body)

theorem expand_core (t : Core n) : expand t = t := by
  induction t with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [expand, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [expand, ihd, ihb]
  | pi attrs domain body ihd ihb => simp only [expand, ihd, ihb]
  | letE name nondep type value body iht ihv ihb => simp only [expand, iht, ihv, ihb]
  | proj name index value ih => simp only [expand, ih]
  | unique enabled => contradiction
  | inst enabled => contradiction

theorem expand_rename (t : Term d n) (ρ : Fin n → Fin m) :
    expand (rename ρ t) = rename ρ (expand t) := by
  induction t generalizing m with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [expand, rename, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [expand, rename, ihd, ihb]
  | pi attrs domain body ihd ihb => simp only [expand, rename, ihd, ihb]
  | letE name nondep type value body iht ihv ihb =>
      simp only [expand, rename, iht, ihv, ihb]
  | proj name index value ih => simp only [expand, rename, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [expand, rename, ihA, ihB, ihs, ihk, ihR, rename_subst, map_five]
  | inst enabled body actuals ihbody ihactuals =>
      simp only [expand, rename, ihactuals, rename_subst]

theorem expand_liftSub (σ : Fin n → Term d m) :
    (fun i => expand (liftSub σ i)) = liftSub (fun i => expand (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [liftSub_succ, expand_rename]

theorem expand_subst (t : Term d n) (σ : Fin n → Term d m) :
    expand (subst σ t) = subst (fun i => expand (σ i)) (expand t) := by
  induction t generalizing m with
  | var i => rfl
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp only [expand, subst, ihf, iha]
  | lam attrs domain body ihd ihb => simp only [expand, subst, ihd, ihb, expand_liftSub]
  | pi attrs domain body ihd ihb => simp only [expand, subst, ihd, ihb, expand_liftSub]
  | letE name nondep type value body iht ihv ihb =>
      simp only [expand, subst, iht, ihv, ihb, expand_liftSub]
  | proj name index value ih => simp only [expand, subst, ih]
  | unique enabled attrs A B step advance relation ihA ihB ihs ihk ihR =>
      simp only [expand, subst, ihA, ihB, ihs, ihk, ihR, subst_comp, map_five]
  | inst enabled body actuals ihbody ihactuals =>
      simp only [expand, subst, ihactuals, subst_comp]

def plug (consumer : View (n+1)) (producer : View r) (actuals : Fin r → View n) : View n :=
  subst (Fin.cases (.inst rfl producer actuals) Term.var) consumer

def corePlug (consumer : Core (n+1)) (producer : Core r) (actuals : Fin r → Core n) : Core n :=
  subst (Fin.cases (subst actuals producer) Term.var) consumer

theorem expand_plug (consumer : View (n+1)) (producer : View r) (actuals : Fin r → View n) :
    expand (plug consumer producer actuals) =
      corePlug (expand consumer) (expand producer) (fun i => expand (actuals i)) := by
  unfold plug corePlug
  rw [expand_subst]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i


end DerivedViewSyntax
