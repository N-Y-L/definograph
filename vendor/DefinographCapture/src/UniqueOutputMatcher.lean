import DerivedViewSyntax

namespace DerivedViewSyntax
open Lean

instance : DecidableEq BinderInfo := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | (apply isFalse; intro h; cases h)

deriving instance DecidableEq for BinderAttrs
deriving instance DecidableEq for UniqueAttrs
deriving instance DecidableEq for Literal

def coreEq : Core n → Core n → Bool
  | .var i, .var j => decide (i = j)
  | .sort u, .sort v => decide (u = v)
  | .const name levels, .const name' levels' => decide (name = name' ∧ levels = levels')
  | .lit value, .lit value' => decide (value = value')
  | .app f a, .app f' a' => coreEq f f' && coreEq a a'
  | .lam attrs domain body, .lam attrs' domain' body' =>
      decide (attrs = attrs') && coreEq domain domain' && coreEq body body'
  | .pi attrs domain body, .pi attrs' domain' body' =>
      decide (attrs = attrs') && coreEq domain domain' && coreEq body body'
  | .letE name nondep type value body, .letE name' nondep' type' value' body' =>
      decide (name = name' ∧ nondep = nondep') && coreEq type type' &&
        coreEq value value' && coreEq body body'
  | .proj name index value, .proj name' index' value' =>
      decide (name = name' ∧ index = index') && coreEq value value'
  | _, _ => false

theorem coreEq_iff (t s : Core n) : coreEq t s = true ↔ t = s := by
  induction t with
  | unique enabled => contradiction
  | inst enabled => contradiction
  | _ =>
    cases s <;> try contradiction
    all_goals simp_all [coreEq, Term.var.injEq, Term.sort.injEq, Term.const.injEq,
      Term.lit.injEq, Term.app.injEq, Term.lam.injEq, Term.pi.injEq,
      Term.letE.injEq, Term.proj.injEq, and_assoc]

def liftPartial (ρ : Fin n → Option (Fin m)) : Fin (n+1) → Option (Fin (m+1)) :=
  Fin.cases (some 0) (fun i => (ρ i).map Fin.succ)

def partialRename (ρ : Fin n → Option (Fin m)) : Core n → Option (Core m)
  | .var i => (ρ i).map Term.var
  | .sort u => some (.sort u)
  | .const name levels => some (.const name levels)
  | .lit value => some (.lit value)
  | .app f a => do return .app (← partialRename ρ f) (← partialRename ρ a)
  | .lam attrs domain body => do
      return .lam attrs (← partialRename ρ domain) (← partialRename (liftPartial ρ) body)
  | .pi attrs domain body => do
      return .pi attrs (← partialRename ρ domain) (← partialRename (liftPartial ρ) body)
  | .letE name nondep type value body => do
      return .letE name nondep (← partialRename ρ type) (← partialRename ρ value)
        (← partialRename (liftPartial ρ) body)
  | .proj name index value => do return .proj name index (← partialRename ρ value)
  | .unique enabled .. => nomatch enabled
  | .inst enabled .. => nomatch enabled

theorem liftPartial_leftInverse (ρ : Fin n → Fin m) (π : Fin m → Option (Fin n))
    (h : ∀ i, π (ρ i) = some i) : ∀ i, liftPartial π (liftRen ρ i) = some i := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp [liftPartial, liftRen, h]

theorem partialRename_rename (t : Core n) (ρ : Fin n → Fin m)
    (π : Fin m → Option (Fin n)) (h : ∀ i, π (ρ i) = some i) :
    partialRename π (rename ρ t) = some t := by
  induction t generalizing m with
  | var i => simp [rename, partialRename, h]
  | sort u => rfl
  | const name levels => rfl
  | lit value => rfl
  | app f a ihf iha => simp [rename, partialRename, ihf _ _ h, iha _ _ h]
  | lam attrs domain body ihd ihb =>
      simp [rename, partialRename, ihd _ _ h, ihb _ _ (liftPartial_leftInverse ρ π h)]
  | pi attrs domain body ihd ihb =>
      simp [rename, partialRename, ihd _ _ h, ihb _ _ (liftPartial_leftInverse ρ π h)]
  | letE name nondep type value body iht ihv ihb =>
      simp [rename, partialRename, iht _ _ h, ihv _ _ h,
        ihb _ _ (liftPartial_leftInverse ρ π h)]
  | proj name index value ih => simp [rename, partialRename, ih _ _ h]
  | unique enabled => contradiction
  | inst enabled => contradiction

def unweaken (t : Core (n+1)) : Option (Core n) :=
  partialRename (Fin.cases none some) t

theorem unweaken_weaken (t : Core n) : unweaken (rename Fin.succ t) = some t := by
  apply partialRename_rename
  intro i; rfl

def unweaken2 (t : Core (n+2)) : Option (Core n) := do
  let t ← unweaken t
  unweaken t

def unweaken4 (t : Core (n+4)) : Option (Core n) := do
  let t ← unweaken2 t
  unweaken2 t

structure UniqueMatch (n : Nat) where
  attrs : UniqueAttrs
  A : Core n
  B : Core n
  step : Core n
  advance : Core n
  relation : Core n

def UniqueMatch.rebuild (result : UniqueMatch n) : Core n :=
  subst (five result.relation result.advance result.step result.B result.A)
    (uniqueTemplate result.attrs)

/- First-use extraction. Repeated fields are intentionally not trusted here:
   matchUnique checks every one by exact reconstructed equality afterward. -/
def extractUnique (u : ULevel) : Core n → Option (UniqueMatch n)
  | .pi x A
      (.letE yName yNondep _ (.app stepX _)
        (.pi a (.app BXY _)
          (.app (.app (.const _ [v]) _)
            (.lam b _
              (.app (.app _
                (.app (.app (.app relationXYAB _) (.app (.app advanceXYAB _) _)) _))
                (.pi z _ (.pi h _ _))))))) => do
      let step ← unweaken stepX
      let B ← unweaken2 BXY
      let advance ← unweaken4 advanceXYAB
      let relation ← unweaken4 relationXYAB
      return ⟨⟨u, v, x, yName, yNondep, a, b, z, h⟩, A, B, step, advance, relation⟩
  | _ => none

def matchUnique (u : ULevel) (source : Core n) : Option (UniqueMatch n) := do
  let result ← extractUnique u source
  if coreEq result.rebuild source then some result else none

theorem matchUnique_sound (source : Core n) (u : ULevel) (result : UniqueMatch n)
    (h : matchUnique u source = some result) : result.rebuild = source := by
  unfold matchUnique at h
  cases he : extractUnique u source with
  | none => simp [he] at h
  | some found =>
    simp only [he] at h
    change (if coreEq found.rebuild source then some found else none) = some result at h
    split at h
    next eq =>
      cases h
      exact (coreEq_iff _ _).mp eq
    next eq => contradiction

theorem extractUnique_complete (result : UniqueMatch n) :
    extractUnique result.attrs.u result.rebuild = some result := by
  cases result with
  | mk attrs A B step advance relation =>
    change (do
      let step' ← unweaken (rename Fin.succ step)
      let B' ← unweaken2 (rename Fin.succ (rename Fin.succ B))
      let advance' ← unweaken4
        (rename Fin.succ (rename Fin.succ (rename Fin.succ (rename Fin.succ advance))))
      let relation' ← unweaken4
        (rename Fin.succ (rename Fin.succ (rename Fin.succ (rename Fin.succ relation))))
      pure (UniqueMatch.mk attrs A B' step' advance' relation')) =
      some (UniqueMatch.mk attrs A B step advance relation)
    simp [unweaken2, unweaken4, unweaken_weaken]

theorem matchUnique_complete (result : UniqueMatch n) :
    matchUnique result.attrs.u result.rebuild = some result := by
  simp only [matchUnique, extractUnique_complete]
  change (if coreEq result.rebuild result.rebuild then some result else none) = some result
  rw [show coreEq result.rebuild result.rebuild = true from (coreEq_iff _ _).mpr rfl]
  rfl

/- Inclusion changes only the constructor-signature index. It is not an Expr
   codec and introduces no new representation or opaque payload. -/
def coreToView : Core n → View n
  | .var i => .var i
  | .sort u => .sort u
  | .const name levels => .const name levels
  | .lit value => .lit value
  | .app f a => .app (coreToView f) (coreToView a)
  | .lam attrs domain body => .lam attrs (coreToView domain) (coreToView body)
  | .pi attrs domain body => .pi attrs (coreToView domain) (coreToView body)
  | .letE name nondep type value body =>
      .letE name nondep (coreToView type) (coreToView value) (coreToView body)
  | .proj name index value => .proj name index (coreToView value)
  | .unique enabled .. => nomatch enabled
  | .inst enabled .. => nomatch enabled

theorem expand_coreToView (t : Core n) : expand (coreToView t) = t := by
  induction t with
  | unique enabled => contradiction
  | inst enabled => contradiction
  | _ => simp_all [coreToView, expand]

def UniqueMatch.fold (result : UniqueMatch n) : View n :=
  .unique rfl result.attrs (coreToView result.A) (coreToView result.B)
    (coreToView result.step) (coreToView result.advance) (coreToView result.relation)

theorem UniqueMatch.expand_fold (result : UniqueMatch n) : expand result.fold = result.rebuild := by
  simp only [UniqueMatch.fold, expand, expand_coreToView, UniqueMatch.rebuild]

theorem matchUnique_expanded_sound (source : Core n) (u : ULevel) (result : UniqueMatch n)
    (h : matchUnique u source = some result) : expand result.fold = source := by
  rw [UniqueMatch.expand_fold]
  exact matchUnique_sound source u result h

theorem matchUnique_expanded_complete (η : UniqueAttrs) (A B step advance relation : View n) :
    matchUnique η.u (expand (.unique rfl η A B step advance relation)) =
      some (UniqueMatch.mk η (expand A) (expand B) (expand step) (expand advance) (expand relation)) :=
  matchUnique_complete (UniqueMatch.mk η (expand A) (expand B) (expand step) (expand advance) (expand relation))

/- This is exactly the same skeleton with the uniqueness conjunction/product
   removed: only R y (advance x a) b remains inside the existential. -/
def existenceTemplate (η : UniqueAttrs) : Core 5 :=
  .pi η.x (.var 4)
    (.letE η.yName η.yNondep (.var 5) (.app (.var 3) (.var 0))
      (.pi η.a (.app (.var 5) (.var 1))
        (.app (.app (.const ``Exists [η.v]) (.app (.var 6) (.var 1)))
          (.lam η.b (.app (.var 6) (.var 1))
            (.app (.app (.app (.var 4) (.var 2))
              (.app (.app (.var 5) (.var 3)) (.var 1))) (.var 0))))))

def UniqueMatch.withoutUniqueness (result : UniqueMatch n) : Core n :=
  subst (five result.relation result.advance result.step result.B result.A)
    (existenceTemplate result.attrs)

theorem extractUnique_withoutUniqueness (result : UniqueMatch n) (u : ULevel) :
    extractUnique u result.withoutUniqueness = none := by
  simp only [UniqueMatch.withoutUniqueness, existenceTemplate, subst]
  unfold extractUnique
  split
  · simp_all [Term.pi.injEq, Term.letE.injEq, Term.app.injEq, Term.lam.injEq]
  · rfl

theorem matchUnique_withoutUniqueness (result : UniqueMatch n) (u : ULevel) :
    matchUnique u result.withoutUniqueness = none := by
  simp [matchUnique, extractUnique_withoutUniqueness]


end DerivedViewSyntax
