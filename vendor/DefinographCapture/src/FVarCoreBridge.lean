import CoreExprBridge

/- Finite external identity registry only. It does not carry declaration types,
   defining values, environment validation or dependent typing certificates. -/
namespace FVarCoreBridge
open Lean DerivedViewSyntax

private def fvarIdDecEq : DecidableEq FVarId := fun a b =>
  match decEq a.name b.name with
  | .isTrue h => .isTrue (by cases a; cases b; cases h; rfl)
  | .isFalse h => .isFalse (fun heq => h (congrArg FVarId.name heq))

local instance : DecidableEq FVarId := fvarIdDecEq

def decideMember (id : FVarId) : (registry : List FVarId) → Decidable (id ∈ registry)
  | [] => .isFalse (fun h => List.not_mem_nil h)
  | head :: tail =>
    if h : id = head then .isTrue (List.mem_cons.mpr (.inl h))
    else match decideMember id tail with
    | .isTrue hm => .isTrue (List.mem_cons.mpr (.inr hm))
    | .isFalse hm => .isFalse (fun hc => (List.mem_cons.mp hc).elim h hm)

-- Exact identity search, with a membership witness excluding failure.
def slotOf : (registry : List FVarId) → (id : FVarId) → id ∈ registry → Fin registry.length
  | [], _, hm => False.elim (List.not_mem_nil hm)
  | head :: tail, id, hm =>
    if heq : id = head then ⟨0, by simp⟩
    else (slotOf tail id (by
      rcases List.mem_cons.mp hm with h | h
      · exact False.elim (heq h)
      · exact h)).succ

theorem get_slotOf (registry : List FVarId) (id : FVarId) (hm : id ∈ registry) :
    registry[(slotOf registry id hm).val] = id := by
  induction registry with
  | nil => cases hm
  | cons head tail ih =>
    by_cases heq : id = head
    · subst id
      simp [slotOf]
    · simp [slotOf, heq, ih]

theorem get_unique (registry : List FVarId) (hd : registry.Nodup)
    (i j : Fin registry.length) (h : registry[i.val] = registry[j.val]) : i = j := by
  induction registry with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
    rcases List.nodup_cons.mp hd with ⟨hhead, htail⟩
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro heq
        change head = tail[j.val] at heq
        have hm := List.getElem_mem j.isLt
        rw [← heq] at hm
        exact False.elim (hhead hm)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro heq
        change tail[i.val] = head at heq
        have hm := List.getElem_mem i.isLt
        rw [heq] at hm
        exact False.elim (hhead hm)
      · intro heq
        exact congrArg Fin.succ (ih htail i j heq)

theorem slotOf_get (registry : List FVarId) (hd : registry.Nodup) (i : Fin registry.length) :
    slotOf registry registry[i.val] (List.getElem_mem i.isLt) = i :=
  get_unique registry hd _ i (get_slotOf registry _ _)

-- With d local binders, local positions are [0,d); the external registry
-- occupies the remaining slots in its explicitly supplied nearest-first order.
def decode (registry : List FVarId) (d : Nat) : Core (registry.length + d) → Expr
  | .var i => if h : i.val < d then .bvar i.val
    else .fvar (registry[i.val - d]'(by have := i.isLt; omega))
  | .sort u => .sort (CoreExprBridge.decodeLevel u)
  | .const name levels => .const name (levels.map CoreExprBridge.decodeLevel)
  | .lit value => .lit value
  | .app fn arg => .app (decode registry d fn) (decode registry d arg)
  | .lam attrs domain body =>
    .lam attrs.name (decode registry d domain) (decode registry (d+1) body) attrs.info
  | .pi attrs domain body =>
    .forallE attrs.name (decode registry d domain) (decode registry (d+1) body) attrs.info
  | .letE name nondep type value body =>
    .letE name (decode registry d type) (decode registry d value) (decode registry (d+1) body) nondep
  | .proj name index value => .proj name index (decode registry d value)
  | .unique impossible _ _ _ _ _ _ => nomatch impossible
  | .inst impossible _ _ => nomatch impossible

def Admitted (registry : List FVarId) : Expr → Nat → Prop
  | .bvar i, d => i < d
  | .fvar id, _ => id ∈ registry
  | .sort u, _ => CoreExprBridge.LevelAdmitted u
  | .const _ levels, _ => CoreExprBridge.LevelsAdmitted levels
  | .lit _, _ => True
  | .app fn arg, d => Admitted registry fn d ∧ Admitted registry arg d
  | .lam _ domain body _, d | .forallE _ domain body _, d =>
    Admitted registry domain d ∧ Admitted registry body (d+1)
  | .letE _ type value body _, d =>
    Admitted registry type d ∧ Admitted registry value d ∧ Admitted registry body (d+1)
  | .proj _ _ value, d => Admitted registry value d
  | .mvar _, _ | .mdata _ _, _ => False

def decideAdmitted (registry : List FVarId) (e : Expr) (d : Nat) : Decidable (Admitted registry e d) :=
  match e with
  | .bvar i => show Decidable (i < d) from inferInstance
  | .fvar id => decideMember id registry
  | .sort u => CoreExprBridge.decideLevel u
  | .const _ levels => CoreExprBridge.decideLevels levels
  | .lit _ => show Decidable True from inferInstance
  | .app fn arg => @instDecidableAnd _ _ (decideAdmitted registry fn d) (decideAdmitted registry arg d)
  | .lam _ domain body _ | .forallE _ domain body _ =>
    @instDecidableAnd _ _ (decideAdmitted registry domain d) (decideAdmitted registry body (d+1))
  | .letE _ type value body _ => @instDecidableAnd _ _ (decideAdmitted registry type d)
    (@instDecidableAnd _ _ (decideAdmitted registry value d) (decideAdmitted registry body (d+1)))
  | .proj _ _ value => decideAdmitted registry value d
  | .mvar _ | .mdata _ _ => show Decidable False from inferInstance

def ofAdmitted (registry : List FVarId) :
    (e : Expr) → (d : Nat) → Admitted registry e d → Core (registry.length + d)
  | .bvar i, d, h => .var ⟨i, by change i < d at h; omega⟩
  | .fvar id, d, h => .var ⟨d + (slotOf registry id h).val, by have := (slotOf registry id h).isLt; omega⟩
  | .sort u, _, h => .sort (CoreExprBridge.ofLevel u h)
  | .const name levels, _, h => .const name (CoreExprBridge.ofLevels levels h)
  | .lit value, _, _ => .lit value
  | .app fn arg, d, h => .app (ofAdmitted registry fn d h.1) (ofAdmitted registry arg d h.2)
  | .lam name domain body info, d, h =>
    .lam ⟨name, info⟩ (ofAdmitted registry domain d h.1) (ofAdmitted registry body (d+1) h.2)
  | .forallE name domain body info, d, h =>
    .pi ⟨name, info⟩ (ofAdmitted registry domain d h.1) (ofAdmitted registry body (d+1) h.2)
  | .letE name type value body nondep, d, h =>
    .letE name nondep (ofAdmitted registry type d h.1) (ofAdmitted registry value d h.2.1)
      (ofAdmitted registry body (d+1) h.2.2)
  | .proj name index value, d, h => .proj name index (ofAdmitted registry value d h)
  | .mvar _, _, h | .mdata _ _, _, h => False.elim h

def reify (registry : List FVarId) (e : Expr) (d : Nat) : Option (Core (registry.length + d)) :=
  letI := decideAdmitted registry e d
  if h : Admitted registry e d then some (ofAdmitted registry e d h) else none

theorem decode_ofAdmitted (registry : List FVarId) (e : Expr) (d : Nat)
    (h : Admitted registry e d) : decode registry d (ofAdmitted registry e d h) = e := by
  induction e generalizing d with
  | bvar i => simp only [ofAdmitted, decode, dif_pos (show i < d from h)]
  | fvar id =>
    have hn : ¬ d + (slotOf registry id h).val < d := by omega
    simp only [ofAdmitted, decode, dif_neg hn, Nat.add_sub_cancel_left, get_slotOf]
  | sort u => simp only [ofAdmitted, decode, CoreExprBridge.decode_ofLevel]
  | const name levels => simp only [ofAdmitted, decode, CoreExprBridge.decode_ofLevels]
  | lit value => simp only [ofAdmitted, decode]
  | app fn arg ihf iha => simp only [ofAdmitted, decode, ihf, iha]
  | lam name domain body info ihd ihb => simp only [ofAdmitted, decode, ihd, ihb]
  | forallE name domain body info ihd ihb => simp only [ofAdmitted, decode, ihd, ihb]
  | letE name type value body nondep iht ihv ihb => simp only [ofAdmitted, decode, iht, ihv, ihb]
  | proj name index value ih => simp only [ofAdmitted, decode, ih]
  | mvar id | mdata data body ih => exact False.elim h

theorem decode_admitted (registry : List FVarId) (d : Nat) (t : Core (registry.length+d)) :
    Admitted registry (decode registry d t) d := by
  cases t with
  | var i =>
    simp only [decode]
    split
    next h => exact h
    next h => exact List.getElem_mem _
  | sort u => simpa only [decode, Admitted] using CoreExprBridge.decodeLevel_admitted u
  | const name levels => simpa only [decode, Admitted] using CoreExprBridge.decodeLevels_admitted levels
  | lit value => simp only [decode, Admitted]
  | app fn arg =>
    simpa only [decode, Admitted] using ⟨decode_admitted registry d fn, decode_admitted registry d arg⟩
  | lam attrs domain body | pi attrs domain body =>
    simpa only [decode, Admitted] using ⟨decode_admitted registry d domain, decode_admitted registry (d+1) body⟩
  | letE name nondep type value body =>
    simpa only [decode, Admitted] using
      ⟨decode_admitted registry d type, decode_admitted registry d value, decode_admitted registry (d+1) body⟩
  | proj name index value => simpa only [decode, Admitted] using decode_admitted registry d value
  | unique impossible | inst impossible => contradiction
termination_by sizeOf t

theorem ofAdmitted_decode (registry : List FVarId) (hd : registry.Nodup)
    (d : Nat) (t : Core (registry.length+d)) (h : Admitted registry (decode registry d t) d) :
    ofAdmitted registry (decode registry d t) d h = t := by
  cases t with
  | var i =>
    by_cases hi : i.val < d
    · simp only [decode, dif_pos hi, ofAdmitted]
    · simp only [decode, dif_neg hi, ofAdmitted]
      apply congrArg Term.var
      apply Fin.ext
      have hs := congrArg Fin.val
        (slotOf_get registry hd (⟨i.val-d, by have := i.isLt; omega⟩ : Fin registry.length))
      dsimp only at hs
      change d + _ = i.val
      rw [hs]
      omega
  | sort u => simp only [decode, ofAdmitted, CoreExprBridge.ofLevel_decode]
  | const name levels => simp only [decode, ofAdmitted, CoreExprBridge.ofLevels_decode]
  | lit value => simp only [decode, ofAdmitted]
  | app fn arg =>
    simp only [decode, ofAdmitted, ofAdmitted_decode registry hd d fn,
      ofAdmitted_decode registry hd d arg]
  | lam attrs domain body | pi attrs domain body =>
    simp only [decode, ofAdmitted, ofAdmitted_decode registry hd d domain,
      ofAdmitted_decode registry hd (d+1) body]
  | letE name nondep type value body =>
    simp only [decode, ofAdmitted, ofAdmitted_decode registry hd d type,
      ofAdmitted_decode registry hd d value, ofAdmitted_decode registry hd (d+1) body]
  | proj name index value => simp only [decode, ofAdmitted, ofAdmitted_decode registry hd d value]
  | unique impossible | inst impossible => contradiction
termination_by sizeOf t

theorem reify_decode (registry : List FVarId) (hd : registry.Nodup)
    (d : Nat) (t : Core (registry.length+d)) : reify registry (decode registry d t) d = some t := by
  simp only [reify, dif_pos (decode_admitted registry d t), ofAdmitted_decode registry hd]

theorem decode_injective (registry : List FVarId) (hd : registry.Nodup)
    (d : Nat) (s t : Core (registry.length+d)) (h : decode registry d s = decode registry d t) : s = t := by
  have hr : reify registry (decode registry d s) d = reify registry (decode registry d t) d :=
    congrArg (fun e => reify registry e d) h
  rw [reify_decode registry hd, reify_decode registry hd] at hr
  exact Option.some.inj hr

-- This direction needs no duplicate-free hypothesis: even the first occurrence
-- of a repeated registry ID still decodes to that exact ID.
theorem reify_readback (registry : List FVarId) (e : Expr) (d : Nat)
    (t : Core (registry.length+d)) (h : reify registry e d = some t) :
    Admitted registry e d ∧ decode registry d t = e := by
  unfold reify at h
  split at h
  next ha =>
    have heq := Option.some.inj h
    exact ⟨ha, heq ▸ decode_ofAdmitted registry e d ha⟩
  next ha => cases h

theorem admitted_iff_reifies (registry : List FVarId) (e : Expr) (d : Nat) :
    Admitted registry e d ↔ ∃ t, reify registry e d = some t := by
  constructor
  · intro h
    exact ⟨ofAdmitted registry e d h, by simp only [reify, dif_pos h]⟩
  · rintro ⟨t, ht⟩
    exact (reify_readback registry e d t ht).1

theorem reify_exact (registry : List FVarId) (e : Expr) (d : Nat)
    (t : Core (registry.length+d)) (h : reify registry e d = some t) :
    ExprReferenceGraph.ExactExpr (decode registry d t) e := by
  rw [(reify_readback registry e d t h).2]
  exact ExprReferenceGraph.ExactExpr.refl e

def reifyNormalized (registry : List FVarId) (e : Expr) (d : Nat) :
    Option (Core (registry.length+d)) :=
  reify registry (ExprReferenceGraph.eraseMetadata e) d

theorem normalized_readback (registry : List FVarId) (e : Expr) (d : Nat)
    (t : Core (registry.length+d)) (h : reifyNormalized registry e d = some t) :
    decode registry d t = ExprReferenceGraph.eraseMetadata e :=
  (reify_readback registry _ d t h).2

theorem normalized_admission (registry : List FVarId) (e : Expr) (d : Nat) :
    Admitted registry (ExprReferenceGraph.eraseMetadata e) d ↔
      ∃ t, reifyNormalized registry e d = some t :=
  admitted_iff_reifies registry _ d

theorem root_readback (registry : List FVarId) (e : Expr)
    (h : Admitted registry e 0) :
    ∃ t : Core registry.length, reify registry e 0 = some t ∧ decode registry 0 t = e := by
  obtain ⟨t, ht⟩ := (admitted_iff_reifies registry e 0).mp h
  exact ⟨t, ht, (reify_readback registry e 0 t ht).2⟩

#print axioms get_slotOf
#print axioms get_unique
#print axioms slotOf_get
#print axioms decode_ofAdmitted
#print axioms decode_admitted
#print axioms reify_decode
#print axioms decode_injective
#print axioms reify_readback
#print axioms admitted_iff_reifies
#print axioms reify_exact
#print axioms normalized_readback
#print axioms normalized_admission
#print axioms root_readback
#print axioms decode
#print axioms reify

end FVarCoreBridge
