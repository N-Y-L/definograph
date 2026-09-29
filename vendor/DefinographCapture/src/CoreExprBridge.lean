import DerivedViewSyntax
import ExprReferenceGraph

/- Exact ordinary Core/Expr boundary. Fixed finite universe syntax, bounded
   bvar slots, no free/metavariable references or metadata in strict admission.
   This is neither a typing theorem nor a Lean substitution compatibility law. -/
namespace CoreExprBridge
open Lean DerivedViewSyntax

def decodeLevel : ULevel → Level
  | .zero => .zero
  | .succ u => .succ (decodeLevel u)
  | .max u v => .max (decodeLevel u) (decodeLevel v)
  | .imax u v => .imax (decodeLevel u) (decodeLevel v)
  | .param name => .param name

def decode : Core n → Expr
  | .var i => .bvar i.val
  | .sort u => .sort (decodeLevel u)
  | .const name levels => .const name (levels.map decodeLevel)
  | .lit value => .lit value
  | .app fn arg => .app (decode fn) (decode arg)
  | .lam attrs domain body => .lam attrs.name (decode domain) (decode body) attrs.info
  | .pi attrs domain body => .forallE attrs.name (decode domain) (decode body) attrs.info
  | .letE name nondep type value body =>
    .letE name (decode type) (decode value) (decode body) nondep
  | .proj name index value => .proj name index (decode value)
  | .unique impossible _ _ _ _ _ _ => nomatch impossible
  | .inst impossible _ _ => nomatch impossible

-- Admission is defined independently over actual Lean syntax.
def LevelAdmitted : Level → Prop
  | .zero | .param _ => True
  | .succ u => LevelAdmitted u
  | .max u v | .imax u v => LevelAdmitted u ∧ LevelAdmitted v
  | .mvar _ => False

def LevelsAdmitted : List Level → Prop
  | [] => True
  | u :: us => LevelAdmitted u ∧ LevelsAdmitted us

def Admitted : Expr → Nat → Prop
  | .bvar i, n => i < n
  | .sort u, _ => LevelAdmitted u
  | .const _ levels, _ => LevelsAdmitted levels
  | .lit _, _ => True
  | .app fn arg, n => Admitted fn n ∧ Admitted arg n
  | .lam _ domain body _, n => Admitted domain n ∧ Admitted body (n+1)
  | .forallE _ domain body _, n => Admitted domain n ∧ Admitted body (n+1)
  | .letE _ type value body _, n => Admitted type n ∧ Admitted value n ∧ Admitted body (n+1)
  | .proj _ _ value, n => Admitted value n
  | .fvar _, _ | .mvar _, _ | .mdata _ _, _ => False

def decideLevel (u : Level) : Decidable (LevelAdmitted u) :=
  match u with
  | .zero | .param _ => show Decidable True from inferInstance
  | .succ u => decideLevel u
  | .max u v | .imax u v => @instDecidableAnd _ _ (decideLevel u) (decideLevel v)
  | .mvar _ => show Decidable False from inferInstance

def decideLevels (us : List Level) : Decidable (LevelsAdmitted us) :=
  match us with
  | [] => show Decidable True from inferInstance
  | u :: us => @instDecidableAnd _ _ (decideLevel u) (decideLevels us)

def decideAdmitted (e : Expr) (n : Nat) : Decidable (Admitted e n) :=
  match e with
  | .bvar i => show Decidable (i < n) from inferInstance
  | .sort u => decideLevel u
  | .const _ levels => decideLevels levels
  | .lit _ => show Decidable True from inferInstance
  | .app fn arg => @instDecidableAnd _ _ (decideAdmitted fn n) (decideAdmitted arg n)
  | .lam _ domain body _ | .forallE _ domain body _ =>
    @instDecidableAnd _ _ (decideAdmitted domain n) (decideAdmitted body (n+1))
  | .letE _ type value body _ => @instDecidableAnd _ _ (decideAdmitted type n)
    (@instDecidableAnd _ _ (decideAdmitted value n) (decideAdmitted body (n+1)))
  | .proj _ _ value => decideAdmitted value n
  | .fvar _ | .mvar _ | .mdata _ _ => show Decidable False from inferInstance

-- Reification on the independently admitted domain, followed below by the
-- executable partial reifier. No whole-term payload or hidden source is stored.
def ofLevel : (u : Level) → LevelAdmitted u → ULevel
  | .zero, _ => .zero
  | .succ u, h => .succ (ofLevel u h)
  | .max u v, h => .max (ofLevel u h.1) (ofLevel v h.2)
  | .imax u v, h => .imax (ofLevel u h.1) (ofLevel v h.2)
  | .param name, _ => .param name
  | .mvar _, h => False.elim h

def ofLevels : (us : List Level) → LevelsAdmitted us → List ULevel
  | [], _ => []
  | u :: us, h => ofLevel u h.1 :: ofLevels us h.2

def ofAdmitted : (e : Expr) → (n : Nat) → Admitted e n → Core n
  | .bvar i, _, h => .var ⟨i, h⟩
  | .sort u, _, h => .sort (ofLevel u h)
  | .const name levels, _, h => .const name (ofLevels levels h)
  | .lit value, _, _ => .lit value
  | .app fn arg, n, h => .app (ofAdmitted fn n h.1) (ofAdmitted arg n h.2)
  | .lam name domain body info, n, h =>
    .lam ⟨name, info⟩ (ofAdmitted domain n h.1) (ofAdmitted body (n+1) h.2)
  | .forallE name domain body info, n, h =>
    .pi ⟨name, info⟩ (ofAdmitted domain n h.1) (ofAdmitted body (n+1) h.2)
  | .letE name type value body nondep, n, h =>
    .letE name nondep (ofAdmitted type n h.1) (ofAdmitted value n h.2.1)
      (ofAdmitted body (n+1) h.2.2)
  | .proj name index value, n, h => .proj name index (ofAdmitted value n h)
  | .fvar _, _, h | .mvar _, _, h | .mdata _ _, _, h => False.elim h

def reify (e : Expr) (n : Nat) : Option (Core n) :=
  letI := decideAdmitted e n
  if h : Admitted e n then some (ofAdmitted e n h) else none

theorem decode_ofLevel (u : Level) (h : LevelAdmitted u) : decodeLevel (ofLevel u h) = u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [ofLevel, decodeLevel, ih]
  | max u v ihu ihv => simp only [ofLevel, decodeLevel, ihu, ihv]
  | imax u v ihu ihv => simp only [ofLevel, decodeLevel, ihu, ihv]
  | param name => rfl
  | mvar id => exact False.elim h

theorem decode_ofLevels (us : List Level) (h : LevelsAdmitted us) :
    (ofLevels us h).map decodeLevel = us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [ofLevels, List.map_cons, decode_ofLevel, ih]

theorem decode_ofAdmitted (e : Expr) (n : Nat) (h : Admitted e n) :
    decode (ofAdmitted e n h) = e := by
  induction e generalizing n with
  | bvar i => rfl
  | sort u => simp only [ofAdmitted, decode, decode_ofLevel]
  | const name levels => simp only [ofAdmitted, decode, decode_ofLevels]
  | lit value => rfl
  | app fn arg ihf iha => simp only [ofAdmitted, decode, ihf, iha]
  | lam name domain body info ihd ihb => simp only [ofAdmitted, decode, ihd, ihb]
  | forallE name domain body info ihd ihb => simp only [ofAdmitted, decode, ihd, ihb]
  | letE name type value body nondep iht ihv ihb => simp only [ofAdmitted, decode, iht, ihv, ihb]
  | proj name index value ih => simp only [ofAdmitted, decode, ih]
  | fvar id | mvar id | mdata data body ih => exact False.elim h

theorem decodeLevel_admitted (u : ULevel) : LevelAdmitted (decodeLevel u) := by
  induction u with
  | zero | param _ => trivial
  | succ u ih => exact ih
  | max u v ihu ihv | imax u v ihu ihv => exact ⟨ihu, ihv⟩

theorem decodeLevels_admitted (us : List ULevel) : LevelsAdmitted (us.map decodeLevel) := by
  induction us with
  | nil => trivial
  | cons u us ih => exact ⟨decodeLevel_admitted u, ih⟩

theorem decode_admitted (t : Core n) : Admitted (decode t) n := by
  induction t with
  | var i => exact i.isLt
  | sort u => exact decodeLevel_admitted u
  | const name levels => exact decodeLevels_admitted levels
  | lit value => trivial
  | app fn arg ihf iha => exact ⟨ihf, iha⟩
  | lam attrs domain body ihd ihb | pi attrs domain body ihd ihb => exact ⟨ihd, ihb⟩
  | letE name nondep type value body iht ihv ihb => exact ⟨iht, ihv, ihb⟩
  | proj name index value ih => exact ih
  | unique impossible | inst impossible => contradiction

theorem ofLevel_decode (u : ULevel) (h : LevelAdmitted (decodeLevel u)) :
    ofLevel (decodeLevel u) h = u := by
  induction u with
  | zero | param _ => rfl
  | succ u ih => simp only [decodeLevel, ofLevel, ih]
  | max u v ihu ihv | imax u v ihu ihv => simp only [decodeLevel, ofLevel, ihu, ihv]

theorem ofLevels_decode (us : List ULevel) (h : LevelsAdmitted (us.map decodeLevel)) :
    ofLevels (us.map decodeLevel) h = us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [List.map_cons, ofLevels, ofLevel_decode, ih]

theorem ofAdmitted_decode (t : Core n) (h : Admitted (decode t) n) :
    ofAdmitted (decode t) n h = t := by
  induction t with
  | var i => rfl
  | sort u => simp only [decode, ofAdmitted, ofLevel_decode]
  | const name levels => simp only [decode, ofAdmitted, ofLevels_decode]
  | lit value => rfl
  | app fn arg ihf iha => simp only [decode, ofAdmitted, ihf, iha]
  | lam attrs domain body ihd ihb | pi attrs domain body ihd ihb =>
    simp only [decode, ofAdmitted, ihd, ihb]
  | letE name nondep type value body iht ihv ihb => simp only [decode, ofAdmitted, iht, ihv, ihb]
  | proj name index value ih => simp only [decode, ofAdmitted, ih]
  | unique impossible | inst impossible => contradiction

theorem reify_decode (t : Core n) : reify (decode t) n = some t := by
  simp only [reify, dif_pos (decode_admitted t), ofAdmitted_decode]

theorem decode_injective (s t : Core n) (h : decode s = decode t) : s = t := by
  have hr : reify (decode s) n = reify (decode t) n := congrArg (fun e => reify e n) h
  rw [reify_decode, reify_decode] at hr
  exact Option.some.inj hr

theorem reify_readback (e : Expr) (n : Nat) (t : Core n) (h : reify e n = some t) :
    Admitted e n ∧ decode t = e := by
  unfold reify at h
  split at h
  next ha =>
    have heq := Option.some.inj h
    exact ⟨ha, heq ▸ decode_ofAdmitted e n ha⟩
  next ha => cases h

theorem admitted_iff_reifies (e : Expr) (n : Nat) :
    Admitted e n ↔ ∃ t, reify e n = some t := by
  constructor
  · intro h
    exact ⟨ofAdmitted e n h, by simp only [reify, dif_pos h]⟩
  · rintro ⟨t, ht⟩
    exact (reify_readback e n t ht).1

-- ExactExpr is the constructor-by-constructor field relation, not BEq.
theorem reify_exact (e : Expr) (n : Nat) (t : Core n) (h : reify e n = some t) :
    ExprReferenceGraph.ExactExpr (decode t) e := by
  rw [(reify_readback e n t h).2]
  exact ExprReferenceGraph.ExactExpr.refl e

-- Optional explicit metadata erasure; strict reify itself never ignores data.
def reifyNormalized (e : Expr) (n : Nat) : Option (Core n) :=
  reify (ExprReferenceGraph.eraseMetadata e) n

theorem normalized_readback (e : Expr) (n : Nat) (t : Core n)
    (h : reifyNormalized e n = some t) :
    decode t = ExprReferenceGraph.eraseMetadata e :=
  (reify_readback _ n t h).2

theorem normalized_admission (e : Expr) (n : Nat) :
    Admitted (ExprReferenceGraph.eraseMetadata e) n ↔ ∃ t, reifyNormalized e n = some t :=
  admitted_iff_reifies _ n


end CoreExprBridge
