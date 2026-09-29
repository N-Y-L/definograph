import SourceBoundary

/- Generic admission over the existing finite Core and CTel data. No fixture dispatch.
   The injected declaration checker is the trust boundary, not a proved kernel model. -/
namespace DefinographAdmission
open Lean Meta DerivedViewSyntax V6Structured V6Compose

abbrev Checks := Array (String × KOut)
abbrev Check := String → Declaration → MetaM KOut

def CTel.items : {n : Nat} → CTel n → Array HItem
  | _, .nil => #[]
  | _, .port C a A => (CTel.items C).push (.port a.name a.info (dec A))
  | _, .letE C nm nd A v => (CTel.items C).push (.letE nm (dec A) (dec v) nd)

theorem forall_decode (C : CTel n) (t : Core n) :
    dec (C.close t) = closeForall (CTel.items C) (dec t) := by
  induction C with
  | nil => rfl
  | port C a A ih => simpa [CTel.close, CTel.items, closeForall, dec,
      CoreExprBridge.decode, Array.foldr_push] using ih (.pi a A t)
  | letE C nm nd A v ih => simpa [CTel.close, CTel.items, closeForall, dec,
      CoreExprBridge.decode, Array.foldr_push] using ih (.letE nm nd A v t)

theorem lambda_decode (C : CTel n) (t : Core n) :
    dec (ctelLam C t) = closeLam (CTel.items C) (dec t) := by
  induction C with
  | nil => rfl
  | port C a A ih => simpa [ctelLam, CTel.items, closeLam, dec,
      CoreExprBridge.decode, Array.foldr_push] using ih (.lam a A t)
  | letE C nm nd A v ih => simpa [ctelLam, CTel.items, closeLam, dec,
      CoreExprBridge.decode, Array.foldr_push] using ih (.letE nm nd A v t)

def checkContextWith (run : Check) (nm : Name) (ls : List Name) (C : CTel n) : MetaM Checks := do
  ensureSourceBasis (← getEnv) [contextExpr C]
  let k ← run "context" (thmD (nm ++ `context)
    (dec (C.close (.const ``True []))) (dec (ctelLam C (.const ``True.intro []))) ls)
  return #[("context", k)]

def checkComponentWith (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (term type : Core n) : MetaM Checks := do
  ensureSourceBasis (← getEnv) [contextExpr C, dec term, dec type]
  let checks ← checkContextWith run nm ls C
  let k ← run "component" (defD (nm ++ `component) (dec (C.close type)) (dec (ctelLam C term)) ls)
  return checks.push ("component", k)

/-- Type formation does not presume a value of the proposed type exists. -/
def checkTypeWith (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (type : Core n) : MetaM Checks :=
  checkComponentWith run nm ls C (.lam ⟨`x, .default⟩ type (.var 0))
    (.pi ⟨`x, .default⟩ type (rename Fin.succ type))

def allAccepted (checks : Checks) : Bool := checks.all (fun p => kAccepted p.2)

/-- A failed early check is retained; later success cannot certify the batch. -/
theorem allAccepted_push (checks : Checks) (label : String) (k : KOut) :
    allAccepted (checks.push (label, k)) = (allAccepted checks && kAccepted k) := by
  simp [allAccepted]

/-- Check the actual finite dependent map, in declaration order. Universe levels
    are supplied and themselves checked as the sorts of the source types. -/
def checkMapComponentsWith (run : Check) (nm : Name) (ls : List Name) (D : CTel m) :
    {n : Nat} → CTel n → (Fin n → Core m) → (Fin n → ULevel) → MetaM Checks
  | _, .nil, _, _ => pure #[]
  | _, .port C _ A, images, sorts => do
    ensureSourceBasis (← getEnv) ([contextExpr C, contextExpr D, dec A] ++
      List.ofFn (fun i => dec (images i)))
    let rest ← checkMapComponentsWith run nm ls D C (fun i => images i.succ) (fun i => sorts i.succ)
    let tag := nm ++ Name.mkSimple s!"slot{rest.size}"
    let sourceType ← checkComponentWith run (tag ++ `sourceType) ls C A (.sort (sorts 0))
    let expected := subst (fun i => images i.succ) A
    let image ← checkComponentWith run (tag ++ `image) ls D (images 0) expected
    return rest ++ sourceType ++ image
  | _, .letE C _ _ A v, images, sorts => do
    ensureSourceBasis (← getEnv) ([contextExpr C, contextExpr D, dec A, dec v] ++
      List.ofFn (fun i => dec (images i)))
    let rest ← checkMapComponentsWith run nm ls D C (fun i => images i.succ) (fun i => sorts i.succ)
    let tag := nm ++ Name.mkSimple s!"slot{rest.size}"
    let sourceType ← checkComponentWith run (tag ++ `sourceType) ls C A (.sort (sorts 0))
    let sourceValue ← checkComponentWith run (tag ++ `sourceValue) ls C v A
    let expected := subst (fun i => images i.succ) A
    let expectedValue := subst (fun i => images i.succ) v
    let image ← checkComponentWith run (tag ++ `image) ls D (images 0) expected
    let eqTy := mkApp3 (mkConst ``Eq [CoreExprBridge.decodeLevel (sorts 0)])
      (dec expected) (dec (images 0)) (dec expectedValue)
    let eqVal := mkApp2 (mkConst ``Eq.refl [CoreExprBridge.decodeLevel (sorts 0)])
      (dec expected) (dec (images 0))
    let k ← run "definition conversion" (thmD (tag ++ `definition)
      (closeForall (CTel.items D) eqTy) (closeLam (CTel.items D) eqVal) ls)
    return rest ++ sourceType ++ sourceValue ++ image ++ #[("definition conversion", k)]

def checkMapWith (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (D : CTel m) (images : Fin n → Core m) (sorts : Fin n → ULevel) : MetaM Checks := do
  ensureSourceBasis (← getEnv) ([contextExpr C, contextExpr D] ++
    (List.finRange n).map (fun i => dec (images i)))
  let source ← checkContextWith run (nm ++ `source) ls C
  let target ← checkContextWith run (nm ++ `target) ls D
  let components ← checkMapComponentsWith run (nm ++ `maps) ls D C images sorts
  return source ++ target ++ components

/-- Raw substitution is the existing specified Core operation, not native Expr instantiation.
    Every offered result has its own output check; no universal typing theorem is presumed. -/
def composeWith (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (D : CTel m) (term type : Core n)
    (images : Fin n → Core m) (sorts : Fin n → ULevel) : MetaM (Core m × Core m × Checks) := do
  ensureSourceBasis (← getEnv) ([contextExpr C, contextExpr D, dec term, dec type] ++
    (List.finRange n).map (fun i => dec (images i)))
  let source ← checkComponentWith run (nm ++ `source) ls C term type
  let map ← checkMapWith run (nm ++ `map) ls C D images sorts
  let outTerm := subst images term
  let outType := subst images type
  let output ← checkComponentWith run (nm ++ `output) ls D outTerm outType
  return (outTerm, outType, source ++ map ++ output)

/-- Ingest arbitrary normalized positional source fields constructor-by-constructor. -/
def ingestContext (items : List HItem) : Option ((n : Nat) × CTel n) :=
  items.foldlM (fun ⟨n, C⟩ item => do
    match item with
    | .port nm bi A => return ⟨n+1, .port C ⟨nm, bi⟩ (← CoreExprBridge.reify A n)⟩
    | .letE nm A v nd => return ⟨n+1, .letE C nm nd (← CoreExprBridge.reify A n)
        (← CoreExprBridge.reify v n)⟩) ⟨0, .nil⟩

def ingestComponent (items : List HItem) (term type : Expr) :
    Option ((n : Nat) × CTel n × Core n × Core n) := do
  let ⟨n, C⟩ ← ingestContext items
  return ⟨n, C, ← CoreExprBridge.reify term n, ← CoreExprBridge.reify type n⟩

#print axioms forall_decode
#print axioms lambda_decode
#print axioms allAccepted_push
end DefinographAdmission
