import NamedContextAdmission
import ExprSubstitutionSpec

namespace DefinographAdmission
open Lean Meta DerivedViewSyntax V6Structured V6Compose

/-- Elaboration assistance only: supplied actuals replace free interface slots
    through the transparent source action, lifting under every binder. -/
def instantiateSlots (vars : Fin n → Expr) (t : Core n) : Expr :=
  ExprSubstitutionSpec.subst (fun i => if h : i < n then vars ⟨i, h⟩ else .bvar i) (dec t)

def withCoreContext {α : Type} : {n : Nat} → CTel n → ((Fin n → Expr) → MetaM α) → MetaM α
  | _, .nil, k => k Fin.elim0
  | _, .port C attrs A, k => withCoreContext C fun vars =>
      withLocalDecl attrs.name attrs.info (instantiateSlots vars A) fun x =>
        k (Fin.cases x vars)
  | _, .letE C nm _ A v, k => withCoreContext C fun vars =>
      withLetDecl nm (instantiateSlots vars A) (instantiateSlots vars v) (nondep := false) fun x =>
        k (Fin.cases x vars)

/-- Infer a candidate type for an ordinary extracted source occurrence.
    Opening an OWNED source let/have exposes its defining value, as Lean's intro
    does. This is different from abstracting a preexisting opaque LocalDecl.
    The source telescope/frames retain the original nondep flag. Inference is
    not admission; checkOriginalWithInferredType checks the exact original. -/
def inferComponent (C : CTel n) (term : Core n) : MetaM NamedComponent := do
  ensureSourceBasis (← getEnv) [contextExpr C, dec term]
  withLCtx {} {} do
    withCoreContext C fun vars => do
      let term' := instantiateSlots vars term
      let type' ← inferType term'
      let some named ← captureLocalContext | throwError "source context outside the finished admission profile"
      let some component := ingestNamedComponent named term' type'
        | throwError "inferred type outside the finished admission profile"
      return component

def inferredTypeAt (C : CTel n) (term : Core n) : MetaM (Core n) := do
  let component ← inferComponent C term
  if h : component.context.ids.length = n then
    let recovered : Core n := h ▸ component.term
    unless coreEq recovered term do throwError "source term changed during context reconstruction"
    return h ▸ component.type
  else throwError "source context changed arity during reconstruction"

/-- Check the original Core/CTel, including exact source nondep flags, against
    the candidate inferred type. No generated-ID or normalized-home receipt
    substitutes for these exact original declarations. -/
def checkOriginalWithInferredType (run : Check) (nm : Name) (ls : List Name)
    (C : CTel n) (term : Core n) : MetaM (Core n × Checks) := do
  let type ← inferredTypeAt C term
  let checks ← checkComponentWith run nm ls C term type
  return (type, checks)

end DefinographAdmission
