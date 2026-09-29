import CheckedComposition

namespace DefinographAdmission
open Lean Meta DerivedViewSyntax V6Structured

/-- Check against the operation's initial environment, including projection
    owners. Later diagnostic declarations must not repair missing source names. -/
def firstMissingConstant (env : Environment) : Expr → Option Name
  | .const name _ => if env.contains name then none else some name
  | .proj name _ value =>
      if env.contains name then firstMissingConstant env value else some name
  | .app fn arg => (firstMissingConstant env fn).orElse fun _ => firstMissingConstant env arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      (firstMissingConstant env domain).orElse fun _ => firstMissingConstant env body
  | .letE _ type value body _ =>
      (firstMissingConstant env type).orElse fun _ =>
        (firstMissingConstant env value).orElse fun _ => firstMissingConstant env body
  | .mdata _ body => firstMissingConstant env body
  | _ => none

def BasisClosed (env : Environment) : Expr → Prop
  | .const name _ => env.contains name = true
  | .proj name _ value => env.contains name = true ∧ BasisClosed env value
  | .app fn arg => BasisClosed env fn ∧ BasisClosed env arg
  | .lam _ domain body _ | .forallE _ domain body _ => BasisClosed env domain ∧ BasisClosed env body
  | .letE _ type value body _ => BasisClosed env type ∧ BasisClosed env value ∧ BasisClosed env body
  | .mdata _ body => BasisClosed env body
  | _ => True

theorem orElse_none (a b : Option Name) :
    a.orElse (fun _ => b) = none ↔ a = none ∧ b = none := by
  cases a <;> simp

theorem basis_check_iff (env : Environment) (e : Expr) :
    firstMissingConstant env e = none ↔ BasisClosed env e := by
  induction e with
  | const name levels => cases h : env.contains name <;> simp [firstMissingConstant, BasisClosed, h]
  | proj name index value ih =>
    cases h : env.contains name <;> simp [firstMissingConstant, BasisClosed, h, ih]
  | app fn arg ihf iha => simp [firstMissingConstant, BasisClosed, orElse_none, ihf, iha]
  | lam name domain body info ihd ihb | forallE name domain body info ihd ihb =>
    simp [firstMissingConstant, BasisClosed, orElse_none, ihd, ihb]
  | letE name type value body nondep iht ihv ihb =>
    simp [firstMissingConstant, BasisClosed, orElse_none, iht, ihv, ihb]
  | mdata data body ih => simpa [firstMissingConstant, BasisClosed] using ih
  | _ => simp [firstMissingConstant, BasisClosed]

def ensureSourceBasis (env : Environment) (expressions : List Expr) : MetaM Unit := do
  for expression in expressions do
    if let some name := firstMissingConstant env expression then
      throwError "source references a declaration absent from the initial environment: {name}"

def contextExpr (C : CTel n) : Expr := dec (C.close (.const ``True []))

#print axioms basis_check_iff
end DefinographAdmission
