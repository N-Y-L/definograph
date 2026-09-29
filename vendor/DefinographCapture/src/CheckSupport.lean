import CompositionBase

set_option autoImplicit false

namespace V6Structured
open Lean Meta DerivedViewSyntax V6BinderShared
open ContextualViewDAG (Table Occ Args)

structure Tally where
  kernelCalls : Nat := 0
  accepted : Nat := 0
  notConvertible : Nat := 0
  typeErrors : Nat := 0
  unknown : Nat := 0
  coreEqCalls : Nat := 0
  checks : Nat := 0

abbrev TRef := IO.Ref Tally

/-- Every expected outcome goes through `ensure`; a failure aborts the run with `CHECK FAILED`. -/
def ensure (tl : TRef) (ok : Bool) (msg : String) : MetaM Unit := do
  tl.modify fun t => { t with checks := t.checks + 1 }
  unless ok do throwError "CHECK FAILED: {msg}"

inductive KOut where
  | accepted
  | notConvertible
  | typeError (kind : String)
  | unknown (msg : String)
  deriving Inhabited

def KOut.str : KOut → String
  | .accepted => "accepted"
  | .notConvertible => "not convertible (declTypeMismatch)"
  | .typeError k => s!"kernel type error ({k})"
  | .unknown m => s!"unknown ({m})"

def H : Nat := 200000 * 1000

def kernelCall (hb : Nat) (decl : Declaration) : MetaM (Except Kernel.Exception Environment) := do
  let env ← getEnv
  let act : IO (Except Kernel.Exception Environment) := do
    match env.addDeclCore hb.toUSize decl none with
    | .ok e => return .ok e
    | .error e => return .error e
  match ← IO.wait (← IO.asTask act (prio := .dedicated)) with
  | .ok r => return r
  | .error e => throwError "CHECK FAILED: kernel thread failed: {e}"

def lvls : List Name := [`u, `v]

def thmD (name : Name) (ty val : Expr) (ls : List Name := lvls) : Declaration :=
  .thmDecl { name, levelParams := ls, type := ty, value := val, all := [name] }

def defD (name : Name) (ty val : Expr) (ls : List Name := lvls) : Declaration :=
  .defnDecl
    { name, levelParams := ls, type := ty, value := val, hints := .abbrev, safety := .safe,
      all := [name] }

def eqProp (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [levelOne]) (mkSort .zero) a b
def reflProp (a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkSort .zero) a

def dec {n : Nat} (t : Core n) : Expr := CoreExprBridge.decode t

inductive HItem where
  | port (name : Name) (bi : BinderInfo) (dom : Expr)
  | letE (name : Name) (type value : Expr) (nondep : Bool)
  deriving Inhabited

def closeForall (items : Array HItem) (body : Expr) : Expr :=
  items.foldr (fun it acc => match it with
    | .port n bi d => .forallE n d acc bi
    | .letE n t v nd => .letE n t v acc nd) body

def closeLam (items : Array HItem) (body : Expr) : Expr :=
  items.foldr (fun it acc => match it with
    | .port n bi d => .lam n d acc bi
    | .letE n t v nd => .letE n t v acc nd) body

/-- Kernel items of a record's owner, decoded from its component references. -/
def OTel.items {Γ : List Nat} (tb : Table Γ) : {k : Nat} → OTel Γ k → Array HItem
  | _, .nil => #[]
  | _, .port T x d => (OTel.items tb T).push (.port x.name x.info (dec (ev tb d)))
  | _, .letE T nm nd ty v => (OTel.items tb T).push (.letE nm (dec (ev tb ty)) (dec (ev tb v)) nd)

end V6Structured
