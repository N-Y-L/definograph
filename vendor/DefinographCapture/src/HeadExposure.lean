import InferComponent
import RawJson

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta DerivedViewSyntax V6Structured V6Compose DefinographAdmission

inductive HeadExposureTarget where
  | term | type
  deriving Inhabited, BEq

def HeadExposureTarget.json : HeadExposureTarget → Json
  | .term => toJson "term"
  | .type => toJson "type"

structure HeadExposureFailure where
  kind : String
  phase : String
  reason : String
  deriving Inhabited

/-- Callers may lower, but not raise, the construction ceilings. Copies and
inserted argument occurrences are charged before their constructors are built. -/
structure HeadExposureLimits where
  maxNodes : Nat := 20000
  maxDepth : Nat := 96
  maxTextBytes : Nat := 128 * 1024
  deriving Inhabited

structure HeadExposureCandidate (n : Nat) where
  target : HeadExposureTarget
  before : Core n
  definition : DefinitionVal
  actualLevels : List ULevel
  arguments : Array (Core n)
  betaApplications : Nat
  after : Core n
  carrier : Core n
  carrierSort : ULevel

inductive HeadExposureState (n : Nat) where
  | unavailable (failure : HeadExposureFailure)
  | candidate (value : HeadExposureCandidate n) (checking : Except String Unit)

private def failure (kind phase reason : String) : HeadExposureFailure := ⟨kind, phase, reason⟩

private structure BuildState where
  limits : HeadExposureLimits
  nodes : Nat := 0
  textBytes : Nat := 0

private abbrev BuildM := StateT BuildState (Except HeadExposureFailure)

private def refuse {α : Type} (reason : String) : BuildM α :=
  throw (failure "unsupported" "definition" reason)

private def charge (depth : Nat) : BuildM Unit := do
  let s ← get
  if depth > s.limits.maxDepth then
    throw (failure "limit" "construction" "definition exposure exceeds the constructor depth limit")
  if s.nodes >= s.limits.maxNodes then
    throw (failure "limit" "construction" "definition exposure exceeds the constructor node limit")
  set { s with nodes := s.nodes + 1 }

private def chargeText (value : String) : BuildM Unit := do
  let s ← get
  if value.utf8ByteSize > s.limits.maxTextBytes - s.textBytes then
    throw (failure "limit" "construction" "definition exposure exceeds the cumulative UTF-8 text limit")
  set { s with textBytes := s.textBytes + value.utf8ByteSize }

private def chargeNat (n : Nat) : BuildM Unit := do
  if n >= 10 ^ 10000 then
    throw (failure "limit" "construction" "definition exposure exceeds the exact natural digit limit")
  chargeText (toString n)

private def inspectName (depth : Nat) (name : Name) : BuildM Unit := do
  if depth > 128 then throw (failure "limit" "construction" "name exceeds its independent transport depth limit")
  match name with
  | .anonymous => pure ()
  | .str p s => inspectName (depth + 1) p; chargeText s
  | .num p n => inspectName (depth + 1) p; chargeNat n

/-- Structural, simultaneous universe substitution. Insertion does not recurse
through the substitution again, and max/imax use their original constructors. -/
private partial def copyLevel (allowed : List Name) (substitution : List (Name × Level))
    (depth : Nat) (level : Level) : BuildM Level := do
  match level with
  | .param name =>
    if let some (_, actual) := substitution.find? (fun p => p.1 == name) then
      return ← copyLevel allowed [] depth actual
    charge depth
    inspectName 0 name
    unless allowed.contains name do refuse "universe parameter is not declared by this input"
    return .param name
  | .zero => charge depth; return .zero
  | .succ u => charge depth; return .succ (← copyLevel allowed substitution (depth + 1) u)
  | .max u v =>
    charge depth
    return .max (← copyLevel allowed substitution (depth + 1) u)
      (← copyLevel allowed substitution (depth + 1) v)
  | .imax u v =>
    charge depth
    return .imax (← copyLevel allowed substitution (depth + 1) u)
      (← copyLevel allowed substitution (depth + 1) v)
  | .mvar _ => refuse "unresolved universe metavariable is outside the finished profile"

/-- Copy a finite expression while optionally removing outer binders. `actuals`
is in binder order (oldest first). `lift` shifts only free ambient references in
inserted arguments; it never changes their own lexical binders. -/
private partial def copyExpr (allowed : List Name) (levels : List (Name × Level))
    (ambient depth lexical lift : Nat) (actuals : Array Expr) (expr : Expr) : BuildM Expr := do
  match expr with
  | .bvar index =>
    if index >= lexical && index - lexical < actuals.size then
      let arg := actuals[actuals.size - 1 - (index - lexical)]!
      return ← copyExpr allowed [] ambient depth 0 lexical #[] arg
    charge depth
    if index < lexical then
      chargeNat index
      return .bvar index
    let free := index - lexical - actuals.size
    unless free < ambient do refuse "bound reference is outside its exact positional home"
    let index := lexical + free + lift
    chargeNat index
    return .bvar index
  | .sort u =>
    charge depth
    return .sort (← copyLevel allowed levels (depth + 1) u)
  | .const name us =>
    charge depth
    inspectName 0 name
    if name == ``sorryAx then refuse "definition exposure contains a placeholder (sorry)"
    let mut out := []
    for u in us do out := (← copyLevel allowed levels (depth + 1) u) :: out
    return .const name out.reverse
  | .lit (.natVal n) => charge depth; chargeNat n; return .lit (.natVal n)
  | .lit (.strVal s) => charge depth; chargeText s; return .lit (.strVal s)
  | .app f a =>
    charge depth
    return .app (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals f)
      (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals a)
  | .lam name type body info =>
    charge depth; inspectName 0 name
    return .lam name (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals type)
      (← copyExpr allowed levels ambient (depth + 1) (lexical + 1) lift actuals body) info
  | .forallE name type body info =>
    charge depth; inspectName 0 name
    return .forallE name (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals type)
      (← copyExpr allowed levels ambient (depth + 1) (lexical + 1) lift actuals body) info
  | .letE name type value body nondep =>
    charge depth; inspectName 0 name
    return .letE name (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals type)
      (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals value)
      (← copyExpr allowed levels ambient (depth + 1) (lexical + 1) lift actuals body) nondep
  | .proj name index value =>
    charge depth; inspectName 0 name; chargeNat index
    return .proj name index (← copyExpr allowed levels ambient (depth + 1) lexical lift actuals value)
  | .fvar _ => refuse "free variables are outside the positional definition profile"
  | .mvar _ => refuse "unresolved expression metavariable is outside the finished profile"
  | .mdata _ _ => refuse "definition metadata is outside the finished profile; it was not erased"

private def validLimits (limits : HeadExposureLimits) : Except HeadExposureFailure Unit := do
  unless limits.maxNodes > 0 && limits.maxNodes <= 20000 &&
      limits.maxDepth > 0 && limits.maxDepth <= 96 &&
      limits.maxTextBytes > 0 && limits.maxTextBytes <= 128 * 1024 do
    throw (failure "limit" "construction" "invalid definition exposure construction limits")

/-- Each standalone expression has its own occurrence/depth/text allowance. -/
def checkHeadExposureExpressions (limits : HeadExposureLimits) (allowed : List Name)
    (expressions : List (Nat × Expr)) : Except HeadExposureFailure Unit := do
  validLimits limits
  for (arity, expr) in expressions do
    let _ ← (copyExpr allowed [] arity 0 0 0 #[] expr).run { limits }

private def reifyExact (expr : Expr) (n : Nat) : Except HeadExposureFailure (Core n) :=
  match CoreExprBridge.reify expr n with
  | some value => .ok value
  | none => .error (failure "unsupported" "definition" "result is outside the exact finished Core profile")

/-- A single body substitution and the original leading-lambda-spine application.
No smart unfolding, zeta, projection, recursor or newly created head reduction. -/
def buildHeadExposure {n : Nat} (initial : Environment) (allowed : List Name)
    (before : Core n) (limits : HeadExposureLimits := {}) :
    Except HeadExposureFailure (DefinitionVal × List ULevel × Array (Core n) × Nat × Core n) := do
  validLimits limits
  let expression := dec before
  checkHeadExposureExpressions limits allowed [(n, expression)]
  let .const name us := expression.getAppFn
    | throw (failure "unsupported" "head" "the selected expression has no global constant application head")
  let some (.defnInfo definition) := initial.find? name
    | throw (failure "unsupported" "head" "the head is not a definition in the initial environment")
  unless definition.safety == .safe do
    throw (failure "unsupported" "head" "only safe definition heads can be exposed")
  unless definition.levelParams.length == us.length do
    throw (failure "unsupported" "universes" "definition universe argument count differs from its parameter count")
  let args := expression.getAppArgs
  let header : BuildM Unit := do
    inspectName 0 definition.name
    for name in definition.levelParams do inspectName 0 name
  let _ ← header.run { limits }
  let mut seen : NameSet := {}
  for name in definition.levelParams do
    if seen.contains name then
      throw (failure "unsupported" "universes" "definition universe parameters are not distinct")
    seen := seen.insert name
  checkHeadExposureExpressions limits definition.levelParams [(0, definition.type), (0, definition.value)]
  let substitution := definition.levelParams.zip us
  let _ ← (copyExpr allowed substitution 0 0 0 0 #[] definition.type).run { limits }
  let (instantiated, _) ← (copyExpr allowed substitution 0 0 0 0 #[] definition.value).run { limits }
  let action : BuildM (Expr × Nat) := do
    let mut body := instantiated
    let mut consumed := 0
    while consumed < args.size do
      match body with
      | .lam _ _ next _ => body := next; consumed := consumed + 1
      | _ => break
    let rest := args.size - consumed
    let mut out ← copyExpr allowed [] n rest 0 0 (args.extract 0 consumed) body
    for index in [consumed:args.size] do
      let depth := args.size - 1 - index
      charge depth
      let arg ← copyExpr allowed [] n (depth + 1) 0 0 #[] args[index]!
      out := .app out arg
    return (out, consumed)
  let ((out, consumed), _) ← action.run { limits }
  let result ← reifyExact out n
  let mut arguments := #[]
  for arg in args do arguments := arguments.push (← reifyExact arg n)
  let mut actualLevels := []
  for u in us do
    let .sort level ← reifyExact (.sort u) 0
      | throw (failure "unsupported" "universes" "invalid actual universe")
    actualLevels := level :: actualLevels
  return (definition, actualLevels.reverse, arguments, consumed, result)

/-- Inference proposes a carrier sort; the final declarations check it. This
boundary requires the literal inferred Sort, with no added weak-head reduction. -/
def prepareHeadExposure {n : Nat} (initial : Environment) (allowed : List Name)
    (C : CTel n) (term type : Core n) (target : HeadExposureTarget)
    (limits : HeadExposureLimits := {}) : MetaM (Except HeadExposureFailure (HeadExposureCandidate n)) := do
  if n > 128 then
    return .error (failure "limit" "context" "the selected context exceeds 128 declarations")
  let before := if target == .term then term else type
  let transformed := buildHeadExposure initial allowed before limits
  let (definition, actualLevels, arguments, betaApplications, after) ← match transformed with
    | .ok result => pure result
    | .error reason => return .error reason
  let inferred ← inferredTypeAt C type
  let .sort level := inferred
    | return .error (failure "unsupported" "carrier" "the carrier's inferred type is not a literal Sort")
  let carrier := if target == .term then type else .sort level
  let carrierSort := if target == .term then level else .succ level
  let candidate : HeadExposureCandidate n := {
    target, before, definition, actualLevels, arguments, betaApplications, after, carrier, carrierSort }
  let expressions := [contextExpr C, definition.type, definition.value, dec before, dec after, dec carrier,
    .sort (CoreExprBridge.decodeLevel carrierSort)]
  ensureSourceBasis initial expressions
  let checked := checkHeadExposureExpressions limits allowed
    [(0, contextExpr C), (n, dec before), (n, dec after), (n, dec carrier),
     (0, .sort (CoreExprBridge.decodeLevel carrierSort))]
  return checked.map fun _ => candidate

def headExposureConversion {n : Nat} (declPrefix : Name) (params : List Name)
    (C : CTel n) (candidate : HeadExposureCandidate n) : Declaration :=
  let universeLevel := CoreExprBridge.decodeLevel candidate.carrierSort
  thmD (declPrefix ++ `conversion)
    (closeForall (CTel.items C) (mkApp3 (mkConst ``Eq [universeLevel])
      (dec candidate.carrier) (dec candidate.before) (dec candidate.after)))
    (closeLam (CTel.items C) (mkApp2 (mkConst ``Eq.refl [universeLevel])
      (dec candidate.carrier) (dec candidate.before))) params

end Definograph
