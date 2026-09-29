import HeadExposure

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta DerivedViewSyntax V6Structured V6Compose DefinographAdmission

/-- A standard-core interpretation is a runtime assumption, not a proof supplied
by a declaration's printed name or by a serialized module descriptor. -/
structure LogicalDescriptor where
  name : Name
  declaringModule : Name
  kind : String
  levelParams : List Name
  type : Expr

structure LogicalOperand where
  role : String
  path : List String

inductive LogicalShape where
  | forallBinder (attrs : BinderAttrs) (bodyUsesBinder : Bool)
  | standard (form : String) (descriptor : LogicalDescriptor) (operands : Array LogicalOperand)
  | unexpanded

structure LogicalDomain (n : Nat) where
  term : Core n
  inferredType : Core n

structure LogicalInspectionCandidate (n : Nat) where
  inferredType : Core n
  domain : Option (LogicalDomain n)
  shape : LogicalShape

private def interpretation (name : Name) : Option (String × Name × Nat × List String) :=
  if name == ``Eq then some ("eq", `Init.Prelude, 1, ["carrier", "left", "right"])
  else if name == ``And then some ("and", `Init.Prelude, 0, ["required-left", "required-right"])
  else if name == ``Or then some ("or", `Init.Prelude, 0, ["alternative-left", "alternative-right"])
  else if name == ``Iff then some ("iff", `Init.Core, 0, ["equivalent-left", "equivalent-right"])
  else if name == ``Not then some ("not", `Init.Prelude, 0, ["negated"])
  else if name == ``Exists then some ("exists", `Init.Core, 1, ["carrier", "predicate"])
  else if name == ``True then some ("true", `Init.Prelude, 0, [])
  else if name == ``False then some ("false", `Init.Prelude, 0, [])
  else none

private def standardShape (initial : Environment) (expression : Expr)
    (limits : HeadExposureLimits) : Except HeadExposureFailure LogicalShape := do
  let .const name levels := expression.getAppFn | return .unexpanded
  let some (form, expectedModule, universeCount, roles) := interpretation name | return .unexpanded
  unless levels.length == universeCount && expression.getAppArgs.size == roles.length do return .unexpanded
  let actualModule := (initial.getModuleIdxFor? name).bind fun index => initial.allImportedModuleNames[index.toNat]?
  unless actualModule == some expectedModule do return .unexpanded
  let some info := initial.find? name | return .unexpanded
  let kind ← match info with
    | .defnInfo value =>
      if name != ``Not || value.safety != .safe then return .unexpanded
      pure "defnDecl"
    | .inductInfo value =>
      if name == ``Not || value.isUnsafe then return .unexpanded
      pure "inductDecl"
    | _ => return .unexpanded
  unless info.levelParams.length == universeCount do return .unexpanded
  let mut seen : NameSet := {}
  for parameter in info.levelParams do
    checkHeadExposureExpressions limits [] [(0, .const parameter [])]
    if parameter == .anonymous || seen.contains parameter then return .unexpanded
    seen := seen.insert parameter
  checkHeadExposureExpressions limits info.levelParams [(0, info.type)]
  let operands := roles.toArray.mapIdx fun index role =>
    { role, path := List.replicate (roles.length - 1 - index) "appFun" ++ ["appArg"] : LogicalOperand }
  return .standard form ⟨name, expectedModule, kind, info.levelParams, info.type⟩ operands

/-- Fresh formation candidates in the unchanged positional home. No isProp or
normalization pass supplies logical authority; the caller checks these exact
pairs and the reader associates each interpretation with its actual receipt. -/
def prepareLogicalInspection {n : Nat} (initial : Environment) (allowed : List Name)
    (context : CTel n) (term type : Core n) (limits : HeadExposureLimits := {}) :
    MetaM (Except HeadExposureFailure (LogicalInspectionCandidate n)) := do
  ensureSourceBasis initial [contextExpr context, dec term, dec type]
  match checkHeadExposureExpressions limits allowed [(0, contextExpr context), (n, dec term), (n, dec type)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  let inferredType ← inferredTypeAt context term
  ensureSourceBasis initial [dec inferredType]
  match checkHeadExposureExpressions limits allowed [(n, dec inferredType)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  match term with
  | .pi attrs domain body =>
    let domainType ← inferredTypeAt context domain
    ensureSourceBasis initial [dec domainType]
    match checkHeadExposureExpressions limits allowed [(n, dec domainType)] with
    | .error reason => return .error reason
    | .ok _ => pure ()
    return .ok ⟨inferredType, some ⟨domain, domainType⟩, .forallBinder attrs ((dec body).hasLooseBVar 0)⟩
  | _ =>
    let shape ← match standardShape initial (dec term) limits with
      | .error reason => return .error reason
      | .ok shape => pure shape
    if let .standard _ descriptor _ := shape then ensureSourceBasis initial [descriptor.type]
    return .ok ⟨inferredType, none, shape⟩

private def operandJson (operand : LogicalOperand) : Json :=
  Json.mkObj [("role", toJson operand.role), ("path", toJson operand.path)]

def logicalShapeJson : LogicalShape → Except String Json
  | .unexpanded => pure (Json.mkObj [("kind", toJson "unexpanded"), ("operands", Json.arr #[])])
  | .forallBinder attrs bodyUsesBinder => pure (Json.mkObj [
      ("kind", toJson "forall"), ("binder", Json.mkObj [("name", nameJson attrs.name), ("info", binderJson attrs.info)]),
      ("bodyUsesBinder", toJson bodyUsesBinder), ("operands", Json.arr #[
        operandJson ⟨"domain", ["piDomain"]⟩, operandJson ⟨"body", ["piBody"]⟩])])
  | .standard form descriptor operands => do
    return Json.mkObj [("kind", toJson "standard"), ("form", toJson form),
      ("descriptor", Json.mkObj [("interpretationId", toJson "lean-standard-core-v1"),
        ("name", nameJson descriptor.name), ("declaringModule", nameJson descriptor.declaringModule),
        ("kind", toJson descriptor.kind), ("levelParams", arr (descriptor.levelParams.map nameJson)),
        ("type", ← exprJson descriptor.type), ("safety", toJson "safe")]),
      ("operands", Json.arr (operands.map operandJson))]

def logicalDomainJson {n : Nat} : Option (LogicalDomain n) → Except String Json
  | none => pure Json.null
  | some domain => return Json.mkObj [("term", ← exprJson (dec domain.term)),
      ("inferredType", ← exprJson (dec domain.inferredType))]

end Definograph
