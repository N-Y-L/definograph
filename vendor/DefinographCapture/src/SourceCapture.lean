import PacketCapture
import NamedContextAdmission
import CheckedExtraction
import RawJson
import FieldInspection
import LogicalInspection

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Definograph
open Lean Meta DerivedViewSyntax V6Structured V6Compose DefinographAdmission

/-- Encoding choice for ignored original metadata only; never a checking policy. -/
inductive RetainedMetadataProfile where
  | normalizedV2
  | rawV1
  deriving Inhabited, BEq

/-- Names, universe parameters and per-check kernel heartbeats are explicit caller
policy. Actual bounds are retained in the callback receipts, not inferred from a
serialized policy name. An enclosing caller must bound total time and output. -/
structure SourceCheckPolicy where
  declarationPrefix : Name
  universeParams : List Name := []
  heartbeatFor : String → Nat
  retainedMetadata : RetainedMetadataProfile := .normalizedV2

/-- Exact source data accompany a local typed result and the checks actually run.
`capture.environments[0]` is the initial environment for this binding. This is
neither a browser certification token nor an admission Boolean. In particular,
an empty check array does not establish admission. -/
structure CapturedSource (α : Type) where
  binding : Json
  capture : CapturedChecks (Except String α)

structure NamedSourceResult where
  component : NamedComponent
  checks : Checks

/-- The selected telescope/component and exact rebuild witness remain in
`selected`. `checks` includes both supplied source typing and inferred-root /
selected-component checks. `sourceChecks` retains the supplied-source subset.
A returned value alone does not assert that any checks were accepted. -/
structure NamedExtractionResult where
  source : NamedComponent
  path : List OccurrenceDecomposition.Step
  sourceChecks : Checks
  selected : OccurrenceDecomposition.SourceHome source.context.telescope source.term
  selectedType : Core selected.extraction.home
  checks : Checks

structure NamedHeadExposureResult where
  base : NamedExtractionResult
  exposure : HeadExposureState base.selected.extraction.home

inductive DecompositionOperation where
  | expose (target : HeadExposureTarget)
  | focus (path : List OccurrenceDecomposition.Step)
  | fields
  | project (index : Nat)
  | typeComponent
  | logical
  deriving Inhabited

inductive DecompositionProfile where
  | legacy | directFields | logicalStructure
  deriving Inhabited, BEq

/-- Existing positional syntax, packaged across heterogeneous selected homes.
No generated free-variable identities become source data. -/
structure DecompositionPair where
  arity : Nat
  context : CTel arity
  term : Core arity
  type : Core arity

structure DecompositionFocus (input : DecompositionPair) where
  selected : OccurrenceDecomposition.SourceHome input.context input.term
  type : Core selected.extraction.home

inductive DecompositionOutput (input : DecompositionPair) where
  | unavailable (reason : HeadExposureFailure)
  | exposed (candidate : HeadExposureCandidate input.arity) (checking : Except String Unit)
  | focused (candidate : DecompositionFocus input) (checking : Except String Unit)
  | catalogued (catalogue : DirectFieldCatalogue input.arity)
  | projected (candidate : DirectFieldCandidate input.arity) (checking : Except String Unit)
  | typeComponent (type : Core input.arity) (checking : Except String Unit)
  | logical (candidate : LogicalInspectionCandidate input.arity) (checking : Except String Unit)

inductive DecompositionReplay where
  | new | matched | mismatch | notCompared
  deriving Inhabited, BEq

structure DecompositionStep where
  index : Nat
  operation : DecompositionOperation
  input : DecompositionPair
  output : DecompositionOutput input
  receiptStart : Nat
  receiptCount : Nat
  replay : DecompositionReplay

structure NamedDecompositionResult where
  base : NamedExtractionResult
  steps : Array DecompositionStep
  stop : Option HeadExposureFailure
  profile : DecompositionProfile := .legacy

structure SourceCompositionResult (m : Nat) where
  term : Core m
  type : Core m
  checks : Checks

private def localKindJson : LocalDeclKind → Json
  | .default => toJson "default"
  | .implDetail => toJson "implDetail"
  | .auxDecl => toJson "auxDecl"

/-- Record the actual constructor, including the opaque stored value of a
nondependent ldecl. Serializing that value neither checks it nor turns it into
a defining equation in the admitted context. -/
def localDeclarationJson : LocalDecl → Except String Json
  | .cdecl index id userName type info kind => do
    return Json.mkObj [
      ("constructor", toJson "cdecl"), ("index", exactNatJson index),
      ("fvarId", nameJson id.name), ("userName", nameJson userName),
      ("type", ← exprJson type), ("binderInfo", binderJson info),
      ("kind", localKindJson kind)]
  | .ldecl index id userName type value nondep kind => do
    return Json.mkObj [
      ("constructor", toJson "ldecl"), ("index", exactNatJson index),
      ("fvarId", nameJson id.name), ("userName", nameJson userName),
      ("type", ← exprJson type), ("value", ← exprJson value),
      ("nondep", toJson nondep), ("kind", localKindJson kind)]

/-- Types and values are exact positional expressions in their own preceding
home. The recursive constructor retains declaration order and genuine lets. -/
private def sourceTelescopeJson : {n : Nat} → CTel n → Except String Json
  | _, .nil => pure (tag "nil")
  | _, .port C attrs type => do
    return tag "port" [← sourceTelescopeJson C, attrsJson attrs, ← exprJson (dec type)]
  | _, .letE C name nondep type value => do
    return tag "letE" [← sourceTelescopeJson C, nameJson name, toJson nondep,
      ← exprJson (dec type), ← exprJson (dec value)]

private def positionalContextJson {n : Nat} (C : CTel n) : Except String Json := do
  return Json.mkObj [("arity", toJson n), ("telescope", ← sourceTelescopeJson C)]

/-- Serialize an actual positional triple; this function does not admit inputs. -/
def selectedTripleJson {n : Nat} (C : CTel n) (term type : Core n) : Except String Json := do
  return Json.mkObj [("home", ← positionalContextJson C),
    ("term", ← exprJson (dec term)), ("type", ← exprJson (dec type))]

private def originalDeclarationsJson (C : NamedContext) (profile : RetainedMetadataProfile) : Except String Json := do
  if profile == .normalizedV2 then return arr (← C.original.mapM localDeclarationJson)
  let ignored := C.original.filterMap fun declaration => match declaration with
    | .ldecl _ _ _ _ value true _ => some value
    | _ => none
  let rawValues ← rawExprsJson ignored.toArray
  let mut cursor := 0
  let mut originals := #[]
  for declaration in C.original do
    let encoded ← match declaration with
      | .ldecl index id userName type _ true kind => do
        let some value := rawValues[cursor]? | throw "raw metadata encoding lost its declaration association"
        cursor := cursor + 1
        pure (Json.mkObj [("constructor", toJson "ldecl"), ("index", exactNatJson index),
          ("fvarId", nameJson id.name), ("userName", nameJson userName), ("type", ← exprJson type),
          ("value", value), ("nondep", toJson true), ("kind", localKindJson kind)])
      | _ => localDeclarationJson declaration
    originals := originals.push encoded
  return .arr originals

private def namedContextJson (C : NamedContext) (profile : RetainedMetadataProfile) : Except String Json := do
  return Json.mkObj [
    ("arity", toJson C.ids.length), ("telescope", ← sourceTelescopeJson C.telescope),
    ("registry", arr (C.ids.map fun id => nameJson id.name)),
    ("registryOrder", toJson "mostRecentFirst"),
    ("originalDeclarations", ← originalDeclarationsJson C profile),
    ("originalDeclarationOrder", toJson "oldestFirst")]

private def sourceStepJson : OccurrenceDecomposition.Step → Json
  | .appFun => tag "appFun"
  | .appArg => tag "appArg"
  | .lamDomain => tag "lamDomain"
  | .lamBody => tag "lamBody"
  | .piDomain => tag "piDomain"
  | .piBody => tag "piBody"
  | .letType => tag "letType"
  | .letValue => tag "letValue"
  | .letBody => tag "letBody"
  | .projValue => tag "projValue"
  | .uniqueArg index => tag "uniqueArg" [exactNatJson index]
  | .instBody => tag "instBody"
  | .instActual index => tag "instActual" [exactNatJson index]

private def bindingFields (attempt operation sourceKind : String)
    (policy : SourceCheckPolicy) : List (String × Json) :=
  [("schema", toJson (if policy.retainedMetadata == .rawV1 then (3 : Nat) else 2)), ("attempt", toJson attempt),
   ("operation", toJson operation), ("sourceKind", toJson sourceKind),
   ("declarationPrefix", nameJson policy.declarationPrefix),
   ("universeParams", arr (policy.universeParams.map nameJson)),
   ("initialEnvironment", toJson (0 : Nat))] ++
  (if policy.retainedMetadata == .rawV1 then
    [("naturalProfile", toJson (2 : Nat)), ("rawProfile", toJson "definograph.raw.v1")] else [])

private def namedBindingJson (attempt operation sourceKind : String)
    (policy : SourceCheckPolicy) (component : NamedComponent)
    (extra : List (String × Json) := []) : Except String Json := do
  return Json.mkObj (bindingFields attempt operation sourceKind policy ++ [
    ("context", ← namedContextJson component.context policy.retainedMetadata),
    ("sourceTerm", ← exprJson component.sourceTerm),
    ("sourceType", ← exprJson component.sourceType),
    ("positionalTerm", ← exprJson (dec component.term)),
    ("positionalType", ← exprJson (dec component.type))] ++ extra)

/-- Only this path runs checks. Action failures are caught *inside* the capture
session, so a later failure preserves prior receipts and environment snapshots.
All source serialization has already succeeded before the session starts. -/
private def captureSourceAction {α : Type} (attempt operation : String)
    (policy : SourceCheckPolicy) (binding : Json)
    (action : Check → MetaM α) : MetaM (Except String (CapturedSource α)) := do
  match checkExactNaturalBudget binding with
  | .error reason => return .error reason
  | .ok _ => pure ()
  try
    let capture ← captureChecks attempt operation policy.heartbeatFor fun run => do
      try
        return Except.ok (← action run)
      catch error =>
        return Except.error (← error.toMessageData.toString)
    return .ok ⟨binding, capture⟩
  catch error =>
    -- Capture setup validation can fail before an action or any check begins.
    return .error (← error.toMessageData.toString)

private def ingestActualSource (sourceTerm sourceType : Expr) :
    MetaM (Except String NamedComponent) := do
  let some context ← captureLocalContext
    | return .error "the actual local context is outside the named source admission profile"
  let some component := ingestNamedComponent context sourceTerm sourceType
    | return .error "the exact source term or supplied type is outside the named source admission profile"
  return .ok component

/-- Capture an exact term and its supplied type against the actual current local
context. Source ingestion and serialization failures are outer errors with no
checks. Attempted action failures are inside `capture.value`, alongside retained
receipts. The typed component preserves both exact named readback witnesses. -/
def captureNamedSource (attempt operation : String) (policy : SourceCheckPolicy)
    (sourceTerm sourceType : Expr) : MetaM (Except String (CapturedSource NamedSourceResult)) := do
  if policy.declarationPrefix == .anonymous then
    return .error "source declaration prefix must be nonempty"
  let component ← match ← ingestActualSource sourceTerm sourceType with
    | .ok component => pure component
    | .error reason => return .error reason
  let binding ← match namedBindingJson attempt operation "namedComponent" policy component with
    | .ok binding => pure binding
    | .error reason => return .error reason
  captureSourceAction attempt operation policy binding fun run => do
    let checks ← checkNamedWith run policy.declarationPrefix policy.universeParams component
    return ⟨component, checks⟩

private def namedExtractionAction (run : Check) (policy : SourceCheckPolicy)
    (component : NamedComponent) (path : List OccurrenceDecomposition.Step) :
    MetaM NamedExtractionResult := do
  let sourceChecks ← checkNamedWith run (policy.declarationPrefix ++ `source)
    policy.universeParams component
  let some ⟨selected, selectedType, checks⟩ ← checkExtractionWith run
      (policy.declarationPrefix ++ `extraction) policy.universeParams
      component.context.telescope component.term path
    | throwError "the selected constructor path is not an ordinary source occurrence"
  return ⟨component, path, sourceChecks, selected, selectedType, sourceChecks ++ checks⟩

/-- Check the exact supplied root type, then extract and check the ordinary source
occurrence at a constructor path. A nonexistent path is an explicit action error,
not an empty successful extraction. The selected home and rebuild proof remain
typed values; no reconstruction from formatted labels or JSON is required. -/
def captureNamedExtraction (attempt operation : String) (policy : SourceCheckPolicy)
    (sourceTerm sourceType : Expr) (path : List OccurrenceDecomposition.Step) :
    MetaM (Except String (CapturedSource NamedExtractionResult)) := do
  if policy.declarationPrefix == .anonymous then
    return .error "source declaration prefix must be nonempty"
  let component ← match ← ingestActualSource sourceTerm sourceType with
    | .ok component => pure component
    | .error reason => return .error reason
  let binding ← match namedBindingJson attempt operation "namedExtraction" policy component
      [("path", arr (path.map sourceStepJson))] with
    | .ok binding => pure binding
    | .error reason => return .error reason
  captureSourceAction attempt operation policy binding fun run => do
    namedExtractionAction run policy component path

private def headBounded (message : String) : String :=
  String.ofList (message.toList.take 2048)

private def headExceptionKind (error : Exception) : String :=
  if error.isMaxHeartbeat || error.isMaxRecDepth then "limit" else "error"

private def headJsonDepthWithin : Nat → Json → Bool
  | 0, .arr _ | 0, .obj _ => false
  | 0, _ => true
  | fuel + 1, .arr values => values.all (headJsonDepthWithin fuel)
  | fuel + 1, .obj fields => fields.toList.all (fun (_, value) => headJsonDepthWithin fuel value)
  | _ + 1, _ => true

private def exposureFailure {n : Nat} (kind phase reason : String) : HeadExposureState n :=
  .unavailable ⟨kind, phase, headBounded reason⟩

private def checkHeadDeclarations {n : Nat} (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (C : CTel n) (candidate : HeadExposureCandidate n) :
    MetaM (Except HeadExposureFailure Unit) := do
  let result := defD (policy.declarationPrefix ++ `result.component)
    (dec (C.close candidate.carrier)) (dec (ctelLam C candidate.after)) policy.universeParams
  let context := thmD (policy.declarationPrefix ++ `result.context)
    (dec (C.close (.const ``True []))) (dec (ctelLam C (.const ``True.intro []))) policy.universeParams
  let conversion := headExposureConversion policy.declarationPrefix policy.universeParams C candidate
  let mut expressions := []
  for declaration in [context, result, conversion] do
    match declaration with
    | .thmDecl value => expressions := value.type :: value.value :: expressions
    | .defnDecl value => expressions := value.type :: value.value :: expressions
    | _ => pure ()
  ensureSourceBasis initial expressions
  match checkHeadExposureExpressions limits policy.universeParams (expressions.map fun e => (0, e)) with
  | .error reason => return .error reason
  | .ok _ => pure ()
  for declaration in [context, result, conversion] do
    let exact ← match declarationJson declaration with
      | .ok exact => pure exact
      | .error reason => return .error ⟨"limit", "declarations", headBounded reason⟩
    if !headJsonDepthWithin 120 exact || exact.compress.utf8ByteSize > 1024 * 1024 then
      return .error ⟨"limit", "declarations", "checking declaration exceeds its transport limit"⟩
  return .ok ()

/-- Fresh base extraction and a single requested head exposure share one actual
callback/environment chain. Parent JSON is compared, never used to reconstruct
the checking environment. Partial extra failures retain the exact candidate. -/
def captureNamedHeadExposure (attempt operation : String) (policy : SourceCheckPolicy)
    (sourceTerm sourceType : Expr) (path : List OccurrenceDecomposition.Step)
    (target : HeadExposureTarget) (expectedSelected : Json) (limits : HeadExposureLimits := {}) :
    MetaM (Except String (CapturedSource NamedHeadExposureResult)) := do
  if policy.declarationPrefix == .anonymous then return .error "source declaration prefix must be nonempty"
  unless headJsonDepthWithin 120 expectedSelected do return .error "expected selection exceeds the nesting limit"
  if expectedSelected.compress.utf8ByteSize > 768 * 1024 then return .error "expected selection exceeds the byte limit"
  let initial ← getEnv
  let component ← match ← ingestActualSource sourceTerm sourceType with
    | .ok component => pure component
    | .error reason => return .error reason
  let binding ← match namedBindingJson attempt operation "namedHeadExposure" policy component [
      ("path", arr (path.map sourceStepJson)), ("target", target.json), ("expectedSelected", expectedSelected)] with
    | .ok binding => pure binding
    | .error reason => return .error reason
  match checkExactNaturalBudget binding with
  | .error reason => return .error reason
  | .ok _ => pure ()
  try
    let capture ← captureChecks attempt operation policy.heartbeatFor fun run =>
      tryCatchRuntimeEx (do
        let base ← namedExtractionAction run policy component path
        let C := base.selected.telescope
        let actual ← match selectedTripleJson C base.selected.extraction.component base.selectedType with
          | .ok actual => pure actual
          | .error reason => throwError "{reason}"
        unless actual == expectedSelected do
          return Except.ok { base, exposure := exposureFailure "prerequisite" "selected-match" "The freshly extracted selected triple differs from the requested parent." }
        let prepared ← tryCatchRuntimeEx
          (prepareHeadExposure initial policy.universeParams C base.selected.extraction.component base.selectedType target limits)
          (fun error => do pure (.error ⟨headExceptionKind error, "preparation", headBounded (← error.toMessageData.toString)⟩))
        let candidate ← match prepared with
          | .ok candidate => pure candidate
          | .error reason => return Except.ok { base, exposure := .unavailable reason }
        let preflight ← tryCatchRuntimeEx
          (checkHeadDeclarations initial policy limits C candidate)
          (fun error => do pure (.error ⟨headExceptionKind error, "declarations", headBounded (← error.toMessageData.toString)⟩))
        match preflight with
        | .error reason => return Except.ok { base, exposure := .unavailable reason }
        | .ok _ => pure ()
        let checking ← tryCatchRuntimeEx (do
          let _ ← checkComponentWith run (policy.declarationPrefix ++ `result)
            policy.universeParams C candidate.after candidate.carrier
          let _ ← run "conversion" (headExposureConversion policy.declarationPrefix policy.universeParams C candidate)
          pure (Except.ok ()))
          (fun error => do pure (Except.error (headBounded (← error.toMessageData.toString))))
        return Except.ok { base, exposure := .candidate candidate checking })
        (fun error => do pure (Except.error (headBounded (← error.toMessageData.toString))))
    return .ok ⟨binding, capture⟩
  catch error => return .error (headBounded (← error.toMessageData.toString))

def headExposureStateJson {n : Nat} (C : CTel n) (state : HeadExposureState n) : Except String Json := do
  match state with
  | .unavailable reason => return Json.mkObj [("status", toJson "unavailable"),
      ("kind", toJson reason.kind), ("phase", toJson reason.phase), ("reason", toJson (headBounded reason.reason))]
  | .candidate candidate checking =>
    let definition := candidate.definition
    let checkJson := match checking with
      | .ok _ => Json.mkObj [("status", toJson "completed")]
      | .error reason => Json.mkObj [("status", toJson "error"), ("reason", toJson (headBounded reason))]
    return Json.mkObj [("status", toJson "candidate"), ("before", ← exprJson (dec candidate.before)),
      ("result", ← selectedTripleJson C candidate.after candidate.carrier),
      ("definition", Json.mkObj [("name", nameJson definition.name),
        ("levelParams", arr (definition.levelParams.map nameJson)), ("type", ← exprJson definition.type),
        ("value", ← exprJson definition.value), ("hints", hintsJson definition.hints), ("safety", toJson "safe")]),
      ("actualLevels", arr (candidate.actualLevels.map fun u => levelJson (CoreExprBridge.decodeLevel u))),
      ("arguments", Json.arr (← candidate.arguments.mapM fun arg => exprJson (dec arg))),
      ("betaApplications", toJson candidate.betaApplications),
      ("carrierSort", levelJson (CoreExprBridge.decodeLevel candidate.carrierSort)), ("checking", checkJson)]

/-- Refuse an incoherent partial capture. In particular, a callback's audit can
fail after installing an environment but before appending its receipt. -/
private def checkHeadCaptureLineage {α : Type} (capture : CapturedChecks α) : Except String Unit := do
  unless capture.checks.size == capture.audits.size do throw "head exposure receipt/audit counts are inconsistent"
  let mut environment := 0
  for index in [:capture.checks.size] do
    let receipt := capture.checks[index]!
    let audit := capture.audits[index]!
    let before ← receipt.getObjValAs? Nat "envBefore"
    let after ← receipt.getObjValAs? Nat "envAfter"
    let id ← receipt.getObjValAs? Nat "id"
    let tag ← (← receipt.getObjVal? "outcome").getObjValAs? String "tag"
    unless id == index && before == environment && after == before + (if tag == "accepted" then 1 else 0) do
      throw "head exposure receipt environment chain is inconsistent"
    unless (← audit.getObjValAs? Nat "checkId") == index &&
        (← audit.getObjValAs? Nat "environment") == after &&
        (← audit.getObjVal? "subject") == (← receipt.getObjVal? "declaration") do
      throw "head exposure audit association is inconsistent"
    environment := after
  unless capture.environments.size == environment + 1 do
    throw "head exposure contains an environment snapshot without its complete receipt and audit"

/-- Complete checking section for the editor adapter. The caller handles any
error by explicitly omitting the whole section, never by truncating receipts. -/
def capturedHeadExposureJson (captured : CapturedSource NamedHeadExposureResult) : Except String Json := do
  checkHeadCaptureLineage captured.capture
  let count := captured.capture.checks.size
  let countMatches : Bool := match captured.capture.value with
    | .error _ => count <= 6
    | .ok result => match result.exposure with
      | .unavailable _ => count == 6
      | .candidate _ (.ok _) => count == 9
      | .candidate _ (.error _) => 6 <= count && count <= 9
  unless countMatches do throw "head exposure action and receipt count are inconsistent"
  let (action, selected, exposure) ← match captured.capture.value with
    | .error reason => pure (Json.mkObj [("status", toJson "error"),
        ("reason", toJson (headBounded reason))], Json.null, Json.null)
    | .ok result => do
      let selected ← selectedTripleJson result.base.selected.telescope result.base.selected.extraction.component result.base.selectedType
      let exposure ← headExposureStateJson result.base.selected.telescope result.exposure
      pure (Json.mkObj [("status", toJson "completed")], selected, exposure)
  let value := Json.mkObj [("status", toJson "captured"), ("action", action),
    ("binding", captured.binding), ("selected", selected), ("exposure", exposure),
    ("checks", Json.arr captured.capture.checks), ("audits", Json.arr captured.capture.audits),
    ("environmentSnapshotCount", toJson captured.capture.environments.size)]
  checkExactNaturalBudget value
  unless headJsonDepthWithin 120 value do throw "head exposure checking exceeds the nesting limit"
  if value.compress.utf8ByteSize > 1024 * 1024 then throw "head exposure checking exceeds the byte limit"
  return value

private def ordinaryStepName : OccurrenceDecomposition.Step → Except String String
  | .appFun => .ok "appFun" | .appArg => .ok "appArg"
  | .lamDomain => .ok "lamDomain" | .lamBody => .ok "lamBody"
  | .piDomain => .ok "piDomain" | .piBody => .ok "piBody"
  | .letType => .ok "letType" | .letValue => .ok "letValue" | .letBody => .ok "letBody"
  | .projValue => .ok "projValue"
  | _ => .error "decomposition paths must select ordinary constructor occurrences"

def decompositionOperationJson : DecompositionOperation → Except String Json
  | .expose target => pure (Json.mkObj [("kind", toJson "expose"), ("target", target.json)])
  | .focus path => do
    return Json.mkObj [("kind", toJson "focus"), ("path", toJson (← path.mapM ordinaryStepName))]
  | .fields => pure (Json.mkObj [("kind", toJson "fields")])
  | .project index => pure (Json.mkObj [("kind", toJson "project"), ("index", toJson index)])
  | .typeComponent => pure (Json.mkObj [("kind", toJson "typeComponent")])
  | .logical => pure (Json.mkObj [("kind", toJson "logical")])

def decompositionPairJson (pair : DecompositionPair) : Except String Json :=
  selectedTripleJson pair.context pair.term pair.type

private def decompositionFailureJson (reason : HeadExposureFailure) : Json :=
  Json.mkObj [("status", toJson "unavailable"), ("kind", toJson reason.kind),
    ("phase", toJson reason.phase), ("reason", toJson (headBounded reason.reason))]

private def decompositionCheckingJson : Except String Unit → Json
  | .ok _ => Json.mkObj [("status", toJson "completed")]
  | .error reason => Json.mkObj [("status", toJson "error"), ("reason", toJson (headBounded reason))]

def decompositionOutputJson {input : DecompositionPair} : DecompositionOutput input → Except String Json
  | .unavailable reason => pure (decompositionFailureJson reason)
  | .exposed candidate checking => headExposureStateJson input.context (.candidate candidate checking)
  | .focused candidate checking => do
    return Json.mkObj [("status", toJson "candidate"),
      ("result", ← selectedTripleJson candidate.selected.telescope candidate.selected.extraction.component candidate.type),
      ("checking", decompositionCheckingJson checking)]
  | .catalogued catalogue => do
    return Json.mkObj [("status", toJson "candidate"), ("result", ← decompositionPairJson input),
      ("catalogue", ← directFieldCatalogueJson catalogue), ("checking", decompositionCheckingJson (.ok ()))]
  | .projected candidate checking => do
    return Json.mkObj [("status", toJson "candidate"), ("field", ← directFieldEntryJson candidate.field),
      ("primitive", ← exprJson (dec candidate.primitive)),
      ("result", ← selectedTripleJson input.context candidate.named candidate.type),
      ("carrierSort", ulevelJson candidate.carrierSort), ("checking", decompositionCheckingJson checking)]
  | .typeComponent type checking => do
    return Json.mkObj [("status", toJson "candidate"),
      ("result", ← selectedTripleJson input.context input.type type),
      ("checking", decompositionCheckingJson checking)]
  | .logical candidate checking => do
    return Json.mkObj [("status", toJson "candidate"), ("result", ← decompositionPairJson input),
      ("formation", Json.mkObj [("inferredType", ← exprJson (dec candidate.inferredType))]),
      ("domain", ← logicalDomainJson candidate.domain), ("shape", ← logicalShapeJson candidate.shape),
      ("checking", decompositionCheckingJson checking)]

private def decompositionOutputPair {input : DecompositionPair} : DecompositionOutput input → Option DecompositionPair
  | .unavailable _ => none
  | .exposed candidate _ => some ⟨input.arity, input.context, candidate.after, candidate.carrier⟩
  | .focused candidate _ => some ⟨candidate.selected.extraction.home, candidate.selected.telescope,
      candidate.selected.extraction.component, candidate.type⟩
  | .catalogued _ => some input
  | .projected candidate _ => some ⟨input.arity, input.context, candidate.named, candidate.type⟩
  | .typeComponent type _ => some ⟨input.arity, input.context, input.type, type⟩
  | .logical _ _ => some input

private def decompositionCompleted {input : DecompositionPair} : DecompositionOutput input → Bool
  | .exposed _ (.ok _) | .focused _ (.ok _) | .projected _ (.ok _) | .catalogued _ => true
  | .typeComponent _ (.ok _) | .logical _ (.ok _) => true
  | _ => false

private def decompositionCandidateJson {input : DecompositionPair} (output : DecompositionOutput input) : Except String Json := do
  let .obj fields ← decompositionOutputJson output | throw "invalid decomposition candidate object"
  return Json.mkObj (fields.toList.filter (fun field => field.1 != "checking"))

private def decompositionSemanticJson (operation : DecompositionOperation) (input : DecompositionPair)
    (output : DecompositionOutput input) : Except String Json := do
  return Json.mkObj [("operation", ← decompositionOperationJson operation),
    ("input", ← decompositionPairJson input), ("candidate", ← decompositionCandidateJson output)]

/-- A completed step's semantic checkpoint excludes request names and outcomes. -/
def decompositionCheckpointJson (step : DecompositionStep) : Except String Json := do
  unless decompositionCompleted step.output do throw "an incomplete decomposition step has no replay checkpoint"
  decompositionSemanticJson step.operation step.input step.output

def decompositionStepJson (step : DecompositionStep) : Except String Json := do
  return Json.mkObj [("index", toJson step.index), ("operation", ← decompositionOperationJson step.operation),
    ("input", ← decompositionPairJson step.input), ("output", ← decompositionOutputJson step.output),
    ("receiptStart", toJson step.receiptStart), ("receiptCount", toJson step.receiptCount),
    ("replay", toJson (match step.replay with
      | .new => "new" | .matched => "matched" | .mismatch => "mismatch" | .notCompared => "not-compared"))]

private def decompositionPreflight (seed : List OccurrenceDecomposition.Step)
    (expectedSelected : Json) (operations : Array DecompositionOperation) (history : Array Json)
    (profile : DecompositionProfile) : Except String Json := do
  unless operations.size > 0 && operations.size <= 8 && operations.size == history.size + 1 do
    throw "decomposition requires one new operation and a bounded history of at most eight operations"
  if seed.length > 64 then throw "source occurrence path exceeds 64 steps"
  let _ ← seed.mapM ordinaryStepName
  let mut totalPaths := seed.length
  let mut reservedChecks := 6
  for index in [:operations.size] do
    reservedChecks := reservedChecks + (match operations[index]! with
      | .expose _ | .project _ => 3 | .focus _ | .typeComponent => 2 | .logical => 4 | .fields => 0)
    match operations[index]! with
    | .expose _ =>
      if profile == .legacy && index % 2 != 0 then throw "decomposition operations must alternate expose and focus"
    | .focus path =>
      if profile == .legacy && index % 2 != 1 then throw "decomposition operations must start with expose and alternate"
      if path.length > 64 then throw "focus path exceeds 64 steps"
      totalPaths := totalPaths + path.length
    | .fields =>
      if profile == .legacy then throw "direct fields require decomposition version two"
    | .project fieldIndex =>
      if profile == .legacy then throw "direct fields require decomposition version two"
      if fieldIndex >= 16 then throw "direct field index exceeds the returned prefix"
      unless index > 0 do throw "field projection requires an immediately preceding catalogue"
      match operations[index - 1]! with
      | .fields => pure ()
      | _ => throw "field projection requires an immediately preceding catalogue"
    | .typeComponent | .logical =>
      unless profile == .logicalStructure do throw "type and logical inspection require decomposition version three"
  if profile == .logicalStructure && reservedChecks > 30 then
    throw "decomposition plan exceeds its reserved thirty-check limit"
  if totalPaths > 128 then throw "decomposition paths exceed their cumulative 128-step limit"
  let plan := Json.mkObj [("expectedSelected", expectedSelected),
    ("operations", Json.arr (← operations.mapM decompositionOperationJson)), ("expectedHistory", Json.arr history)]
  unless headJsonDepthWithin 120 plan do throw "decomposition request exceeds the nesting limit"
  checkExactNaturalBudget plan
  if plan.compress.utf8ByteSize > 2 * 1024 * 1024 then throw "decomposition request exceeds the byte limit"
  return plan

private def decompositionCallbackBasis (initial : Environment) (declaration : Declaration) : MetaM Unit :=
  match declaration with
  | .thmDecl value => ensureSourceBasis initial [value.type, value.value]
  | .defnDecl value => ensureSourceBasis initial [value.type, value.value]
  | _ => throwError "unsupported decomposition checking declaration"

private def decompositionFocusPreflight (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (input : DecompositionPair) (path : List OccurrenceDecomposition.Step) :
    MetaM (Except HeadExposureFailure (DecompositionFocus input)) := do
  ensureSourceBasis initial [contextExpr input.context, dec input.term, dec input.type]
  let some selected := OccurrenceDecomposition.extractSource input.context input.term path
    | return .error ⟨"unsupported", "focus-path", "The path is not an ordinary occurrence of the preceding result term."⟩
  if selected.extraction.home > 128 then
    return .error ⟨"limit", "focus-context", "The selected home exceeds 128 entries."⟩
  match checkHeadExposureExpressions limits policy.universeParams [
      (0, contextExpr selected.telescope), (selected.extraction.home, dec selected.extraction.component)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  let type ← inferredTypeAt selected.telescope selected.extraction.component
  ensureSourceBasis initial [dec type]
  let declarations := [
    thmD (policy.declarationPrefix ++ `focus.context)
      (dec (selected.telescope.close (.const ``True [])))
      (dec (ctelLam selected.telescope (.const ``True.intro []))) policy.universeParams,
    defD (policy.declarationPrefix ++ `focus.component)
      (dec (selected.telescope.close type))
      (dec (ctelLam selected.telescope selected.extraction.component)) policy.universeParams]
  for declaration in declarations do
    decompositionCallbackBasis initial declaration
    let expressions := match declaration with
      | .thmDecl value => [(0, value.type), (0, value.value)]
      | .defnDecl value => [(0, value.type), (0, value.value)]
      | _ => []
    match checkHeadExposureExpressions limits policy.universeParams expressions with
    | .error reason => return .error reason
    | .ok _ => pure ()
    match declarationJson declaration with
    | .error reason => return .error ⟨"limit", "focus-declarations", headBounded reason⟩
    | .ok json =>
      if !headJsonDepthWithin 120 json || json.compress.utf8ByteSize > 2 * 1024 * 1024 then
        return .error ⟨"limit", "focus-declarations", "A focus declaration exceeds the output profile."⟩
  return .ok ⟨selected, type⟩

private def decompositionComponentDeclarations {n : Nat} (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (tag : Name) (context : CTel n) (term type : Core n) :
    MetaM (Except HeadExposureFailure Unit) := do
  ensureSourceBasis initial [contextExpr context, dec term, dec type]
  let declarations := [
    thmD (policy.declarationPrefix ++ tag ++ `context)
      (dec (context.close (.const ``True [])))
      (dec (ctelLam context (.const ``True.intro []))) policy.universeParams,
    defD (policy.declarationPrefix ++ tag ++ `component)
      (dec (context.close type)) (dec (ctelLam context term)) policy.universeParams]
  for declaration in declarations do
    decompositionCallbackBasis initial declaration
    let expressions := match declaration with
      | .thmDecl value => [(0, value.type), (0, value.value)]
      | .defnDecl value => [(0, value.type), (0, value.value)]
      | _ => []
    match checkHeadExposureExpressions limits policy.universeParams expressions with
    | .error reason => return .error reason
    | .ok _ => pure ()
    match declarationJson declaration with
    | .error reason => return .error ⟨"limit", "component-declarations", headBounded reason⟩
    | .ok json =>
      if !headJsonDepthWithin 120 json || json.compress.utf8ByteSize > 2 * 1024 * 1024 then
        return .error ⟨"limit", "component-declarations", "An inspection declaration exceeds the output profile."⟩
  return .ok ()

private def decompositionTypePreflight (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (input : DecompositionPair) :
    MetaM (Except HeadExposureFailure (Core input.arity)) := do
  ensureSourceBasis initial [contextExpr input.context, dec input.term, dec input.type]
  match checkHeadExposureExpressions limits policy.universeParams [
      (0, contextExpr input.context), (input.arity, dec input.term), (input.arity, dec input.type)] with
  | .error reason => return .error reason
  | .ok _ => pure ()
  let type ← inferredTypeAt input.context input.type
  match ← decompositionComponentDeclarations initial policy limits `typeComponent input.context input.type type with
  | .error reason => return .error reason
  | .ok _ => return .ok type

private def decompositionLogicalPreflight (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (input : DecompositionPair) :
    MetaM (Except HeadExposureFailure (LogicalInspectionCandidate input.arity)) := do
  let candidate ← match ← prepareLogicalInspection initial policy.universeParams input.context input.term input.type limits with
    | .error reason => return .error reason
    | .ok candidate => pure candidate
  match ← decompositionComponentDeclarations initial policy limits `logical.root input.context input.term candidate.inferredType with
  | .error reason => return .error reason
  | .ok _ => pure ()
  if let some domain := candidate.domain then
    match ← decompositionComponentDeclarations initial policy limits `logical.domain input.context domain.term domain.inferredType with
    | .error reason => return .error reason
    | .ok _ => pure ()
  return .ok candidate

private def decompositionFieldDeclarations (initial : Environment) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (input : DecompositionPair) (candidate : DirectFieldCandidate input.arity) :
    MetaM (Except HeadExposureFailure Unit) := do
  let declarations := [
    thmD (policy.declarationPrefix ++ `project.context)
      (dec (input.context.close (.const ``True [])))
      (dec (ctelLam input.context (.const ``True.intro []))) policy.universeParams,
    defD (policy.declarationPrefix ++ `project.component)
      (dec (input.context.close candidate.type))
      (dec (ctelLam input.context candidate.named)) policy.universeParams,
    directFieldConversion policy.declarationPrefix policy.universeParams input.context candidate]
  for declaration in declarations do
    decompositionCallbackBasis initial declaration
    let expressions := match declaration with
      | .thmDecl value => [(0, value.type), (0, value.value)]
      | .defnDecl value => [(0, value.type), (0, value.value)]
      | _ => []
    match checkHeadExposureExpressions limits policy.universeParams expressions with
    | .error reason => return .error reason
    | .ok _ => pure ()
    match declarationJson declaration with
    | .error reason => return .error ⟨"limit", "field-declarations", headBounded reason⟩
    | .ok json =>
      if !headJsonDepthWithin 120 json || json.compress.utf8ByteSize > 2 * 1024 * 1024 then
        return .error ⟨"limit", "field-declarations", "A projection declaration exceeds the output profile."⟩
  return .ok ()

/-- Execute one actual positional operation against a frozen environment basis.
The caller owns the isolated capture and total budget. The bounded candidate is
prepared before `beforeChecks`, which can refuse retaining it before any check;
callback failures retain the candidate and the checks already performed. -/
def runDecompositionOperation (initial : Environment) (run : Check) (policy : SourceCheckPolicy)
    (limits : HeadExposureLimits) (operation : DecompositionOperation) (input : DecompositionPair)
    (beforeChecks : DecompositionOutput input → MetaM (Except HeadExposureFailure Unit)) :
    MetaM (DecompositionOutput input × Option HeadExposureFailure) := do
  let unavailable := fun reason => (DecompositionOutput.unavailable reason, some reason)
  let retain := fun candidate => tryCatchRuntimeEx (beforeChecks candidate) fun error => do
    pure (.error ⟨headExceptionKind error, "trace-output", headBounded (← error.toMessageData.toString)⟩)
  match operation with
  | .expose target =>
    let prepared ← tryCatchRuntimeEx
      (prepareHeadExposure initial policy.universeParams input.context input.term input.type target limits)
      (fun error => do pure (.error ⟨headExceptionKind error, "preparation", headBounded (← error.toMessageData.toString)⟩))
    let candidate ← match prepared with
      | .ok candidate => pure candidate
      | .error reason => return unavailable reason
    let preflight ← tryCatchRuntimeEx (checkHeadDeclarations initial policy limits input.context candidate)
      (fun error => do pure (.error ⟨headExceptionKind error, "declarations", headBounded (← error.toMessageData.toString)⟩))
    match preflight with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    match ← retain (.exposed candidate (.ok ())) with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    tryCatchRuntimeEx (do
      let _ ← checkComponentWith run (policy.declarationPrefix ++ `result) policy.universeParams
        input.context candidate.after candidate.carrier
      let _ ← run "conversion" (headExposureConversion policy.declarationPrefix policy.universeParams input.context candidate)
      return (.exposed candidate (.ok ()), none)) fun error => do
        let reason := headBounded (← error.toMessageData.toString)
        return (.exposed candidate (.error reason), some ⟨headExceptionKind error, "operation-checking", reason⟩)
  | .focus path =>
    let prepared ← tryCatchRuntimeEx (decompositionFocusPreflight initial policy limits input path)
      (fun error => do pure (.error ⟨headExceptionKind error, "focus-preparation", headBounded (← error.toMessageData.toString)⟩))
    let candidate ← match prepared with
      | .ok candidate => pure candidate
      | .error reason => return unavailable reason
    match ← retain (.focused candidate (.ok ())) with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    tryCatchRuntimeEx (do
      let _ ← checkComponentWith run (policy.declarationPrefix ++ `focus) policy.universeParams
        candidate.selected.telescope candidate.selected.extraction.component candidate.type
      return (.focused candidate (.ok ()), none)) fun error => do
        let reason := headBounded (← error.toMessageData.toString)
        return (.focused candidate (.error reason), some ⟨headExceptionKind error, "operation-checking", reason⟩)
  | .fields =>
    let prepared ← tryCatchRuntimeEx (prepareDirectFieldCatalogue initial policy.universeParams
      input.context input.term input.type limits)
      (fun error => do pure (.error ⟨headExceptionKind error, "field-preparation", headBounded (← error.toMessageData.toString)⟩))
    let catalogue ← match prepared with
      | .error reason => return unavailable reason
      | .ok catalogue => pure catalogue
    match ← retain (.catalogued catalogue) with
    | .error reason => return unavailable reason
    | .ok _ => return (.catalogued catalogue, none)
  | .typeComponent =>
    let prepared ← tryCatchRuntimeEx (decompositionTypePreflight initial policy limits input)
      (fun error => do pure (.error ⟨headExceptionKind error, "type-preparation", headBounded (← error.toMessageData.toString)⟩))
    let type ← match prepared with
      | .error reason => return unavailable reason
      | .ok type => pure type
    match ← retain (.typeComponent type (.ok ())) with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    tryCatchRuntimeEx (do
      let _ ← checkComponentWith run (policy.declarationPrefix ++ `typeComponent) policy.universeParams
        input.context input.type type
      return (.typeComponent type (.ok ()), none)) fun error => do
        let reason := headBounded (← error.toMessageData.toString)
        return (.typeComponent type (.error reason), some ⟨headExceptionKind error, "operation-checking", reason⟩)
  | .logical =>
    let prepared ← tryCatchRuntimeEx (decompositionLogicalPreflight initial policy limits input)
      (fun error => do pure (.error ⟨headExceptionKind error, "logical-preparation", headBounded (← error.toMessageData.toString)⟩))
    let candidate ← match prepared with
      | .error reason => return unavailable reason
      | .ok candidate => pure candidate
    match ← retain (.logical candidate (.ok ())) with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    tryCatchRuntimeEx (do
      let _ ← checkComponentWith (fun label declaration => run ("logical.root." ++ label) declaration)
        (policy.declarationPrefix ++ `logical.root) policy.universeParams input.context input.term candidate.inferredType
      if let some domain := candidate.domain then
        let _ ← checkComponentWith (fun label declaration => run ("logical.domain." ++ label) declaration)
          (policy.declarationPrefix ++ `logical.domain) policy.universeParams input.context domain.term domain.inferredType
      return (.logical candidate (.ok ()), none)) fun error => do
        let reason := headBounded (← error.toMessageData.toString)
        return (.logical candidate (.error reason), some ⟨headExceptionKind error, "operation-checking", reason⟩)
  | .project index =>
    let prepared ← tryCatchRuntimeEx (prepareDirectField initial policy.universeParams
      input.context input.term input.type index limits)
      (fun error => do pure (.error ⟨headExceptionKind error, "field-preparation", headBounded (← error.toMessageData.toString)⟩))
    let candidate ← match prepared with
      | .error reason => return unavailable reason
      | .ok candidate => pure candidate
    let preflight ← tryCatchRuntimeEx (decompositionFieldDeclarations initial policy limits input candidate)
      (fun error => do pure (.error ⟨headExceptionKind error, "field-declarations", headBounded (← error.toMessageData.toString)⟩))
    match preflight with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    match ← retain (.projected candidate (.ok ())) with
    | .error reason => return unavailable reason
    | .ok _ => pure ()
    tryCatchRuntimeEx (do
      let _ ← checkComponentWith run (policy.declarationPrefix ++ `project) policy.universeParams
        input.context candidate.named candidate.type
      let _ ← run "conversion" (directFieldConversion policy.declarationPrefix policy.universeParams input.context candidate)
      return (.projected candidate (.ok ()), none)) fun error => do
        let reason := headBounded (← error.toMessageData.toString)
        return (.projected candidate (.error reason), some ⟨headExceptionKind error, "operation-checking", reason⟩)

/-- A single isolated capture replays real operations from the actual named
source. Historical semantic comparison follows its fresh checks, never replaces
them, and a mismatch prevents every later operation. -/
def captureNamedDecomposition (attempt operation : String) (policy : SourceCheckPolicy)
    (sourceTerm sourceType : Expr) (path : List OccurrenceDecomposition.Step) (expectedSelected : Json)
    (operations : Array DecompositionOperation) (expectedHistory : Array Json)
    (limits : HeadExposureLimits := {}) (profile : DecompositionProfile := .legacy) :
    MetaM (Except String (CapturedSource NamedDecompositionResult)) := do
  let plan ← match decompositionPreflight path expectedSelected operations expectedHistory profile with
    | .ok plan => pure plan
    | .error reason => return .error reason
  if policy.declarationPrefix == .anonymous then return .error "source declaration prefix must be nonempty"
  let initial ← getEnv
  let component ← match ← ingestActualSource sourceTerm sourceType with
    | .ok component => pure component
    | .error reason => return .error reason
  if component.context.ids.length > 128 then return .error "source context exceeds 128 entries"
  if let some selected := OccurrenceDecomposition.extractSource component.context.telescope component.term path then
    if selected.extraction.home > 128 then return .error "source selected home exceeds 128 entries"
  let binding ← match namedBindingJson attempt operation "namedDecomposition" policy component [
      ("path", arr (path.map sourceStepJson)), ("expectedSelected", expectedSelected),
      ("operations", (plan.getObjVal? "operations").toOption.getD .null), ("expectedHistory", Json.arr expectedHistory)] with
    | .ok binding => pure binding
    | .error reason => return .error reason
  unless headJsonDepthWithin 120 binding do return .error "decomposition binding exceeds the nesting limit"
  match checkExactNaturalBudget binding with
  | .error reason => return .error reason
  | .ok _ => pure ()
  if binding.compress.utf8ByteSize > 2 * 1024 * 1024 then return .error "decomposition binding exceeds the byte limit"
  try
    let capture ← captureChecks attempt operation policy.heartbeatFor fun callback => do
      let count ← IO.mkRef 0
      let run : Check := fun label declaration => do
        decompositionCallbackBasis initial declaration
        let result ← callback label declaration
        count.modify (· + 1)
        return result
      tryCatchRuntimeEx (do
        let base ← namedExtractionAction run policy component path
        let mut input : DecompositionPair := ⟨base.selected.extraction.home, base.selected.telescope,
          base.selected.extraction.component, base.selectedType⟩
        let actual ← match decompositionPairJson input with
          | .ok actual => pure actual
          | .error reason => throwError "{reason}"
        unless actual == expectedSelected do
          return Except.ok { base, profile, steps := #[], stop := some ⟨"prerequisite", "selected-match",
            "The freshly extracted selected triple differs from the requested parent."⟩ }
        let mut steps : Array DecompositionStep := #[]
        let mut semanticBytes := 0
        let mut stop := none
        for index in [:operations.size] do
          let selectedOperation := operations[index]!
          let currentInput := input
          let receiptStart ← count.get
          let stepPolicy := { policy with declarationPrefix := policy.declarationPrefix ++ Name.mkSimple s!"step{index}" }
          let charged ← IO.mkRef semanticBytes
          let preparedCheckpoint ← IO.mkRef Json.null
          let beforeChecks := fun output => do
            match decompositionSemanticJson selectedOperation currentInput output with
            | .error reason => return Except.error ⟨"limit", "trace-output", headBounded reason⟩
            | .ok value =>
              unless headJsonDepthWithin 120 value do
                return Except.error ⟨"limit", "trace-output", "The semantic trace exceeds its nesting limit."⟩
              let bytes := semanticBytes + value.compress.utf8ByteSize + 4096
              if bytes > 2 * 1024 * 1024 then
                return Except.error ⟨"limit", "trace-output", "The accumulated semantic trace exceeds 2 MiB."⟩
              charged.set bytes
              preparedCheckpoint.set value
              return Except.ok ()
          let (output, failure) ← runDecompositionOperation initial run stepPolicy limits selectedOperation currentInput beforeChecks
          semanticBytes ← charged.get
          let receiptCount := (← count.get) - receiptStart
          let mut replay := DecompositionReplay.notCompared
          stop := failure
          if decompositionCompleted output then
            if index < expectedHistory.size then
              -- Use the bounded semantic record already prepared before checks.
              -- Fresh callback outcomes are deliberately excluded from replay.
              let checkpoint ← preparedCheckpoint.get
              if checkpoint == expectedHistory[index]! then replay := .matched
              else
                replay := .mismatch
                stop := some ⟨"prerequisite", "history-match", "A freshly replayed semantic checkpoint differs from retained history."⟩
            else replay := .new
          steps := steps.push ⟨index, selectedOperation, currentInput, output, receiptStart, receiptCount, replay⟩
          if stop.isSome then break
          let some next := decompositionOutputPair output
            | throwError "a completed decomposition operation has no actual result"
          input := next
        return Except.ok { base, steps, stop, profile })
        (fun error => do pure (Except.error (headBounded (← error.toMessageData.toString))))
    return .ok ⟨binding, capture⟩
  catch error => return .error (headBounded (← error.toMessageData.toString))

def capturedDecompositionJson (captured : CapturedSource NamedDecompositionResult) : Except String Json := do
  checkHeadCaptureLineage captured.capture
  let (action, selected, steps, stop) ← match captured.capture.value with
    | .error reason =>
      if captured.capture.checks.size > 6 then throw "decomposition base error cannot discard executed operation records"
      pure (Json.mkObj [("status", toJson "error"), ("reason", toJson (headBounded reason))], Json.null, #[], Json.null)
    | .ok result => do
      let mut offset := 6
      let mut index := 0
      for step in result.steps do
        unless step.index == index && step.receiptStart == offset do throw "decomposition receipt offsets are inconsistent"
        let maxCount := match step.operation with
          | .expose _ | .project _ => 3
          | .focus _ | .typeComponent => 2
          | .fields => 0
          | .logical => match step.input.term with | .pi .. => 4 | _ => 2
        unless step.receiptCount <= maxCount && (!decompositionCompleted step.output || step.receiptCount == maxCount) do
          throw "decomposition action and local receipt counts are inconsistent"
        match step.output with
        | .unavailable _ => unless step.receiptCount == 0 do throw "unavailable operation has callback receipts"
        | _ => pure ()
        offset := offset + step.receiptCount
        index := index + 1
      let maximum := if result.profile == .legacy then 26 else 30
      unless captured.capture.checks.size == offset && offset <= maximum do throw "decomposition global receipt count is inconsistent"
      pure (Json.mkObj [("status", toJson "completed")],
        ← selectedTripleJson result.base.selected.telescope result.base.selected.extraction.component result.base.selectedType,
        ← result.steps.mapM decompositionStepJson, result.stop.map decompositionFailureJson |>.getD Json.null)
  let value := Json.mkObj [("status", toJson "captured"), ("action", action), ("binding", captured.binding),
    ("selected", selected), ("steps", Json.arr steps), ("stop", stop),
    ("checks", Json.arr captured.capture.checks), ("audits", Json.arr captured.capture.audits),
    ("environmentSnapshotCount", toJson captured.capture.environments.size)]
  checkExactNaturalBudget value
  unless headJsonDepthWithin 120 value do throw "decomposition checking exceeds the nesting limit"
  if value.compress.utf8ByteSize > 2 * 1024 * 1024 then throw "decomposition checking exceeds 2 MiB"
  return value

/-- Compose exact positional sources through an explicitly supplied dependent
map. Images and their source sorts are indexed in de Bruijn order, most recent
source declaration first. The output and the actual source/map/output checks
are returned separately; no general typing theorem or admission flag is inferred. -/
def captureSourceComposition (attempt operation : String) (policy : SourceCheckPolicy)
    {n m : Nat} (C : CTel n) (D : CTel m) (term type : Core n)
    (images : Fin n → Core m) (sorts : Fin n → ULevel) :
    MetaM (Except String (CapturedSource (SourceCompositionResult m))) := do
  if policy.declarationPrefix == .anonymous then
    return .error "source declaration prefix must be nonempty"
  let serialized : Except String Json := do
    return Json.mkObj (bindingFields attempt operation "positionalComposition" policy ++ [
      ("sourceContext", ← positionalContextJson C),
      ("targetContext", ← positionalContextJson D),
      ("sourceTerm", ← exprJson (dec term)), ("sourceType", ← exprJson (dec type)),
      ("images", arr (← (List.finRange n).mapM fun i => exprJson (dec (images i)))),
      ("imagesOrder", toJson "mostRecentFirst"),
      ("sorts", arr ((List.finRange n).map fun i => ulevelJson (sorts i))),
      ("sortsOrder", toJson "mostRecentFirst")])
  let binding ← match serialized with
    | .ok binding => pure binding
    | .error reason => return .error reason
  captureSourceAction attempt operation policy binding fun run => do
    let (outTerm, outType, checks) ← composeWith run policy.declarationPrefix
      policy.universeParams C D term type images sorts
    return ⟨outTerm, outType, checks⟩

end Definograph
