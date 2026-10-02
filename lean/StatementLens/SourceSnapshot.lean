import Lean
import SourceCapture

set_option autoImplicit false
set_option maxRecDepth 8192

namespace StatementLens.SourceSnapshot
open Lean Meta Elab

structure Selection where
  startByte : Nat
  endByte : Nat
  requestedStartByte : Nat
  requestedEndByte : Nat

def validCaptureId (value : String) : Bool :=
  value.length == 36 && value.toList.zipIdx.all fun (c, i) =>
    if [8, 13, 18, 23].contains i then c == '-'
    else ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def declarationPrefix (captureId : String) : Name := .str `StatementLens.SourceSnapshot captureId

private def bounded (value : String) : String := (value.take 4096).toString

private def unavailable (kind phase reason : String) : Json := Json.mkObj [
  ("status", toJson "unavailable"), ("kind", toJson kind),
  ("phase", toJson phase), ("reason", toJson (bounded reason))]

private def checkingUnavailable (kind phase reason : String) (attempted := false) : Json :=
  (unavailable kind phase reason).setObjVal! "attempted" (toJson attempted)

private def rawLimits : Definograph.RawJsonLimits := {
  maxNodes := 20000, maxDepth := 96, maxTextBytes := 128 * 1024,
  maxNaturalDigits := 10000, maxOutputBytes := 256 * 1024
}

private def expectedLimits : Definograph.RawJsonLimits := { rawLimits with maxOutputBytes := 128 * 1024 }

private def encodingError (phase reason : String) : Json := unavailable "limit" phase reason

private def exceptionKind (error : Exception) : String :=
  if error.isMaxHeartbeat || error.isMaxRecDepth then "limit" else "error"

private def expectedTypeJson (term : TermInfo) : Json :=
  match term.expectedType? with
  | none => Json.mkObj [("status", toJson "absent")]
  | some type => match Definograph.rawExprJson type expectedLimits with
    | .ok value => Json.mkObj [("status", toJson "available"), ("expression", value)]
    | .error reason => encodingError "expected-type" reason

private structure Original where
  value : Json
  inferredType : Option Expr

private def originalCapture (term : TermInfo) : MetaM Original := do
  let saved ← Meta.saveState
  try
    tryCatchRuntimeEx (do
      let type ← inferType term.expr
      let result ← Definograph.captureRawFrame term.expr type rawLimits
      return { inferredType := some type, value := match result with
        | .ok frame => Json.mkObj [("status", toJson "available"),
          ("typeOrigin", toJson "inferred"), ("frame", frame)]
        | .error reason => encodingError "original-serialization" reason }) fun error => do
      let reason ← error.toMessageData.toString
      return { inferredType := none, value := unavailable (exceptionKind error) "original-inference" reason }
  finally saved.restore

private def sourceHasSorry (term type : Expr) (context : LocalContext) : Bool :=
  term.hasSorry || type.hasSorry || context.foldl (fun found declaration =>
    found || declaration.type.hasSorry || match declaration with
      | .ldecl _ _ _ _ value false _ => value.hasSorry
      | _ => false) false

/-- These are the exact parameters needed by the prepared checking input. The
order is chronological local type/value traversal, then selected term and type;
opaque stored values contribute no semantic parameters. -/
def checkerUniverseParams (context : LocalContext) (term type : Expr) : List Name := Id.run do
  let mut state : CollectLevelParams.State := {}
  for declaration in context do
    state := collectLevelParams state declaration.type
    if let .ldecl _ _ _ _ value false _ := declaration then
      state := collectLevelParams state value
  state := collectLevelParams state term
  state := collectLevelParams state type
  return state.params.toList

/-- Modify declarations in place: rebuilding a LocalContext would renumber
indices, while ignored nondependent stored values must remain untouched. -/
def prepareContext (context : LocalContext) : MetaM LocalContext := do
  let mut prepared := context
  for declaration in context do
    let mut next := declaration.setType (← instantiateMVars declaration.type)
    if let .ldecl _ _ _ _ value false _ := declaration then
      next := next.setValue (← instantiateMVars value)
    prepared := prepared.modifyLocalDecl declaration.fvarId (fun _ => next)
  return prepared

private def capturedJson (captured : Definograph.CapturedSource Definograph.NamedSourceResult) : Json :=
  let action := match captured.capture.value with
    | .ok _ => Json.mkObj [("status", toJson "completed")]
    | .error reason => Json.mkObj [("status", toJson "error"), ("reason", toJson (bounded reason))]
  Json.mkObj [("status", toJson "captured"), ("action", action),
    ("binding", captured.binding), ("checks", Json.arr captured.capture.checks),
    ("audits", Json.arr captured.capture.audits),
    ("environmentSnapshotCount", toJson captured.capture.environments.size)]

private def jsonDepthWithin : Nat → Json → Bool
  | 0, .arr _ => false
  | 0, .obj _ => false
  | 0, _ => true
  | fuel + 1, .arr values => values.all (jsonDepthWithin fuel)
  | fuel + 1, .obj fields => fields.toList.all (fun (_, value) => jsonDepthWithin fuel value)
  | _ + 1, _ => true

private def boundChecking (value : Json) : Json :=
  if !jsonDepthWithin 120 value then
    checkingUnavailable "limit" "checking-output" "The complete checking record exceeds the transport nesting limit; no receipts are displayed." true
  else if value.compress.utf8ByteSize > 768 * 1024 then
    checkingUnavailable "limit" "checking-output" "The complete checking record exceeds 768 KiB; no receipts are displayed." true
  else value

private def preparationFailure (kind phase reason : String) : Json × Json :=
  (unavailable kind phase reason,
    checkingUnavailable "prerequisite" "checking-prerequisite" "The exact prepared frame is unavailable.")

private def preparedCapture (captureId : String) (term : TermInfo) (type : Expr) : MetaM (Json × Json) := do
  let saved ← Meta.saveState
  try
    tryCatchRuntimeEx (do
      -- Inference itself can allocate or assign metavariables. Repeat it from
      -- the same original snapshot and keep this run's state for preparation;
      -- an Expr alone cannot transport those inference-state effects.
      let repeatedType ← inferType term.expr
      let originalWire ← match Definograph.rawExprJson type rawLimits with
        | .ok value => pure value
        | .error reason => return preparationFailure "limit" "inference-repeat" reason
      let repeatedWire ← match Definograph.rawExprJson repeatedType rawLimits with
        | .ok value => pure value
        | .error reason => return preparationFailure "limit" "inference-repeat" reason
      unless originalWire.compress == repeatedWire.compress do
        return preparationFailure "error" "inference-repeat" "Repeating inference from the captured context produced a different exact type."
      let preparedContext ← prepareContext (← getLCtx)
      let preparedTerm ← instantiateMVars term.expr
      let preparedType ← instantiateMVars repeatedType
      withLCtx preparedContext (← getLocalInstances) do
        let encoded ← Definograph.captureRawFrame preparedTerm preparedType rawLimits
        let frame ← match encoded with
          | .ok value => pure value
          | .error reason => return preparationFailure "limit" "prepared-serialization" reason
        let params := checkerUniverseParams preparedContext preparedTerm preparedType
        let prepared := Json.mkObj [("status", toJson "available"),
          ("typeOrigin", toJson "inferred-instantiated"), ("frame", frame),
          ("checkerUniverseParams", Definograph.arr (params.map Definograph.nameJson))]
        if preparedContext.foldl (fun n _ => n + 1) (0 : Nat) > 128 then
          return (prepared, checkingUnavailable "limit" "context-policy" "The prepared context exceeds 128 declarations.")
        if sourceHasSorry preparedTerm preparedType preparedContext then
          return (prepared, checkingUnavailable "unsupported" "source-policy" "The prepared source contains a placeholder (sorry).")
        let checking ← tryCatchRuntimeEx (do
          let result ← Definograph.captureNamedSource captureId "editor-source" {
            declarationPrefix := declarationPrefix captureId, universeParams := params,
            heartbeatFor := fun _ => 200000, retainedMetadata := .rawV1
          } preparedTerm preparedType
          pure (match result with
            | .ok captured => boundChecking (capturedJson captured)
            | .error reason => checkingUnavailable
              (if (reason.splitOn "limit").length > 1 then "limit" else "unsupported") "source-capture" reason true))
          fun error => do
            pure (checkingUnavailable (exceptionKind error) "source-capture"
              (← error.toMessageData.toString) true)
        return (prepared, checking)) fun error => do
      return preparationFailure (exceptionKind error) "preparation" (← error.toMessageData.toString)
  finally saved.restore

private def snapshot (selection expected original prepared checking : Json) : Json := Json.mkObj [
  ("schema", toJson "definograph.source-snapshot.v1"), ("selection", selection),
  ("policy", Json.mkObj [("id", toJson "named-source-v1"), ("operation", toJson "editor-source"),
    ("preparation", toJson "Lean.instantiateMVars"), ("heartbeatBound", Definograph.exactNatJson 200000),
    ("retainedMetadata", toJson "definograph.raw.v1")]),
  ("expectedType", expected), ("original", original), ("prepared", prepared), ("checking", checking)]

private def boundSnapshot (selection expected original prepared checking : Json) : Json := Id.run do
  let full := snapshot selection expected original prepared checking
  if full.compress.utf8ByteSize ≤ 1536 * 1024 then return full
  let attempted := (checking.getObjValAs? String "status").toOption == some "captured" ||
    (checking.getObjValAs? Bool "attempted").toOption.getD false
  let omitted := checkingUnavailable "limit" "snapshot-output"
    "The aggregate source snapshot exceeds its budget; the complete checking record is omitted." attempted
  return snapshot selection expected original prepared omitted

/-- Capture original and prepared input in separate executions of the same
InfoTree snapshot. The caller runs the legacy exporter in its own execution too;
no mutable preparation state or generated name escapes into that exporter. -/
def capture (term : TermInfo) (context : ContextInfo) (captureId : String) (selection : Selection) : IO Json := do
  unless validCaptureId captureId do throw (IO.userError "captureId must be a UUID")
  unless selection.startByte ≤ selection.endByte && selection.requestedStartByte ≤ selection.requestedEndByte &&
      [selection.startByte, selection.endByte, selection.requestedStartByte, selection.requestedEndByte].all
        (· ≤ 9007199254740991) do throw (IO.userError "invalid source snapshot selection")
  let parent ← match context.parentDecl? with
    | none => pure Json.null
    | some name => do
      -- Charge structured names with the same bounded raw codec, then extract
      -- the exact name field. This is not a source/reference interpretation.
      let encoded ← IO.ofExcept (Definograph.rawExprJson (.fvar ⟨name⟩) expectedLimits)
      let parts ← IO.ofExcept encoded.getArr?
      pure parts[1]!
  let selected := Json.mkObj [("startByte", toJson selection.startByte), ("endByte", toJson selection.endByte),
    ("requestedStartByte", toJson selection.requestedStartByte), ("requestedEndByte", toJson selection.requestedEndByte),
    ("parentDeclaration", parent)]
  let expected := expectedTypeJson term
  let original ← term.runMetaM context <| withOptions (fun opts =>
    opts.set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (400000 : Nat)) (originalCapture term)
  let (prepared, checking) ← match original.inferredType with
    | none => pure (preparationFailure "prerequisite" "preparation" "The original source type could not be inferred.")
    | some type => term.runMetaM context <| withOptions (fun opts =>
      opts.set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (400000 : Nat)) (preparedCapture captureId term type)
  return boundSnapshot selected expected original.value prepared checking

private structure DecompositionRequest where
  profile : Definograph.DecompositionProfile
  previousCaptureId : String
  parentStepIndex : Nat
  expectedSelected : Json
  operations : Array Definograph.DecompositionOperation
  operationsJson : Json
  expectedHistory : Array Json

private structure OccurrenceRequest where
  parentCaptureId : String
  selection : Json
  prepared : Json
  path : Array String
  steps : List OccurrenceDecomposition.Step
  headExposure : Option (Definograph.HeadExposureTarget × Json) := none
  decomposition : Option DecompositionRequest := none

private def exactKeys (value : Json) (keys : List String) : Bool :=
  match value.getObj? with
  | .error _ => false
  | .ok fields => fields.toList.length == keys.length &&
      fields.toList.all (fun (key, _) => keys.contains key)

private def occurrenceStep : String → Except String OccurrenceDecomposition.Step
  | "appFun" => pure .appFun
  | "appArg" => pure .appArg
  | "lamDomain" => pure .lamDomain
  | "lamBody" => pure .lamBody
  | "piDomain" => pure .piDomain
  | "piBody" => pure .piBody
  | "letType" => pure .letType
  | "letValue" => pure .letValue
  | "letBody" => pure .letBody
  | "projValue" => pure .projValue
  | _ => throw "Only ordinary prepared source-expression steps may be selected."

private def parseOccurrenceRequest (value : Json) : Except String OccurrenceRequest := do
  unless jsonDepthWithin 120 value && value.compress.utf8ByteSize ≤ 512 * 1024 do
    throw "The occurrence request exceeds its transport limit."
  unless exactKeys value ["schema", "parentCaptureId", "selection", "prepared", "path"] &&
      (← value.getObjValAs? String "schema") == "definograph.source-occurrence-request.v1" do
    throw "Unsupported occurrence request fields or schema."
  let parentCaptureId ← value.getObjValAs? String "parentCaptureId"
  unless validCaptureId parentCaptureId do throw "The parent capture identity must be a UUID."
  let selection ← value.getObjVal? "selection"
  unless exactKeys selection ["startByte", "endByte", "requestedStartByte", "requestedEndByte", "parentDeclaration"] do
    throw "Invalid parent selection fields."
  let start ← selection.getObjValAs? Nat "startByte"
  let stop ← selection.getObjValAs? Nat "endByte"
  let requestedStart ← selection.getObjValAs? Nat "requestedStartByte"
  let requestedStop ← selection.getObjValAs? Nat "requestedEndByte"
  unless start ≤ requestedStart && requestedStart ≤ requestedStop && requestedStop ≤ stop &&
      stop ≤ 9007199254740991 do throw "Invalid parent selection range."
  let prepared ← value.getObjVal? "prepared"
  unless exactKeys prepared ["status", "typeOrigin", "frame", "checkerUniverseParams"] &&
      (← prepared.getObjValAs? String "status") == "available" &&
      (← prepared.getObjValAs? String "typeOrigin") == "inferred-instantiated" do
    throw "The parent must contain an available prepared source frame."
  let path ← value.getObjValAs? (Array String) "path"
  unless path.size ≤ 64 do throw "An occurrence path may contain at most 64 steps."
  let steps ← path.toList.mapM occurrenceStep
  return { parentCaptureId, selection, prepared, path, steps }

private def parseHeadExposureRequest (value : Json) : Except String OccurrenceRequest := do
  unless jsonDepthWithin 120 value && value.compress.utf8ByteSize ≤ 768 * 1024 do
    throw "The definition-head request exceeds its transport limit."
  unless exactKeys value ["schema", "parentCaptureId", "selection", "prepared", "path", "target", "expectedSelected"] &&
      (← value.getObjValAs? String "schema") == "definograph.source-head-exposure-request.v1" do
    throw "Unsupported definition-head request fields or schema."
  let target ← match ← value.getObjValAs? String "target" with
    | "term" => pure Definograph.HeadExposureTarget.term
    | "type" => pure Definograph.HeadExposureTarget.type
    | _ => throw "Definition-head target must be term or type."
  let expected ← value.getObjVal? "expectedSelected"
  unless exactKeys expected ["home", "term", "type"] do
    throw "The definition-head request requires the retained selected triple."
  -- Reuse parent-field parsing only. This does not manufacture an occurrence
  -- record or reconstruct a context from the supplied comparison data.
  let base ← parseOccurrenceRequest (Json.mkObj [
    ("schema", toJson "definograph.source-occurrence-request.v1"),
    ("parentCaptureId", ← value.getObjVal? "parentCaptureId"),
    ("selection", ← value.getObjVal? "selection"),
    ("prepared", ← value.getObjVal? "prepared"), ("path", ← value.getObjVal? "path")])
  return { base with headExposure := some (target, expected) }

private def parseDecompositionRequest (value : Json) : Except String OccurrenceRequest := do
  unless jsonDepthWithin 120 value && value.compress.utf8ByteSize ≤ 2 * 1024 * 1024 do
    throw "The decomposition request exceeds its transport limit."
  Definograph.checkExactNaturalBudget value
  let schema ← value.getObjValAs? String "schema"
  let profile := if schema == "definograph.source-decomposition-request.v3" then
    Definograph.DecompositionProfile.logicalStructure else if schema == "definograph.source-decomposition-request.v2" then
    .directFields else .legacy
  unless exactKeys value ["schema", "parentCaptureId", "previousCaptureId", "parentStepIndex",
      "selection", "prepared", "path", "expectedSelected", "operations", "expectedHistory"] &&
      (schema == "definograph.source-decomposition-request.v1" || schema == "definograph.source-decomposition-request.v2" || schema == "definograph.source-decomposition-request.v3") do
    throw "Unsupported decomposition request fields or schema."
  let previousCaptureId ← value.getObjValAs? String "previousCaptureId"
  unless validCaptureId previousCaptureId do throw "The previous capture identity must be a UUID."
  let parentStepIndex ← value.getObjValAs? Nat "parentStepIndex"
  unless parentStepIndex < 8 do throw "The selected continuation index exceeds its limit."
  let expectedSelected ← value.getObjVal? "expectedSelected"
  unless exactKeys expectedSelected ["home", "term", "type"] do
    throw "Decomposition requires the retained original selected triple."
  let base ← parseOccurrenceRequest (Json.mkObj [
    ("schema", toJson "definograph.source-occurrence-request.v1"),
    ("parentCaptureId", ← value.getObjVal? "parentCaptureId"),
    ("selection", ← value.getObjVal? "selection"),
    ("prepared", ← value.getObjVal? "prepared"), ("path", ← value.getObjVal? "path")])
  let recipe ← value.getObjValAs? (Array Json) "operations"
  let expectedHistory ← value.getObjValAs? (Array Json) "expectedHistory"
  unless 1 ≤ recipe.size && recipe.size ≤ 8 && expectedHistory.size + 1 == recipe.size do
    throw "Decomposition requires exactly one new bounded operation."
  if previousCaptureId == base.parentCaptureId then
    unless profile != .legacy && parentStepIndex == 0 && expectedHistory.isEmpty do
      throw "Only version two or later may start at the original empty operation prefix."
  else
    unless 2 ≤ recipe.size && parentStepIndex + 1 == expectedHistory.size do
      throw "Decomposition requires the exact retained operation prefix."
  let mut totalPath := base.path.size
  let mut operations := #[]
  for index in [:recipe.size] do
    let item := recipe[index]!
    let kind ← item.getObjValAs? String "kind"
    if profile == .legacy && kind != (if index % 2 == 0 then "expose" else "focus") then
      throw "Version one must alternate exposure and focus."
    if kind == "expose" then
      unless exactKeys item ["kind", "target"] do throw "Invalid exposure operation fields."
      let target ← match ← item.getObjValAs? String "target" with
        | "term" => pure Definograph.HeadExposureTarget.term
        | "type" => pure Definograph.HeadExposureTarget.type
        | _ => throw "Definition-head target must be term or type."
      operations := operations.push (.expose target)
    else if kind == "focus" then
      unless exactKeys item ["kind", "path"] do throw "Invalid focus operation fields."
      let path ← item.getObjValAs? (Array String) "path"
      unless path.size ≤ 64 do throw "A focus path may contain at most 64 steps."
      totalPath := totalPath + path.size
      unless totalPath ≤ 128 do throw "Decomposition paths exceed 128 total steps."
      operations := operations.push (.focus (← path.toList.mapM occurrenceStep))
    else if kind == "fields" && profile != .legacy then
      unless exactKeys item ["kind"] do throw "Invalid catalogue operation fields."
      operations := operations.push .fields
    else if kind == "project" && profile != .legacy then
      unless exactKeys item ["kind", "index"] do throw "Invalid projection operation fields."
      let fieldIndex ← item.getObjValAs? Nat "index"
      unless fieldIndex < 16 && index > 0 do throw "Projection requires an available direct field."
      match operations[index - 1]! with
      | .fields => operations := operations.push (.project fieldIndex)
      | _ => throw "Projection requires the immediately preceding catalogue."
    else if kind == "typeComponent" && profile == .logicalStructure then
      unless exactKeys item ["kind"] do throw "Invalid type-component operation fields."
      operations := operations.push .typeComponent
    else if kind == "logical" && profile == .logicalStructure then
      unless exactKeys item ["kind"] do throw "Invalid logical operation fields."
      operations := operations.push .logical
    else throw "Unsupported decomposition operation."
  let reserved := operations.foldl (fun total operation => total + (match operation with
    | .expose _ | .project _ => 3 | .focus _ | .typeComponent => 2 | .logical => 4 | .fields => 0)) 6
  if profile == .logicalStructure && reserved > 30 then throw "Decomposition plan exceeds its reserved thirty-check limit."
  return { base with decomposition := some {
    profile, previousCaptureId, parentStepIndex, expectedSelected, operations, operationsJson := Json.arr recipe, expectedHistory } }

private def decompositionOperationName (profile : Definograph.DecompositionProfile) : String :=
  if profile == .legacy then "editor-decomposition" else if profile == .directFields then "editor-decomposition-v2" else "editor-decomposition-v3"

private def decompositionPolicy (profile : Definograph.DecompositionProfile) : Json := Json.mkObj <| [
  ("id", toJson (if profile == .legacy then "bounded-decomposition-v1" else if profile == .directFields then "bounded-decomposition-v2" else "bounded-decomposition-v3")),
  ("operation", toJson (decompositionOperationName profile)),
  ("preparation", toJson "Lean.instantiateMVars"), ("universeSubstitution", toJson "structural"),
  ("reduction", toJson "original-lambda-spine"),
  ("heartbeatBound", Definograph.exactNatJson 200000),
  ("retainedMetadata", toJson "definograph.raw.v1"), ("maxOperations", toJson (8 : Nat))] ++
  (if profile == .legacy then [] else [("maxChecks", toJson (30 : Nat)), ("maxFields", toJson (16 : Nat))]) ++
  (if profile == .logicalStructure then [("logicalInterpretation", toJson "lean-standard-core-v1")] else [])

private def decompositionRecord (request : OccurrenceRequest) (captureId : String) (checking : Json) : Json :=
  match request.decomposition with
  | none => .null
  | some plan => Json.mkObj [("schema", toJson (if plan.profile == .legacy then
      "definograph.source-decomposition.v1" else if plan.profile == .directFields then "definograph.source-decomposition.v2" else "definograph.source-decomposition.v3")),
      ("parentCaptureId", toJson request.parentCaptureId), ("previousCaptureId", toJson plan.previousCaptureId),
      ("parentStepIndex", toJson plan.parentStepIndex), ("captureId", toJson captureId),
      ("path", toJson request.path),
      ("operations", plan.operationsJson),
      ("policy", decompositionPolicy plan.profile), ("checking", checking)]

/-- Preserve identity while omitting the whole incomplete/oversized capture. -/
def omitDecompositionChecking (value : Json) (reason : String) : Json := Id.run do
  let checking := (value.getObjVal? "checking").toOption.getD .null
  let attempted := (checking.getObjValAs? String "status").toOption == some "captured" ||
    (checking.getObjValAs? Bool "attempted").toOption.getD false
  return value.setObjVal! "checking" (checkingUnavailable "limit" "decomposition-output" reason attempted)

private def boundDecomposition (value : Json) : Json :=
  if !jsonDepthWithin 120 value || value.compress.utf8ByteSize > 2 * 1024 * 1024 then
    omitDecompositionChecking value "The complete decomposition record exceeds its transport limit; no receipts are displayed."
  else value

private def headExposurePolicy : Json := Json.mkObj [
  ("id", toJson "safe-definition-head-v1"), ("operation", toJson "editor-head-exposure"),
  ("preparation", toJson "Lean.instantiateMVars"), ("universeSubstitution", toJson "structural"),
  ("reduction", toJson "original-lambda-spine"),
  ("heartbeatBound", Definograph.exactNatJson 200000),
  ("retainedMetadata", toJson "definograph.raw.v1")]

private def headExposureRecord (request : OccurrenceRequest) (captureId : String) (checking : Json) : Json :=
  Json.mkObj [("schema", toJson "definograph.source-head-exposure.v1"),
    ("parentCaptureId", toJson request.parentCaptureId), ("captureId", toJson captureId),
    ("path", toJson request.path),
    ("target", toJson (match request.headExposure with | some (.type, _) => "type" | _ => "term")),
    ("policy", headExposurePolicy), ("checking", checking)]

/-- Complete omission preserves the operation's identity and explicit attempt
status, but never invents a valid prefix after an output or bookkeeping failure. -/
def omitHeadExposureChecking (value : Json) (reason : String) : Json := Id.run do
  let checking := (value.getObjVal? "checking").toOption.getD .null
  let attempted := (checking.getObjValAs? String "status").toOption == some "captured" ||
    (checking.getObjValAs? Bool "attempted").toOption.getD false
  return value.setObjVal! "checking" (checkingUnavailable "limit" "head-exposure-output" reason attempted)

private def boundHeadExposure (value : Json) : Json :=
  if !jsonDepthWithin 120 value then
    omitHeadExposureChecking value "The complete definition-head record exceeds its nesting limit; no receipts are displayed."
  else if value.compress.utf8ByteSize > 1024 * 1024 then
    omitHeadExposureChecking value "The complete definition-head record exceeds 1 MiB; no receipts are displayed."
  else value

private def occurrencePolicy : Json := Json.mkObj [
  ("id", toJson "named-extraction-v1"), ("operation", toJson "editor-occurrence"),
  ("preparation", toJson "Lean.instantiateMVars"),
  ("heartbeatBound", Definograph.exactNatJson 200000),
  ("retainedMetadata", toJson "definograph.raw.v1")]

private def occurrenceRecord (request : OccurrenceRequest) (captureId : String) (checking : Json) : Json :=
  Json.mkObj [("schema", toJson "definograph.source-occurrence.v1"),
    ("parentCaptureId", toJson request.parentCaptureId), ("captureId", toJson captureId),
    ("path", toJson request.path), ("policy", occurrencePolicy), ("checking", checking)]

/-- Replace the complete checking record, never a prefix of receipts. This is
also used when the combined context response exceeds its transport allowance. -/
def omitOccurrenceChecking (value : Json) (reason : String) : Json := Id.run do
  let checking := (value.getObjVal? "checking").toOption.getD .null
  let attempted := (checking.getObjValAs? String "status").toOption == some "captured" ||
    (checking.getObjValAs? Bool "attempted").toOption.getD false
  return value.setObjVal! "checking" (checkingUnavailable "limit" "occurrence-output" reason attempted)

private def boundOccurrence (value : Json) : Json :=
  if !jsonDepthWithin 120 value then
    omitOccurrenceChecking value "The complete occurrence record exceeds the transport nesting limit; no receipts are displayed."
  else if value.compress.utf8ByteSize > 768 * 1024 then
    omitOccurrenceChecking value "The complete occurrence record exceeds 768 KiB; no receipts are displayed."
  else value

private def occurrenceTelescopeJson : {n : Nat} → V6Structured.CTel n → Except String Json
  | _, .nil => pure (Definograph.tag "nil")
  | _, .port C attrs type => do
    return Definograph.tag "port" [← occurrenceTelescopeJson C, Definograph.attrsJson attrs,
      ← Definograph.exprJson (V6Structured.dec type)]
  | _, .letE C name nondep type value => do
    return Definograph.tag "letE" [← occurrenceTelescopeJson C, Definograph.nameJson name, toJson nondep,
      ← Definograph.exprJson (V6Structured.dec type), ← Definograph.exprJson (V6Structured.dec value)]

private def capturedOccurrenceJson
    (captured : Definograph.CapturedSource Definograph.NamedExtractionResult) : Except String Json := do
  let (action, selected) ← match captured.capture.value with
    | .error reason => pure (Json.mkObj [("status", toJson "error"), ("reason", toJson (bounded reason))], Json.null)
    | .ok result => do
      let selected := Json.mkObj [
        ("home", Json.mkObj [("arity", toJson result.selected.extraction.home),
          ("telescope", ← occurrenceTelescopeJson result.selected.telescope)]),
        ("term", ← Definograph.exprJson (V6Structured.dec result.selected.extraction.component)),
        ("type", ← Definograph.exprJson (V6Structured.dec result.selectedType))]
      pure (Json.mkObj [("status", toJson "completed")], selected)
  let record := Json.mkObj [("status", toJson "captured"), ("action", action),
    ("binding", captured.binding), ("selected", selected), ("checks", Json.arr captured.capture.checks),
    ("audits", Json.arr captured.capture.audits),
    ("environmentSnapshotCount", toJson captured.capture.environments.size)]
  Definograph.checkExactNaturalBudget record
  return record

/-- Optional notation is a sidecar, never a field of an exact capture or receipt. -/
def presentationUnavailable (captureId reason : String) : Json := Json.mkObj [
  ("schema", toJson "definograph.source-presentation.v1"), ("captureId", toJson captureId),
  ("status", toJson "unavailable"), ("reason", toJson (reason.take 512).toString)]

/-- Print only the last requested exposure, from its owned telescope in the
original environment. The printer may hide implicit arguments; it supplies no
new checked expression, reduction, or receipt. Its Meta state is always restored. -/
private def capturedPresentation (captureId : String) (initial : Environment)
    (originalOptions : Options) (requestedSteps : Nat)
    (captured : Definograph.CapturedSource Definograph.NamedDecompositionResult) : MetaM Json := do
  let absent := presentationUnavailable captureId "No captured exposed result is available for native notation."
  let .ok result := captured.capture.value | return absent
  unless result.steps.size == requestedSteps do return absent
  let some step := result.steps.back? | return absent
  let .expose target := step.operation | return absent
  let .exposed candidate _ := step.output | return absent
  let context := DefinographAdmission.contextExpr step.input.context
  let expression := V6Structured.dec candidate.after
  let carrier := V6Structured.dec candidate.carrier
  if [context, expression, carrier].any (fun e => e.approxDepth > 80) ||
      context.sizeWithoutSharing + expression.sizeWithoutSharing + carrier.sizeWithoutSharing > 4000 then
    return presentationUnavailable captureId "The exposed result or its scope exceeds the optional notation input limit."
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let used := now - ctx.initHeartbeats
  let remaining := if ctx.maxHeartbeats == 0 then 10000000 else ctx.maxHeartbeats - used
  -- Leave budget for the unchanged context response and any other optional views.
  let budget := min 10000000 (remaining - 1000000)
  if budget < 1000 then
    return presentationUnavailable captureId "No optional notation printing budget remains."
  let saved ← Meta.saveState
  try
    tryCatchRuntimeEx (withTheReader Core.Context (fun state =>
      { state with initHeartbeats := now, maxHeartbeats := budget, maxRecDepth := min state.maxRecDepth 128 }) do
      -- withOptions also refreshes Core.Context.maxRecDepth, including when the
      -- delaborator changes an option internally, so keep the cap in both places.
      withEnv initial <| withOptions (fun _ => originalOptions
          |>.set `maxRecDepth (min (maxRecDepth.get originalOptions) 128)
          |>.set `pp.maxSteps (min (getPPMaxSteps originalOptions) 20000)
          |>.set `pp.beta false) do
        withLCtx {} {} do
          DefinographAdmission.withCoreContext step.input.context fun vars => do
            let opened := DefinographAdmission.instantiateSlots vars candidate.after
            if opened.hasLooseBVars then
              return presentationUnavailable captureId "The exposed result could not be printed in its recorded scope."
            let printed ← PrettyPrinter.ppExprWithInfos opened
            let omitted := printed.infos.toList.any fun (_, info) => match info with
              | .ofDelabTermInfo term => term.docString?.any fun reason =>
                [PrettyPrinter.Delaborator.OmissionReason.deep,
                  .proof, .maxSteps].any (fun omission => reason == omission.toString)
              | _ => false
            if omitted then
              return presentationUnavailable captureId "The native printer omitted a subexpression under its display options or limits; the exact result is retained."
            let text := printed.fmt.pretty 88
            if text.length > 8192 || text.utf8ByteSize > 32768 then
              return presentationUnavailable captureId "Native notation exceeds the display text limit; the exact result is retained."
            let .ok exactResult := Definograph.selectedTripleJson step.input.context candidate.after candidate.carrier
              | return presentationUnavailable captureId "The result association exceeds the optional notation serialization limit."
            let value := Json.mkObj [
              ("schema", toJson "definograph.source-presentation.v1"), ("captureId", toJson captureId),
              ("status", toJson "available"), ("stepIndex", toJson step.index),
              ("target", target.json), ("result", exactResult), ("text", toJson text)]
            if value.compress.utf8ByteSize > 128 * 1024 then
              return presentationUnavailable captureId "The result association exceeds the optional notation transport limit."
            return value) fun _ =>
        pure (presentationUnavailable captureId "Native notation is unavailable for this result; its exact expression and scope are retained.")
  finally saved.restore

private def preparedOccurrence (captureId : String) (request : OccurrenceRequest)
    (term : TermInfo) (originalType : Expr)
    (presentation : Option (IO.Ref (Option Json)) := none) : MetaM Json := do
  let saved ← Meta.saveState
  try
    tryCatchRuntimeEx (do
      -- Preserve the inference effects of this run. In particular, a type Expr
      -- transplanted from another run cannot supply fresh metavariable state.
      let repeatedType ← inferType term.expr
      let .ok originalWire := Definograph.rawExprJson originalType rawLimits
        | return checkingUnavailable "limit" "preparation" "The original inferred type exceeds the comparison profile."
      let .ok repeatedWire := Definograph.rawExprJson repeatedType rawLimits
        | return checkingUnavailable "limit" "preparation" "The repeated inferred type exceeds the comparison profile."
      unless originalWire == repeatedWire do
        return checkingUnavailable "error" "preparation" "Repeating inference produced a different exact source type."
      let preparedContext ← prepareContext (← getLCtx)
      let preparedTerm ← instantiateMVars term.expr
      let preparedType ← instantiateMVars repeatedType
      withLCtx preparedContext (← getLocalInstances) do
        let encoded ← Definograph.captureRawFrame preparedTerm preparedType rawLimits
        let frame ← match encoded with
          | .ok value => pure value
          | .error reason => return checkingUnavailable "limit" "preparation" reason
        let params := checkerUniverseParams preparedContext preparedTerm preparedType
        let prepared := Json.mkObj [("status", toJson "available"),
          ("typeOrigin", toJson "inferred-instantiated"), ("frame", frame),
          ("checkerUniverseParams", Definograph.arr (params.map Definograph.nameJson))]
        unless prepared == request.prepared do
          return checkingUnavailable "prerequisite" "parent-match" "The freshly prepared frame or checking parameters differ from the requested parent."
        if preparedContext.foldl (fun n _ => n + 1) (0 : Nat) > 128 then
          return checkingUnavailable "limit" "source-policy" "The prepared context exceeds 128 declarations."
        if sourceHasSorry preparedTerm preparedType preparedContext then
          return checkingUnavailable "unsupported" "source-policy" "The prepared source contains a placeholder (sorry)."
        tryCatchRuntimeEx (do
          if let some plan := request.decomposition then
            let initial ← getEnv
            let originalOptions ← getOptions
            let result ← Definograph.captureNamedDecomposition captureId (decompositionOperationName plan.profile) {
              declarationPrefix := .str `StatementLens.SourceDecomposition captureId,
              universeParams := params, heartbeatFor := fun _ => 200000, retainedMetadata := .rawV1
            } preparedTerm preparedType request.steps plan.expectedSelected plan.operations plan.expectedHistory {} plan.profile
            match result with
            | .error reason =>
              return checkingUnavailable (if (reason.splitOn "limit").length > 1 then "limit" else "unsupported")
                "decomposition-capture" reason true
            | .ok captured =>
              match Definograph.capturedDecompositionJson captured with
              | .ok value =>
                if let some output := presentation then
                  -- A failure anywhere in this optional path, including its
                  -- input preflight, must not replace the serialized exact record.
                  let readable ← tryCatchRuntimeEx
                    (capturedPresentation captureId initial originalOptions plan.operations.size captured)
                    (fun _ => pure (presentationUnavailable captureId
                      "Native notation is unavailable for this result; its exact expression and scope are retained."))
                  output.set (some readable)
                return value
              | .error reason =>
                let kind := if reason == "decomposition checking exceeds the nesting limit" ||
                    reason == "decomposition checking exceeds 2 MiB" then "limit" else "error"
                return checkingUnavailable kind "decomposition-output" reason true
          if let some (target, expected) := request.headExposure then
            let result ← Definograph.captureNamedHeadExposure captureId "editor-head-exposure" {
              declarationPrefix := .str `StatementLens.SourceHeadExposure captureId,
              universeParams := params, heartbeatFor := fun _ => 200000, retainedMetadata := .rawV1
            } preparedTerm preparedType request.steps target expected
            match result with
            | .error reason =>
              return checkingUnavailable (if (reason.splitOn "limit").length > 1 then "limit" else "unsupported")
                "head-exposure-capture" reason true
            | .ok captured =>
              match Definograph.capturedHeadExposureJson captured with
              | .ok value => return value
              | .error reason => return checkingUnavailable "error" "head-exposure-output" reason true
          let result ← Definograph.captureNamedExtraction captureId "editor-occurrence" {
            declarationPrefix := .str `StatementLens.SourceOccurrence captureId,
            universeParams := params, heartbeatFor := fun _ => 200000, retainedMetadata := .rawV1
          } preparedTerm preparedType request.steps
          match result with
          | .error reason =>
            return checkingUnavailable (if (reason.splitOn "limit").length > 1 then "limit" else "unsupported")
              "occurrence-capture" reason true
          | .ok captured =>
            match capturedOccurrenceJson captured with
            | .ok value => return value
            | .error reason => return checkingUnavailable "limit" "occurrence-output" reason true)
          fun error => do
            return checkingUnavailable (exceptionKind error) "occurrence-capture" (← error.toMessageData.toString) true)
      fun error => do
        return checkingUnavailable (exceptionKind error) "preparation" (← error.toMessageData.toString)
  finally saved.restore

/-- An explicit occurrence request starts a fresh isolated capture of the same
selected InfoTree term. Parent JSON is compared as data only: it never rebuilds
an environment, local context or metavariable state, and never supplies a proof. -/
private def captureFreshSelection (term : TermInfo) (context : ContextInfo) (captureId : String)
    (selection : Selection) (request : OccurrenceRequest) (freshSnapshot : Json)
    (finish : Json → Json) (presentation : Option (IO.Ref (Option Json)) := none) : IO Json := do
  unless validCaptureId captureId do throw (IO.userError "captureId must be a UUID")
  unless request.parentCaptureId != captureId do
    return finish (checkingUnavailable "prerequisite" "parent-match" "An occurrence requires a fresh capture identity.")
  let selected := (freshSnapshot.getObjVal? "selection").toOption.getD .null
  let actualParent ← match context.parentDecl? with
    | none => pure Json.null
    | some name => do
      let encoded ← IO.ofExcept (Definograph.rawExprJson (.fvar ⟨name⟩) expectedLimits)
      let parts ← IO.ofExcept encoded.getArr?
      pure parts[1]!
  let rangeMatches := (selected.getObjValAs? Nat "startByte").toOption == some selection.startByte &&
    (selected.getObjValAs? Nat "endByte").toOption == some selection.endByte &&
    (selected.getObjValAs? Nat "requestedStartByte").toOption == some selection.requestedStartByte &&
    (selected.getObjValAs? Nat "requestedEndByte").toOption == some selection.requestedEndByte &&
    (selected.getObjVal? "parentDeclaration").toOption == some actualParent
  let fixedPolicy := Json.mkObj [("id", toJson "named-source-v1"), ("operation", toJson "editor-source"),
    ("preparation", toJson "Lean.instantiateMVars"), ("heartbeatBound", Definograph.exactNatJson 200000),
    ("retainedMetadata", toJson "definograph.raw.v1")]
  unless rangeMatches && selected == request.selection &&
      (freshSnapshot.getObjVal? "policy").toOption == some fixedPolicy &&
      (freshSnapshot.getObjVal? "prepared").toOption == some request.prepared do
    return finish (checkingUnavailable "prerequisite" "parent-match" "The fresh selection, parent declaration, prepared frame or policy differs from the requested parent.")
  let original ← term.runMetaM context <| withOptions (fun opts =>
    opts.set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (400000 : Nat)) (originalCapture term)
  let checking ← match original.inferredType with
    | none => pure (checkingUnavailable "prerequisite" "prerequisite" "The fresh original source type could not be inferred.")
    | some type =>
      term.runMetaM context (withOptions (fun opts =>
        opts.set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (400000 : Nat))
        (preparedOccurrence captureId request term type presentation))
  return finish checking

/-- Fresh ordinary extraction; the established occurrence schema is unchanged. -/
def captureOccurrence (term : TermInfo) (context : ContextInfo) (captureId : String)
    (selection : Selection) (requestValue freshSnapshot : Json) : IO Json := do
  let request ← IO.ofExcept (parseOccurrenceRequest requestValue)
  captureFreshSelection term context captureId selection request freshSnapshot
    (fun checking => boundOccurrence (occurrenceRecord request captureId checking))

/-- An explicit fresh operation retains its own selected candidate and result;
no derived expression is relabelled as an original source occurrence. -/
def captureHeadExposure (term : TermInfo) (context : ContextInfo) (captureId : String)
    (selection : Selection) (requestValue freshSnapshot : Json) : IO Json := do
  let request ← IO.ofExcept (parseHeadExposureRequest requestValue)
  captureFreshSelection term context captureId selection request freshSnapshot
    (fun checking => boundHeadExposure (headExposureRecord request captureId checking))

/-- Replay a retained linear prefix against this fresh source, then perform one
explicit new operation. Comparison JSON is never used as elaboration input. -/
def captureDecomposition (term : TermInfo) (context : ContextInfo) (captureId : String)
    (selection : Selection) (requestValue freshSnapshot : Json) : IO (Json × Json) := do
  let request ← IO.ofExcept (parseDecompositionRequest requestValue)
  if let some plan := request.decomposition then
    unless captureId != plan.previousCaptureId do
      return (boundDecomposition (decompositionRecord request captureId
        (checkingUnavailable "prerequisite" "parent-match" "Decomposition requires a fresh capture identity.")),
        presentationUnavailable captureId "Native notation requires a fresh result capture.")
  let presentation ← IO.mkRef (none : Option Json)
  let record ← captureFreshSelection term context captureId selection request freshSnapshot
    (fun checking => boundDecomposition (decompositionRecord request captureId checking)) (some presentation)
  return (record, (← presentation.get).getD
    (presentationUnavailable captureId "No captured exposed result is available for native notation."))

end StatementLens.SourceSnapshot
