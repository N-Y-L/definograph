import Lean
import StatementLens.Export
import StatementLens.Response
import StatementLens.SourceSnapshot

/- A trusted-project adapter, deliberately separate from the closed-term worker.
   The native exporter is not imported into the project's elaboration environment. -/
open Lean Meta Elab
namespace StatementLens.Context

def guidedContextContract : String := "definograph.guided-context.v1"

structure Candidate where
  context : ContextInfo
  term : TermInfo
  startByte : Nat
  endByte : Nat

partial def candidates (tree : InfoTree) (outer : Option ContextInfo) (start stop : Nat)
    (out : Array Candidate := #[]) : Array Candidate := Id.run do
  if out.size >= 2048 then return out
  match tree with
  | .context inner child => return candidates child (inner.mergeIntoOuter? outer) start stop out
  | .hole _ => return out
  | .node info children =>
    let mut result := out
    if let some ctx := outer then
      if let .ofTermInfo term := info then
        if !term.isBinder then
          if let some range := term.stx.getRange? (canonicalOnly := true) then
            if range.start.byteIdx <= start && stop <= range.stop.byteIdx &&
                (start < range.stop.byteIdx || start == stop && range.start.byteIdx == start) &&
                (start == stop || range.start.byteIdx == start && range.stop.byteIdx == stop) then
              result := result.push ⟨ctx, term, range.start.byteIdx, range.stop.byteIdx⟩
    for child in children do result := candidates child outer start stop result
    return result

/-- Local context is an explicitly parameterized fragment, not a universally asserted theorem. -/
partial def contextTree (locals : Array LocalDecl) (index : Nat) (expression : Expr)
    (bs : Bounds := #[]) (path := "context") (policy : ExportPolicy := {}) : MetaM Json := do
  if index >= locals.size then return ← tree expression bs (path ++ ".selected") policy
  let localDecl :=  locals[index]!
  let ty ← zetaReduce (← instantiateMVars localDecl.type)
  if ty.hasMVar || ty.hasSorry then throwError "The selected context has an unresolved or placeholder type."
  let auxiliary := localDecl.isImplementationDetail
  let declarationKind := if localDecl.kind == .auxDecl then "auxDecl" else "implDetail"
  let assumption ← if auxiliary then pure false else isProp ty
  let b : Bound := ⟨localDecl.fvarId, path ++ ".binder", binderName localDecl.userName, ← pp ty,
    if auxiliary then "auxiliary" else if assumption then "assumption" else "parameter"⟩
  let bj ← if auxiliary then basicBinderJson b ty bs else binderJson b ty bs
  let bj ← if auxiliary then pure (bj.setObjVal! "declarationKind" (str declarationKind))
    else reflectBinder b ty bs bj (fun e bs path => tree e bs path {} 0 0 false)
  let body ← contextTree locals (index + 1) expression (bs.push b) (path ++ ".body") policy
  let premise ← if assumption then pure #[← tree ty bs (path ++ ".premise") policy] else pure #[]
  let expr := obj [("kind", str (if assumption then "forall" else "lambda")), ("binder", bj),
    ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf body)]
  return (node path (if auxiliary then "auxiliary" else if assumption then "implies" else "parameter")
    (if auxiliary then s!"{if declarationKind == "auxDecl" then "Auxiliary entry" else "Context entry"} {b.name}, recorded kind {declarationKind}"
      else if assumption then s!"Assume {b.name}" else s!"Context parameter {b.name}")
    b.type (premise.push body) expr (some bj)).setObjVal! "scope" (toJson (bs.map (·.id)))

def exportCandidate (candidate : Candidate) (source : String) (fileName : String) (request : Json) : IO Json := do
  unless (request.getObjValAs? String "guidedContextContract").toOption == some guidedContextContract do
    throw (IO.userError "Incompatible guided context format. Rebuild the matching checkout and extension, then reopen Definograph: Visualize Selection. Exact source capture remains separate.")
  candidate.term.runMetaM candidate.context <| withOptions (fun opts =>
    opts.set `statementLens.projectContext true |>.set `maxRecDepth (256 : Nat) |>.set `maxHeartbeats (400000 : Nat)) do
    -- InfoTrees can retain assigned expression and universe metavariables in
    -- local declaration types. The kernel reads those declarations directly;
    -- normalize the actual local context before checking the selected term.
    let mut normalizedContext ← getLCtx
    for localDecl in ← getLCtx do
      let ty ← instantiateMVars localDecl.type
      let mut normalized := localDecl.setType ty
      if let some value := localDecl.value? (allowNondep := true) then
        normalized := normalized.setValue (← instantiateMVars value)
      normalizedContext := normalizedContext.modifyLocalDecl localDecl.fvarId (fun _ => normalized)
    withLCtx normalizedContext (← getLocalInstances) do
      let original ← instantiateMVars (← zetaReduce (← instantiateMVars candidate.term.expr))
      if original.hasMVar || original.hasSorry then throwError "The selected term is incomplete or contains sorry."
      let originalType ← inferType original
      let proof ← isProp originalType
      let expression ← if ← isProp original then pure original else if proof then pure originalType
        else throwError "Select a proposition, theorem statement, or proof term with a proposition type."
      checkWithKernel original
      checkWithKernel expression
      let expression ← instantiateMVars (← zetaReduce expression)
      if expression.hasMVar || expression.hasSorry then throwError "The selected proposition contains an unresolved term or sorry after local definitions are substituted."
      let mut locals := #[]
      for localDecl in ← getLCtx do
        if !localDecl.isLet then
          -- InfoTree contexts may retain assigned metavariables in local types.
          -- Use the same checked, normalized types for the tree, definition
          -- inventory, and optional previews; none may inspect a stale raw type.
          let ty ← instantiateMVars (← zetaReduce (← instantiateMVars localDecl.type))
          if ty.hasMVar || ty.hasSorry then throwError "The selected context has an unresolved or placeholder type."
          checkWithKernel ty
          locals := locals.push (localDecl.setType ty)
      if locals.size > 128 then throwError "The selected local context exceeds 128 declarations."
      let policy ← readPolicy request
      let result ← contextTree locals 0 expression #[] "context" policy
      let pretty ← pp expression
      let type ← pp (← inferType expression)
      let ordinaryLocals := locals.filter (! ·.isImplementationDetail)
      let contextExpressions := #[expression] ++ ordinaryLocals.map (·.type)
      let mut definitions := #[]
      let mut definitionNames : Array Name := #[]
      for contextExpression in contextExpressions do
        if definitions.size >= 128 then break
        for name in contextExpression.getUsedConstants do
          if definitions.size >= 128 then break
          if definitionNames.contains name then continue
          if let some info := (← getEnv).find? name then
            if info.isDefinition && !info.isUnsafe && !info.isPartial then
              definitions := definitions.push (← declarationJson info)
              definitionNames := definitionNames.push name
      let previews ← definitionPreviews request policy contextExpressions pretty
        (fun previewPolicy => contextTree locals 0 expression #[] "context" previewPolicy)
      return obj [
        ("ok", toJson true), ("schemaVersion", toJson (2 : Nat)), ("leanVersion", str Lean.versionString),
        ("source", str source), ("pretty", str pretty), ("type", str type),
        ("validation", str "kernel-type-checked-context-fragment"),
        ("provenance", obj [("assistant", str "lean"), ("inputMode", str "editor"),
          ("inspected", str "context-fragment"), ("fileName", str fileName),
          ("selectionKind", str (if proof then "proof-type" else "proposition")),
          ("startByte", toJson candidate.startByte), ("endByte", toJson candidate.endByte),
          ("requestedStartByte", (request.getObjVal? "startByte").toOption.getD Json.null),
          ("requestedEndByte", (request.getObjVal? "endByte").toOption.getD Json.null),
          ("parentDeclaration", candidate.context.parentDecl?.map (str ∘ Name.toString) |>.getD Json.null),
          ("contextParameters", toJson ordinaryLocals.size),
          ("auxiliaryContextEntries", toJson (locals.size - ordinaryLocals.size)),
          ("localLetBindings", str "substituted-definitionally")]),
        ("expansionPolicy", obj [("constants", toJson (policy.constants.map Name.toString)), ("maxDepth", toJson policy.maxDepth)]),
        ("definitions", Json.arr definitions), ("definitionPreviews", Json.arr previews), ("tree", result), ("expression", expressionOf result),
        ("sourceTerms", Json.arr #[obj [("startByte", toJson candidate.startByte), ("endByte", toJson candidate.endByte),
          ("lean", str pretty), ("type", str type), ("isBinder", toJson false), ("origin", str "lean-infotree")]]),
        ("metrics", Json.arr #[]), ("diagnostics", Json.arr #[])]

unsafe def analyze (request : Json) : IO Json := do
  let source ← IO.ofExcept (request.getObjValAs? String "source")
  let fileName ← IO.ofExcept (request.getObjValAs? String "fileName")
  let start ← IO.ofExcept (request.getObjValAs? Nat "startByte")
  let stop ← IO.ofExcept (request.getObjValAs? Nat "endByte")
  let captureId ← IO.ofExcept (request.getObjValAs? String "captureId")
  unless SourceSnapshot.validCaptureId captureId do
    throw (IO.userError "captureId must be a UUID")
  if source.utf8ByteSize > 524288 || start > stop || stop > source.utf8ByteSize then
    throw (IO.userError "Invalid source buffer or byte selection (maximum 512 KiB).")
  let opts := ({} : Options).set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (800000 : Nat)
    |>.set `Elab.async false
  let mainModule := ((request.getObjValAs? String "mainModule").toOption.getD "StatementLensEditorBuffer").toName
  -- Host selections and retained source ranges refer to the exact original
  -- buffer bytes. Default CRLF normalization would shift every later range.
  let input := Parser.mkInputContext source fileName (normalizeLineEndings := false)
  let (header, parserState, messages) ← Parser.parseHeader input
  let (env, messages) ← processHeader header opts messages input (mainModule := mainModule)
  if messages.hasErrors then throw (IO.userError "Project imports could not be loaded. Build the project's saved dependencies using its normal Lean workflow.")
  let state ← Elab.IO.processCommands input parserState (Command.mkState env messages opts)
  let infoState := state.commandState.infoState.substituteLazy.get
  let mut found := #[]
  for tree in infoState.trees do
    found := candidates (tree.substitute infoState.assignment) none start stop found
  found := found.qsort fun a b => a.endByte - a.startByte < b.endByte - b.startByte
  let mut selected : Option Candidate := none
  for candidate in found do
    let eligible ← try candidate.term.runMetaM candidate.context do
      let e ← instantiateMVars candidate.term.expr
      pure ((← isProp e) || (← isProp (← inferType e)))
      catch _ => pure false
    if eligible then
      selected := some candidate
      break
  -- Keep all previous proposition choices. If none is eligible, the smallest
  -- available term may still have an inspectable raw snapshot; guided export
  -- reports its own boundary without discarding that term.
  let some chosen := selected.orElse (fun _ => found[0]?) |
    throw (IO.userError "No elaborated term is available at this selection.")
  -- Do not fall back from an invalid selected proposition to a larger unrelated one.
  let (snapshot, captureFailure) ← try
    let value ← SourceSnapshot.capture chosen.term chosen.context captureId {
      startByte := chosen.startByte, endByte := chosen.endByte,
      requestedStartByte := start, requestedEndByte := stop
    }
    pure (some value, none)
  catch error => pure (none, some ((error.toString.take 4096).toString))
  let explicitActions := ["occurrence", "headExposure", "decomposition"].filter fun key =>
    (request.getObjVal? key).toOption.isSome
  if explicitActions.length > 1 then
    throw (IO.userError "Occurrence, definition-head and decomposition requests are mutually exclusive.")
  let (occurrence, occurrenceFailure) ← match (request.getObjVal? "occurrence").toOption with
    | none => pure (none, none)
    | some occurrenceRequest => match snapshot with
      | none => pure (none, some "A fresh source snapshot is unavailable; occurrence checking did not begin.")
      | some fresh => do
        try
          let value ← SourceSnapshot.captureOccurrence chosen.term chosen.context captureId {
            startByte := chosen.startByte, endByte := chosen.endByte,
            requestedStartByte := start, requestedEndByte := stop
          } occurrenceRequest fresh
          pure (some value, none)
        catch error => pure (none, some ((error.toString.take 4096).toString))
  let (headExposure, headExposureFailure) ← match (request.getObjVal? "headExposure").toOption with
    | none => pure (none, none)
    | some exposureRequest => match snapshot with
      | none => pure (none, some "A fresh source snapshot is unavailable; definition-head checking did not begin.")
      | some fresh => do
        try
          let value ← SourceSnapshot.captureHeadExposure chosen.term chosen.context captureId {
            startByte := chosen.startByte, endByte := chosen.endByte,
            requestedStartByte := start, requestedEndByte := stop
          } exposureRequest fresh
          pure (some value, none)
        catch error => pure (none, some ((error.toString.take 4096).toString))
  let (decomposition, decompositionFailure) ← match (request.getObjVal? "decomposition").toOption with
    | none => pure (none, none)
    | some decompositionRequest => match snapshot with
      | none => pure (none, some "A fresh source snapshot is unavailable; decomposition checking did not begin.")
      | some fresh => do
        try
          let value ← SourceSnapshot.captureDecomposition chosen.term chosen.context captureId {
            startByte := chosen.startByte, endByte := chosen.endByte,
            requestedStartByte := start, requestedEndByte := stop
          } decompositionRequest fresh
          pure (some value, none)
        catch error => pure (none, some ((error.toString.take 4096).toString))
  let result ← try exportCandidate chosen source fileName request catch error =>
    pure (obj [("ok", toJson false), ("error", str error.toString), ("diagnostics", Json.arr #[])])
  let mut diagnostics := #[]
  for msg in state.commandState.messages.toList do
    if diagnostics.size >= 100 then break
    let message := (← msg.data.toString).take 4096 |>.toString
    let severity := match msg.severity with | .error => "error" | .warning => "warning" | .information => "information"
    diagnostics := diagnostics.push (obj [("severity", str severity), ("message", str message),
      ("line", toJson msg.pos.line), ("column", toJson msg.pos.column)])
  if let some reason := captureFailure then
    diagnostics := diagnostics.push (obj [("severity", str "warning"),
      ("message", str ("Exact source capture unavailable: " ++ reason))])
  let mut result := result.setObjVal! "diagnostics" (Json.arr diagnostics)
    |>.setObjVal! "guidedContextContract" (str guidedContextContract)
  if let some occurrence := occurrence then result := result.setObjVal! "sourceOccurrence" occurrence
  if let some reason := occurrenceFailure then result := result.setObjVal! "sourceOccurrenceUnavailable" (str reason)
  if let some value := headExposure then result := result.setObjVal! "sourceHeadExposure" value
  if let some reason := headExposureFailure then result := result.setObjVal! "sourceHeadExposureUnavailable" (str reason)
  if let some value := decomposition then result := result.setObjVal! "sourceDecomposition" value
  if let some reason := decompositionFailure then result := result.setObjVal! "sourceDecompositionUnavailable" (str reason)
  if let some snapshot := snapshot then return result.setObjVal! "sourceSnapshot" snapshot
  if let some reason := captureFailure then return result.setObjVal! "sourceSnapshotUnavailable" (str reason)
  return result

/-- Preserve the existing 2 MiB guided-export policy independently of the bounded
snapshot. In particular, optional legacy trimming must never enter raw source
records or diagnostic declarations and delete a constructor field by its name. -/
def serializeContextResponse (result : Json) : String := Id.run do
  let snapshot := (result.getObjVal? "sourceSnapshot").toOption
  let unavailable := (result.getObjVal? "sourceSnapshotUnavailable").toOption
  let occurrence := (result.getObjVal? "sourceOccurrence").toOption
  let occurrenceUnavailable := (result.getObjVal? "sourceOccurrenceUnavailable").toOption
  let headExposure := (result.getObjVal? "sourceHeadExposure").toOption
  let headExposureUnavailable := (result.getObjVal? "sourceHeadExposureUnavailable").toOption
  let decomposition := (result.getObjVal? "sourceDecomposition").toOption
  let decompositionUnavailable := (result.getObjVal? "sourceDecompositionUnavailable").toOption
  let legacy := match result.getObj? with
    | .ok fields => Json.mkObj (fields.toList.filter fun (key, _) =>
      !["sourceSnapshot", "sourceSnapshotUnavailable", "sourceOccurrence", "sourceOccurrenceUnavailable",
        "sourceHeadExposure", "sourceHeadExposureUnavailable", "sourceDecomposition", "sourceDecompositionUnavailable"].contains key)
    | .error _ => result
  let serialized := Response.serializeResponse legacy
  let legacyText := if serialized.utf8ByteSize > 2097152 then
    (obj [("ok", toJson false), ("error", str "The selected context exceeds the 2 MiB export limit."),
      ("diagnostics", Json.arr #[])]).compress else serialized
  let append := fun (text key : String) (value : Json) =>
    (text.dropEnd 1).toString ++ "," ++ (str key).compress ++ ":" ++ value.compress ++ "}"
  let snapshotText := match snapshot with
    | some value => append legacyText "sourceSnapshot" value
    | none => match unavailable with
      | some reason => append legacyText "sourceSnapshotUnavailable" reason
      | none => legacyText
  let occurrenceText := match occurrence with
    | some value => Id.run do
      let complete := append snapshotText "sourceOccurrence" value
      if complete.utf8ByteSize ≤ 4 * 1024 * 1024 then return complete
      return append snapshotText "sourceOccurrence" (SourceSnapshot.omitOccurrenceChecking value
        "The combined context response exceeds 4 MiB; the complete occurrence checking record is omitted.")
    | none => match occurrenceUnavailable with
      | some reason => append snapshotText "sourceOccurrenceUnavailable" reason
      | none => snapshotText
  let exposureText := match headExposure with
    | some value => Id.run do
      let complete := append occurrenceText "sourceHeadExposure" value
      if complete.utf8ByteSize ≤ 4 * 1024 * 1024 then return complete
      return append occurrenceText "sourceHeadExposure" (SourceSnapshot.omitHeadExposureChecking value
        "The combined context response exceeds 4 MiB; the complete definition-head checking record is omitted.")
    | none => match headExposureUnavailable with
      | some reason => append occurrenceText "sourceHeadExposureUnavailable" reason
      | none => occurrenceText
  match decomposition with
  | some value =>
    let complete := append exposureText "sourceDecomposition" value
    if complete.utf8ByteSize ≤ 4 * 1024 * 1024 then return complete
    return append exposureText "sourceDecomposition" (SourceSnapshot.omitDecompositionChecking value
      "The combined context response exceeds 4 MiB; the complete decomposition checking record is omitted.")
  | none => match decompositionUnavailable with
    | some reason => return append exposureText "sourceDecompositionUnavailable" reason
    | none => return exposureText

unsafe def run : IO Unit := do
  let sysroot ← match ← IO.getEnv "STATEMENTLENS_LEAN_SYSROOT" with
    | some p => pure (System.FilePath.mk p)
    | none => findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  let input ← (← IO.getStdin).getLine
  let parsed := Json.parse input
  let result ← try analyze (← IO.ofExcept parsed) catch error => do
    let result := obj [("ok", toJson false), ("error", str error.toString), ("diagnostics", Json.arr #[])]
    let result := if (parsed.toOption.bind fun value => (value.getObjVal? "occurrence").toOption).isSome then
      result.setObjVal! "sourceOccurrenceUnavailable"
        (str ("Occurrence capture could not begin: " ++ (error.toString.take 4000).toString))
      else result
    let result := if (parsed.toOption.bind fun value => (value.getObjVal? "headExposure").toOption).isSome then
      result.setObjVal! "sourceHeadExposureUnavailable"
        (str ("Definition-head capture could not begin: " ++ (error.toString.take 4000).toString))
      else result
    if (parsed.toOption.bind fun value => (value.getObjVal? "decomposition").toOption).isSome then
      pure (result.setObjVal! "sourceDecompositionUnavailable"
        (str ("Decomposition capture could not begin: " ++ (error.toString.take 4000).toString)))
    else pure result
  -- Project commands may write stdout. A private one-shot result file keeps their
  -- output out of the protocol; Node still bounds stdout/stderr separately.
  let some resultFile ← IO.getEnv "STATEMENTLENS_CONTEXT_RESULT" |
    throw (IO.userError "The context result path is missing.")
  let output := serializeContextResponse result
  IO.FS.writeFile resultFile output

end StatementLens.Context
unsafe def main : IO Unit := StatementLens.Context.run
