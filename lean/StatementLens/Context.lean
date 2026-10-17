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
  /-- The index of the top-level InfoTree, one per command, that recorded this term. -/
  tree : Nat := 0

partial def candidates (tree : InfoTree) (outer : Option ContextInfo) (start stop : Nat)
    (out : Array Candidate := #[]) (treeIndex : Nat := 0) : Array Candidate := Id.run do
  if out.size >= 2048 then return out
  match tree with
  | .context inner child => return candidates child (inner.mergeIntoOuter? outer) start stop out treeIndex
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
              result := result.push ⟨ctx, term, range.start.byteIdx, range.stop.byteIdx, treeIndex⟩
    for child in children do result := candidates child outer start stop result treeIndex
    return result

/-- Smallest byte range first. `candidates` records a parent before its children,
so among terms with the same range the outermost comes first: an anonymous
constructor is read as the whole term, not as its synthesized constructor constant. -/
def orderCandidates (found : Array Candidate) : Array Candidate :=
  (found.zipIdx.qsort fun (a, i) (b, j) =>
    let spanA := a.endByte - a.startByte
    let spanB := b.endByte - b.startByte
    spanA < spanB || spanA == spanB && i < j).map (·.1)

/-- The byte ranges of every `variable` command, from the commands' own InfoTree records. -/
partial def variableCommandRanges (tree : InfoTree) (out : Array (Nat × Nat) := #[]) : Array (Nat × Nat) := Id.run do
  match tree with
  | .context _ child => return variableCommandRanges child out
  | .hole _ => return out
  | .node info children =>
    let mut result := out
    if let .ofCommandInfo command := info then
      if command.stx.getKind == ``Lean.Parser.Command.variable then
        if let some range := command.stx.getRange? (canonicalOnly := true) then
          result := result.push (range.start.byteIdx, range.stop.byteIdx)
    for child in children do result := variableCommandRanges child result
    return result

/-- Where Lean recorded the binder of each local: the start byte of every binder `TermInfo` whose expression is that
free variable. Lean re-elaborates the section's `variable` binders for every declaration and records each one at the
identifier written in its `variable` command (`Term.addLocalVarInfo`). -/
partial def binderPositions (tree : InfoTree) (out : Std.HashMap FVarId (Array Nat) := {}) : Std.HashMap FVarId (Array Nat) := Id.run do
  match tree with
  | .context _ child => return binderPositions child out
  | .hole _ => return out
  | .node info children =>
    let mut result := out
    if let .ofTermInfo term := info then
      if term.isBinder then
        if let .fvar id := term.expr then
          if let some position := term.stx.getPos? (canonicalOnly := true) then
            result := result.insert id ((result.getD id #[]).push position.byteIdx)
    for child in children do result := binderPositions child result
    return result

/-- What the reader knows about where the selection's locals were bound. -/
structure BinderOrigins where
  variableRanges : Array (Nat × Nat) := #[]
  binders : Std.HashMap FVarId (Array Nat) := {}
  /-- The environment after the whole buffer was processed, which holds the enclosing declaration if Lean added it. -/
  finalEnv : Option Environment := none

/-- A section variable: a local whose every binder record lies in a `variable` command. A local Lean recorded nowhere,
or anywhere else, is not one as far as the reader can tell, and is drawn as before. -/
def BinderOrigins.isSectionVariable (origins : BinderOrigins) (decl : LocalDecl) : Bool :=
  match origins.binders.get? decl.fvarId with
  | some positions => !decl.isImplementationDetail && !positions.isEmpty &&
      positions.all fun position => origins.variableRanges.any fun (start, stop) => start ≤ position && position < stop
  | none => false

/-- Whether `type` opens with one binder for each of `pre`, in order, each with that local's user name, binder
annotation and type, and then continues with a binder for `next` in the same way, or, without `next`, is exactly `rest`. -/
def opensWith (type : Expr) (pre : Array LocalDecl) (next : Option LocalDecl) (rest : Expr) : Bool := Id.run do
  let mut current := type
  let mut fvars : Array Expr := #[]
  for decl in pre do
    let .forallE name domain body info := current | return false
    unless name == decl.userName && info == decl.binderInfo && domain.instantiateRev fvars == decl.type do return false
    fvars := fvars.push (.fvar decl.fvarId)
    current := body
  match next with
  | some decl =>
    let .forallE name domain _ info := current | return false
    return name == decl.userName && info == decl.binderInfo && domain.instantiateRev fvars == decl.type
  | none => return current.instantiateRev fvars == rest

/-- How `sectionVariables` decided which section variables are drawn, and what it could not decide. -/
structure SectionVariableReport where
  check : String
  /-- Each section variable left out of the drawing, with its reason: `not-taken` or `undetermined`. -/
  omitted : Array (LocalDecl × String) := #[]
  /-- Locals that are drawn although the test did not confirm that the declaration takes them: an unnamed instance
  variable, or a section variable that only such a local mentions. Empty after `matched`. -/
  unconfirmed : Array LocalDecl := #[]

/-- Which section variables in the selection's context the enclosing declaration takes, so that one it does not take
is never drawn as one of its assumptions. Returns how this was decided, each section variable left out of the drawing
with its reason, and each local that is drawn without the test confirming it.

Lean 4.28.0's rule (`Elab/MutualDef.lean`, `withHeaderSecVars` and `withUsed`): a theorem takes the section variables
its header mentions, those named by `include`, every variable a taken one mentions, and each instance-implicit variable
whose type mentions only taken variables, less those named by `omit`; any other declaration takes the variables its
header or its value mentions, with every variable they mention. The `include` and `omit` sets and the section's
variable map are not saved after elaboration, so the rule is not recomputed here. Instead:

* A local Lean recorded nowhere that sits among the section variables, such as an unnamed instance variable, is in
  doubt like a section variable. With no named section variable in scope it counts only when a `variable` command
  ends before the selection starts.
* One that the selected term, its statement or another drawn local mentions, directly or through the types of such
  locals, is taken under either rule, and is drawn. When every one in doubt is mentioned, the check is `mentioned`.
* For the others, every choice of which of them the declaration takes is tested against the declaration's final
  type in the processed environment. That type must open with the drawn locals that precede the first local Lean
  recorded inside the declaration, in order, followed by that local; with no such local, it must be exactly the
  selected statement after them. When exactly one choice passes (`matched`), the ones it leaves out are reported as
  `not-taken` and the ones it keeps are drawn. Otherwise (`mismatch`), or with no declaration of this buffer in the
  environment (`no-declaration`: an `example`, a `#check`, a declaration that failed, or one whose name is an
  imported constant's), or with more than ten to choose among (`not-checked`, and no type is compared), the section
  variables among them are reported as `undetermined` and left out, and the other ones are drawn and reported as
  `unconfirmed`.
* `none-in-scope` means that nothing is in doubt.

Neither `not-taken` nor `undetermined` is drawn, as an assumption or as a parameter; both are listed apart with their
reason. -/
def sectionVariables (locals : Array LocalDecl) (term statement : Expr) (declaration : Option Name) (selectionStart : Nat)
    (origins : BinderOrigins) : SectionVariableReport := Id.run do
  let candidates := locals.filter origins.isSectionVariable
  let isCandidate (decl : LocalDecl) := candidates.any (·.fvarId == decl.fvarId)
  let ordinary := locals.filter (!·.isImplementationDetail)
  -- The first local Lean recorded inside the declaration: its first own binder, or the first one its body introduced.
  let next := ordinary.find? fun decl => !isCandidate decl && origins.binders.contains decl.fvarId
  let before (decl : LocalDecl) := next.all fun first => decl.index < first.index
  -- A local Lean recorded nowhere that sits among the section variables, such as an unnamed instance variable. It is
  -- drawn unless the declaration's type shows that it is not taken, and reported when that was not shown.
  let unrecorded := if candidates.isEmpty && !origins.variableRanges.any (·.2 ≤ selectionStart) then #[]
    else ordinary.filter fun decl => !origins.binders.contains decl.fvarId && before decl
  if candidates.isEmpty && unrecorded.isEmpty then return { check := "none-in-scope" }
  let isUnrecorded (decl : LocalDecl) := unrecorded.any (·.fvarId == decl.fvarId)
  -- What must be drawn because something drawn mentions it. A local's type mentions only earlier locals, so one pass
  -- from the newest closes the set.
  let mentioned (open? : LocalDecl → Bool) : CollectFVars.State := Id.run do
    let mut needed : CollectFVars.State := collectFVars (collectFVars {} term) statement
    for decl in locals do
      if !open? decl then needed := collectFVars needed decl.type
    for decl in locals.reverse do
      if needed.fvarSet.contains decl.fvarId then needed := collectFVars needed decl.type
    return needed
  -- A section variable that an unrecorded local mentions is drawn whenever that local is.
  let kept := mentioned isCandidate
  let undecided := candidates.filter fun decl => !kept.fvarSet.contains decl.fvarId
  let strict := mentioned fun decl => isCandidate decl || isUnrecorded decl
  let choices := ordinary.filter fun decl => (isCandidate decl || isUnrecorded decl) && !strict.fvarSet.contains decl.fvarId
  if choices.isEmpty then return { check := "mentioned" }
  let undetermined : SectionVariableReport :=
    { check := "", omitted := undecided.map (·, "undetermined")
      unconfirmed := choices.filter fun decl => !undecided.any (·.fvarId == decl.fvarId) }
  -- Only a declaration this buffer added is compared: a failed one may share its name with an imported constant.
  let some info := (do
      let name ← declaration
      let env ← origins.finalEnv
      guard (env.getModuleIdxFor? name).isNone
      env.find? name) | return { undetermined with check := "no-declaration" }
  if choices.size > 10 then return { undetermined with check := "not-checked" }
  let mut passing : Array (Array LocalDecl) := #[]
  for choice in [0:2 ^ choices.size] do
    let chosen := (choices.zipIdx.filter fun (_, bit) => (choice >>> bit) % 2 == 1).map (·.1)
    let drawn (decl : LocalDecl) := !choices.any (·.fvarId == decl.fvarId) || chosen.any (·.fvarId == decl.fvarId)
    let pre := ordinary.filter fun decl => drawn decl && before decl
    if opensWith info.type pre next statement then passing := passing.push chosen
  let [chosen] := passing.toList | return { undetermined with check := "mismatch" }
  return { check := "matched", omitted := (choices.filter fun decl => !chosen.any (·.fvarId == decl.fvarId)).map (·, "not-taken") }

/-- `text` cut to at most `limit` characters, the last of them an ellipsis when it was cut, so that the reader's
limits on a section-variable entry never refuse the record. -/
def boundedText (text : String) (limit : Nat) : String :=
  if text.length ≤ limit then text else (text.take (limit - 1)).toString ++ "…"

/-- How Lean's elaborator classifies a selected term: a proposition, a proof of
one, or neither. This is `Meta.isProp`, not a kernel check. A term whose
classification fails is reported as neither. -/
def selectionClass (candidate : Candidate) : IO String :=
  try candidate.term.runMetaM candidate.context do
    let e ← instantiateMVars candidate.term.expr
    if ← isProp e then pure "proposition"
    else if ← isProp (← inferType e) then pure "proof"
    else pure "other"
  catch _ => pure "other"

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

def exportCandidate (candidate : Candidate) (source : String) (fileName : String) (request : Json) (origins : BinderOrigins := {}) : IO Json := do
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
      -- The guided reading draws the statement, so only the statement is checked here. A selected proof is checked by
      -- the source snapshot's own declaration, under its heartbeat bound, and not here, where no bound would apply.
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
      -- A section variable the enclosing declaration does not take is not one of its assumptions: it is listed apart.
      -- Only a host that shows that list asks for it; for any other host nothing is left out of the drawing.
      let mut sectionJson : List (String × Json) := []
      if (request.getObjValAs? Bool "sectionVariableReport").toOption == some true then
        let sections := sectionVariables locals original expression candidate.context.parentDecl? candidate.startByte origins
        locals := locals.filter fun decl => !sections.omitted.any (·.1.fvarId == decl.fvarId)
        let entry (decl : LocalDecl) : MetaM (List (String × Json)) := do
          pure [("name", str (boundedText (binderName decl.userName) 512)), ("type", str (boundedText (← pp decl.type) 4096))]
        let mut omittedJson := #[]
        for (decl, reason) in sections.omitted do
          omittedJson := omittedJson.push (obj ((← entry decl) ++ [("reason", str reason)]))
        let mut unconfirmedJson := #[]
        for decl in sections.unconfirmed do
          unconfirmedJson := unconfirmedJson.push (obj (← entry decl))
        sectionJson := [("sectionVariables", obj [("check", str sections.check), ("omitted", Json.arr omittedJson),
          ("unconfirmed", Json.arr unconfirmedJson)])]
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
        ("provenance", obj ([("assistant", str "lean"), ("inputMode", str "editor"),
          ("inspected", str "context-fragment"), ("fileName", str fileName),
          ("selectionKind", str (if proof then "proof-type" else "proposition")),
          ("startByte", toJson candidate.startByte), ("endByte", toJson candidate.endByte),
          ("requestedStartByte", (request.getObjVal? "startByte").toOption.getD Json.null),
          ("requestedEndByte", (request.getObjVal? "endByte").toOption.getD Json.null),
          ("parentDeclaration", candidate.context.parentDecl?.map (str ∘ Name.toString) |>.getD Json.null),
          ("contextParameters", toJson ordinaryLocals.size),
          ("auxiliaryContextEntries", toJson (locals.size - ordinaryLocals.size)),
          ("localLetBindings", str "substituted-definitionally")] ++ sectionJson)),
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
  let trees := infoState.trees.toArray.map (·.substitute infoState.assignment)
  let mut found := #[]
  for (tree, index) in trees.zipIdx do
    found := candidates tree none start stop found index
  let ordered := orderCandidates found
  let mut selected : Option (Candidate × String) := none
  for candidate in ordered do
    let classification ← selectionClass candidate
    if classification != "other" then
      selected := some (candidate, classification)
      break
  -- Keep all previous proposition choices. If none is eligible, the smallest
  -- available term may still have an inspectable raw snapshot; guided export
  -- reports its own boundary without discarding that term.
  let some (chosen, chosenClass) := selected.orElse (fun _ => ordered[0]?.map (·, "other")) |
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
  let (decomposition, decompositionFailure, presentation) ← match (request.getObjVal? "decomposition").toOption with
    | none => pure (none, none, none)
    | some decompositionRequest => match snapshot with
      | none => pure (none, some "A fresh source snapshot is unavailable; decomposition checking did not begin.", none)
      | some fresh => do
        try
          let (value, presentation) ← SourceSnapshot.captureDecomposition chosen.term chosen.context captureId {
            startByte := chosen.startByte, endByte := chosen.endByte,
            requestedStartByte := start, requestedEndByte := stop
          } decompositionRequest fresh
          pure (some value, none, some presentation)
        catch error => pure (none, some ((error.toString.take 4096).toString), none)
  let variableRanges := trees.foldl (fun ranges tree => variableCommandRanges tree ranges) #[]
  let binders := match trees[chosen.tree]? with
    | some tree => binderPositions tree
    | none => {}
  let origins : BinderOrigins := { variableRanges, binders, finalEnv := some state.commandState.env }
  let result ← try exportCandidate chosen source fileName request origins catch error =>
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
  -- The class belongs to the chosen term, not to the guided reading: it is
  -- reported whether or not the guided export succeeded.
  let mut result := result.setObjVal! "diagnostics" (Json.arr diagnostics)
    |>.setObjVal! "guidedContextContract" (str guidedContextContract)
    |>.setObjVal! "selectionClass" (str chosenClass)
  if let some occurrence := occurrence then result := result.setObjVal! "sourceOccurrence" occurrence
  if let some reason := occurrenceFailure then result := result.setObjVal! "sourceOccurrenceUnavailable" (str reason)
  if let some value := headExposure then result := result.setObjVal! "sourceHeadExposure" value
  if let some reason := headExposureFailure then result := result.setObjVal! "sourceHeadExposureUnavailable" (str reason)
  if let some value := decomposition then result := result.setObjVal! "sourceDecomposition" value
  if let some value := presentation then result := result.setObjVal! "sourceDecompositionPresentation" value
  if let some reason := decompositionFailure then result := result.setObjVal! "sourceDecompositionUnavailable" (str reason)
  if let some snapshot := snapshot then return result.setObjVal! "sourceSnapshot" snapshot
  if let some reason := captureFailure then return result.setObjVal! "sourceSnapshotUnavailable" (str reason)
  return result

/-- Preserve the existing 2 MiB guided-export policy independently of the bounded
snapshot. In particular, optional legacy trimming must never enter raw source
records or diagnostic declarations and delete a constructor field by its name.
The selection class is appended the same way, so it also survives a guided
reading that is replaced for exceeding that limit. -/
def serializeContextResponse (result : Json) : String := Id.run do
  let selectionClass := (result.getObjVal? "selectionClass").toOption
  let snapshot := (result.getObjVal? "sourceSnapshot").toOption
  let unavailable := (result.getObjVal? "sourceSnapshotUnavailable").toOption
  let occurrence := (result.getObjVal? "sourceOccurrence").toOption
  let occurrenceUnavailable := (result.getObjVal? "sourceOccurrenceUnavailable").toOption
  let headExposure := (result.getObjVal? "sourceHeadExposure").toOption
  let headExposureUnavailable := (result.getObjVal? "sourceHeadExposureUnavailable").toOption
  let decomposition := (result.getObjVal? "sourceDecomposition").toOption
  let decompositionUnavailable := (result.getObjVal? "sourceDecompositionUnavailable").toOption
  let presentation := (result.getObjVal? "sourceDecompositionPresentation").toOption
  let legacy := match result.getObj? with
    | .ok fields => Json.mkObj (fields.toList.filter fun (key, _) =>
      !["selectionClass", "sourceSnapshot", "sourceSnapshotUnavailable", "sourceOccurrence", "sourceOccurrenceUnavailable",
        "sourceHeadExposure", "sourceHeadExposureUnavailable", "sourceDecomposition", "sourceDecompositionUnavailable",
        "sourceDecompositionPresentation"].contains key)
    | .error _ => result
  let serialized := Response.serializeResponse legacy
  let legacyText := if serialized.utf8ByteSize > 2097152 then
    (obj [("ok", toJson false), ("error", str "The selected context exceeds the 2 MiB export limit."),
      ("diagnostics", Json.arr #[])]).compress else serialized
  let append := fun (text key : String) (value : Json) =>
    (text.dropEnd 1).toString ++ "," ++ (str key).compress ++ ":" ++ value.compress ++ "}"
  let classText := match selectionClass with
    | some value => append legacyText "selectionClass" value
    | none => legacyText
  let snapshotText := match snapshot with
    | some value => append classText "sourceSnapshot" value
    | none => match unavailable with
      | some reason => append classText "sourceSnapshotUnavailable" reason
      | none => classText
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
    if complete.utf8ByteSize ≤ 4 * 1024 * 1024 then
      if let some sidecar := presentation then
        let withPresentation := append complete "sourceDecompositionPresentation" sidecar
        if withPresentation.utf8ByteSize ≤ 4 * 1024 * 1024 then return withPresentation
        -- Optional display must never displace the exact checking history.
        let captureId := (value.getObjValAs? String "captureId").toOption.getD ""
        let omitted := append complete "sourceDecompositionPresentation" (SourceSnapshot.presentationUnavailable captureId
          "Native notation is omitted because the complete response exceeds its transport limit.")
        if omitted.utf8ByteSize ≤ 4 * 1024 * 1024 then return omitted
      return complete
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
