import Lean
import StatementLens.Export
import StatementLens.Response

/- A trusted-project adapter, deliberately separate from the closed-term worker.
   The native exporter is not imported into the project's elaboration environment. -/
open Lean Meta Elab
namespace StatementLens.Context

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
  let assumption ← isProp ty
  let b : Bound := ⟨localDecl.fvarId, path ++ ".binder", binderName localDecl.userName, ← pp ty,
    if assumption then "assumption" else "parameter"⟩
  let bj ← binderJson b ty bs
  let body ← contextTree locals (index + 1) expression (bs.push b) (path ++ ".body") policy
  let premise ← if assumption then pure #[← tree ty bs (path ++ ".premise") policy] else pure #[]
  let expr := obj [("kind", str (if assumption then "forall" else "lambda")), ("binder", bj),
    ("binderType", ← encode ty bs (path ++ ".type")), ("body", expressionOf body)]
  return (node path (if assumption then "implies" else "parameter")
    (if assumption then s!"Assume {b.name}" else s!"Context parameter {b.name}")
    b.type (premise.push body) expr (some bj)).setObjVal! "scope" (toJson (bs.map (·.id)))

def exportCandidate (candidate : Candidate) (source : String) (fileName : String) (request : Json) : IO Json := do
  candidate.term.runMetaM candidate.context <| withOptions (fun opts =>
    opts.set `statementLens.projectContext true |>.set `maxRecDepth (256 : Nat) |>.set `maxHeartbeats (400000 : Nat)) do
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
      if !localDecl.isLet then locals := locals.push localDecl
    if locals.size > 128 then throwError "The selected local context exceeds 128 declarations."
    let policy ← readPolicy request
    let result ← contextTree locals 0 expression #[] "context" policy
    let pretty ← pp expression
    let type ← pp (← inferType expression)
    let mut definitions := #[]
    for name in expression.getUsedConstants do
      if definitions.size >= 128 then break
      if let some info := (← getEnv).find? name then
        if info.isDefinition && !info.isUnsafe && !info.isPartial then
          definitions := definitions.push (← declarationJson info)
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
        ("contextParameters", toJson locals.size), ("localLetBindings", str "substituted-definitionally")]),
      ("expansionPolicy", obj [("constants", toJson (policy.constants.map Name.toString)), ("maxDepth", toJson policy.maxDepth)]),
      ("definitions", Json.arr definitions), ("tree", result), ("expression", expressionOf result),
      ("sourceTerms", Json.arr #[obj [("startByte", toJson candidate.startByte), ("endByte", toJson candidate.endByte),
        ("lean", str pretty), ("type", str type), ("isBinder", toJson false), ("origin", str "lean-infotree")]]),
      ("metrics", Json.arr #[]), ("diagnostics", Json.arr #[])]

unsafe def analyze (request : Json) : IO Json := do
  let source ← IO.ofExcept (request.getObjValAs? String "source")
  let fileName ← IO.ofExcept (request.getObjValAs? String "fileName")
  let start ← IO.ofExcept (request.getObjValAs? Nat "startByte")
  let stop ← IO.ofExcept (request.getObjValAs? Nat "endByte")
  if source.utf8ByteSize > 524288 || start > stop || stop > source.utf8ByteSize then
    throw (IO.userError "Invalid source buffer or byte selection (maximum 512 KiB).")
  let opts := ({} : Options).set `maxRecDepth (512 : Nat) |>.set `maxHeartbeats (800000 : Nat)
    |>.set `Elab.async false
  let mainModule := ((request.getObjValAs? String "mainModule").toOption.getD "StatementLensEditorBuffer").toName
  let input := Parser.mkInputContext source fileName
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
  let some chosen := selected | throw (IO.userError "No elaborated proposition at this selection. Select a complete statement or proposition in the Lean source.")
  -- Do not fall back from an invalid selected proposition to a larger unrelated one.
  let result ← exportCandidate chosen source fileName request
  let mut diagnostics := #[]
  for msg in state.commandState.messages.toList do
    if diagnostics.size >= 100 then break
    let message := (← msg.data.toString).take 4096 |>.toString
    let severity := match msg.severity with | .error => "error" | .warning => "warning" | .information => "information"
    diagnostics := diagnostics.push (obj [("severity", str severity), ("message", str message),
      ("line", toJson msg.pos.line), ("column", toJson msg.pos.column)])
  return result.setObjVal! "diagnostics" (Json.arr diagnostics)

unsafe def run : IO Unit := do
  let sysroot ← match ← IO.getEnv "STATEMENTLENS_LEAN_SYSROOT" with
    | some p => pure (System.FilePath.mk p)
    | none => findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  let input ← (← IO.getStdin).getLine
  let result ← try analyze (← IO.ofExcept (Json.parse input)) catch error =>
    pure (obj [("ok", toJson false), ("error", str error.toString), ("diagnostics", Json.arr #[])])
  -- Project commands may write stdout. A private one-shot result file keeps their
  -- output out of the protocol; Node still bounds stdout/stderr separately.
  let some resultFile ← IO.getEnv "STATEMENTLENS_CONTEXT_RESULT" |
    throw (IO.userError "The context result path is missing.")
  let output := Response.serializeResponse result
  let output := if output.utf8ByteSize > 2097152 then
    "{\"ok\":false,\"error\":\"The selected context exceeds the 2 MiB export limit.\",\"diagnostics\":[]}" else output
  IO.FS.writeFile resultFile output

end StatementLens.Context
unsafe def main : IO Unit := StatementLens.Context.run
