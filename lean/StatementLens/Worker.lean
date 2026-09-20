import Lean
import StatementLens.Response
import StatementLens.Export

/- StatementLens never loads source files supplied by clients. The only user-controlled
   input is parsed as one term, checked against a closed syntax allowlist, elaborated
   as Prop, and independently checked by Lean's kernel. No declaration is added. -/
open Lean Meta Elab Term

namespace StatementLens

def imports : Array Import := #[
  { module := `StatementLens.ReadableMath },
  { module := `Mathlib.Topology.MetricSpace.Basic },
  { module := `Mathlib.Analysis.InnerProductSpace.PiL2 }
]

def analyze (source : String) (request : Json) (renderNotation : Expr → MetaM Json) : TermElabM Json := withoutErrToSorry do
  let env ← getEnv
  let policy ← readPolicy request
  let inputMode ← match request.getObjValAs? String "inputMode" with
    | .ok mode => pure mode
    | .error _ => if (request.getObjVal? "inputMode").isOk then throwError "inputMode must be a string." else pure "term"
  unless inputMode == "term" || inputMode == "declaration" do throwError "inputMode must be term or declaration."
  let stx ← match Parser.runParserCategory env `term source "<statement>" with
    | .ok s => pure s
    | .error err => throwError "{err}"
  let mut declaration := Json.null
  let mut definitionExpression := Json.null
  let mut definitionMathExpression : Option Expr := none
  let mut definitionTree := Json.null
  let mut definitionBodyStatus := "not-a-definition"
  let mut inspected := "statement"
  let expression ← if inputMode == "declaration" then do
      unless stx.isIdent do throwError "Declaration mode expects one exact imported declaration name."
      let name := stx.getId
      let some info := env.find? name | throwError "Unknown imported declaration: {name}"
      if info.isUnsafe || info.isPartial then throwError "Unsafe and partial declarations are not inspected."
      declaration ← declarationJson info
      if info.isDefinition then
        let body := info.value!
        if body.approxDepth <= 80 && body.sizeWithoutSharing <= 1500 then
          checkWithKernel body
          definitionMathExpression := some body
          definitionTree ← tree body #[] "definition" policy
          definitionExpression := expressionOf definitionTree
          definitionBodyStatus := "available"
        else definitionBodyStatus := "export-size-limit"
      if info.isDefinition && info.type == mkSort levelZero then
        inspected := "proposition-definition"
        pure (Lean.mkConst name (info.levelParams.map Level.param))
      else
        inspected := if (← isProp info.type) then "statement" else "signature"
        pure info.type
    else do
      match validateSyntax stx with
      | .error err => throwError "{err}"
      | .ok _ => pure ()
      let e ← elabTermEnsuringType stx (some (mkSort levelZero))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  if expression.hasMVar then throwError "Unresolved metavariables remain; provide explicit types."
  if expression.hasSorry then throwError "A placeholder or sorry remains; the statement was rejected."
  let proposition ← isProp expression
  if inputMode == "term" && !proposition then throwError "Input must be a mathematical proposition (a term of type Prop)."
  checkWithKernel expression
  let result ← tree expression #[] "n" policy
  let mut terms := #[]
  let infoState ← getInfoState
  for t in infoState.trees do terms ← sourceTerms (t.substitute infoState.assignment) terms
  let mut definitions := if (declaration.getObjValAs? Bool "canExpand").toOption.getD false then #[declaration] else #[]
  for name in expression.getUsedConstants do
    if definitions.size >= 128 then break
    if let some info := env.find? name then
      if info.isDefinition && !info.isUnsafe && !info.isPartial then
        let entry ← declarationJson info
        if !definitions.contains entry then definitions := definitions.push entry
  -- Finish every required semantic operation before invoking optional presentation code.
  let pretty ← pp expression
  let printedType ← pp (← inferType expression)
  let originalExpression ← encode expression #[] "original"
  let readableMath ← renderNotation expression
  let definitionReadableMath ← match definitionMathExpression with
    | some body => renderNotation body
    | none => pure (obj [("provider", toJson "leantex"), ("status", toJson "unavailable"),
      ("reason", toJson "No bounded definition body is available for notation printing.")])
  return obj [
    ("ok", toJson true), ("schemaVersion", toJson (2 : Nat)),
    ("leanVersion", str Lean.versionString), ("source", str source),
    ("pretty", str pretty), ("type", str printedType),
    ("validation", str (if proposition then "kernel-type-checked-statement" else "kernel-type-checked-declaration-type")),
    ("provenance", obj [("assistant", str "lean"), ("inputMode", str inputMode), ("inspected", str inspected),
      ("declaration", declaration), ("mathlibRevision", str "8f9d9cff6bd728b17a24e163c9402775d9e6a365")]),
    ("expansionPolicy", obj [("constants", toJson (policy.constants.map Name.toString)), ("maxDepth", toJson policy.maxDepth)]),
    ("definitions", Json.arr definitions), ("sourceTerms", Json.arr terms),
    ("definitionExpression", definitionExpression), ("definitionTree", definitionTree),
    ("definitionBodyStatus", str definitionBodyStatus),
    ("readableMath", readableMath), ("definitionReadableMath", definitionReadableMath),
    ("tree", result), ("expression", expressionOf result), ("originalExpression", originalExpression),
    ("metrics", Json.arr #[]), ("diagnostics", Json.arr #[])]

def errorResult (message : String) : Json := obj [("ok", toJson false), ("schemaVersion", toJson (2 : Nat)), ("error", str message),
  ("diagnostics", Json.arr #[obj [("severity", str "error"), ("message", str message)]])]

unsafe def main : IO Unit := do
  let sysroot ← match ← IO.getEnv "STATEMENTLENS_LEAN_SYSROOT" with
    | some p => pure (System.FilePath.mk p)
    | none => findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  let opts := ({} : Options).set `maxRecDepth (256 : Nat) |>.set `maxHeartbeats (400000 : Nat) |>.set `autoImplicit false
  let env ← importModules imports opts 0 (loadExts := true)
  -- This exact, trusted declaration is the only optional printer entry point.
  -- User expressions are data; no client-selected declaration is evaluated as code.
  let renderNotation := (env.evalConst (Expr → MetaM Json) opts
    `StatementLens.ReadableMath.render).toOption.getD (fun _ => pure
      (Response.unavailable "The optional notation printer could not initialize."))
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let requestId := ((Json.parse line).toOption.bind fun request => (request.getObjVal? "requestId").toOption).getD Json.null
    let result ← try
      let request ← IO.ofExcept (Json.parse line)
      let source ← IO.ofExcept (request.getObjValAs? String "source")
      if source.utf8ByteSize > 65536 then throw (IO.userError "Statement exceeds 65536 bytes.")
      let action := MetaM.run' (TermElabM.run' (analyze source request renderNotation))
      Core.CoreM.toIO' action { fileName := "<statement>", fileMap := FileMap.ofString source, options := opts } { env }
    catch err => pure (errorResult err.toString)
    let result := if requestId == Json.null then result else result.setObjVal! "requestId" requestId
    stdout.putStrLn (Response.serializeResponse result)
    stdout.flush

end StatementLens

unsafe def main : IO Unit := StatementLens.main
